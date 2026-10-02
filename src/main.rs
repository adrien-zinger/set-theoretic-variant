// TODO:
//
// Language server rust-analyzer:
//
// Workspace `/home/azinger/Documents/projects/hindley_milner_rs/Cargo.toml` has sysroot errors: can't load standard library from sysroot
// /nix/store/nwsrya1c3y3dzgacw1x79y85989i63s0-rustc-1.95.0
// (discovered via `rustc --print sysroot`)
// try installing `rust-src` the same way you installed `rustc`
//
// rustup add rust-src

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT_TYPE_VAR: AtomicUsize = AtomicUsize::new(0);

type Id = String;
type TypePtr = Rc<RefCell<Type>>;

/* DATASTRUCTURES */

#[derive(Debug, PartialEq, Clone)]
struct TypeVar {
    name: String,
}

#[derive(Debug, PartialEq, Clone)]
struct TypeCon {
    name: String,
    args: Vec<TypePtr>,
}

#[derive(Debug, Clone, PartialEq)]
enum Type {
    Var(TypeVar), // TyVar("a"), because a is associated to the variable but unconstrained :)
    Con(TypeCon), // TyCon("list", [TyVar("a")]) | TyCon("list", [TyCon("int", [])]) | TyCon("int", [])

    /* Variant type */
    Variant(String, TypePtr),

    /* semantic-subtyping things */
    Union(TypePtr, TypePtr),
    Intersection(TypePtr, TypePtr),
    Negation(TypePtr),
    Bottom,

    /* Generalization */
    Scheme(Scheme),
}

#[derive(Debug, Clone, PartialEq)]
struct Scheme {
    for_all: Vec<TypePtr>,
    ty: TypePtr,
}

impl From<TypeVar> for Type {
    fn from(var: TypeVar) -> Self {
        Type::Var(var)
    }
}

impl From<&TypeVar> for Type {
    fn from(var: &TypeVar) -> Self {
        Type::Var(var.clone())
    }
}

impl From<Type> for TypePtr {
    fn from(ty: Type) -> Self {
        Rc::new(RefCell::new(ty))
    }
}

impl From<TypeCon> for Type {
    fn from(con: TypeCon) -> Self {
        Type::Con(con)
    }
}

impl Type {
    fn find(&self, env: &TypeEnv) -> TypePtr {
        match self {
            Type::Var(var) => {
                if let Some(ty) = env.get_substitution(var) {
                    ty.resolve(env)
                } else {
                    self.clone().into()
                }
            }
            Type::Con(con) => Type::con_with_args(
                &con.name,
                con.args.iter().map(|arg| arg.resolve(env)).collect(),
            ),
            Type::Scheme(scheme) => Type::scheme(scheme.for_all.clone(), scheme.ty.resolve(env)),
            Type::Variant(tag, payload) => Type::variant(tag, payload.resolve(env)),
            Type::Union(a, b) => Type::union(a.resolve(env), b.resolve(env)),
            Type::Intersection(a, b) => Type::intersection(a.resolve(env), b.resolve(env)),
            Type::Negation(ty) => Type::negation(ty.resolve(env)),
            Type::Bottom => Type::bottom(),
        }
    }

    fn var(name: &str) -> TypePtr {
        Type::Var(TypeVar { name: name.into() }).into()
    }

    fn con(name: &str) -> TypePtr {
        Self::con_with_args(name, vec![])
    }

    fn con_with_args(name: &str, args: Vec<TypePtr>) -> TypePtr {
        Type::Con(TypeCon {
            name: name.into(),
            args,
        })
        .into()
    }

    fn scheme(for_all: Vec<TypePtr>, ty: TypePtr) -> TypePtr {
        Type::Scheme(Scheme { for_all, ty }).into()
    }

    fn variant(name: &str, ty: TypePtr) -> TypePtr {
        Type::Variant(name.to_string(), ty).into()
    }

    fn union(a: TypePtr, b: TypePtr) -> TypePtr {
        Type::Union(a, b).into()
    }

    fn intersection(a: TypePtr, b: TypePtr) -> TypePtr {
        Type::Intersection(a, b).into()
    }

    fn negation(ty: TypePtr) -> TypePtr {
        Type::Negation(ty).into()
    }

    fn bottom() -> TypePtr {
        Type::Bottom.into()
    }

    fn top() -> TypePtr {
        Type::negation(Type::bottom())
    }

    /// Set-theoretic type difference:
    /// A \ B = A ∩ ¬B
    fn difference(a: TypePtr, b: TypePtr) -> TypePtr {
        Type::intersection(a, Type::negation(b))
    }

    fn function(argument: TypePtr, result: TypePtr) -> TypePtr {
        Self::con_with_args("->", vec![argument, result])
    }

    // A variant carrying an impossible payload is itself empty.
    fn variant_or_bottom(tag: &str, payload: TypePtr) -> TypePtr {
        if payload.is_bottom() {
            Type::bottom()
        } else {
            Type::variant(tag, payload)
        }
    }
}

/* TYPE OPERATIONS */

/// Operations on shared type pointers. An extension trait keeps the
/// Rc<RefCell<Type>> representation while allowing method syntax.
trait TypePtrExt {
    fn resolve(&self, env: &TypeEnv) -> TypePtr;
    fn same(&self, other: &TypePtr) -> bool;
    fn is_bottom(&self) -> bool;
    fn is_top(&self) -> bool;
    fn is_open_variant(&self, tag: &str) -> bool;
    fn join(self, other: TypePtr) -> TypePtr;
    fn meet(self, other: TypePtr) -> TypePtr;
    fn subtract(self, other: TypePtr) -> TypePtr;
    fn normalize(self) -> TypePtr;
    fn generalize(&self) -> Type;
    fn instantiate(&self) -> Type;
}

impl TypePtrExt for TypePtr {
    /// Binds with `find`
    fn resolve(&self, env: &TypeEnv) -> TypePtr {
        self.borrow().find(env)
    }

    fn same(&self, b: &TypePtr) -> bool {
        *self.borrow() == *b.borrow()
    }

    fn is_bottom(&self) -> bool {
        matches!(&*self.borrow(), Type::Bottom)
    }

    fn is_top(&self) -> bool {
        match &*self.borrow() {
            Type::Negation(x) => x.is_bottom(),
            _ => false,
        }
    }

    ///  Helper to check if a type is an open variant (a variant with an inner type
    ///  that can be anything. It occurs when:
    ///  fn unwrap(x) {
    ///      match x {
    ///          'A(v) => v     // here, the type of x ɑ is a subtype of 'A(Top)
    ///      }
    ///  }
    fn is_open_variant(&self, tag: &str) -> bool {
        match &*self.borrow() {
            Type::Variant(name, payload) => name == tag && payload.is_top(),

            _ => false,
        }
    }

    /// See meet-join algorithm. That methods creates the join of
    /// two set-theoretical types.
    fn join(self, b: TypePtr) -> TypePtr {
        let a = self;
        // When one is everything, return everything.
        if a.is_top() {
            return a;
        } else if b.is_top() {
            return b;
        }

        // When one is nothing, return the other
        if a.is_bottom() {
            return b;
        } else if b.is_bottom() {
            return a;
        }

        // If both are the same, it doesn't matter, return one of them
        if a.same(&b) {
            return a;
        }

        // in any other case, return the union
        Type::union(a, b)
    }

    /// See meet-join algorithm. That methods creates the meet of two
    /// set theoretical types (union, bottom, variants, etc...)
    fn meet(self, b: TypePtr) -> TypePtr {
        let a = self;
        // if both are bottom, the meet of them is also a bottom
        if a.is_bottom() || b.is_bottom() {
            return Type::bottom();
        }

        // If "a" is everything, the meet (like the intersection) is b.
        // Whether b is everything or nothing too.
        if a.is_top() {
            return b;
        }

        // If "b" is everything, return a. (like the previous condition, symetricaly)
        if b.is_top() {
            return a;
        }

        // If both are equals, return one of them, it doesn't matter.
        if a.same(&b) {
            return a;
        }

        // A ∩ ¬B = A \ B
        //
        // If "b" is a negation, take the excluded and substract them from "a"
        if let Type::Negation(excluded) = b.borrow().clone() {
            return a.subtract(excluded);
        }

        // Same thing but with "a"
        if let Type::Negation(excluded) = a.borrow().clone() {
            return b.subtract(excluded);
        }

        // (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C)
        if let Type::Union(l, r) = a.borrow().clone() {
            return l.meet(b.clone()).join(r.meet(b));
        }

        if let Type::Union(l, r) = b.borrow().clone() {
            return a.clone().meet(l).join(a.meet(r));
        }

        // Different variant tags are disjoint.
        if let (Type::Variant(ta, pa), Type::Variant(tb, pb)) = (&*a.borrow(), &*b.borrow()) {
            return if ta == tb {
                Type::variant_or_bottom(ta, pa.clone().meet(pb.clone()))
            } else {
                // Not the same variant. But should I meet pa and pb in that case?
                Type::bottom()
            };
        }

        // Unknown case: retain the symbolic intersection.
        Type::intersection(a, b)
    }

    // Let's say t1 = 'A(u32) V 'B(bool)
    // and t2 = 'A(_).
    // so t1 \ t2 = 'B(bool), ok?
    fn subtract(self, b: TypePtr) -> TypePtr {
        let a = self;
        if a.is_bottom() || b.is_top() || a.same(&b) {
            return Type::bottom();
        }

        if b.is_bottom() {
            return a;
        }

        // A \ ¬B = A ∩ B
        if let Type::Negation(x) = b.borrow().clone() {
            return a.meet(x);
        }

        // (A ∪ B) \ C
        if let Type::Union(l, r) = a.borrow().clone() {
            return l.subtract(b.clone()).join(r.subtract(b));
        }

        // A \ (B ∪ C)
        if let Type::Union(l, r) = b.borrow().clone() {
            return a.subtract(l).subtract(r);
        }

        // (A ∩ B) \ C = (A \ C) ∩ B
        if let Type::Intersection(l, r) = a.borrow().clone() {
            return l.subtract(b).meet(r);
        }

        // Variant-specific difference.
        if let (Type::Variant(ta, pa), Type::Variant(tb, pb)) = (&*a.borrow(), &*b.borrow()) {
            return if ta == tb {
                Type::variant_or_bottom(ta, pa.clone().subtract(pb.clone()))
            } else {
                a.clone()
            };
        }

        // Top \ B = ¬B
        if a.is_top() {
            return Type::negation(b);
        }

        // Cannot simplify further.
        Type::difference(a, b)
    }

    fn normalize(self) -> TypePtr {
        let current = self.borrow().clone();

        match current {
            // union case, normalize a and b and join them.
            Type::Union(a, b) => a.normalize().join(b.normalize()),
            // Intersection case, normalize a and b and meet them.
            Type::Intersection(a, b) => a.normalize().meet(b.normalize()),
            Type::Negation(x) => {
                // Let start normalize the inner type.
                let x = x.normalize();
                // apply some simplifications in case we have:
                // 1. negation of nothing (it gives everything instead)
                // 2. negation of negation. (it gives just the inner type ¬¬A = A)
                let inner = x.borrow().clone();
                match inner {
                    Type::Bottom => Type::top(),
                    Type::Negation(y) => y,
                    _ => Type::negation(x),
                }
            }
            // return the normalized variant type
            Type::Variant(tag, payload) => Type::variant_or_bottom(&tag, payload.normalize()),
            // first leaf, return the type (normalizing recursively its args)
            Type::Con(con) => Type::con_with_args(
                &con.name,
                con.args.into_iter().map(TypePtrExt::normalize).collect(),
            ),

            // latest leaf, other types are preserved.
            // In particular, we don't normalize under Scheme here.
            other => other.into(),
        }
    }

    fn generalize(&self) -> Type {
        let ty_inner = self.borrow();
        match &*ty_inner {
            Type::Var(_) => Type::Scheme(Scheme {
                for_all: vec![self.clone()],
                ty: self.clone(),
            }),
            Type::Con(con) => Type::Scheme(Scheme {
                for_all: con.args.clone(),
                ty: self.clone(),
            }),
            _ => ty_inner.clone(),
        }
    }

    fn instantiate(&self) -> Type {
        let ty_inner = self.borrow();
        match &*ty_inner {
            Type::Scheme(sche) => sche.ty.borrow().clone(),
            _ => ty_inner.clone(),
        }
    }
}

/* ENVIRONMENT */

#[derive(Clone, Debug)]
enum Constraint {
    Equals(TypePtr, TypePtr),
    Subtype(TypePtr, TypePtr), // todo
}

#[derive(Default, Clone, Debug)]
struct TypeEnv {
    /// a -> b
    /// b -> t0
    variables: HashMap<Id, TypePtr>,
    /// t0 -> u32
    /// t1 -> bool
    substitutions: HashMap<String, TypePtr>,
    constraints: Vec<Constraint>,
}

impl TypeEnv {
    fn get(&self, name: &str) -> Option<&TypePtr> {
        self.variables.get(name)
    }

    fn insert(&mut self, name: String, ty: TypePtr) -> Option<TypePtr> {
        self.variables.insert(name, ty)
    }

    fn substitute(&mut self, var: &TypeVar, ty: TypePtr) {
        self.substitutions.insert(var.name.clone(), ty);
    }

    fn get_substitution(&self, var: &TypeVar) -> Option<TypePtr> {
        self.substitutions.get(&var.name).cloned()
    }

    /// Create a globally fresh type variable.
    ///
    /// Relaxed ordering is enough: we only need every returned
    /// integer to be unique.
    fn fresh(&self) -> TypePtr {
        let id = NEXT_TYPE_VAR.fetch_add(1, Ordering::Relaxed);
        Type::var(&format!("t{id}"))
    }
}

/* AST AND INFERENCE */

#[derive(Debug, Clone)]
enum Kind {
    Var,
    Num,
    Assignation,
    Function,
    If,
    Apply,

    /* match case (semantic subtyping) */
    Match,
    Arm,
    Variant,
    PatternWildcard, // _ => ..
    PatternTag,      // a => ..
    PatternBind,     // A(a) => ..
}

#[derive(Debug, Clone)]
struct Node<'a> {
    lexem: &'a str,
    kind: Kind,
    children: Vec<Node<'a>>,
    r#type: RefCell<Option<TypePtr>>,
}

impl<'a> Node<'a> {
    // Small AST constructor to keep examples and tests readable.
    fn new(lexem: &'a str, kind: Kind, children: Vec<Self>) -> Self {
        Self {
            lexem,
            kind,
            children,
            r#type: RefCell::default(),
        }
    }

    fn set_type(&self, ty: TypePtr) {
        self.r#type.borrow_mut().replace(ty);
    }

    fn find(&self, env: &mut TypeEnv) -> TypePtr {
        self.get_type(env).resolve(env)
    }

    fn get_type(&self, env: &mut TypeEnv) -> TypePtr {
        if let Some(ty) = env.get(self.lexem) {
            println!("get {} from env: {:?}", self.lexem, ty);
            let ty = ty.clone();
            self.set_type(ty.clone());
            ty
        } else {
            let ty = self
                .r#type
                .borrow_mut()
                .get_or_insert_with(|| Type::var(self.lexem))
                .clone();

            env.insert(self.lexem.to_owned(), ty.clone());
            ty
        }
    }

    fn set_type_equals(&self, ty: TypePtr, env: &mut TypeEnv) {
        println!("enter: make {}'s type equals: {:?}", self.lexem, ty);

        let current = self.get_type(env);
        let current_type = current.borrow().clone();

        match current_type {
            Type::Var(var) => {
                env.substitute(&var, ty);
            }
            _ => {
                unify(current, ty, env);
            }
        }
    }

    fn infer(&self, env: &mut TypeEnv) {
        match self.kind {
            Kind::Num => self.set_type_equals(Type::con("u32"), env),
            Kind::Assignation => {
                let [left, right] = &self.children[..] else {
                    panic!("expected an assignment target and its value");
                };
                left.infer(env);
                right.infer(env);
                let left_type = left.find(env);
                let right_type = right.find(env);
                env.constraints
                    .push(Constraint::Equals(left_type, right_type));
                self.set_type_equals(Type::con("()"), env);
            }
            Kind::Var => {}
            Kind::Function => {
                let mut function_env = env.clone();

                // we need to "bind" a fresh variable in the function's env
                let arg = &self.children[0];
                let arg_type = function_env.fresh();
                arg.set_type(arg_type.clone());
                function_env.insert(arg.lexem.to_string(), arg_type.clone());

                // infer return's type (body type)
                self.children[1].infer(&mut function_env);
                let body_type = self.children[1].find(&mut function_env);

                let arg_type = arg_type.resolve(&function_env);
                let ty = Type::function(arg_type, body_type);
                self.set_type_equals(ty, env);
            }
            Kind::If => todo!(),
            Kind::Apply => {
                let [function, argument] = &self.children[..] else {
                    panic!("unexpected apply children size");
                };

                // Infer both sides independently.
                function.infer(env);
                argument.infer(env);

                let function_type = function.find(env);
                let argument_type = argument.find(env);

                let result_type = env.fresh();
                let expected_function_type = Type::function(argument_type, result_type.clone());

                env.constraints
                    .push(Constraint::Equals(function_type, expected_function_type));

                let result_type = result_type.resolve(env);
                self.set_type_equals(result_type, env);
            }
            Kind::Variant => {
                let [argument] = &self.children[..] else {
                    panic!("unexpected variant children size");
                };

                // Infer the variant payload.
                argument.infer(env);

                // Retrieve its inferred type.
                let argument_type = argument.find(env);

                // Construct the variant type: `Tag(argument_type)
                let variant_type = Type::variant(self.lexem, argument_type);

                // Store the result directly in the AST node.
                self.set_type(variant_type);
            }
            Kind::Match => self.infer_match(env),
            _ => panic!("node not managed {self:?}"),
        }
    }

    fn infer_match(&self, env: &mut TypeEnv) {
        // Get the scrutinee and the arms of expression:
        // match scrutinee {
        //    arms...
        // }
        let scrutinee = &self.children[0];
        let arms = &self.children[1..];

        scrutinee.infer(env);

        let scrutinee_ty = scrutinee.get_type(env);

        let mut covered = Type::bottom();
        let mut result = Type::bottom();

        // Pass through all arms, tracking the covered branches
        // so the select type is: actual pattern type \ covered.
        for arm in arms {
            let [pattern, body] = &arm.children[..] else {
                panic!("expected a match pattern and its body")
            };

            // retreive the type of that arm (we say that it is an accepted
            // type because we can enter into that branch)
            let accepted = pattern.accepted_type();

            // But actually, the accepted type by the branch is not the
            // "selected".

            // Let's S the type of the scrutinee, C the
            // already covered types. And finally A the one found
            // for the arm.

            // We can already tell that the selected type is in
            // S \ C. But that should be intersected
            // with A. So t_selected is: (S \ C) ∩ A
            let selected = Type::intersection(
                Type::difference(scrutinee_ty.clone(), covered.clone()),
                accepted.clone(),
            )
            .normalize();

            println!("selected: \n\n{selected:#?}\n\n");

            // Save the outer expression bindings.
            // Substitutions and constraints must survive the branch.
            // todo just clone?
            let outer_variables = env.variables.clone();

            // Introduce pattern-bound variables.
            pattern.bind_pattern(selected, env);

            // Infer the branch body.
            body.infer(env);

            let branch_ty = body.get_type(env);
            println!("branch type: \n\n{branch_ty:#?}\n\n");

            // The result is the union of branch results.
            result = Type::union(result, branch_ty);

            // Restore lexical scope.
            env.variables = outer_variables;

            // Remember which values have already been matched.
            covered = Type::union(covered, accepted);
        }

        println!("result: \n\n{result:#?}\n\n");
        println!("covered: \n\n{covered:#?}\n\n");

        // Exhaustiveness: t0 <= union of accepted patterns.
        env.constraints
            .push(Constraint::Subtype(scrutinee_ty, covered));

        self.set_type(result);
    }

    /// In a match expression context, binding patterns means that we want to
    /// increase our envirronment with selected variables.
    ///
    /// For instance, let a Variant be A(num) | B(_).
    /// and that expression to be check:
    ///
    /// match x /* our variant */ {
    ///     /* 1 */ _ => ...
    ///     /* 2 */ v => ...
    ///     /* 3 */ A(v) => ...
    /// }
    ///
    /// The first arm is a wildcard, we don't need to creates any variable in our
    /// envirronment.
    ///
    /// The second arm is a PatternBind. Means that we want "v" to be something we
    /// know (the selected). Supposing x is u32Vbool. the variable v created is
    /// of the same type.
    ///
    /// In the latest situation, we know that v must match with the type of the
    /// variant's arm selected. For instance A(u32). v is so binded with u32.
    ///
    /// That function generates symbolic subtype constraints only.
    fn bind_pattern(&self, selected: TypePtr, env: &mut TypeEnv) {
        match self.kind {
            Kind::PatternWildcard => {}
            Kind::PatternBind => {
                env.insert(self.lexem.to_owned(), selected);
            }
            Kind::PatternTag => {
                let selected = selected.normalize();

                // Clone the inner Type to release the RefCell borrow.
                let current = selected.borrow().clone();

                match current {
                    // The selected type is a variant with the expected tag.
                    // We can directly extract its payload type.
                    Type::Variant(tag, payload) if tag == self.lexem => {
                        self.children[0].bind_pattern(payload, env);
                    }
                    // The branch is unreachable.
                    Type::Bottom => {
                        self.children[0].bind_pattern(Type::bottom(), env);
                    }

                    // Other cases require a more complete projection
                    // or the tallying algorithm.
                    _ => {
                        // So in "match x" we have x a number, a type variable
                        // with no substitution, or anything that is added after
                        // that comment.

                        // That case is agnostic about the type of x. Actually, anything
                        // it is, we have here to create a constraints: type of x is a
                        // subtype of the pattern were looking in.

                        // For instance, the pattern "A(value) => value", accept all
                        // variant A(T). The type of x (let's write X) must respect that:
                        // x <= A(T).

                        // But we don't find that directly. Instead, we creates the
                        // constraint that the selected type is a subtype of something
                        // we'll get later
                        let fresh = env.fresh();
                        env.constraints.push(Constraint::Subtype(
                            selected,
                            Type::variant(self.lexem, fresh.clone()),
                        ));

                        self.children[0].bind_pattern(fresh, env);
                    }
                }
            }

            _ => panic!("unsupported pattern"),
        }
    }

    /// In case of match branch, retreive the type given a pattern.
    /// For instance:
    /// match x {
    ///     _ => ... /* top */
    ///     v => ... /* top */
    ///     A(v) => ... /* type variant A(top) */
    /// }
    fn accepted_type(&self) -> TypePtr {
        match self.kind {
            // wildcard accept everything, as bottom is the empty set, its negation is fair
            Kind::PatternWildcard | Kind::PatternBind => Type::top(),
            Kind::PatternTag => Type::variant(self.lexem, self.children[0].accepted_type()),
            _ => panic!("unexpected match subpattern"),
        }
    }
}

fn inferno(ast: &Node<'_>, mut env: TypeEnv) -> TypeEnv {
    ast.infer(&mut env);

    // TODO, I need inferno to not solve anything actually.
    // (or maybe just the equality constraints).
    solve(env)
}

/* UNIFICATION AND CONSTRAINT SOLVING */

/// Merge r#type. If everything ok, left ends to be the same as right. Inplace function
fn unify(left: TypePtr, right: TypePtr, env: &mut TypeEnv) {
    let left = left.resolve(env);
    let right = right.resolve(env);

    if left.same(&right) {
        // Same variable: nothing to do.
        return;
    }

    let lty = left.borrow().clone();
    let rty = right.borrow().clone();

    match (lty, rty) {
        (Type::Var(var), _) => {
            // TODO: occurs check
            env.substitute(&var, right);
        }

        (_, Type::Var(var)) => {
            // TODO: occurs check
            env.substitute(&var, left);
        }

        (Type::Con(left_con), Type::Con(right_con)) => {
            if left_con.name != right_con.name {
                panic!("unify failed: {} != {}", left_con.name, right_con.name);
            }

            if left_con.args.len() != right_con.args.len() {
                panic!("unify failed: args size");
            }

            for (left_arg, right_arg) in left_con.args.into_iter().zip(right_con.args) {
                unify(left_arg, right_arg, env);
            }
        }

        (Type::Scheme(_), _) | (_, Type::Scheme(_)) => {
            todo!("scheme unification")
        }

        _ => todo!(),
    }
}

// Solve all the constraints, Equals and Subtypes.
fn solve(mut env: TypeEnv) -> TypeEnv {
    let constraints = std::mem::take(&mut env.constraints);

    let mut subtypes = Vec::new();

    // First pass: resolve equality constraints.
    for constraint in constraints {
        match constraint {
            Constraint::Equals(a, b) => {
                unify(a, b, &mut env);
            }

            Constraint::Subtype(a, b) => {
                subtypes.push((a, b));
            }
        }
    }

    solve_single_variant_match(&subtypes, &mut env);

    // Second pass: check subtype constraints.
    for (a, b) in subtypes {
        // Apply the substitutions produced by unify().
        let left = a.resolve(&env);
        let right = b.resolve(&env);

        // A <= B iff A \ B is empty.
        let remainder = Type::difference(left.clone(), right.clone()).normalize();

        if !remainder.is_bottom() {
            // that constraint cannot be solved right now. Let store it into
            // the new env. Furthermore, we can tell that a is b.

            env.constraints.push(Constraint::Subtype(a, b));
            println!(
                "could not prove subtype: {:?} <= {:?} (remainder: {:?})",
                left.borrow(),
                right.borrow(),
                remainder.borrow()
            );
        }
    }

    env
}

fn solve_single_variant_match(constraints: &[(TypePtr, TypePtr)], env: &mut TypeEnv) {
    for (left, right) in constraints {
        let left = left.resolve(env).normalize();
        let right = right.resolve(env).normalize();

        // Look for a right-hand side of the form:
        //
        // `A(beta)
        //
        let Type::Variant(tag, payload) = right.borrow().clone() else {
            continue;
        };

        // This restricted case expects a symbolic payload.
        if !matches!(&*payload.borrow(), Type::Var(_)) {
            continue;
        }

        // Look for:
        //
        // (alpha ∩ `A(Top)) <= `A(beta)
        //
        let Type::Intersection(a, b) = left.borrow().clone() else {
            continue;
        };

        let alpha = match (a.borrow().clone(), b.borrow().clone()) {
            (Type::Var(var), _) if b.is_open_variant(&tag) => var,

            (_, Type::Var(var)) if a.is_open_variant(&tag) => var,

            _ => continue,
        };

        // We also need the exhaustiveness constraint:
        //
        // alpha <= `A(Top)
        //
        // Without it, we cannot globally restrict alpha
        // to the A variant: there might be other branches.
        let exhaustive = constraints.iter().any(|(lo, hi)| {
            let lo = lo.resolve(env).normalize();
            let hi = hi.resolve(env).normalize();

            let is_alpha = match lo.borrow().clone() {
                Type::Var(v) => v.name == alpha.name,
                _ => false,
            };

            is_alpha && hi.is_open_variant(&tag)
        });

        if !exhaustive {
            continue;
        }

        // Instead of choosing:
        //
        // alpha := `A(beta)
        //
        // introduce another fresh variable gamma:
        //
        // alpha := `A(beta) ∩ gamma
        //
        let gamma = env.fresh();
        let candidate = Type::intersection(Type::variant(&tag, payload), gamma);

        println!("\n\ncandidate type:\n{candidate:#?}\n\n");

        // todo
        // if occurs_in(&alpha.name, &candidate, env) {
        //     panic!("recursive subtype solution");
        // }

        env.substitute(&alpha, candidate);
    }
}

/// Dummy implementation of a Damas-Hindley-Milner inference algorithm in Rust
///
/// AST (with some explicit type annotations?) -> AST with every node typed!
///
/// References:
/// - https://bernsteinbear.com/blog/type-inference/

fn main() {
    let a_is_b = Node::new(
        "=",
        Kind::Assignation,
        vec![
            Node::new("a", Kind::Var, vec![]),
            Node::new("b", Kind::Var, vec![]),
        ],
    );

    let b_is_num = Node::new(
        "=",
        Kind::Assignation,
        vec![
            Node::new("b", Kind::Var, vec![]),
            Node::new("42", Kind::Num, vec![]),
        ],
    );

    println!("first call");
    let mut env = inferno(&a_is_b, TypeEnv::default());

    println!("second call");
    env = inferno(&b_is_num, env);
    println!("start checks");

    // check if type has been created
    assert_eq!(
        *a_is_b.children[0].find(&mut env).borrow(),
        Type::Con(TypeCon {
            name: "u32".into(),
            args: vec![]
        })
    );
}

/* TESTS */

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn match_unknown_scrutinee() {
        let ast = Node::new(
            "match",
            Kind::Match,
            vec![
                Node::new("x", Kind::Var, vec![]),
                // Arm: `A(value) => value
                Node::new(
                    "=>",
                    Kind::Arm,
                    vec![
                        // Pattern: `A(value)
                        Node::new(
                            "A",
                            Kind::PatternTag,
                            vec![Node::new("value", Kind::PatternBind, vec![])],
                        ),
                        // Body: value
                        Node::new("value", Kind::Var, vec![]),
                    ],
                ),
            ],
        );

        let mut env = inferno(&ast, TypeEnv::default());

        let inferred = ast.find(&mut env).normalize();

        let ty_x = &ast.children[0].find(&mut env);
        println!("\n\ntype of x: {ty_x:#?}\n\n");

        assert!(matches!(&*inferred.borrow(), Type::Var(_)));
    }

    #[test]
    fn match_variant_extracts_payload() {
        let ast = Node::new(
            "match",
            Kind::Match,
            vec![
                // Scrutinee: `A(42)
                Node::new("A", Kind::Variant, vec![Node::new("42", Kind::Num, vec![])]),
                // Arm: `A(value) => value
                Node::new(
                    "=>",
                    Kind::Arm,
                    vec![
                        // Pattern: `A(value)
                        Node::new(
                            "A",
                            Kind::PatternTag,
                            vec![Node::new("value", Kind::PatternBind, vec![])],
                        ),
                        // Body: value
                        Node::new("value", Kind::Var, vec![]),
                    ],
                ),
            ],
        );

        let mut env = inferno(&ast, TypeEnv::default());

        let inferred = ast.find(&mut env).normalize();

        assert_eq!(*inferred.borrow(), *Type::con("u32").borrow());
    }

    #[test]
    fn difference_removes_variant() {
        let a = Type::variant("A", Type::con("u32"));
        let b = Type::variant("B", Type::con("bool"));

        // `A(u32) | `B(bool)
        let input = Type::union(a, b.clone());

        // Remove every possible `A value.
        let excluded = Type::variant("A", Type::top());

        let result = Type::difference(input, excluded).normalize();

        // Only `B(bool) should remain.
        assert_eq!(*result.borrow(), *b.borrow());
    }

    #[test]
    fn match_branch_refinement() {
        let a = Type::variant("A", Type::con("u32"));
        let b = Type::variant("B", Type::con("bool"));

        // Type of the scrutinee.
        let t0 = Type::union(a.clone(), b.clone());

        // Accepted types of the first two patterns.
        let pa = Type::variant("A", Type::top());
        let pb = Type::variant("B", Type::top());

        // First branch: (t0 \ Bottom) ∩ pa
        let first = Type::intersection(Type::difference(t0.clone(), Type::bottom()), pa.clone())
            .normalize();

        assert_eq!(*first.borrow(), *a.borrow());

        // Second branch: (t0 \ pa) ∩ pb
        let second =
            Type::intersection(Type::difference(t0.clone(), pa.clone()), pb.clone()).normalize();

        assert_eq!(*second.borrow(), *b.borrow());

        // Third branch: wildcard.
        // Both previous patterns have already covered t0.
        let covered = Type::union(pa, pb);

        let third = Type::difference(t0, covered).normalize();

        assert!(third.is_bottom());
    }

    #[test]
    fn difference_inside_variant_payload() {
        // `A(Top) \ `A(u32)
        let source = Type::variant("A", Type::top());

        let excluded = Type::variant("A", Type::con("u32"));

        let result = Type::difference(source, excluded).normalize();

        // Expected: `A(¬u32)
        let expected = Type::variant("A", Type::negation(Type::con("u32")));

        assert_eq!(*result.borrow(), *expected.borrow());
    }

    #[test]
    fn a_is_a_variable() {
        let input = Node::new("a", Kind::Var, vec![]);

        let mut env = inferno(&input, TypeEnv::default());

        // check if type has been created
        assert_eq!(
            *input.get_type(&mut env).borrow(),
            Type::Var(TypeVar { name: "a".into() })
        );
    }

    #[test]
    fn paper_example_2_inferno() {
        // ------------------------------------------------------
        // Initial types:
        //
        // A = `A(u32)
        // B = `B(u32)
        //
        // id2 : (A | B) -> (A | B)
        // x   : A | B
        // ------------------------------------------------------

        let a = Type::variant("A", Type::con("u32"));
        let b = Type::variant("B", Type::con("u32"));

        let ab = Type::union(a.clone(), b.clone());

        let mut env = TypeEnv::default();

        env.insert("x".into(), ab.clone());

        env.insert("id2".into(), Type::function(ab.clone(), ab.clone()));

        // ------------------------------------------------------
        // AST:
        //
        // match id2(x) {
        //     A(_) => B(42),
        //     y    => y,
        // }
        // ------------------------------------------------------

        let ast = Node::new(
            "match",
            Kind::Match,
            vec![
                // Scrutinee: id2(x)
                Node::new(
                    "id2(x)",
                    Kind::Apply,
                    vec![
                        Node::new("id2", Kind::Var, vec![]),
                        Node::new("x", Kind::Var, vec![]),
                    ],
                ),
                // First arm: A(_) => B(42)
                Node::new(
                    "=>",
                    Kind::Arm,
                    vec![
                        Node::new(
                            "A",
                            Kind::PatternTag,
                            vec![Node::new("_", Kind::PatternWildcard, vec![])],
                        ),
                        Node::new("B", Kind::Variant, vec![Node::new("42", Kind::Num, vec![])]),
                    ],
                ),
                // Second arm: y => y
                Node::new(
                    "=>",
                    Kind::Arm,
                    vec![
                        Node::new("y", Kind::PatternBind, vec![]),
                        Node::new("y", Kind::Var, vec![]),
                    ],
                ),
            ],
        );

        // ------------------------------------------------------
        // Run inference. No manual branch refinement!
        // ------------------------------------------------------

        let mut env = inferno(&ast, env);

        let inferred = ast.find(&mut env).normalize();

        // The entire expression must return only B(u32),
        // rather than A(u32) | B(u32).
        assert_eq!(*inferred.borrow(), *b.borrow(),);
    }

    #[test]
    fn paper_example_2_semantic_core() {
        let a = Type::variant("A", Type::con("()"));
        let b = Type::variant("B", Type::con("()"));

        // Assume the type of id2 x is A | B.
        let scrutinee = Type::union(a, b.clone());

        // First pattern accepts A(anything).
        let accepted = Type::variant("A", Type::top());

        // Type available to the second branch.
        let remaining = Type::difference(scrutinee, accepted).normalize();

        assert_eq!(*remaining.borrow(), *b.borrow());

        // A -> B returns B.
        // y -> y also returns B.
        let result = Type::union(b.clone(), remaining).normalize();

        assert_eq!(*result.borrow(), *b.borrow());
    }

    #[test]
    fn function_decl() {
        // push: (list 'a, 'a) -> ()

        // let a = [] # a: list u32
        // push(a /* TypeCon("[]", [T]) */, 42 /* T */)
        // push(a, "hello") # type error on that line
        //
        // a = b
        // b = 42
        //
        // TypeVar(a) = TypeVar(b)
        // TypeVar(b) = 'u32
        //
        // TypeVar(a) = TypeCon("[]", [TypeVar("t0")])
        //
        // apply :
        // unification TypeCon("[]", [TypeCon("u32")]) avec TypeVar(a) = TypeCon("[]", [TypeVar("t0")])

        // Version 2 plus dure, une HashMap?
        //
        // let x = {} # JSON-like notation ^^' ?!
        // key = "a"
        // value = 42
        //
        // push2: (map 'a 'b, 'a, 'b) -> ()
        // push2(x, key, value)
        //
        // can push2 be called push?
        // function are like variables (same scoping) -> push et push2
        // function are top level thingies -> overkill?
        //
        //
        // x : []
        // x : ['a]
        // x : ['a, ...]
    }

    #[test]
    fn apply() {
        println!("function declaration");
        let id = Node::new(
            "id",
            Kind::Function,
            vec![
                Node::new("a", Kind::Var, vec![]),
                Node::new("a", Kind::Var, vec![]),
            ],
        );
        let env = inferno(&id, TypeEnv::default());
        println!("{env:?}\n\napply call");

        let apply_id = Node::new(
            "id()",
            Kind::Apply,
            vec![
                Node::new("id", Kind::Var, vec![]),
                Node::new("42", Kind::Num, vec![]),
            ],
        );

        let mut env = inferno(&apply_id, env);

        println!("env\n\n{env:?}\n\n");

        assert_eq!(
            *apply_id.find(&mut env).borrow(),
            Type::Con(TypeCon {
                name: "u32".into(),
                args: vec![]
            })
        );
    }

    /*
    #[test]
    fn if_case() {
        let id = Node {
            lexem: "if",
            children: vec![
                Node {
                    lexem: "a",
                    children: vec![],
                    r#type: Default::default(),
                    kind: Kind::Var,
                },
                Node {
                    lexem: "a",
                    children: vec![],
                    r#type: Default::default(),
                    kind: Kind::Var,
                },
            ],
            r#type: Default::default(),
            kind: Kind::If,
        };

        let mut env = inferno(&id, TypeEnv::default());
        // check if types have been created
        assert!(id.children[0].r#type.borrow().is_some());
        assert!(id.children[1].r#type.borrow().is_some());
        let ty = id.find(&mut env);
        let ty = ty.generalize();
        assert_eq!(
            ty,
            Type::Scheme(Scheme {
                for_all: vec![Type::var("a"), Type::var("a")],
                ty: Type::function(Type::var("a"), Type::var("a")),
            })
        );
    }
    */

    #[test]
    fn identity() {
        let id = Node::new(
            "id",
            Kind::Function,
            vec![
                Node::new("a", Kind::Var, vec![]),
                Node::new("a", Kind::Var, vec![]),
            ],
        );

        println!("start inference");
        let _ = inferno(&id, TypeEnv::default());
        // check if types have been created
        assert!(id.children[0].r#type.borrow().is_some());
        assert!(id.children[1].r#type.borrow().is_some());

        assert_eq!(
            id.children[0].r#type.borrow().as_ref().unwrap().as_ptr(),
            id.children[1].r#type.borrow().as_ref().unwrap().as_ptr()
        );
    }

    #[test]
    fn a_is_b() {
        let a_is_b = Node::new(
            "=",
            Kind::Assignation,
            vec![
                Node::new("a", Kind::Var, vec![]),
                Node::new("b", Kind::Var, vec![]),
            ],
        );

        let _ = inferno(&a_is_b, TypeEnv::default());
        // check if types have been created
        assert!(a_is_b.children[0].r#type.borrow().is_some());
        assert!(a_is_b.children[1].r#type.borrow().is_some());
    }

    #[test]
    fn test_generalize() {
        let ty_a = Type::var("a").generalize();
        assert_eq!(
            ty_a,
            Type::Scheme(Scheme {
                for_all: vec![Type::var("a")],
                ty: Type::var("a")
            })
        );

        let ty_b = Type::con_with_args("b", vec![Type::var("a")]).generalize();
        assert_eq!(
            ty_b,
            Type::Scheme(Scheme {
                for_all: vec![Type::var("a")],
                ty: Type::con_with_args("b", vec![Type::var("a")])
            })
        );
    }

    #[test]
    fn test_instantiate() {
        let var_a = Type::var("a");
        let ty_a = Type::scheme(vec![var_a.clone()], var_a);
        let ty_a = ty_a.instantiate();
        assert_eq!(
            ty_a,
            Type::Var(TypeVar {
                name: "a".to_string(),
            })
        );
    }

    #[test]
    fn a_is_a_num() {
        let a_is_a_num = Node::new(
            "=",
            Kind::Assignation,
            vec![
                Node::new("a", Kind::Var, vec![]),
                Node::new("42", Kind::Num, vec![]),
            ],
        );

        let mut env = inferno(&a_is_a_num, TypeEnv::default());
        // check if type has been created
        assert!(a_is_a_num.children[0].r#type.borrow().is_some());
        assert_eq!(
            *a_is_a_num.children[0].find(&mut env).borrow(),
            Type::Con(TypeCon {
                name: "u32".into(),
                args: vec![]
            })
        );
    }

    #[test]
    fn simple_variable_assignation() {
        let a_is_b = Node::new(
            "=",
            Kind::Assignation,
            vec![
                Node::new("a", Kind::Var, vec![]),
                Node::new("b", Kind::Var, vec![]),
            ],
        );

        let b_is_num = Node::new(
            "=",
            Kind::Assignation,
            vec![
                Node::new("b", Kind::Var, vec![]),
                Node::new("42", Kind::Num, vec![]),
            ],
        );

        println!("first call");
        let mut env = inferno(&a_is_b, TypeEnv::default());

        println!("second call");
        env = inferno(&b_is_num, env);
        println!("start checks");

        // check if type has been created
        assert_eq!(
            *a_is_b.children[0].find(&mut env).borrow(),
            Type::Con(TypeCon {
                name: "u32".into(),
                args: vec![]
            })
        );
    }
}
