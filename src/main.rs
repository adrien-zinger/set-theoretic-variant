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
use std::fmt::Debug;
use std::rc::Rc;

use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT_TYPE_VAR: AtomicUsize = AtomicUsize::new(0);

/// Dummy implementation of a Damas-Hindley-Milner inference algorithm in Rust
///
/// AST (with some explicit type annotations?) -> AST with every node typed!
///
/// References:
/// - https://bernsteinbear.com/blog/type-inference/

fn main() {
    let a_is_b = Node {
        lexem: "=",
        children: vec![
            Node {
                lexem: "a",
                children: vec![],
                r#type: Default::default(),
                kind: Kind::Var,
            },
            Node {
                lexem: "b",
                children: vec![],
                r#type: Default::default(),
                kind: Kind::Var,
            },
        ],
        r#type: Default::default(),
        kind: Kind::Assignation,
    };

    let b_is_num = Node {
        lexem: "=",
        children: vec![
            Node {
                lexem: "b",
                children: vec![],
                r#type: Default::default(),
                kind: Kind::Var,
            },
            Node {
                lexem: "42",
                children: vec![],
                r#type: Default::default(),
                kind: Kind::Num,
            },
        ],
        r#type: Default::default(),
        kind: Kind::Assignation,
    };

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

impl Into<Type> for TypeVar {
    fn into(self) -> Type {
        Type::Var(self)
    }
}

impl Into<Type> for &TypeVar {
    fn into(self) -> Type {
        Type::Var(self.clone())
    }
}

impl Into<TypePtr> for Type {
    fn into(self) -> TypePtr {
        Rc::new(RefCell::new(self.clone()))
    }
}

impl Into<Type> for TypeCon {
    fn into(self) -> Type {
        Type::Con(self)
    }
}

fn instanciate(ty: &TypePtr) -> Type {
    let ty_inner = ty.borrow();
    match &*ty_inner {
        Type::Scheme(sche) => sche.ty.borrow().clone(),
        _ => return ty_inner.clone(),
    }
}

fn generalize(ty: &TypePtr) -> Type {
    let ty_inner = ty.borrow();
    match &*ty_inner {
        Type::Var(_) => Type::Scheme(Scheme {
            for_all: vec![ty.clone()],
            ty: ty.clone(),
        }),
        Type::Con(con) => Type::Scheme(Scheme {
            for_all: con.args.clone(),
            ty: ty.clone(),
        }),
        _ => ty_inner.clone(),
    }
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

impl Type {
    fn find(&self, env: &TypeEnv) -> TypePtr {
        match self {
            Type::Var(var) => {
                if let Some(ty) = env.get_substitution(var) {
                    ty.borrow().find(env)
                } else {
                    self.clone().into()
                }
            }
            Type::Con(con) => Type::con_with_args(
                &con.name,
                con.args.iter().map(|arg| arg.borrow().find(env)).collect(),
            ),
            Type::Scheme(scheme) => {
                Type::scheme(scheme.for_all.clone(), scheme.ty.borrow().find(env))
            }
            Type::Variant(tag, payload) => {
                let resolved = payload.borrow().find(env);
                Type::variant(tag, resolved)
            }
            Type::Union(a, b) => {
                let a = a.borrow().find(env);
                let b = b.borrow().find(env);
                Type::union(a, b)
            }
            Type::Intersection(a, b) => {
                let a = a.borrow().find(env);
                let b = b.borrow().find(env);
                Type::intersection(a, b)
            }
            Type::Negation(ty) => {
                let resolved = ty.borrow().find(env);
                Type::negation(resolved)
            }
            Type::Bottom => Type::bottom(),
        }
    }

    fn var(name: &str) -> TypePtr {
        Type::Var(TypeVar { name: name.into() }).into()
    }

    fn con(name: &str) -> TypePtr {
        Type::Con(TypeCon {
            name: name.into(),
            args: vec![],
        })
        .into()
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

    fn name(&self) -> String {
        match self {
            Type::Con(c) => c.name.clone(),
            Type::Var(v) => v.name.clone(),
            Type::Scheme(s) => s.ty.borrow().name(),

            _ => todo!(),
        }
    }

    fn args(&self) -> Vec<TypePtr> {
        match self {
            Type::Con(c) => c.args.clone(),
            _ => vec![],
        }
    }
}

type Id = String;
type TypePtr = Rc<RefCell<Type>>;

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

#[derive(Default, Clone)]
struct Env<'a> {
    type_env: TypeEnv,
    functions: HashMap<Id, Node<'a>>,
}

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

#[derive(Clone, Debug)]
enum Constraint {
    Equals(TypePtr, TypePtr),
    Subtype(TypePtr, TypePtr), // todo
}

#[derive(Debug, Clone)]
struct Node<'a> {
    lexem: &'a str,
    kind: Kind,
    children: Vec<Node<'a>>,
    r#type: RefCell<Option<TypePtr>>,
}

impl Node<'_> {
    fn find(&self, env: &mut TypeEnv) -> TypePtr {
        let ty = self.get_type(env);
        let result = ty.borrow().find(env);
        result
    }

    fn get_type(&self, env: &mut TypeEnv) -> TypePtr {
        if let Some(ty) = env.get(self.lexem) {
            println!("get {} from env: {:?}", self.lexem, ty);
            let ty = ty.clone();
            let _ = self.r#type.borrow_mut().insert(ty.clone());
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
}

/* IMPLEMENTATION */

/* TODO, that should be implementation of TypePtr. */

fn same(a: &TypePtr, b: &TypePtr) -> bool {
    *a.borrow() == *b.borrow()
}

fn is_bottom(t: &TypePtr) -> bool {
    matches!(&*t.borrow(), Type::Bottom)
}

fn is_top(t: &TypePtr) -> bool {
    match &*t.borrow() {
        Type::Negation(x) => is_bottom(x),
        _ => false,
    }
}

// A variant carrying an impossible payload is itself empty.
fn variant_or_bottom(tag: &str, payload: TypePtr) -> TypePtr {
    if is_bottom(&payload) {
        Type::bottom()
    } else {
        Type::variant(tag, payload)
    }
}

///  Helper to check if a type is an open variant (a variant with an inner type
///  that can be anything. It occurs when:
///  fn unwrap(x) {
///      match x {
///          'A(v) => v     // here, the type of x ɑ is a subtype of 'A(Top)
///      }
///  }
fn is_open_variant(ty: &TypePtr, tag: &str) -> bool {
    match ty.borrow().clone() {
        Type::Variant(name, payload) => name == tag && is_top(&payload),

        _ => false,
    }
}

/// See meet-join algorithm. That methods creates the join of
/// two set-theoretical types.
fn join(a: TypePtr, b: TypePtr) -> TypePtr {
    // When one is everything, return everything.
    if is_top(&a) {
        return a;
    } else if is_top(&b) {
        return b;
    }

    // When one is nothing, return the other
    if is_bottom(&a) {
        return b;
    } else if is_bottom(&b) {
        return a;
    }

    // If both are the same, it doesn't matter, return one of them
    if same(&a, &b) {
        return a;
    }

    // in any other case, return the union
    Type::union(a, b)
}

/// See meet-join algorithm. That methods creates the meet of two
/// set theoretical types (union, bottom, variants, etc...)
fn meet(a: TypePtr, b: TypePtr) -> TypePtr {
    // if both are bottom, the meet of them is also a bottom
    if is_bottom(&a) || is_bottom(&b) {
        return Type::bottom();
    }

    // If "a" is everything, the meet (like the intersection) is b.
    // Whether b is everything or nothing too.
    if is_top(&a) {
        return b;
    }

    // If "b" is everything, return a. (like the previous condition, symetricaly)
    if is_top(&b) {
        return a;
    }

    // If both are equals, return one of them, it doesn't matter.
    if same(&a, &b) {
        return a;
    }

    // A ∩ ¬B = A \ B
    //
    // If "b" is a negation, take the excluded and substract them from "a"
    if let Type::Negation(excluded) = b.borrow().clone() {
        return subtract(a, excluded);
    }

    // Same thing but with "a"
    if let Type::Negation(excluded) = a.borrow().clone() {
        return subtract(b, excluded);
    }

    // (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C)
    if let Type::Union(l, r) = a.borrow().clone() {
        return join(meet(l, b.clone()), meet(r, b));
    }

    if let Type::Union(l, r) = b.borrow().clone() {
        return join(meet(a.clone(), l), meet(a, r));
    }

    // Different variant tags are disjoint.
    if let (Type::Variant(ta, pa), Type::Variant(tb, pb)) = (&*a.borrow(), &*b.borrow()) {
        return if ta == tb {
            variant_or_bottom(ta, meet(pa.clone(), pb.clone()))
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
fn subtract(a: TypePtr, b: TypePtr) -> TypePtr {
    if is_bottom(&a) || is_top(&b) || same(&a, &b) {
        return Type::bottom();
    }

    if is_bottom(&b) {
        return a;
    }

    // A \ ¬B = A ∩ B
    if let Type::Negation(x) = b.borrow().clone() {
        return meet(a, x);
    }

    // (A ∪ B) \ C
    if let Type::Union(l, r) = a.borrow().clone() {
        return join(subtract(l, b.clone()), subtract(r, b));
    }

    // A \ (B ∪ C)
    if let Type::Union(l, r) = b.borrow().clone() {
        return subtract(subtract(a, l), r);
    }

    // (A ∩ B) \ C = (A \ C) ∩ B
    if let Type::Intersection(l, r) = a.borrow().clone() {
        return meet(subtract(l, b.clone()), r);
    }

    // Variant-specific difference.
    if let (Type::Variant(ta, pa), Type::Variant(tb, pb)) = (&*a.borrow(), &*b.borrow()) {
        return if ta == tb {
            variant_or_bottom(ta, subtract(pa.clone(), pb.clone()))
        } else {
            a.clone()
        };
    }

    // Top \ B = ¬B
    if is_top(&a) {
        return Type::negation(b);
    }

    // Cannot simplify further.
    Type::difference(a, b)
}

fn normalize(t: TypePtr) -> TypePtr {
    let current = t.borrow().clone();

    match current {
        // union case, normalize a and b and join them.
        Type::Union(a, b) => join(normalize(a), normalize(b)),
        // Intersection case, normalize a and b and meet them.
        Type::Intersection(a, b) => meet(normalize(a), normalize(b)),
        Type::Negation(x) => {
            // Let start normalize the inner type.
            let x = normalize(x);
            // apply some simplifications in case we have:
            // 1. negation of nothing (it gives everything instead)
            // 2. negation of negation. (it gives just the inner type ¬¬A = A)
            match x.borrow().clone() {
                Type::Bottom => Type::top(),
                Type::Negation(y) => y,
                _ => Type::negation(x.clone()),
            }
        }
        // return the normalized variant type
        Type::Variant(tag, payload) => variant_or_bottom(&tag, normalize(payload)),
        // first leaf, return the type (normalizing recursively its args)
        Type::Con(con) => {
            Type::con_with_args(&con.name, con.args.into_iter().map(normalize).collect())
        }

        // latest leaf, other types are preserved.
        // In particular, we don't normalize under Scheme here.
        other => other.into(),
    }
}

/* END of TODO note*/

/// Merge r#type. If everything ok, left ends to be the same as right. Inplace function
fn unify(left: TypePtr, right: TypePtr, env: &mut TypeEnv) {
    let left = left.borrow().find(env);
    let right = right.borrow().find(env);

    let lty = left.borrow().clone();
    let rty = right.borrow().clone();

    match (lty, rty) {
        (Type::Var(left_var), Type::Var(right_var)) if left_var.name == right_var.name => {
            // Same variable: nothing to do.
        }

        (Type::Var(var), _) => {
            // TODO: occurs check
            env.substitute(&var, right);
        }

        (_, Type::Var(_)) => {
            unify(right, left, env);
        }

        (Type::Con(left_con), Type::Con(right_con)) => {
            if left_con.name != right_con.name {
                panic!("unify failed: {} != {}", left_con.name, right_con.name);
            }

            if left_con.args.len() != right_con.args.len() {
                panic!("unify failed: args size");
            }

            for (left_arg, right_arg) in left_con.args.into_iter().zip(right_con.args.into_iter()) {
                unify(left_arg, right_arg, env);
            }
        }

        (Type::Scheme(_), _) | (_, Type::Scheme(_)) => {
            todo!("scheme unification")
        }

        _ => todo!(),
    }
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
fn bind_pattern(pattern: &Node, selected: TypePtr, env: &mut TypeEnv) {
    match pattern.kind {
        Kind::PatternWildcard => {}
        Kind::PatternBind => {
            env.insert(pattern.lexem.to_owned(), selected);
        }
        Kind::PatternTag => {
            let selected = normalize(selected);

            // Clone the inner Type to release the RefCell borrow.
            let current = selected.borrow().clone();

            match current {
                // The selected type is a variant with the expected tag.
                // We can directly extract its payload type.
                Type::Variant(tag, payload) if tag == pattern.lexem => {
                    bind_pattern(&pattern.children[0], payload, env);
                }
                // The branch is unreachable.
                Type::Bottom => {
                    bind_pattern(&pattern.children[0], Type::bottom(), env);
                }

                // Other cases require a more complete projection
                // or the tallying algorithm.
                other => {
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
                        Type::variant(pattern.lexem, fresh.clone()),
                    ));

                    bind_pattern(&pattern.children[0], fresh, env);
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
fn accepted_type(pattern: &Node) -> TypePtr {
    match pattern.kind {
        // wildcard accept everything, as bottom is the empty set, its negation is fair
        Kind::PatternWildcard | Kind::PatternBind => Type::top(),
        Kind::PatternTag => Type::variant(pattern.lexem, accepted_type(&pattern.children[0])),
        _ => panic!("unexpected match subpattern"),
    }
}

fn inferno<'a>(ast: &'a Node<'a>, env: TypeEnv) -> TypeEnv {
    fn inferno_rec<'a>(ast: &'a Node<'a>, mut env: TypeEnv) -> TypeEnv {
        match ast.kind {
            Kind::Num => ast.set_type_equals(Type::con("u32"), &mut env),
            Kind::Assignation => {
                let [left, right] = &ast.children.as_array().unwrap();
                env = inferno_rec(left, env);
                env = inferno_rec(right, env);
                let left_type = left.find(&mut env);
                let right_type = right.find(&mut env);
                env.constraints
                    .push(Constraint::Equals(left_type, right_type));
                ast.set_type_equals(Type::con("()"), &mut env);
            }
            Kind::Var => {}
            Kind::Function => {
                let mut function_env = env.clone();

                // we need to "bind" a fresh variable in the function's env
                let arg = &ast.children[0];
                let arg_type = function_env.fresh();
                arg.r#type.borrow_mut().replace(arg_type.clone());
                function_env.insert(arg.lexem.to_string(), arg_type.clone());

                // infer return's type (body type)
                function_env = inferno_rec(&ast.children[1], function_env);
                let body_type = ast.children[1].find(&mut function_env);

                let arg_type = arg_type.borrow().find(&function_env);
                let ty = Type::con_with_args("->", vec![arg_type, body_type]);
                ast.set_type_equals(ty, &mut env);
            }
            Kind::If => todo!(),
            Kind::Apply => {
                let [function, argument] = &ast.children[..] else {
                    panic!("unexpected apply children size");
                };

                // Infer both sides independently.
                env = inferno_rec(function, env);
                env = inferno_rec(argument, env);

                let function_type = function.find(&mut env);
                let argument_type = argument.find(&mut env);

                let result_type = env.fresh();
                let expected_function_type =
                    Type::con_with_args("->", vec![argument_type, result_type.clone()]);

                env.constraints
                    .push(Constraint::Equals(function_type, expected_function_type));

                let result_type = result_type.borrow().find(&env);
                ast.set_type_equals(result_type, &mut env);
            }
            Kind::Variant => {
                let [argument] = &ast.children[..] else {
                    panic!("unexpected variant children size");
                };

                // Infer the variant payload.
                env = inferno_rec(argument, env);

                // Retrieve its inferred type.
                let argument_type = argument.find(&mut env);

                // Construct the variant type: `Tag(argument_type)
                let variant_type = Type::variant(ast.lexem, argument_type);

                // Store the result directly in the AST node.
                ast.r#type.borrow_mut().replace(variant_type);
            }
            Kind::Match => {
                // Get the scrutinee and the arms of expression:
                // match scrutinee {
                //    arms...
                // }
                let scrutinee = &ast.children[0];
                let arms = &ast.children[1..];

                env = inferno_rec(scrutinee, env);

                let scrutinee_ty = scrutinee.get_type(&mut env);

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
                    let accepted = accepted_type(pattern);

                    // But actually, the accepted type by the branch is not the
                    // "selected".

                    // Let's S the type of the scrutinee, C the
                    // already covered types. And finally A the one found
                    // for the arm.

                    // We can already tell that the selected type is in
                    // S \ C. But that should be intersected
                    // with A. So t_selected is: (S \ C) ∩ A
                    let selected = normalize(Type::intersection(
                        Type::difference(scrutinee_ty.clone(), covered.clone()),
                        accepted.clone(),
                    ));

                    println!("selected: \n\n{selected:#?}\n\n");

                    // Save the outer expression bindings.
                    // Substitutions and constraints must survive the branch.
                    // todo just clone?
                    let outer_variables = env.variables.clone();

                    // Introduce pattern-bound variables.
                    bind_pattern(pattern, selected, &mut env);

                    // Infer the branch body.
                    env = inferno_rec(body, env);

                    let branch_ty = body.get_type(&mut env);
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

                ast.r#type.borrow_mut().replace(result);
            }
            _ => panic!("node not managed {ast:?}"),
        }
        env
    }

    // TODO, I need inferno to not solve anything actually.
    // (or maybe just the equality constraints).
    solve(inferno_rec(&ast, env))
}

fn solve_single_variant_match(constraints: &[(TypePtr, TypePtr)], env: &mut TypeEnv) {
    for (left, right) in constraints {
        let left = normalize(left.borrow().find(env));
        let right = normalize(right.borrow().find(env));

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
            (Type::Var(var), _) if is_open_variant(&b, &tag) => var,

            (_, Type::Var(var)) if is_open_variant(&a, &tag) => var,

            _ => continue,
        };

        // We also need the exhaustiveness constraint:
        //
        // alpha <= `A(Top)
        //
        // Without it, we cannot globally restrict alpha
        // to the A variant: there might be other branches.
        let exhaustive = constraints.iter().any(|(lo, hi)| {
            let lo = normalize(lo.borrow().find(env));
            let hi = normalize(hi.borrow().find(env));

            let is_alpha = match lo.borrow().clone() {
                Type::Var(v) => v.name == alpha.name,
                _ => false,
            };

            is_alpha && is_open_variant(&hi, &tag)
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
        let left = a.borrow().find(&env);
        let right = b.borrow().find(&env);

        // A <= B iff A \ B is empty.
        let remainder = normalize(Type::difference(left.clone(), right.clone()));

        if !is_bottom(&remainder) {
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

/* TESTS */

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn match_unknown_scrutinee() {
        let ast = Node {
            lexem: "match",
            kind: Kind::Match,
            children: vec![
                Node {
                    lexem: "x",
                    kind: Kind::Var,
                    children: vec![],
                    r#type: Default::default(),
                },
                // Arm: `A(value) => value
                Node {
                    lexem: "=>",
                    kind: Kind::Arm,
                    children: vec![
                        // Pattern: `A(value)
                        Node {
                            lexem: "A",
                            kind: Kind::PatternTag,
                            children: vec![Node {
                                lexem: "value",
                                kind: Kind::PatternBind,
                                children: vec![],
                                r#type: Default::default(),
                            }],
                            r#type: Default::default(),
                        },
                        // Body: value
                        Node {
                            lexem: "value",
                            kind: Kind::Var,
                            children: vec![],
                            r#type: Default::default(),
                        },
                    ],
                    r#type: Default::default(),
                },
            ],
            r#type: Default::default(),
        };

        let mut env = inferno(&ast, TypeEnv::default());

        let inferred = normalize(ast.find(&mut env));

        let ty_x = &ast.children[0].find(&mut env);
        println!("\n\ntype of x: {ty_x:#?}\n\n");

        assert!(matches!(&*inferred.borrow(), Type::Var(_)));
    }

    #[test]
    fn match_variant_extracts_payload() {
        let ast = Node {
            lexem: "match",
            kind: Kind::Match,
            children: vec![
                // Scrutinee: `A(42)
                Node {
                    lexem: "A",
                    kind: Kind::Variant,
                    children: vec![Node {
                        lexem: "42",
                        kind: Kind::Num,
                        children: vec![],
                        r#type: Default::default(),
                    }],
                    r#type: Default::default(),
                },
                // Arm: `A(value) => value
                Node {
                    lexem: "=>",
                    kind: Kind::Arm,
                    children: vec![
                        // Pattern: `A(value)
                        Node {
                            lexem: "A",
                            kind: Kind::PatternTag,
                            children: vec![Node {
                                lexem: "value",
                                kind: Kind::PatternBind,
                                children: vec![],
                                r#type: Default::default(),
                            }],
                            r#type: Default::default(),
                        },
                        // Body: value
                        Node {
                            lexem: "value",
                            kind: Kind::Var,
                            children: vec![],
                            r#type: Default::default(),
                        },
                    ],
                    r#type: Default::default(),
                },
            ],
            r#type: Default::default(),
        };

        let mut env = inferno(&ast, TypeEnv::default());

        let inferred = normalize(ast.find(&mut env));

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

        let result = normalize(Type::difference(input, excluded));

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
        let first = normalize(Type::intersection(
            Type::difference(t0.clone(), Type::bottom()),
            pa.clone(),
        ));

        assert_eq!(*first.borrow(), *a.borrow());

        // Second branch: (t0 \ pa) ∩ pb
        let second = normalize(Type::intersection(
            Type::difference(t0.clone(), pa.clone()),
            pb.clone(),
        ));

        assert_eq!(*second.borrow(), *b.borrow());

        // Third branch: wildcard.
        // Both previous patterns have already covered t0.
        let covered = Type::union(pa, pb);

        let third = normalize(Type::difference(t0, covered));

        assert!(is_bottom(&third));
    }

    #[test]
    fn difference_inside_variant_payload() {
        // `A(Top) \ `A(u32)
        let source = Type::variant("A", Type::top());

        let excluded = Type::variant("A", Type::con("u32"));

        let result = normalize(Type::difference(source, excluded));

        // Expected: `A(¬u32)
        let expected = Type::variant("A", Type::negation(Type::con("u32")));

        assert_eq!(*result.borrow(), *expected.borrow());
    }

    #[test]
    fn a_is_a_variable() {
        let input = Node {
            lexem: "a",
            children: vec![],
            r#type: Default::default(),
            kind: Kind::Var,
        };

        let mut env = inferno(&input, TypeEnv::default());

        // check if type has been created
        assert_eq!(
            *input.get_type(&mut env).borrow(),
            Type::Var(TypeVar { name: "a".into() })
        );
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
        let id = Node {
            lexem: "id",
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
            kind: Kind::Function,
        };
        let env = inferno(&id, TypeEnv::default());
        println!("{env:?}\n\napply call");

        let apply_id = Node {
            lexem: "id()",
            children: vec![
                Node {
                    lexem: "id",
                    children: vec![],
                    r#type: Default::default(),
                    kind: Kind::Var,
                },
                Node {
                    lexem: "42",
                    children: vec![],
                    r#type: Default::default(),
                    kind: Kind::Num,
                },
            ],
            r#type: Default::default(),
            kind: Kind::Apply,
        };

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
        let ty = generalize(&ty);
        assert_eq!(
            ty,
            Type::Scheme(Scheme {
                for_all: vec![Type::var("a"), Type::var("a")],
                ty: Type::con_with_args("->", vec![Type::var("a"), Type::var("a")]),
            })
        );
    }
    */

    #[test]
    fn identity() {
        let id = Node {
            lexem: "id",
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
            kind: Kind::Function,
        };

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
        let a_is_b = Node {
            lexem: "=",
            children: vec![
                Node {
                    lexem: "a",
                    children: vec![],
                    r#type: Default::default(),
                    kind: Kind::Var,
                },
                Node {
                    lexem: "b",
                    children: vec![],
                    r#type: Default::default(),
                    kind: Kind::Var,
                },
            ],
            r#type: Default::default(),
            kind: Kind::Assignation,
        };

        let _ = inferno(&a_is_b, TypeEnv::default());
        // check if types have been created
        assert!(a_is_b.children[0].r#type.borrow().is_some());
        assert!(a_is_b.children[1].r#type.borrow().is_some());
    }

    #[test]
    fn test_generalize() {
        let ty_a = generalize(&Type::var("a"));
        assert_eq!(
            ty_a,
            Type::Scheme(Scheme {
                for_all: vec![Type::var("a")],
                ty: Type::var("a")
            })
        );

        let ty_b = generalize(&Type::con_with_args("b", vec![Type::var("a")]));
        assert_eq!(
            ty_b,
            Type::Scheme(Scheme {
                for_all: vec![Type::var("a")],
                ty: Type::con_with_args("b", vec![Type::var("a")])
            })
        );
    }

    #[test]
    fn test_instanciate() {
        let var_a = Type::var("a");
        let ty_a = Type::scheme(vec![var_a.clone()], var_a);
        let ty_a = instanciate(&ty_a);
        assert_eq!(
            ty_a,
            Type::Var(TypeVar {
                name: "a".to_string(),
            })
        );
    }

    #[test]
    fn a_is_a_num() {
        let a_is_a_num = Node {
            lexem: "=",
            children: vec![
                Node {
                    lexem: "a",
                    children: vec![],
                    r#type: Default::default(),
                    kind: Kind::Var,
                },
                Node {
                    lexem: "42",
                    children: vec![],
                    r#type: Default::default(),
                    kind: Kind::Num,
                },
            ],
            r#type: Default::default(),
            kind: Kind::Assignation,
        };

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
        let a_is_b = Node {
            lexem: "=",
            children: vec![
                Node {
                    lexem: "a",
                    children: vec![],
                    r#type: Default::default(),
                    kind: Kind::Var,
                },
                Node {
                    lexem: "b",
                    children: vec![],
                    r#type: Default::default(),
                    kind: Kind::Var,
                },
            ],
            r#type: Default::default(),
            kind: Kind::Assignation,
        };

        let b_is_num = Node {
            lexem: "=",
            children: vec![
                Node {
                    lexem: "b",
                    children: vec![],
                    r#type: Default::default(),
                    kind: Kind::Var,
                },
                Node {
                    lexem: "42",
                    children: vec![],
                    r#type: Default::default(),
                    kind: Kind::Num,
                },
            ],
            r#type: Default::default(),
            kind: Kind::Assignation,
        };

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
