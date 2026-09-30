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

    fn name(&self) -> String {
        match self {
            Type::Con(c) => c.name.clone(),
            Type::Var(v) => v.name.clone(),
            Type::Scheme(s) => s.ty.borrow().name(),
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
                unify(left.find(&mut env), right.find(&mut env), &mut env);
                ast.set_type_equals(Type::con("()"), &mut env);
            }
            Kind::Var => {}
            Kind::Function => {
                let mut function_env = env.clone();

                // Here we have an issue when:
                // a = 42
                // let foo = fn(a) -> ...
                //
                // we need to "bind" a fresh variable in the function's env
                let arg = &ast.children[0];
                let arg_type = arg.get_type(&mut function_env);
                function_env = inferno_rec(&ast.children[1], function_env);

                let body_type = ast.children[1].find(&mut function_env);
                let arg_type = {
                    let resolved = arg_type.borrow().find(&function_env);
                    resolved
                };
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

                unify(function_type, expected_function_type, &mut env);

                let result_type = {
                    let resolved = result_type.borrow().find(&env);
                    resolved
                };

                ast.set_type_equals(result_type, &mut env);
            }
        }
        env
    }

    inferno_rec(&ast, env)
}

/* TESTS */

#[cfg(test)]
mod tests {
    use super::*;

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
        let mut env = inferno(&id, TypeEnv::default());
        // check if types have been created
        assert!(id.children[0].r#type.borrow().is_some());
        assert!(id.children[1].r#type.borrow().is_some());

        assert_eq!(
            id.children[0].r#type.borrow().as_ref().unwrap().as_ptr(),
            id.children[1].r#type.borrow().as_ref().unwrap().as_ptr()
        );
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
