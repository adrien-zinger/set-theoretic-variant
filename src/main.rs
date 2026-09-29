use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::Debug;
use std::rc::Rc;

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
    let mut env = inferno(&a_is_b, Env::default());

    println!("second call");
    env = inferno(&b_is_num, env);
    println!("start checks");

    // check if type has been created
    assert_eq!(
        *a_is_b.children[0].find(&mut env.type_env).borrow(),
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
    eq: Option<String>,
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
    fn var(name: &str) -> TypePtr {
        Type::Var(TypeVar {
            name: name.into(),
            eq: None,
        })
        .into()
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

    fn set_eq(&mut self, eq: String) {
        match self {
            Type::Var(c) => c.eq = Some(eq),
            _ => {}
        }
    }
}

type Id = String;
type TypePtr = Rc<RefCell<Type>>;
type TypeEnv = HashMap<Id, TypePtr>;

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
        let mut ty = self.get_type(env);
        while let Type::Var(type_var) = ty.clone().borrow().clone() {
            println!("ploup");
            if let Some(type_eq) = &type_var.eq {
                println!("try get {type_eq}");
                ty = env.get(type_eq).unwrap().clone();
            } else {
                break;
            }
        }
        println!("end");
        ty
    }

    fn get_type(&self, env: &mut TypeEnv) -> TypePtr {
        if let Some(ty) = env.get(self.lexem) {
            println!("get {} from env: {:?}", self.lexem, ty.clone());
            let _ = self.r#type.borrow_mut().insert(ty.clone());
            ty.clone()
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
        let name = ty.borrow().name();
        env.insert(name.clone(), ty.clone());
        let ty_found = self.find(env);
        let ty_mut = &mut ty_found.borrow_mut();
        ty_mut.set_eq(name);
        println!("exit: make {}'s type equals: {:?}", self.lexem, ty);
    }
}

/* IMPLEMENTATION */

/// Merge r#type. If everything ok, left ends to be the same as right.
fn unify<'a>(left: &'a Node, right: &'a Node, env: &mut TypeEnv) {
    let lty = left.find(env).borrow().clone();
    let rty = right.find(env).borrow().clone();
    match (&lty, &rty) {
        (Type::Var(_), _) => {
            // todo check if were not creating a loop, and also implement a true make_equals
            left.set_type_equals(right.get_type(env), env);
            return;
        }
        (_, Type::Var(_)) => {}
        (Type::Con(ty_left), Type::Con(ty_right)) => {
            if ty_left.name != ty_right.name {
                panic!("unify failed: name unmatch");
            }

            if ty_left.args.len() != ty_right.args.len() {
                panic!("unify failed: args size");
            }
            return;

            for (a, b) in ty_left.args.iter().zip(ty_right.args.iter().cloned()) {
                (_, env) = unify(a, b, env);
            }
        }
        _ => todo!(),
    };

    unify(right, left, env)
}

fn inferno<'a>(ast: &'a Node<'a>, env: Env<'a>) -> Env<'a> {
    fn inferno_rec<'a>(ast: &'a Node<'a>, mut env: Env<'a>) -> Env<'a> {
        match ast.kind {
            Kind::Num => ast.set_type_equals(Type::con("u32"), &mut env.type_env),
            Kind::Assignation => {
                let [left, right] = &ast.children.as_array().unwrap();
                env = inferno_rec(left, env);
                env = inferno_rec(right, env);
                unify(left, right, &mut env.type_env);
                ast.set_type_equals(Type::con("()"), &mut env.type_env);
            }
            Kind::Var => {}
            Kind::Function => {
                env.functions.insert(ast.lexem.to_string(), ast.clone());
                let mut function_env = env.clone();
                // fresh variable for the function argument
                let arg = &ast.children[0];
                let arg_type = arg.get_type(&mut function_env.type_env);
                inferno_rec(&ast.children[1], function_env);
                let ty = Type::con_with_args(
                    "->",
                    vec![arg_type, ast.children[1].get_type(&mut env.type_env)],
                )
                .into();
                ast.set_type_equals(ty, &mut env.type_env);
            }
            Kind::If => todo!(),
            Kind::Apply => {
                // retreive called function
                let body = env.functions.get(ast.children[0].lexem).unwrap().clone();
                // infer argument and get its type
                env = inferno_rec(&ast.children[1], env);
                let arg_type = ast.children[1].find(&mut env.type_env);

                let mut function_env = env.clone();
                function_env
                    .type_env
                    .insert(body.children[0].lexem.to_string(), arg_type);
                function_env = inferno_rec(&body, function_env);

                ast.set_type_equals(
                    body.children[1].get_type(&mut function_env.type_env),
                    &mut env.type_env,
                );
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

        let mut env = inferno(&input, Env::default());

        // check if type has been created
        assert_eq!(
            *input.get_type(&mut env.type_env).borrow(),
            Type::Var(TypeVar {
                name: "a".into(),
                eq: None
            })
        );
    }

    #[test]
    fn apply() {
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
        let env = inferno(&id, Env::default());

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
        assert_eq!(
            *apply_id.get_type(&mut env.type_env).borrow(),
            Type::Var(TypeVar {
                name: "id()".into(),
                eq: Some("u32".to_string())
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
        let mut env = inferno(&id, Env::default());
        // check if types have been created
        assert!(id.children[0].r#type.borrow().is_some());
        assert!(id.children[1].r#type.borrow().is_some());
        let ty = id.find(&mut env.type_env);
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

        let _ = inferno(&a_is_b, Env::default());
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
                eq: None
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

        let mut env = inferno(&a_is_a_num, Env::default());
        // check if type has been created
        assert!(a_is_a_num.children[0].r#type.borrow().is_some());
        assert_eq!(
            *a_is_a_num.children[0].find(&mut env.type_env).borrow(),
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
        let mut env = inferno(&a_is_b, Env::default());

        println!("second call");
        env = inferno(&b_is_num, env);
        println!("start checks");

        // check if type has been created
        assert_eq!(
            *a_is_b.children[0].find(&mut env.type_env).borrow(),
            Type::Con(TypeCon {
                name: "u32".into(),
                args: vec![]
            })
        );
    }
}
