use std::cell::RefCell;
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
                monotype: Default::default(),
                kind: Kind::Var,
            },
            Node {
                lexem: "b",
                children: vec![],
                monotype: Default::default(),
                kind: Kind::Var,
            },
        ],
        monotype: Default::default(),
        kind: Kind::Assignation,
    };

    let b_is_num = Node {
        lexem: "=",
        children: vec![
            Node {
                lexem: "b",
                children: vec![],
                monotype: Default::default(),
                kind: Kind::Var,
            },
            Node {
                lexem: "42",
                children: vec![],
                monotype: Default::default(),
                kind: Kind::Num,
            },
        ],
        monotype: Default::default(),
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
        MonoType::Con(TypeCon {
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
    args: Vec<MonoTypePtr>,
}

impl Into<MonoType> for TypeVar {
    fn into(self) -> MonoType {
        MonoType::Var(self)
    }
}

impl Into<MonoType> for &TypeVar {
    fn into(self) -> MonoType {
        MonoType::Var(self.clone())
    }
}

impl Into<MonoTypePtr> for MonoType {
    fn into(self) -> MonoTypePtr {
        Rc::new(RefCell::new(self.clone()))
    }
}

impl Into<MonoType> for TypeCon {
    fn into(self) -> MonoType {
        MonoType::Con(self)
    }
}

#[derive(Debug, Clone, PartialEq)]
enum MonoType {
    Var(TypeVar), // TyVar("a"), because a is associated to the variable but unconstrained :)
    Con(TypeCon), // TyCon("list", [TyVar("a")]) | TyCon("list", [TyCon("int", [])]) | TyCon("int", [])
}

impl MonoType {
    fn var(name: &str) -> MonoTypePtr {
        MonoType::Var(TypeVar {
            name: name.into(),
            eq: None,
        })
        .into()
    }

    fn con(name: &str) -> MonoTypePtr {
        MonoType::Con(TypeCon {
            name: name.into(),
            args: vec![],
        })
        .into()
    }

    fn con_with_args(name: &str, args: Vec<MonoTypePtr>) -> MonoTypePtr {
        MonoType::Con(TypeCon {
            name: name.into(),
            args,
        })
        .into()
    }

    fn name(&self) -> String {
        match self {
            MonoType::Con(c) => c.name.clone(),
            MonoType::Var(c) => c.name.clone(),
        }
    }

    fn set_eq(&mut self, eq: String) {
        match self {
            MonoType::Var(c) => c.eq = Some(eq),
            _ => {}
        }
    }
}

type Id = String;
type MonoTypePtr = Rc<RefCell<MonoType>>;
type TypeEnv = std::collections::HashMap<Id, MonoTypePtr>;

#[derive(Debug, Clone)]
enum Kind {
    Var,
    Num,
    Assignation,
    Function(u32),
}

#[derive(Debug, Clone)]
struct Node<'a> {
    lexem: &'a str,
    kind: Kind,
    children: Vec<Node<'a>>,
    monotype: RefCell<Option<MonoTypePtr>>,
}

impl Node<'_> {
    fn find(&self, env: &mut TypeEnv) -> MonoTypePtr {
        let mut ty = self.get_type(env);
        while let MonoType::Var(type_var) = ty.clone().borrow().clone() {
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

    fn get_type(&self, env: &mut TypeEnv) -> MonoTypePtr {
        if let Some(ty) = env.get(self.lexem) {
            println!("get {} from env: {:?}", self.lexem, ty.clone());
            let _ = self.monotype.borrow_mut().insert(ty.clone());
            ty.clone()
        } else {
            let ty = self
                .monotype
                .borrow_mut()
                .get_or_insert_with(|| MonoType::var(self.lexem))
                .clone();

            env.insert(self.lexem.to_owned(), ty.clone());
            ty
        }
    }

    fn set_type_equals(&self, ty: MonoTypePtr, env: &mut TypeEnv) {
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

/// Merge monotype. If everything ok, left ends to be the same as right.
fn unify<'a>(left: &'a Node, right: &'a Node, env: &mut TypeEnv) {
    let lty = left.find(env).borrow().clone();
    let rty = right.find(env).borrow().clone();
    match (&lty, &rty) {
        (MonoType::Var(_), _) => {
            // todo check if were not creating a loop, and also implement a true make_equals
            left.set_type_equals(right.get_type(env), env);
            return;
        }
        (_, MonoType::Var(_)) => {}
        (MonoType::Con(ty_left), MonoType::Con(ty_right)) => {
            if ty_left.name != ty_right.name {
                panic!("unify failed: name unmatch");
            }

            if ty_left.args.len() != ty_right.args.len() {
                panic!("unify failed: args size");
            }
            return;

            /* todo
            for (a, b) in ty_left.args.iter().zip(ty_right.args.iter().cloned()) {
                (_, env) = unify(&a.into(), &b.into(), env);
            }
            */
        }
    };

    unify(right, left, env)
}

fn inferno<'a>(ast: &'a Node<'a>, env: TypeEnv) -> TypeEnv {
    fn inferno_rec<'a>(ast: &'a Node<'a>, mut env: TypeEnv) -> TypeEnv {
        match ast.kind {
            Kind::Num => ast.set_type_equals(MonoType::con("u32"), &mut env),
            Kind::Assignation => {
                let [left, right] = &ast.children.as_array().unwrap();
                env = inferno_rec(left, env);
                env = inferno_rec(right, env);
                unify(left, right, &mut env);
                ast.set_type_equals(MonoType::con("()"), &mut env);
            }
            Kind::Var => {}
            Kind::Function(_) => {
                let mut function_env = env.clone();
                // fresh variable for the function argument
                let arg = &ast.children[0];
                let arg_type = arg.get_type(&mut function_env);
                inferno_rec(&ast.children[1], function_env);
                ast.set_type_equals(
                    MonoType::con_with_args(
                        "->",
                        vec![arg_type, ast.children[1].get_type(&mut env)],
                    ),
                    &mut env,
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
            monotype: Default::default(),
            kind: Kind::Var,
        };

        let mut env = inferno(&input, TypeEnv::default());

        // check if type has been created
        assert_eq!(
            *input.get_type(&mut env).borrow(),
            MonoType::Var(TypeVar {
                name: "a".into(),
                eq: None
            })
        );
    }

    #[test]
    fn identity() {
        let id = Node {
            lexem: "id",
            children: vec![
                Node {
                    lexem: "a",
                    children: vec![],
                    monotype: Default::default(),
                    kind: Kind::Var,
                },
                Node {
                    lexem: "a",
                    children: vec![],
                    monotype: Default::default(),
                    kind: Kind::Var,
                },
            ],
            monotype: Default::default(),
            kind: Kind::Function(1),
        };

        let mut env = inferno(&id, TypeEnv::default());
        // check if types have been created
        assert!(id.children[0].monotype.borrow().is_some());
        assert!(id.children[1].monotype.borrow().is_some());
        assert_eq!(
            *id.find(&mut env).borrow(),
            MonoType::Con(TypeCon {
                name: "->".into(),
                args: vec![MonoType::var("a"), MonoType::var("a")]
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
                    monotype: Default::default(),
                    kind: Kind::Var,
                },
                Node {
                    lexem: "b",
                    children: vec![],
                    monotype: Default::default(),
                    kind: Kind::Var,
                },
            ],
            monotype: Default::default(),
            kind: Kind::Assignation,
        };

        let _ = inferno(&a_is_b, TypeEnv::default());
        // check if types have been created
        assert!(a_is_b.children[0].monotype.borrow().is_some());
        assert!(a_is_b.children[1].monotype.borrow().is_some());
    }

    #[test]
    fn a_is_a_num() {
        let a_is_a_num = Node {
            lexem: "=",
            children: vec![
                Node {
                    lexem: "a",
                    children: vec![],
                    monotype: Default::default(),
                    kind: Kind::Var,
                },
                Node {
                    lexem: "42",
                    children: vec![],
                    monotype: Default::default(),
                    kind: Kind::Num,
                },
            ],
            monotype: Default::default(),
            kind: Kind::Assignation,
        };

        let mut env = inferno(&a_is_a_num, TypeEnv::default());
        // check if type has been created
        assert!(a_is_a_num.children[0].monotype.borrow().is_some());
        assert_eq!(
            *a_is_a_num.children[0].find(&mut env).borrow(),
            MonoType::Con(TypeCon {
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
                    monotype: Default::default(),
                    kind: Kind::Var,
                },
                Node {
                    lexem: "b",
                    children: vec![],
                    monotype: Default::default(),
                    kind: Kind::Var,
                },
            ],
            monotype: Default::default(),
            kind: Kind::Assignation,
        };

        let b_is_num = Node {
            lexem: "=",
            children: vec![
                Node {
                    lexem: "b",
                    children: vec![],
                    monotype: Default::default(),
                    kind: Kind::Var,
                },
                Node {
                    lexem: "42",
                    children: vec![],
                    monotype: Default::default(),
                    kind: Kind::Num,
                },
            ],
            monotype: Default::default(),
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
            MonoType::Con(TypeCon {
                name: "u32".into(),
                args: vec![]
            })
        );
    }
}
