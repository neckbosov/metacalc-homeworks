use std::collections::HashMap;
use std::f64;
use crate::BinaryOp::{Minus, Multiply, Plus, Divide};
use crate::Val::Float;
use crate::Expr::BinOp;

#[derive(Clone, Debug, PartialEq, Hash, Eq)]
struct Var(String);

#[derive(Copy, Clone, Debug, PartialEq)]
enum BinaryOp {
    Plus,
    Minus,
    Multiply,
    Divide,
}

impl BinaryOp {
    fn get_fn(&self) -> impl FnOnce(f64, f64) -> f64 {
        match self {
            BinaryOp::Plus => { |a, b| a + b }
            BinaryOp::Minus => { |a, b| a - b }
            BinaryOp::Multiply => { |a, b| a * b }
            BinaryOp::Divide => { |a, b| a / b }
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
enum UnaryOp {
    Sin,
    Cos
}

impl UnaryOp {
    fn get_fn(&self) -> impl FnOnce(f64) -> f64 {
        match self {
            UnaryOp::Sin => { |x: f64| x.sin() }
            UnaryOp::Cos => { |x: f64| x.cos() }
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
enum Val {
    Zero,
    One,
    Float(f64),
}

impl Val {
    fn to_float(&self) -> f64 {
        match self {
            Val::Zero => { 0.0 }
            Val::One => { 1.0 }
            Val::Float(x) => { *x }
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
enum Expr {
    Value(Val),
    Variable(Var),
    BinOp(BinaryOp, Box<Expr>, Box<Expr>),
    UnOp(UnaryOp, Box<Expr>),
}

impl Expr {
    fn new_val(x: f64) -> Expr {
        Expr::Value(Val::Float(x))
    }
    fn new_var<S: ToString>(x: S) -> Expr {
        Expr::Variable(Var(x.to_string()))
    }
    fn new_binop(op: BinaryOp, lhs: Expr, rhs: Expr) -> Expr {
        Expr::BinOp(op, Box::new(lhs), Box::new(rhs))
    }
    fn new_unop(op: UnaryOp, e: Expr) -> Expr {
        Expr::UnOp(op, Box::new(e))
    }
}

fn eval(e: &Expr, env: &HashMap<Var, f64>) -> f64 {
    match e {
        Expr::Value(x) => { x.to_float() }
        Expr::Variable(name) => { env[name] }
        Expr::BinOp(op, x, y) => {
            op.get_fn()(eval(x, &env), eval(y, &env))
        }
        Expr::UnOp(op, x) => { op.get_fn()(eval(x, &env)) }
    }
}

fn diff_no_opt(e: Expr, var: &Var) -> Expr {
    match e {
        Expr::Value(_) => { Expr::Value(Val::Zero) }
        Expr::Variable(v) if v == *var => { Expr::Value(Val::One) }
        Expr::Variable(_) => { Expr::Value(Val::Zero) }
        Expr::BinOp(op, x, y) => {
            match op {
                BinaryOp::Plus | BinaryOp::Minus => {
                    Expr::BinOp(op, Box::new(diff_no_opt(*x, var)), Box::new(diff_no_opt(*y, var)))
                }
                BinaryOp::Multiply => {
                    let dx = Box::new(diff_no_opt(*x.clone(), var));
                    let dy = Box::new(diff_no_opt(*y.clone(), var));
                    Expr::BinOp(
                        Plus,
                        Box::new(Expr::BinOp(Multiply, dx, y)),
                        Box::new(Expr::BinOp(Multiply, x, dy)),
                    )
                }
                BinaryOp::Divide => {
                    let dx = Box::new(diff_no_opt(*x.clone(), var));
                    let dy = Box::new(diff_no_opt(*y.clone(), var));
                    Expr::BinOp(
                        Divide,
                        Box::new(Expr::BinOp(
                            Minus,
                            Box::new(Expr::BinOp(Multiply, dx, y.clone())),
                            Box::new(Expr::BinOp(Multiply, x, dy)),
                        )),
                        Box::new(Expr::BinOp(Multiply, y.clone(), y)),
                    )
                }
            }
        }
        Expr::UnOp(op, x) => {
            let dx = diff_no_opt(*x.clone(), var);
            Expr::BinOp(
                Multiply,
                Box::new(match op {
                    UnaryOp::Sin => { Expr::UnOp(UnaryOp::Cos, Box::new(diff_no_opt(*x, var))) }
                    UnaryOp::Cos => {
                        Expr::BinOp(
                            Minus,
                            Box::new(Expr::Value(Val::Zero)),
                            Box::new(Expr::UnOp(UnaryOp::Sin, Box::new(diff_no_opt(*x, var)))),
                        )
                    }
                }),
                Box::new(dx),
            )
        }
    }
}

fn optimize(e: Expr) -> Expr {
    match e {
        v @ Expr::Value(_) => { v }
        v @ Expr::Variable(_) => { v }
        Expr::BinOp(op, x, y) => {
            let x = optimize(*x);
            let y = optimize(*y);
            match (&x, &y) {
                (Expr::Value(Val::Zero), Expr::Value(Val::Zero)) => {
                    Expr::Value(Val::Zero)
                }
                (Expr::Value(Val::Zero), _) => {
                    match op {
                        Plus => { y }
                        Minus => { Expr::BinOp(Minus, Box::new(x), Box::new(y)) }
                        Multiply | Divide => { Expr::Value(Val::Zero) }
                    }
                }
                (_, Expr::Value(Val::Zero)) => {
                    match op {
                        Plus | Minus => { x }
                        Multiply => { Expr::Value(Val::Zero) }
                        Divide => { panic!("Division by zero") }
                    }
                }
                (Expr::Value(Val::One), Expr::Value(Val::One)) => {
                    match op {
                        Multiply | Divide => { Expr::Value(Val::One) }
                        Minus => { Expr::Value(Val::Zero) }
                        Plus => { Expr::Value(Float(2.0)) }
                    }
                }
                (_, Expr::Value(Val::One)) => {
                    match op {
                        Multiply | Divide => { x }
                        _ => { Expr::new_binop(op, x, y) }
                    }
                }
                (Expr::Value(Val::One), _) => {
                    match op {
                        Multiply => { y }
                        _ => { Expr::new_binop(op, x, y) }
                    }
                }
                (_, _) => {
                    BinOp(op, Box::new(x), Box::new(y))
                }
            }
        }
        Expr::UnOp(op, x) => {
            let x = optimize(*x);
            if let Expr::Value(Val::Zero) = x {
                match op {
                    UnaryOp::Sin => { Expr::Value(Val::Zero) }
                    UnaryOp::Cos => { Expr::Value(Val::One) }
                }
            } else {
                Expr::UnOp(op, Box::new(x))
            }
        }
    }
}

fn diff(e: Expr, var: &Var) -> Expr {
    optimize(diff_no_opt(e, var))
}

#[cfg(test)]
mod tests {
    use crate::{Expr, BinaryOp, Val, Var, eval, UnaryOp, diff};
    use std::collections::HashMap;
    use std::iter::FromIterator;

    #[test]
    fn simple_test() {
        let e = Expr::BinOp(
            BinaryOp::Plus,
            Box::new(Expr::Variable(Var("x".to_string()))),
            Box::new(Expr::Variable(Var("y".to_string()))),
        );
        let env = HashMap::from_iter(
            vec![
                (Var("x".to_string()), 2.0),
                (Var("y".to_string()), 3.0)
            ].into_iter()
        );
        let v = eval(&e, &env);
        assert_eq!(v, 5.0);
    }

    #[test]
    fn test_diff() {
        let e = Expr::new_binop(
            BinaryOp::Multiply,
            Expr::new_binop(
                BinaryOp::Plus,
                Expr::new_var("x"),
                Expr::Value(Val::One),
            ),
            Expr::new_unop(
                UnaryOp::Sin,
                Expr::new_var("y"),
            ),
        );
        let env = HashMap::from_iter(
            vec![(Var("x".to_string()), 3.0), (Var("y".to_string()), 0.5f64.asin())].into_iter()
        );
        assert_eq!(eval(&e, &env), 2.0);
        let d = diff(e.clone(), &Var("x".to_string()));
        let expected = Expr::new_unop(UnaryOp::Sin, Expr::new_var("y"));
        assert_eq!(d, expected);
    }
}


fn main() {
    println!("{}", 3.0f64.powi(-1));
}
