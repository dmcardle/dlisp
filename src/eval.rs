use std::fmt::Display;

use crate::{expr::Expr, token};

#[derive(Debug)]
pub enum RuntimeError {
    ParseError(token::ParseError),
    Uncallable,
    Unaddable,
    CarEmpty,
    UnknownFunction(String),
    WrongType { want: &'static str, got: Expr },
    WrongNumArgs { want: usize, got: usize },
}

impl Display for RuntimeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RuntimeError::ParseError(e) => write!(f, "ParseError {}", e),
            RuntimeError::Uncallable => write!(f, "Uncallable"),
            RuntimeError::Unaddable => write!(f, "Unaddable"),
            RuntimeError::CarEmpty => write!(f, "Car called on empty"),
            RuntimeError::UnknownFunction(s) => write!(f, "Unknown function {}", s),
            RuntimeError::WrongType { want, got } => {
                write!(f, "Wanted a value of type {}, but got {}", want, got)
            }
            RuntimeError::WrongNumArgs { want, got } => {
                write!(f, "Wanted {} args, but got {}", want, got)
            }
        }
    }
}

pub fn eval(code: &str) -> Result<Expr, RuntimeError> {
    let expr = Expr::parse_str(code).map_err(RuntimeError::ParseError)?;
    eval_expr(&expr)
}

pub fn eval_expr(expr: &Expr) -> Result<Expr, RuntimeError> {
    match expr {
        Expr::False
        | Expr::True
        | Expr::Int(_)
        | Expr::String(_)
        | Expr::Symbol(_)
        | Expr::Quoted(_) => Ok(expr.clone()),
        Expr::Application(boxed_expr, args) => match boxed_expr.as_ref() {
            Expr::Symbol(func_name) => match func_name.as_str() {
                "quote" => Ok(Expr::Quoted(args.clone())),
                "cond" => builtin_cond(&args),
                "print" => builtin_print(&args),
                "show" => builtin_show(&args),
                "add" => builtin_add(&args),
                "car" => builtin_car(&args),
                "cons" => builtin_cons(&args),
                _ => Err(RuntimeError::UnknownFunction(func_name.to_string())),
            },
            _ => Err(RuntimeError::Uncallable),
        },
    }
}

fn builtin_cond(args: &[Expr]) -> Result<Expr, RuntimeError> {
    match args {
        [selector, e1, e2] => {
            // Evaluate the selector to decide which sub-expression to evaluate.
            match eval_expr(selector)? {
                Expr::False | Expr::Int(0) => eval_expr(e2),
                _ => eval_expr(e1),
            }
        }
        _ => Err(RuntimeError::WrongNumArgs {
            want: 3,
            got: args.len(),
        }),
    }
}

fn builtin_show(args: &[Expr]) -> Result<Expr, RuntimeError> {
    let exprs: Vec<Expr> = args.iter().map(eval_expr).try_collect()?;
    let expr_strings: Vec<String> = exprs.iter().map(Expr::to_string).collect();
    Ok(Expr::String(expr_strings.join(" ")))
}

fn builtin_print(args: &[Expr]) -> Result<Expr, RuntimeError> {
    for arg in args {
        match eval_expr(arg) {
            Ok(expr) => println!("{}", expr),
            Err(err) => println!("@ {}", err),
        }
    }
    Ok(Expr::True)
}

fn builtin_add(args: &[Expr]) -> Result<Expr, RuntimeError> {
    let mut sum = 0;
    for arg in args {
        match eval_expr(&arg)? {
            Expr::Int(n) => {
                sum += n;
            }
            _ => {
                return Err(RuntimeError::Unaddable);
            }
        }
    }
    Ok(Expr::Int(sum))
}

fn builtin_car(args: &[Expr]) -> Result<Expr, RuntimeError> {
    match args {
        [Expr::Quoted(expr)] => match expr.first() {
            Some(head) => Ok(head.clone()),
            _ => Err(RuntimeError::CarEmpty),
        },
        [e] => match eval_expr(&e) {
            Ok(quoted @ Expr::Quoted(_)) => {
                let args = [quoted.clone()];
                builtin_car(&args)
            }
            Ok(e2) => Err(RuntimeError::WrongType {
                want: "Quoted",
                got: e2.clone(),
            }),
            err @ Err(_) => err,
        },
        _ => Err(RuntimeError::WrongNumArgs {
            want: 1,
            got: args.len(),
        }),
    }
}

fn builtin_cons(args: &[Expr]) -> Result<Expr, RuntimeError> {
    todo!()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::assert_matches::assert_matches;

    #[test]
    fn test_cond() {
        let expr = Expr::parse_str("(cond 0 \"truth\" \"lies\")").unwrap();
        let expr = eval_expr(&expr).unwrap();
        assert_eq!(expr, Expr::String(String::from("lies")));

        let expr = Expr::parse_str("(cond 1 \"truth\" \"lies\")").unwrap();
        let expr = eval_expr(&expr).unwrap();
        assert_eq!(expr, Expr::String(String::from("truth")));

        let expr = Expr::parse_str("(cond 2 \"truth\" \"lies\")").unwrap();
        let expr = eval_expr(&expr).unwrap();
        assert_eq!(expr, Expr::String(String::from("truth")));

        let expr = Expr::parse_str("(cond \"x\" \"truth\" \"lies\")").unwrap();
        let expr = eval_expr(&expr).unwrap();
        assert_eq!(expr, Expr::String(String::from("truth")));
    }

    #[test]
    fn test_cond_complex_selector() {
        let expr = Expr::parse_str("(cond (add 0 0) \"truth\" \"lies\")").unwrap();
        let expr = eval_expr(&expr).unwrap();
        assert_eq!(expr, Expr::String(String::from("lies")));

        let expr = Expr::parse_str("(cond (add 1 0) \"truth\" \"lies\")").unwrap();
        let expr = eval_expr(&expr).unwrap();
        assert_eq!(expr, Expr::String(String::from("truth")));
    }

    #[test]
    fn test_cond_complex_result() {
        let expr = Expr::parse_str("(cond 1 (cond 0 \"a\" \"b\") \"c\")").unwrap();
        let expr = eval_expr(&expr).unwrap();
        assert_eq!(expr, Expr::String(String::from("b")));

        let expr = Expr::parse_str("(cond 0 \"c\" (cond 0 \"a\" \"b\"))").unwrap();
        let expr = eval_expr(&expr).unwrap();
        assert_eq!(expr, Expr::String(String::from("b")));
    }

    #[test]
    fn test_car_empty() {
        let expr = Expr::parse_str("(car (quote))").unwrap();
        assert_matches!(eval_expr(&expr), Err(RuntimeError::CarEmpty));
    }

    #[test]
    fn test_car_simple() {
        let expr = Expr::parse_str("(car (quote 1 2 3))").unwrap();
        assert_matches!(eval_expr(&expr), Ok(Expr::Int(1)));
    }

    /// Test that `car` evaluates its argument rather than assuming it's already
    /// a quoted expression.
    #[test]
    fn test_car_eval_args() {
        let expr = Expr::parse_str("(car (cond 0 (quote) (quote 1 2)))").unwrap();
        assert_matches!(eval_expr(&expr), Ok(Expr::Int(1)));
    }

    #[test]
    fn test_car_eval_args_two_levels() {
        let expr = Expr::parse_str("(car (cond 0 (quote) (cond 0 (quote) (quote 1 2))))").unwrap();
        assert_matches!(eval_expr(&expr), Ok(Expr::Int(1)));
    }

    #[test]
    fn test_car_eval_args_empty() {
        let expr = Expr::parse_str("(car (cond 1 (quote) (quote 1 2)))").unwrap();
        assert_matches!(eval_expr(&expr), Err(RuntimeError::CarEmpty));
    }

    #[test]
    fn test_car_eval_args_wrong_type() {
        let expr = Expr::parse_str("(car (cond 1 42 (quote 1 2)))").unwrap();
        assert_matches!(
            eval_expr(&expr),
            Err(RuntimeError::WrongType { want: _, got: _ })
        );
    }
}
