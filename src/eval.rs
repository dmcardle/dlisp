use std::collections::HashMap;
use std::fmt::Display;

use crate::{expr::Expr, token};

#[derive(Debug)]
pub enum RuntimeError {
    ParseError(token::ParseError),
    Uncallable,
    Unaddable,
    UndefinedSymbol,
    CarEmpty,
    UnknownFunction(String),
    MalformedFunction(Expr),
    WrongType {
        func: &'static str,
        want: &'static str,
        got: Expr,
    },
    WrongNumArgs {
        func: &'static str,
        want: usize,
        got: usize,
    },
}

impl Display for RuntimeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RuntimeError::ParseError(e) => write!(f, "ParseError {}", e),
            RuntimeError::Uncallable => write!(f, "Uncallable"),
            RuntimeError::Unaddable => write!(f, "Unaddable"),
            RuntimeError::UndefinedSymbol => write!(f, "Undefined symbol"),
            RuntimeError::CarEmpty => write!(f, "Car called on empty"),
            RuntimeError::UnknownFunction(s) => write!(f, "Unknown function {}", s),
            RuntimeError::MalformedFunction(s) => write!(f, "Malformed function {}", s),
            RuntimeError::WrongType { func, want, got } => {
                write!(f, "{func} wanted a value of type {want}, but got {got}")
            }
            RuntimeError::WrongNumArgs { func, want, got } => {
                write!(f, "{func} wanted {want} args, but got {got}")
            }
        }
    }
}

pub struct Evaluator {
    pub env: HashMap<String, Expr>,
}

impl Evaluator {
    pub fn new() -> Evaluator {
        Evaluator {
            env: HashMap::new(),
        }
    }
    pub fn eval(&mut self, code: &str) -> Result<Expr, RuntimeError> {
        let expr = Expr::parse_str(code).map_err(RuntimeError::ParseError)?;
        self.eval_expr(&expr)
    }

    pub fn eval_expr(&mut self, expr: &Expr) -> Result<Expr, RuntimeError> {
        match expr {
            Expr::Nil | Expr::True | Expr::Int(_) | Expr::String(_) | Expr::Quoted(_) => {
                Ok(expr.clone())
            }
            Expr::Symbol(symbol) => {
                if let Some(value) = self.env.get(symbol) {
                    Ok(value.clone())
                } else {
                    Err(RuntimeError::UndefinedSymbol)
                }
            }
            Expr::Application(boxed_expr, args) => match boxed_expr.as_ref() {
                Expr::Symbol(func_name) => match func_name.as_str() {
                    "quote" => Ok(Expr::Quoted(args.clone())),
                    "cond" => self.builtin_cond(&args),
                    "print" => self.builtin_print(&args),
                    "show" => self.builtin_show(&args),
                    "add" => self.builtin_add(&args),
                    "car" => self.builtin_car(&args),
                    "cons" => self.builtin_cons(&args),
                    _ => {
                        // TODO evaluate the function expression? Or just do
                        // simple environment lookups? let left = self.eval(boxed_expr)?;
                        //
                        // If expr looks like this: (quote (quote a b c) (add a c))
                        //
                        // 1. Strip the parameter list, (quote a b c)
                        //
                        // 2. Create a new environment that maps `a` to
                        // `args[0]`, `b` to `args[1]`, etc.
                        //
                        // 3. Eval in the new environment.
                        match self.env.get(func_name) {
                            Some(func_value @ Expr::Quoted(func_def)) => {
                                match func_def.as_slice() {
                                    [Expr::Quoted(args), func_body] => {
                                        print!("Evaluating {func_name}(");
                                        for arg in args {
                                            print!("{arg},");
                                        }
                                        println!(") = {func_body}");
                                        todo!("evaluate function with arguments")
                                    }
                                    _ => Err(RuntimeError::MalformedFunction(func_value.clone())),
                                }
                            }
                            Some(expr) => Err(RuntimeError::MalformedFunction(expr.clone())),
                            None => Err(RuntimeError::UnknownFunction(func_name.to_string())),
                        }
                    }
                },
                _ => Err(RuntimeError::Uncallable),
            },
            Expr::Def(name, expr) => {
                if let Expr::Nil = expr.as_ref() {
                    self.env.remove(name);
                } else {
                    let expr = self.eval_expr(expr)?;
                    self.env.insert(name.to_string(), expr);
                }
                Ok(Expr::Nil)
            }
        }
    }

    fn builtin_cond(&mut self, args: &[Expr]) -> Result<Expr, RuntimeError> {
        match args {
            [selector, e1, e2] => {
                // Evaluate the selector to decide which sub-expression to evaluate.
                match self.eval_expr(selector)? {
                    Expr::Nil | Expr::Int(0) => self.eval_expr(e2),
                    _ => self.eval_expr(e1),
                }
            }
            _ => Err(RuntimeError::WrongNumArgs {
                func: "cond",
                want: 3,
                got: args.len(),
            }),
        }
    }

    fn builtin_show(&mut self, args: &[Expr]) -> Result<Expr, RuntimeError> {
        let exprs: Vec<Expr> = args.iter().map(|e| self.eval_expr(e)).try_collect()?;
        let expr_strings: Vec<String> = exprs.iter().map(Expr::to_string).collect();
        Ok(Expr::String(expr_strings.join(" ")))
    }

    fn builtin_print(&mut self, args: &[Expr]) -> Result<Expr, RuntimeError> {
        for arg in args.iter() {
            let expr = self.eval_expr(arg)?;
            match expr {
                Expr::String(s) => {
                    println!("{}", s);
                }
                _ => {
                    return Err(RuntimeError::WrongType {
                        func: "print",
                        want: "String",
                        got: arg.clone(),
                    })
                }
            }
        }
        Ok(Expr::Nil)
    }

    fn builtin_add(&mut self, args: &[Expr]) -> Result<Expr, RuntimeError> {
        let mut sum = 0;
        for arg in args {
            match self.eval_expr(&arg)? {
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

    fn builtin_car(&mut self, args: &[Expr]) -> Result<Expr, RuntimeError> {
        match args {
            [Expr::Quoted(expr)] => match expr.first() {
                Some(head) => Ok(head.clone()),
                _ => Err(RuntimeError::CarEmpty),
            },
            [e] => match self.eval_expr(&e) {
                Ok(quoted @ Expr::Quoted(_)) => {
                    let args = [quoted.clone()];
                    self.builtin_car(&args)
                }
                Ok(e2) => Err(RuntimeError::WrongType {
                    func: "car",
                    want: "Quoted",
                    got: e2.clone(),
                }),
                err @ Err(_) => err,
            },
            _ => Err(RuntimeError::WrongNumArgs {
                func: "car",
                want: 1,
                got: args.len(),
            }),
        }
    }

    fn builtin_cons(&mut self, args: &[Expr]) -> Result<Expr, RuntimeError> {
        match args {
            [left, right] => {
                let left = self.eval_expr(left)?;
                let right = self.eval_expr(right)?;

                match right {
                    Expr::Quoted(items) => Ok(Expr::Quoted(
                        std::iter::once(&left)
                            .chain(items.iter())
                            .cloned()
                            .collect(),
                    )),
                    Expr::Nil => Ok(Expr::Quoted(vec![left])),
                    _ => Err(RuntimeError::WrongType {
                        func: "cons",
                        want: "Quoted",
                        got: right.clone(),
                    }),
                }
            }
            _ => Err(RuntimeError::WrongNumArgs {
                func: "cons",
                want: 2,
                got: args.len(),
            }),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::assert_matches::assert_matches;

    #[test]
    fn test_cond() {
        let expr = Expr::parse_str("(cond 0 \"truth\" \"lies\")").unwrap();
        let expr = Evaluator::new().eval_expr(&expr).unwrap();
        assert_eq!(expr, Expr::String(String::from("lies")));

        let expr = Expr::parse_str("(cond 1 \"truth\" \"lies\")").unwrap();
        let expr = Evaluator::new().eval_expr(&expr).unwrap();
        assert_eq!(expr, Expr::String(String::from("truth")));

        let expr = Expr::parse_str("(cond 2 \"truth\" \"lies\")").unwrap();
        let expr = Evaluator::new().eval_expr(&expr).unwrap();
        assert_eq!(expr, Expr::String(String::from("truth")));

        let expr = Expr::parse_str("(cond \"x\" \"truth\" \"lies\")").unwrap();
        let expr = Evaluator::new().eval_expr(&expr).unwrap();
        assert_eq!(expr, Expr::String(String::from("truth")));
    }

    #[test]
    fn test_cond_complex_selector() {
        let expr = Expr::parse_str("(cond (add 0 0) \"truth\" \"lies\")").unwrap();
        let expr = Evaluator::new().eval_expr(&expr).unwrap();
        assert_eq!(expr, Expr::String(String::from("lies")));

        let expr = Expr::parse_str("(cond (add 1 0) \"truth\" \"lies\")").unwrap();
        let expr = Evaluator::new().eval_expr(&expr).unwrap();
        assert_eq!(expr, Expr::String(String::from("truth")));
    }

    #[test]
    fn test_cond_complex_result() {
        let expr = Expr::parse_str("(cond 1 (cond 0 \"a\" \"b\") \"c\")").unwrap();
        let expr = Evaluator::new().eval_expr(&expr).unwrap();
        assert_eq!(expr, Expr::String(String::from("b")));

        let expr = Expr::parse_str("(cond 0 \"c\" (cond 0 \"a\" \"b\"))").unwrap();
        let expr = Evaluator::new().eval_expr(&expr).unwrap();
        assert_eq!(expr, Expr::String(String::from("b")));
    }

    #[test]
    fn test_car_empty() {
        let expr = Expr::parse_str("(car (quote))").unwrap();
        assert_matches!(
            Evaluator::new().eval_expr(&expr),
            Err(RuntimeError::CarEmpty)
        );
    }

    #[test]
    fn test_car_simple() {
        let expr = Expr::parse_str("(car (quote 1 2 3))").unwrap();
        assert_matches!(Evaluator::new().eval_expr(&expr), Ok(Expr::Int(1)));
    }

    /// Test that `car` evaluates its argument rather than assuming it's already
    /// a quoted expression.
    #[test]
    fn test_car_eval_args() {
        let expr = Expr::parse_str("(car (cond 0 (quote) (quote 1 2)))").unwrap();
        assert_matches!(Evaluator::new().eval_expr(&expr), Ok(Expr::Int(1)));
    }

    #[test]
    fn test_car_eval_args_two_levels() {
        let expr = Expr::parse_str("(car (cond 0 (quote) (cond 0 (quote) (quote 1 2))))").unwrap();
        assert_matches!(Evaluator::new().eval_expr(&expr), Ok(Expr::Int(1)));
    }

    #[test]
    fn test_car_eval_args_empty() {
        let expr = Expr::parse_str("(car (cond 1 (quote) (quote 1 2)))").unwrap();
        assert_matches!(
            Evaluator::new().eval_expr(&expr),
            Err(RuntimeError::CarEmpty)
        );
    }

    #[test]
    fn test_car_eval_args_wrong_type() {
        let expr = Expr::parse_str("(car (cond 1 42 (quote 1 2)))").unwrap();
        assert_matches!(
            Evaluator::new().eval_expr(&expr),
            Err(RuntimeError::WrongType {
                func: _,
                want: _,
                got: _
            })
        );
    }

    #[test]
    fn test_eval_func_malformed() {
        let mut evaluator = Evaluator::new();
        assert_matches!(evaluator.eval("(def f (quote (add x 1)))"), Ok(Expr::Nil));
        assert_matches!(
            evaluator.eval("(f 42)"),
            Err(RuntimeError::MalformedFunction(_))
        );
    }

    #[test]
    #[should_panic]
    fn test_eval_func() {
        let mut evaluator = Evaluator::new();
        assert_matches!(
            evaluator.eval("(def f (quote (quote x) (add x 1)))"),
            Ok(Expr::Nil)
        );
        assert_matches!(evaluator.eval("(f 42)"), Ok(Expr::Int(43)));
    }
}
