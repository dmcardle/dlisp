# dlisp

This is a toy Lisp implementation.
The primary goal has been to have fun and learn, which means correctness is an afterthought.
I've intentionally avoided consulting any other Lisp implementations, so dlisp is almost certainly not compatible with any existing Lisp codebases.

## Key features

* Dynamic scoping because it's just what happened
* Builtin `print` function which is picky and only takes strings
* Builtin `show` function which does its darnedest to turn things into strings
* Builtin `quote`, `cond`, `cons`, `car`, `cdr`, `add`, `sub` do what you'd expect
* Syntactic sugar: `'(a b c)` is equivalent to  `(quote a b c)`
* You can define functions, e.g. `(def or '(a b) (cond a a b))`
* No optimizations whatsoever
* No filesystem access nor ability to make syscalls
* Exit the REPL by typing `quit`

For example code, see [stdlib.dl](stdlib.dl).

