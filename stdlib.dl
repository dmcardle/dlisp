;;;;
;;;; The DLISP standard library.
;;;;

(print "OK")

(def id '(x) x)
(print (show (id 42)))

(def not '(p) (cond p nil true))
(def and '(p q) (cond p q p))
(def or '(a b) (cond a a b))

;; A casting function from truthy values to `nil` or `false`. Note that this is
;; a second-order function because it invokes `not`, which is defined right here
;; in the stdlib!
(def bool '(p) (not (not p)))

;; Multiplication of positive integers.
;;
;; TODO: Design a scheme for handling bad inputs.
(def mul '(a b) (_mul a b 0))

;; Tail-recursive helper function for `mul`. Returns n * m + sum.
(def _mul '(n m sum)
  ;; Although (not n) would be sufficient, we can also
  ;; short-circuit when m is zero as an optimization.
  (cond (or (not n) (not m))
        sum
        (_mul (sub n 1)
              m
              (add sum m))))

;; Factorial of positive integers.
(def fact '(n)
  (cond (not n)
        1
        (mul n (fact (sub n 1)))))

;; A very horrible equality check for positive integers.
(def pos_eq '(a b)
  (cond (and (not a) (not b))
        true
        (cond (or (and (not a) b)
                  (and a (not b)))
              nil
              (pos_eq (sub a 1) (sub b 1)))))

;; Given positive integers `start` and `end`, returns the list of intermediate
;; values. Includes `start`, but excludes `end`.
(def range '(start end)
  (cond (pos_eq start end)
        '()
        (cons start
              (range (add start 1)
                     end))))

(def map '(f xs)
  (cond xs
        (cons (f (car xs)) (map f (cdr xs)))
        '()))

(def filter '(f xs)
  (cond xs
        (cond (f (car xs))
              (cons (car xs) (filter f (cdr xs)))
              (filter f (cdr xs)))
        '()))
