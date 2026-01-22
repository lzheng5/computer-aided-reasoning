#|

Author: Pete Manolios
Date:   9/13/2022

Code used in lecture 2 of Computer-Aided Reasoning.

|#

(in-package "ACL2S")
(in-theory (disable acl2s-cancel-mod-+))

"
BEGIN DEMO 1

We introduce the ACL2s data definition framework via a sequence of
examples. The idea is to just remind everyone of defdata.  These notes
are not meant to be exhaustive.  So, read the reading material!
"

"
Range types allow us to define a range of numbers.  The two
examples below show how to define the rational interval [0..1]
and the integers greater than 2^{64}.
"

(defdata probability (range rational (0 <= _ <= 1)))
(defdata big-nat (range integer ((expt 2 64) < _)))

"
Property-based testing with property
"

(property (x :all)
  (=> (intp x) (rationalp x)))

(property (x :all)
  :hyps (intp x)
  (rationalp x))

(property (x :int)
  (rationalp x))

(property (x :all)
  (=> (rationalp x) (intp x)))

(property (x :probability y :probability)
  (probabilityp (+ x y)))

(property (x :probability y :probability)
  (probabilityp (* x y)))

(property (x :big-nat y :big-nat)
  (big-natp (+ x y)))

(property (x :big-nat y :big-nat)
  (big-natp (- x y)))

(property (x :big-nat)
  (big-natp (1- x)))

"
We can create list types using the listof combinator as follows.
"

(defdata loi (listof int))

"
This defines the type consisting of lists of integers.
"

"
Recursive type expressions involve the oneof
combinator and product combinations, where additionally there is
a (recursive) reference to the type being defined.
For example, here is another way of defining a list of integers.
"

(defdata loint (or nil (cons int loint)))

"Notice that lointp and loip are equivalent.
"

(property (x :all)
  (== (lointp x) (loip x)))

"
Consider a more complex data definition
"

(defdata UnaryOp '~)
(defdata BinOp (enum '(& + => ==)))
(defdata PropEx (or bool
                    var
                    (list UnaryOp PropEx)
                    (list PropEx Binop PropEx)))

"We now show an example of a custom data definition with a recognizer
and an enumerator for natural numbers divisible by 9 and >100.
"

(+ 1 2)
0

(definec customp (x :all) :bool
  (^ (integerp x)
     (= 0 (mod x 9))
     (> x 100)))

(definec nth-custom-builtin (n :nat) :int
  :post (customp (nth-custom-builtin n))
  (+ (* 9 n) 108))

"Here is the simplest way to create a custom type.
"

(register-type custom :predicate customp :enumerator nth-custom-builtin)

(defdata locustom (listof custom))

"Pay attention to the stats.
"

(must-fail
  (property (x :custom)
    :proofs? nil
    (!= 0 (mod x 17))))

"Notice that without the custom type, the stats are not as good.
"

(must-fail
  (property (x :int)
    (=> (^ (= 0 (mod x 9))
           (> x 100))
        (! (= 0 (mod x 17))))))

"We can use custom types to construct new types without restriction.
"

(defdata fob (or custom bool))

"Some examples of the enumerator.
"

(nth-fob 0)
(nth-fob 1)
(nth-fob 2)
(nth-fob 3)
(nth-fob 4)
(nth-fob 5)

"Next we consider signatures.
We define concat, which is the same as app,
but for which we do not have any theorems.
"

(definec concat (x :tl y :tl) :tl
  (if (endp x)
      y
    (cons (first x) (concat (rest x) y))))

; Holds due to the contract theorem
(property (x :tl y :tl)
  (tlp (concat x y)))

; Requires proof by induction
(property (x :loi y :loi)
  (loip (concat x y)))

; No proof by induction, due to a signature rule
(property (x :loi y :loi)
  (loip (append x y)))

; Here is an example of a signature rule
(sig concat ((listof :a) (listof :a)) => (listof :a))

; Now, notice that this goes through with no induction
(property (x :loi y :loi)
  (loip (concat x y)))

"
Look at the sig forms in the file base-theory.lisp to
see more examples. Here are a few.
"

(sig nth (nat (listof :a)) => :a
  :satisfies (< x1 (len x2)))

; got up to here
