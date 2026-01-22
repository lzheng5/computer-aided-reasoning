#|

Copyright © 2026 by Pete Manolios 

Author: Pete Manolios
Date:   1/16/2022

Code used in lecture 3 of Computer-Aided Reasoning.  

|#

(in-package "ACL2S")

"BEGIN DEMO 1

"

(in-package "ACL2")
:pe +
:pe *
:pe append
:pe listp
:pe true-listp
:pe acl2s::tlp
:pe tlp
:pe cadr
:trans1 (* 1 2 3)
:trans1 (*)
:trans1 (cadr '(1 2 . 3))
:trans1 (append '(1 2) '(3 4) '(5 6))
(in-package "ACL2S")

#|

Rotate buffer to the left begin.

An example of how contracts are used to help students learn how
to program and specify contracts.

|#


"
Define a function that given a buffer, l, (a true list) and a natural
number, n, rotates the buffer to the left n times.

(Rotate-Left '(1 2 3 4 5) 2) = '(3 4 5 1 2)

"

(definec Rotate-Left (l :tl n :nat) :tl
  (cond ((= n 0) l)
        (t (Rotate-left (app (tail l) (head l))
                        (1- n)))))

(definec Rotate-Left (l :tl n :nat) :tl
  (cond ((= n 0) l)
        ((endp l) nil)
        (t (Rotate-Left (app (tail l) (head l))
                        (1- n)))))

(definec Rotate-Left (l :tl n :nat) :tl
  (cond ((= n 0) l)
        ((endp l) nil)
        (t (Rotate-Left (app (tail l) (list (head l)))
                               (1- n)))))
  
(check= (Rotate-Left '(1 2 3 4 5) 2) '(3 4 5 1 2))

(definec Rotate-Left2 (l :tl n :nat) :tl
  (match (list l n)
    ((:or (& 0) (nil &)) l)
    (((f . r) &) (Rotate-Left2 (app r (list f)) (1- n)))))

(property (l :tl n :nat)
  (== (Rotate-Left2 l n)
      (Rotate-Left l n)))

(property (l :tl n :nat)
  (= (len (Rotate-Left l n))
     (len l)))

(definec RL (l :tl n :nat) :tl
  (match (list l n)
    ((:or (& 0) (nil &)) l)
    (((f . r) &) (Rotate-Left2 (app (list f) r) (1- n)))))

(property (l :tl n :nat)
  (== (RL l n)
      (Rotate-Left l n)))

(definec drop-last (x :tl) :tl
  (match x
    ((:or nil (&)) nil)
    ((f . r) (cons f (drop-last r)))))

(property (l :tl l :cons)
  (= (len (drop-last l))
     (1- (len l))))

"We have :ne-tl too!"

(property (l :ne-tl)
  (= (len (drop-last l))
     (1- (len l))))

(definec prefixes (l :tl) :tl
  (match l
    (nil '( () ))
    (& (cons l (prefixes (drop-last l))))))

(prefixes '(a b c))

"That went through automatically. Let's investigate.
First undo the previous event. See :doc history.
"

:doc history

:u

"Next, revert to ACL2's built-in termination analysis.
"

(set-termination-method :measure)

"Next, definec is a macro that does a lot of stuff we don't 
see, so let's expand it enough to find the defun it generates.
"

:trans1 (definec prefixes (l :tl) :tl
          (match l
            (nil '( () ))
            (& (cons l (prefixes (drop-last l))))))

"This is the form that generates the defun
"

:trans1 (definec-core prefixes nil (l :tl)
          :tl (match l (nil '(nil))
                (& (cons l (prefixes (drop-last l))))))

"If we keep going, eventually, we see this defun, after stripping
declarations.
"

(defun prefixes (l)
  (mbe :logic (if (true-listp l)
                  (match l
                    (nil '(nil))
                    (& (cons l (prefixes (drop-last l)))))
                (acl2s-true-list-undefined 'prefixes
                                           (list l)))
       :exec (match l
               (nil '(nil))
               (& (cons l (prefixes (drop-last l)))))))


"Notice that it did in fact have to prove a size theorems
about drop-last!
"

"Now on to a few other examples.
"

(definec e1 (a b :pos) :pos
  (match (list a b)
    ((:or (1 &) (& 1)) 1)
    ((:t (< a b)) (e1 (- a 1) (- b 1)))
    (& (e1 b a))))

"Switch back to ACL2's termination method.
"

(set-termination-method :ccg)

(definec e1 (a b :pos) :pos
  (match (list a b)
    ((:or (1 &) (& 1)) 1)
    ((:t (< a b)) (e1 (- a 1) (- b 1)))
    (& (e1 b a))))

"These timeouts indicate non-terminating functions. Why?
Because testing takes a long time. We can set timeouts
for testing and for defunc"

:doc acl2s::cgen-timeout
:doc defunc
:doc set-defunc-timeout

"We can also force ACL2s to accept the definition by
using :program mode, but first, we disable testing.
"

:doc acl2::cgen
:doc acl2s::testing-enabled
(acl2s-defaults :set testing-enabled nil)
:program

(definec e1 (a b :pos) :pos
  (match (list a b)
    ((:or (1 &) (& 1)) 1)
    ((:t (< a b)) (e1 (- a 1) (- b 1)))
    (& (e1 b a))))

"Find a non-terminating input"

(e1 2 2)

"So, not admissible due to nontermination. 
(e1 2 2) will reach the third cond clause,
where the recursive call is (e1 2 2).
"
:pbt 1
:ubt! 7

"How can we fix e1?
(definec e1 (a :pos b :pos) :pos
  (match (list a b)
    ((:or (1 &) (& 1)) 1)
    ((:t (< a b)) (e1 (- a 1) (- b 1)))
    (& (e1 b a))))
"

(definec e1 (a b :pos) :pos
  (match (list a b)
    ((:or (1 &) (& 1)) 1)
    ((:t (<= a b)) (e1 (- a 1) (- b 1)))
    (& (e1 b a))))

(set-termination-method :ccg)

(definec e1 (a b :pos) :pos
  (match (list a b)
    ((:or (1 &) (& 1)) 1)
    ((:t (<= a b)) (e1 (- a 1) (- b 1)))
    (& (e1 b a))))

"Example 2. Terminating?
"

(definec e2 (x y :int) :int
  (if (< x y)
      (+ x y)
    (+ x (e2 x (1+ y)))))

(set-termination-method :measure)

(definec e3 (x :nat y :pos) :nat
  (match (list x y)
    ((0 &) x)
    ((& 1) y)
    ((:t (> x y)) (e3 y x))
    (& (e3 x (- y 1)))))

"Let's try to come up with a measure.
"

(definec m (x :nat y :pos) :nat
  (+ (* 2 x) y))

"We're not using the ACL2s termination analysis, which means that we
need to define a measure function that operates on any inputs. That
leads to the measure below which just returns 0 when e3's input
contract is violated and uses m for the interesting case.
"

(definec e3 (x :nat y :pos) :nat
  (declare (xargs :measure (if (! (^ (natp x) (posp y))) 0 (m x y))))
  (match (list x y)
    ((0 &) x)
    ((& 1) y)
    ((:t (> x y)) (e3 y x))
    (& (e3 x (- y 1)))))

"Exercise. Come up with a measure for e3 that works. See HWK 2.
"

"Let's see if CCG gets it.

"
:ubt! 8

(definec e3 (x :nat y :pos) :nat
  (match (list x y)
    ((0 &) x)
    ((& 1) y)
    ((:t (> x y)) (e3 y x))
    (& (e3 x (- y 1)))))

"One more example showing how to deal with rationals.
Does this terminate?
"

(definec e4 (x y :rational z :pos-rational) :rational
  (if (>= x 0)
      (* x y z)
    (+ (* x y z) (e4 (+ x z) (- y 1) z))))

"What's a measure?
"

(definec e4-measure (x :rational z :pos-rational) :nat
  (if (>= x 0)
      0
    (ceiling (- x) z)))

"Here is how you communicate measures to ACL2s. So, notice that there
is a difference between using ACL2s' default termination method, :ccg,
and using ACL2's termination method, :measure.
"

(definec e4 (x y :rational z :pos-rational) :rational
  (declare (xargs :consider-only-ccms ((e4-measure x z))))
  (if (>= x 0)
      (* x y z)
    (+ (* x y z) (e4 (+ x z) (- y 1) z))))

"In fact, ccms are just really measure hints. For example, 
we could done the following. Notice the difference between
consider-only-ccms and consider-ccms. If you use consider-ccms,
you are telling ACL2s to use that expression in constructing 
measures, but it is free to combine it with other expressions.
With consider-only-ccms, you are telling ACL2s to only use the
provided measure hints.
"
:u
:u

(definec e4 (x y :rational z :pos-rational) :rational
  (declare (xargs :consider-ccms ((ceiling (- x) z))))
  (if (>= x 0)
      (* x y z)
    (+ (* x y z) (e4 (+ x z) (- y 1) z))))

"If you want to  know more, see the CCG papers.
"

(set-termination-method :measure)

(definec weird (x y :nat) :pos
  (match (list x y)
    ((0 &) (1+ y))
    ((& 0) (weird (1- x) 1))
    (& (weird (1- x) (weird x (1- y))))))

"Does the above function terminate? What is a measure?
"

"Let's use ccg, but first programs whose complexity is high take long
during cgen so let's try using ccg but after turning testing off.
"

(set-termination-method :ccg)
(acl2s-defaults :set testing-enabled nil)

(definec weird (x y :nat) :pos
  (match (list x y)
    ((0 &) (1+ y))
    ((& 0) (weird (1- x) 1))
    (& (weird (1- x) (weird x (1- y))))))

"Think about what a measure for weird might be. 

This example highlights why we want to go beyond natural number
measures.
"

"Termination is undecidable. 

What's a really simple example of a function whose termination is
unknown?

This one.
"

(definec c (n :nat) :nat
  (match n
    ((:or 0 1) n)
    (:even (c (/ n 2)))
    (& (c (+ 1 (* 3 n))))))

:program

(definec c (n :nat) :nat
  (match n
    ((:or 0 1) n)
    (:even (c (/ n 2)))
    (& (c (+ 1 (* 3 n))))))

(c 121)
(c 8)
(c 7)
(c 5555555555)

"Let's see what's really going on by tracing c.
"

(trace$ c)

(c 121)
(c 8)
(c 7)
(c 55)
(c 5555555555)
(c 6171)
(c 837799)

"END DEMO"

