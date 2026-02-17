#|

 Copyright © 2026 by Pete Manolios
 CS 4820 Fall 2026

 Homework 4.
 Due: 2/16 (Midnight)

 For this assignment, work in groups of 1-2. Send me and the grader
 exactly one solution per team and make sure to follow the submission
 instructions on the course Web page. In particular, make sure that
 the subject of your email submission is "CS 4820 HWK 4".

 The group members are:
 Lingxiao Zheng

|#

#|

 In this homework, you will use ACL2s to prove theorems.  Think of
 ACL2s as a proof checker. You give it a proof outline and it checks
 it for you.  The high-level idea is that you provide ACL2s with
 theorems (named properties) that can be proved with, ideally, one
 level of induction. ACL2s will take care of the details, so that you
 do not have to, but you are still responsible for coming up with a
 proof outline.

 To use ACL2s effectively, you need to understand how ACL2s works,
 which we covered in class. For example, recall that theorems can be
 of different types; see rule-classes. Most of your theorems will be
 rewrite rules, so make sure you orient them appropriately and follow
 the other guidelines mentioned in class.  Also, you can specify which
 induction to use or any other hints, using the same options as defthm
 takes (see the documentation).

 The main challenge is figuring out which supporting theorems (lemmas)
 you need to prove the top-level theorems. The use of the professional
 method can be very helpful here.

 When ACL2s gets stuck or some theorem is not going through, use the
 "method" to figure out what ACL2s does not know that will allow it to
 make progress.

 For all your proofs in this homework, ACL2s should never do nested
 inductions. If it does, specify an appropriate lemma so that nested
 inductions are not needed.

 This homework has some hard problems, so start early and ask
 questions.

|#

(in-package "ACL2S")
(set-gag-mode nil) ; ACL2s shows what it is doing.

#|

 Start with the configuration below and once you are done with the
 homework, go to the next configuration, cranking up the rigor all the
 way up to (modeling-admit-all). That is, when you submit your
 homework the form below must be (modeling-admit-all), if you want to
 get full credit.

 After (modeling-start), try (modeling-validate-defs), then
 (modeling-admit-defs) and finally (modeling-admit-all).

 Tip: once you get one configuration working, you can test that there
 were no errors by going to the shell buffer and typing the following.

 (ubt! 1)
 (ld "hwk4.lisp")

 The first form undoes everything and the second loads hwk4.lisp. For
 the ld to work, you must have started acl2s in the directory where
 hwk4 resides, otherwise you have to specify a path. If the ld
 encounters an error, you will see it and you can see where that error
 occurred by typing

 (pbt 0)

 which will show you what events were accepted.

 Once that is working, change the configuration to the next one and do
 it again, fixing problems until done.

 Each problem has its own configuration, which gives you the
 flexibility work on problems in any order and to have different
 levels of rigor per problem, at a given point in time. All
 configurations should be set to (modeling-admit-all) to get full
 credit.

|#

;(modeling-start)

(set-induction-depth-limit 1)
(set-termination-method :measure)

(modeling-admit-all)

#|

Q1. Consider the following definition

|#

;; (definec bad-app (x y acc :tl) :tl
;;   (match (list x y)
;;     ((nil nil) acc)
;;     ((& nil) (bad-app y x acc))
;;     ((nil (f . r)) (bad-app x r (cons f acc)))
;;     (& (bad-app x nil (bad-app acc nil y)))))

#|

 ACL2s accepts the definition, but your job is to come up with a
 measure function and ACL2s proofs of the corresponding proof
 obligations. See the RAP lecture notes on measures; you can use
 generalized measure functions.

|#

; Define, m-bad-app, a measure function for bad-app.
; Q1a. We are using the definition on page 126

; Note: fill in the ...'s above, as you can use the generalized
; measure functions, as mentioned in Section 5.5.

; Q1b. Fill in the definition
(definec m-bad-app (x y :tl acc :all)
  :nat
  (match (list x y)
    ((nil nil) 0)
    ((& nil) (+ 1 (len x)))
    ((nil (& . &)) (len y))
    (& (+ 2 (len x) (len acc)))))

; The proof obligations for the termination proof of bad-app, using
; properties.  Make sure that ACL2s can prove all of these
; properties. When you increase the configuration for gradual
; verification to the final setting, ACL2s will require proofs. You
; can (and should) prove lemmas as needed.

; Q1c

(property bad-app-1 (x y acc :tl)
  (implies
   (and (consp x)
        (endp y))
   (< (m-bad-app y x acc)
      (m-bad-app x y acc))))

(property bad-app-2 (x y acc :tl)
  (implies
   (and (endp x)
        (consp y))
   (< (m-bad-app x (rest y) (cons (first y) acc))
      (m-bad-app x y acc))))

(property bad-app-3 (x y acc :tl)
  (implies
   (and (consp x)
        (consp y))
   (< (m-bad-app x nil (m-bad-app acc nil y))
      (m-bad-app x y acc))))

(property bad-app-4 (x y acc :tl)
  (implies
   (and (consp x)
        (consp y))
   (< (m-bad-app acc nil y)
      (m-bad-app x y acc))))

(definec bad-app (x y acc :tl)
  :tl
  (declare (xargs :measure (m-bad-app x y acc)))
  (match (list x y)
    ((nil nil) acc)
    ((& nil) (bad-app y x acc))
    ((nil (f . r)) (bad-app x r (cons f acc)))
    (& (bad-app x nil (bad-app acc nil y)))))

; Relate bad-app to app.
; Fill in the ... part below. You can only use functions app, rev, if
; and endp. Make sure that ACL2s can prove the property.

; Q1d

(property bad-app-nil-nil-acc (acc :tl)
  (== (bad-app nil nil acc) acc))

(property bad-app-x-nil-acc (x acc :tl)
  (implies (consp x)
           (== (bad-app x nil acc)
               (bad-app nil x acc))))

;; Checked with Pete. It is alright to use [append] instead of [app].
(property bad-app-nil-y-acc (x y acc :tl)
  (implies (endp x)
           (== (bad-app x y acc)
               (append (rev y) acc)))
    :hints (("goal" :induct (bad-app x y acc))))

(property bad-app-cons-y-nil (x y acc :tl)
  (implies (and (consp x)
                (endp acc))
           (== (bad-app x y acc)
               (append (rev x) y)))
    :hints (("goal" :induct (bad-app x y acc))))

(property bad-app-x-y-nil (x y :tl)
  (== (bad-app x y nil)
      (if (endp x)
          (rev y)
          (append (rev x) y))))

; Configuration: update as per instructions
; (modeling-start)

#|

Q2. Consider the following definition.

|#

;; (definec ack (n m :nat) :pos
;;   :skip-tests t ; ack is slow, so skip testing
;;   (match (list n m)
;;     ((0 &) (1+ m))
;;     ((& 0) (ack (1- n) 1))
;;     (& (ack (1- n) (ack n (1- m))))))

#|

 ACL2s accepts the definition, but your job is to come up with a
 measure function and ACL2s proofs of the corresponding proof
 obligations.

|#

; Define, m-ack, a measure function for ack.
; Q2a. We are using the definition on page 128-129

; Note: fill in the ...'s above, as you can use the generalized
; measure functions, as mentioned in Section 5.5.

; Q2b. Fill in the definition

(definec m-ack (n :nat m :all)
  :lex
  (if (natp m) (list n m) n))

; The proof obligations for the termination proof of ack, using
; properties.  Make sure that ACL2s can prove all of these
; properties.

; Q2c

(property m-ack-1 (n m :nat)
    (implies
     (and (not (zp n))
          (zp m))
     (l< (m-ack (1- n) m)
         (m-ack n m))))

(property m-ack-2 (n m :nat)
    (implies
     (and (not (zp n))
          (not (zp m)))
     (l< (m-ack n (1- m))
         (m-ack n m))))

(property m-ack-3 (n m :nat)
    (implies
     (and (not (zp n))
          (not (zp m)))
     (l< (m-ack (1- n) (m-ack n (1- m)))
         (m-ack n m))))

(definec ack (n m :nat)
  :pos
  :skip-tests t ; ack is slow, so skip testing
  (declare (xargs :measure (m-ack n m)))
  (match (list n m)
    ((0 &) (1+ m))
    ((& 0) (ack (1- n) 1))
    (& (ack (1- n) (ack n (1- m))))))

; Configuration: update as per instructions
; (modeling-start)

#|

Q3. Consider the following definitions.

|#

(defdata if-atom (or bool var))
(defdata if-expr (or if-atom (list 'if if-expr if-expr if-expr)))
(defdata norm-if-expr (or if-atom (list 'if if-atom norm-if-expr norm-if-expr)))

; Notice that norm-if-expr is a subtype of if-expr.
(defdata-subtype-strict norm-if-expr if-expr)

; The :skip-admissibilityp command below tells ACL2s to skip the
; termination proof, as ACL2s cannot prove termination without help.

;; (definec if-flat (x :if-expr) :norm-if-expr
;;   :skip-admissibilityp t
;;   (match x
;;     (:if-atom x)
;;     (('if a b c)
;;      (match a
;;        (:if-atom `(if ,a ,(if-flat b) ,(if-flat c)))
;;        (('if d e f)
;;         (if-flat `(if ,d (if ,e ,b ,c) (if ,f ,b ,c))))))))

#|

 Since match is a macro, it may help to know exactly what it expands
 into. If you aren't familiar with the backquote/comma duo, look it up
 and it may be useful to see what this expands into also. You can
 check using the ":trans1" form, which expands the top-level form one
 time and expands backquote/commas. To fully expand a form you can use
 ":trans" but that expands lets and conds and so on and may not be
 that readable. Try the following

 :trans1 (match x
           (:if-atom x)
           (('if a b c)
            (match a
              (:if-atom `(if ,a ,(if-flat b) ,(if-flat c)))
              (('if d e f)
               (if-flat `(if ,d (if ,e ,b ,c) (if ,f ,b ,c)))))))

 Notice that the nested match was not expanded, but you can copy that
 form and run trans1 on it to expand it.

|#

; Define, m-if-flat, a measure function for if-flat.
; Q3a. We are using the definition on page 127


; Q3b. Fill in the definition. This definition must be accepted by
; ACL2s.

;; Consulted Claude
(definec m-if-flat (x :if-expr) :pos
  (match x
    (:if-atom 1)
    (('if a b c)
     (* (m-if-flat a)
        (+ 1 (m-if-flat b) (m-if-flat c))))))

; The proof obligations for the termination proof of if-flat, using
; properties.  Make sure that ACL2s can prove all of these
; properties. When you increase the configuration for gradual
; verification to the final setting, ACL2s will require proofs. You
; can (and should) prove lemmas as needed.

; Q3c
(property m-if-flat-1 (x :if-expr)
  (implies
   (and (consp x)
        (eq (car x) 'if)
        (consp (cdr x))
        (consp (cdr (cdr x)))
        (consp (cdr (cdr (cdr x))))
        (eq (cdr (cdr (cdr (cdr x)))) nil)
        (let ((a (car (cdr x))))
          (if-atomp a)))
   (let ((b (car (cdr (cdr x)))))
     (l< (m-if-flat b)
         (m-if-flat x)))))

(property m-if-flat-2 (x :if-expr)
  (implies
   (and (consp x)
        (eq (car x) 'if)
        (consp (cdr x))
        (consp (cdr (cdr x)))
        (consp (cdr (cdr (cdr x))))
        (eq (cdr (cdr (cdr (cdr x)))) nil)
        (let ((a (car (cdr x))))
          (if-atomp a)))
   (let ((c (car (cdr (cdr (cdr x))))))
     (l< (m-if-flat c)
         (m-if-flat x)))))

(property m-if-flat-3 (x :if-expr)
  (implies
   (and (consp x)
        (eq (car x) 'if)
        (consp (cdr x))
        (consp (cdr (cdr x)))
        (consp (cdr (cdr (cdr x))))
        (eq (cdr (cdr (cdr (cdr x)))) nil)
        (let ((a (car (cdr x))))
          (and (consp a)
               (eq (car a) 'if)
               (consp (cdr a))
               (consp (cdr (cdr a)))
               (consp (cdr (cdr (cdr a))))
               (eq (cdr (cdr (cdr (cdr a)))) nil))))
   (let ((a (car (cdr x)))
         (b (car (cdr (cdr x))))
         (c (car (cdr (cdr (cdr x))))))
     (let ((d (car (cdr a)))
           (e (car (cdr (cdr a))))
           (f (car (cdr (cdr (cdr a))))))
       (l< (m-if-flat `(if ,d (if ,e ,b ,c) (if ,f ,b ,c)))
           (m-if-flat x))))))

(definec if-flat (x :if-expr) :norm-if-expr
  (declare (xargs :measure (m-if-flat x)))
  (match x
    (:if-atom x)
    (('if a b c)
     (match a
       (:if-atom `(if ,a ,(if-flat b) ,(if-flat c)))
       (('if d e f)
        (if-flat `(if ,d (if ,e ,b ,c) (if ,f ,b ,c))))))))

#|

 We will now prove that if-flat does not change the semantics of if
 expressions using ideas similar to those from HWK2. We will define
 assignments and an evaluator for if expressions.

|#

(defdata if-assign (alistof var bool))

; Notice that if var is not in the if-assign, we return nil.
(definec lookup-var (var :var a :if-assign) :bool
  (match a
    (nil nil)
    (((!var . val) . &) val)
    (& (lookup-var var (cdr a)))))

(definec lookup-atom (e :if-atom a :if-assign) :bool
  (match e
    (:bool e)
    (& (lookup-var e a))))

(definec if-eval (e :if-expr a :if-assign) :bool
  (match e
    (:if-atom (lookup-atom e a))
    (('if x y z)
     (if (if-eval x a) (if-eval y a) (if-eval z a)))))

; Q3d
; State and prove that for all if-assign's, an if-expr e evaluates to
; the same thing as (if-flat e). This should go though automatically,
; but, remember, you have to provide enough lemmas so that there are
; no nested inductions! Also, remember theorems are rewrite rules, so
; orient appropriately.

;; how come this type of subgoal showed up and cannot be refuted automatically ???
(property bad-if-eval (x y :all a :if-assign)
  (implies (and (not (consp x))
                (if-exprp (list* 'if x y))
                (consp y)
                (consp (cdr y))
                (not (cddr y))
                (not (booleanp x))
                (not (varp x))
                (if-assignp a))
           (not (if-eval (list* 'if x y) a))))

(property if-flat-equal-if (x :if-expr a :if-assign)
  (== (if-eval (if-flat x) a) (if-eval x a))
  :hints (("goal" :induct (if-flat x))))

#|

 Check-validp is a simple validity checker for if-expr's.  The idea is
 to use if-flat to normalize the if-expr. Then, we start with an empty
 if-assign and check validity by traversing the expression. When we
 get to a variable that is not assigned, we check that the expression
 is a validity when the variable is t and when it is nil.

|#

; Lookup assoc-equal in the documentation.
(definec assignedp (e :if-atom a :if-assign) :bool
  (or (boolp e)
      (consp (assoc-equal e a))))

(definec validp (e :norm-if-expr a :if-assign) :bool
  (match e
    (:if-atom (lookup-atom e a))
    (('if x y z)
     (if (assignedp x a)
         (if (lookup-atom x a)
             (validp y a)
           (validp z a))
       (and (validp y (acons x t a))
            (validp z (acons x nil a)))))))

(definec check-validp (e :if-expr) :bool
  (validp (if-flat e) nil))

; Q3e
;
; Formalize and prove the soundness of check-validp.  That is, if
; (check-validp e) = t, then evaluating e under a, an arbitrary
; if-assign, results in t.

(property lookup-var-append-snd (x :var a b :if-assign)
  (implies
   (not (assoc-equal x a))
   (== (lookup-var x (append a b)) (lookup-var x b))))

;; `lookup_var` returns `t` then `v \in a`
;; but not the other way around
(property lookup-var-assoc-equal (x :var a :if-assign)
  (implies
   (lookup-var x a)
   (assoc-equal x a)))

;; lemma about `lookup-atom`
(property lookup-atom-assigned (e :if-atom a :if-assign)
  (implies
   (lookup-atom e a)
   (assignedp e a)))

(property lookup-atom-append-fst (e :if-atom a b :if-assign)
  (implies
   (assignedp e a)
   (== (lookup-atom e (append a b))
       (lookup-atom e a))))

(property lookup-atom-append-snd (e :if-atom a b :if-assign)
  (implies
   (not (assignedp e a))
   (== (lookup-atom e (append a b))
       (lookup-atom e b))))

(property if-eval-append-acons-not-in-1 (e :if-expr x :var a b :if-assign)
  (implies
   (and (lookup-var x b)
        (not (assoc-equal x a)))
   (== (if-eval e (cons (cons x t) (append a b)))
       (if-eval e (append a b)))))

(property if-eval-append-acons-not-in-2 (e :if-expr x :var a b :if-assign)
  (implies
   (and (not (lookup-var x b))
        (not (assoc-equal x a)))
   (== (if-eval e (cons (cons x nil) (append a b)))
       (if-eval e (append a b)))))

;; The following cases corresponds to the case analysis of [validp-sound] in q3.thy.
;; These are proved in ACL2s.
;; But sadly, ACL2s cannot pick them up no matter how I rearrange them.

(property validp-sound-if-atom (x :norm-if-expr a b :if-assign)
  (implies
   (and (if-atomp x)
        (validp x a))
   (if-eval x (append a b))))

(property validp-sound-1 (x :if-atom y z :norm-if-expr a b :if-assign)
  (implies
   (and (implies
         (and (assignedp x a)
              (lookup-atom x a)
              (validp y a))
         (if-eval y (append a b)))
        (assignedp x a)
        (lookup-atom x a)
        (validp y a))
   (if-eval `(if ,x ,y ,z) (append a b))))

(property validp-sound-1-1 (x :if-atom y z :norm-if-expr a b :if-assign)
  (implies
   (and (assignedp x a)
        (lookup-atom x a)
        (validp y a)
        (if-eval y (append a b)))
   (if-eval `(if ,x ,y ,z) (append a b))))

(property validp-sound-1-1-1 (e :norm-if-expr a b :if-assign)
  (implies
   (and (consp e)
        (equal (car e) 'if)
        (consp (cdr e))
        (consp (cddr e))
        (consp (cdddr e))
        (not (cddddr e))
        (let ((x (cadr e))
              (y (caddr e)))
          (and (assignedp x a)
               (lookup-atom x a)
               (validp y a)
               (if-eval y (append a b)))))
   (if-eval e (append a b))))

(property validp-sound-2 (x :if-atom y z :norm-if-expr a b :if-assign)
  (implies
   (and (implies
         (and (assignedp x a)
              (not (lookup-atom x a))
              (validp z a))
         (if-eval z (append a b)))
        (assignedp x a)
        (not (lookup-atom x a))
        (validp z a))
   (if-eval `(if ,x ,y ,z) (append a b))))

(property validp-sound-2-2 (x :if-atom y z :norm-if-expr a b :if-assign)
  (implies
   (and (assignedp x a)
        (not (lookup-atom x a))
        (validp z a)
        (if-eval z (append a b)))
   (if-eval `(if ,x ,y ,z) (append a b))))

(property validp-sound-2-2-2 (e :norm-if-expr a b :if-assign)
  (implies
   (and (consp e)
        (equal (car e) 'if)
        (consp (cdr e))
        (consp (cddr e))
        (consp (cdddr e))
        (not (cddddr e))
        (let ((x (cadr e))
              (z (cadddr e)))
          (and (assignedp x a)
               (not (lookup-atom x a))
               (validp z a)
               (if-eval z (append a b)))))
   (if-eval e (append a b))))

(property validp-sound-3 (x :var y z :norm-if-expr a b :if-assign)
  (implies
   (and (implies
         (and (not (assignedp x a))
              (validp y (acons x t a)))
         (if-eval y (append (acons x t a) b)))

        (not (assignedp x a))
        ;; (validp `(if ,x ,y ,z) a)
        (and (validp y (acons x t a))
             (validp z (acons x nil a)))

        (lookup-atom x (append a b)))
   (if-eval `(if ,x ,y ,z) (append a b))))

(property validp-sound-3-3 (x :var y z :norm-if-expr a b :if-assign)
  (implies
   (and (not (assignedp x a))
        (validp y (acons x t a))
        (lookup-atom x (append a b))
        (if-eval y (append (acons x t a) b)))
   (if-eval `(if ,x ,y ,z) (append a b))))

(property validp-sound-3-3-3 (e :norm-if-expr a b :if-assign)
  (implies
   (and (consp e)
        (equal (car e) 'if)
        (consp (cdr e))
        (consp (cddr e))
        (consp (cdddr e))
        (not (cddddr e))
        (let ((x (cadr e))
              (y (caddr e)))
          (and (not (assignedp x a))
               (validp y (acons x t a))
               (lookup-atom x (append a b))
               (if-eval y (append (acons x t a) b)))))
   (if-eval e (append a b))))

(property validp-sound-4 (x :var y z :norm-if-expr a b :if-assign)
  (implies
   (and (implies
         (and (not (assignedp x a))
              (validp z (acons x nil a)))
         (if-eval z (append (acons x nil a) b)))

        (not (assignedp x a))
        ;; (validp `(if ,x ,y ,z) a)
        (and (validp y (acons x t a))
             (validp z (acons x nil a)))

        (not (lookup-atom x (append a b))))
   (if-eval `(if ,x ,y ,z) (append a b))))

(property validp-sound-4-4 (x :var y z :norm-if-expr a b :if-assign)
  (implies
   (and (not (assignedp x a))
        (validp z (acons x nil a))
        (not (lookup-atom x (append a b)))
        (if-eval z (append (acons x nil a) b)))
   (if-eval `(if ,x ,y ,z) (append a b))))

(property validp-sound-4-4-4 (e :norm-if-expr a b :if-assign)
  (implies
   (and (consp e)
        (equal (car e) 'if)
        (consp (cdr e))
        (consp (cddr e))
        (consp (cdddr e))
        (not (cddddr e))
        (let ((x (cadr e))
              (z (cadddr e)))
          (and (not (assignedp x a))
               (validp z (acons x nil a))
               (not (lookup-atom x (append a b)))
               (if-eval z (append (acons x nil a) b)))))
   (if-eval e (append a b))))

;; ------------------------------------------------------
;; Below doesn't work in ACL2s.

;; I gave up here
;; See the alternative proof [validp-sound] in q3.thy.

;(set-induction-depth-limit nil)
;(set-gag-mode t)

;; `a` is the assignment built by `validp` so far
(property validp-sound (e :norm-if-expr a b :if-assign)
  (implies
   (validp e a)
   (if-eval e (append a b)))
  :hints (("goal" :induct (validp e a))))

(property check-validp-is-sound (e :if-expr a :if-assign)
  (implies (check-validp e) (if-eval e a)))

; Configuration: update as per instructions
; (modeling-start)


; Q3f
;
; Prove that check-validp is complete by showing that when
; check-validp returns nil, there is some if-assign under which the
; if-expr evaluates to nil. With this proof, we now know that
; check-validp is a decision procedure for PL validity.


;; See [validp-complete] in q3.thy

(property check-validp-is-complete (e :if-expr a :if-assign)
  (implies (if-eval e a) (check-validp e)))

#|

 Q4. We will now reason about sorting algorithms. Consider the
 following definitions for insert sort and quicksort.

|#

;; See the documentation for <<, which is a total order on the ACL2s
;; universe, so we can compare anything, no matter the types. This
;; allows us to define sorting algorithms that work on integers,
;; rationals, strings, whatever (but using the << ordering).

(definec <<= (x y :all) :bool
  (or (== x y)
      (<< x y)))

(definec insert (a :all x :tl) :tl
  (match x
    (() (list a))
    ((e . es) (if (<<= a e)
                  (cons a x)
                (cons e (insert a es))))))

(definec isort (x :tl) :tl
  (match x
    (() ())
    ((e . es) (insert e (isort es)))))

(definec less (a :all x :tl) :tl
  (match x
    (() ())
    ((e . es) (if (<< e a)
                  (cons e (less a es))
                (less a es)))))

(definec notless (a :all x :tl) :tl
  (match x
    (() ())
    ((e . es) (if (<<= a e)
                  (cons e (notless a es))
                (notless a es)))))

(definec qsort (x :tl) :tl
  (match x
    (() ())
    ((e . es) (app (qsort (less e es))
                   (list e)
                   (qsort (notless e es))))))

#|

 Q4. Prove the following property.

 This is not easy, so I strongly recommend that you come up with a
 plan and use the professional method to sketch out a proof.

|#

;; See [isort_qsort] in q4.thy

(property qsort=isort (x :tl)
  (== (qsort x)
      (isort x)))

#|

 Extra Credit 1. (25 points each, all or nothing)


 1. First, prove (in ACL2s) that if x and y are ordered true lists,
 under <<=, and permutations of each other, they are equal. Second,
 prove that qsort and isort return ordered permutations of their
 input.

;; See [mset_sorted] in q4.thy

 2. Do the homework in another theorem prover of your choice. Try to
 make it as equivalent as possible. Provide a summary of your
 findings.  This is only recommended for those of you that already
 have experience with other theorem provers. ACL2 is not allowed this
 time.

;; For slightly more complicated proofs, like reasoning about programming languages,
;; ACL2s does *not* scale. Why?

;; 1. It desugars pattern match forms, making the subgoals very hard to reason about,
;;    essentially we have to mentally reconstruct the terms!

;; 2. No stable rewrites!
;;    This makes the subgoals very easy to go out of whack. And the user is lost where she is.

;; 3. It simplifies too much, even the induction hypothesis gets simplified away!
;;    As a result, we have no idea what the IH is.

;; 4. It couldn't pick up lemmas very easily.

|#
