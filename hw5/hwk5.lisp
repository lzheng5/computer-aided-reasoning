#|

 Copyright © 2026 by Pete Manolios
 CS 4820 Fall 2026

 Homework 5.
 Due: 3/12 (Midnight)

 For this assignment, work in groups of 1-2. Send me and the grader
 exactly one solution per team and make sure to follow the submission
 instructions on the course Web page. In particular, make sure that
 the subject of your email submission is "CS 4820 HWK 5".

 The group members are:

 Ling Zheng

 To make sure that we are all on the same page, build the latest
 version of ACL2s, as per HWK1. You are going to be using SBCL, which
 you already have, due to the build process in

 Next, install quicklisp. See https://www.quicklisp.org/beta/.

 To make sure everything is OK with quicklisp and to initialize it,
 start sbcl and issue the following commands

 (load "~/quicklisp/setup.lisp")
 (ql:quickload :trivia)
 (ql:quickload :cl-ppcre)
 (ql:quickload :let-plus)
 (setf ppcre:*allow-named-registers* t)
 (exit)

 Next, clone the ACL2s interface repository:
 (https) https://gitlab.com/acl2s/external-tool-support/interface.git
 (ssh)   git@gitlab.com:acl2s/external-tool-support/interface.git

 This repository includes scripts for interfacing with ACL2s from lisp.
 Put this directory in the ...books/acl2s/ of your ACL2 repository, or
 use a symbolic link.

 Now, certify the books, by going to ...books/acl2s/interface and
 typing

 "cert.pl -j 4 top"

 Look at the documentation for cert.pl. If cert.pl isn't in your path,
 then use

 "...books/build/cert.pl -j 4 top"

 The "-j 4" option indicates that you want to run up to 4 instances of
 ACL2 in parallel. Set this number to the number of cores you have.

 As mentioned at the beginning of the semester, some of the code we
 will write is in Lisp. You can find the common lisp manual online in
 various formats by searching for "common lisp manual."

 Other references that you might find useful and are available online
 include

 - Common Lisp: A Gentle Introduction to Symbolic Computation by David
   Touretzky
 - ANSI Common Lisp by Paul Graham

|#

(in-package "ACL2S")

;; Now for some ACL2s systems programming.

;; This book is already included in ACL2s, so this is a no-op, but I'm
;; putting it here so that you can see where the code for ACL2s
;; systems programming is coming from.
(include-book "acl2s/interface/top" :dir :system)
(set-ignore-ok t)

;; This gets us to raw lisp.
:q

#|

 The interface books provide us with the ability to call the theorem
 prover within lisp, which will be useful in checking your code.

 Here are some examples you can try. acl2s-compute is the form you use
 when you are using ACL2s to compute something, e.g., running a
 function on some input. acl2s-query is the form you use when you are
 querying ACL2s, e.g., a property without a name. If the property has
 a name, then that is not a query, but an event and you have to use
 acl2s-event.

 (acl2s-compute '(+ 1 2))
 (acl2s-query '(property (p q :all)
                 (iff (=> p q)
                      (v (! p) q))))
|#

#|

 Next, we need to load some software libraries using quicklisp.  For
 example, the trivia library provides pattern matching
 capabilities. Search for "match" below. Links to online documentation
 for the software libraries are provided below.

|#

(load "~/quicklisp/setup.lisp")

; See https://lispcookbook.github.io/cl-cookbook/pattern_matching.html
(ql:quickload :trivia)

; See https://www.quicklisp.org/beta/UNOFFICIAL/docs/cl-ppcre/doc/index.html
(ql:quickload :cl-ppcre)

; See https://github.com/sharplispers/let-plus
(ql:quickload :let-plus)

(setf ppcre:*allow-named-registers* t)

#|

 We now define our own package.

|#

(defpackage :tp (:use :cl :trivia :ppcre :let-plus :acl2 :acl2s))
(in-package :tp)

;; We import acl2s-compute and acl2s-query into our package.

(import 'acl2s-interface-internal::(acl2s-compute acl2s-query))

#|

 We have a list of the propositional operators and information about
 them.

 :arity can be a positive integer or - (meaning arbitrary arity) If
 :arity is -, there must be an identity and the function must be
 associative and commutative.

 If :identity is non-nil, then the operator has the indicated
 identity.

 An operator is idempotent iff :idem is t.

 If :sink is not -, then it must be the case that (op ... sink ...) =
 sink, e.g., (and ... nil ...) = nil.

 FYI: it is common for global variables to be enclosed in *'s.

|#

(defparameter *p-ops*
  '((and     :arity - :identity t   :idem t   :sink nil)
    (or      :arity - :identity nil :idem t   :sink t)
    (not     :arity 1 :identity -   :idem nil :sink -)
    (implies :arity 2 :identity -   :idem nil :sink -)
    (iff     :arity - :identity t   :idem nil :sink -)
    (xor     :arity - :identity nil :idem nil :sink -)
    (if      :arity 3 :identity -   :idem nil :sink -)))

#|

 mapcar is like map. See the common lisp manual.
 In general if you have questions about lisp, ask on Piazza.

|#

(defparameter *p-funs* (mapcar #'car *p-ops*))

#|

 See the definition of member in the common lisp manual.  Notice that
 there are different types of equality, including =, eql, eq, equal
 and equals. We need to be careful, so we'll just use equal and we'll
 define functions that are similar to the ACL2s functions we're
 familiar with.

|#

(defun in (a x)
  (member a x :test #'equal))

(defmacro len (l) `(length ,l))

(defun p-funp (x)
  (in x *p-funs*))

(defun key-alist->val (k l)
  (let* ((in (assoc k l :test #'equal)))
    (values (cdr in) in)))

(key-alist->val 'iff *p-ops*)

(defun key-list->val (k l)
  (let* ((in (member k l :test #'equal)))
    (values (cadr in) in)))

(key-list->val ':arity  (key-alist->val 'iff *p-ops*))

(defun pfun-key->val (fun key)
  (key-list->val key (key-alist->val fun *p-ops*)))

(defun remove-dups (l)
  (remove-duplicates l :test #'equal))

(defmacro == (x y) `(equal ,x ,y))
(defmacro != (x y) `(not (equal ,x ,y)))

(defparameter *booleans* '(t nil))

(defun booleanp (x)
  (in x *booleans*))

(defun pfun-argsp (pop args)
  (and (p-funp pop)
       (let ((arity (key-list->val :arity (key-alist->val pop *p-ops*))))
         (and (or (== arity '-)
                  (== (len args) arity))
              (every #'p-formulap args)))))

#|

 Here is the definition of a propositional formula.

|#

(defun p-formulap (f)
  (match f
    ((type boolean) t) ; don't need this case, but here for emphasis
    ((type symbol) t)
    ((list* pop args)
     (if (p-funp pop)
         (pfun-argsp pop args)
       t))
    (_ nil)))

#|

 Notice that in addition to propositional variables, we allow atoms
 such as (foo x).

 Here are some assertions (see the common lisp manual).

|#

(assert (p-formulap '(and)))
(assert (p-formulap '(and x y z)))
(assert (p-formulap '(and t nil)))
(assert (not (p-formulap '(implies x t nil))))
(assert (p-formulap 'q))
(assert (p-formulap '(implies (foo x) (bar y))))
(assert (p-formulap '(iff p q r s t)))
(assert (p-formulap '(xor p q r s t)))
(assert (not (p-formulap '(if p q r t))))

#|

 The propositional skeleton is what remains when we remove
 non-variable atoms.

|#

(defun p-skeleton-args (args amap acc)
  (if (endp args)
      (values (reverse acc) amap)
    (let+ (((&values na namap)
            (p-skeleton (car args) amap)))
          (p-skeleton-args (cdr args) namap (cons na acc)))))

(defun p-skeleton (f &optional amap) ;amap is nil if not specified
  (match f
    ((type symbol) (values f amap))
    ((list* pop args)
     (if (p-funp pop)
         (let+ (((&values nargs namap)
                 (p-skeleton-args args amap nil)))
               (values (cons pop nargs) namap))
       (let ((geta (key-alist->val f amap)))
         (if geta
             (values geta amap)
           (let ((gen (gentemp "P")))
             (values gen (acons f gen amap)))))))
    (_ (error "Not a p-formula"))))

#|

 Here are some examples you can try.

(p-skeleton
 '(or p q r s))

(p-skeleton
 '(iff q r))

(p-skeleton
 '(or p (iff q r)))

(p-skeleton
 '(or p (iff q r) (and p q p) (if p (and p q) (or p q))))

(p-skeleton
 '(iff p p q (foo t nil) (foo t nil) (or p q)))

(p-skeleton
 '(xor p p q (foo t nil) (foo t nil) (or p q)))

(p-skeleton
 '(iff p p q (foo t r) (foo s nil) (or p q)))

(p-skeleton
 '(or (foo a (g a c)) (g a c) (not (foo a (g a c)))))

|#

#|

 Next we have some utilities for converting propositional formulas to
 ACL2s formulas.

|#

(defun nary-to-2ary (fun args)
  (let ((identity (pfun-key->val fun :identity)))
    (match args
      (nil identity)
      ((list x) (to-acl2s x))
      (_ (acl2s::xxxjoin (to-acl2s fun) (mapcar #'to-acl2s args))))))

(defun to-acl2s (f)
  (let ((s (p-skeleton f)))
    (match s
      ((type symbol) (intern (symbol-name f) "ACL2S"))
      ((cons x xs)
       (if (in x '(iff xor))
           (nary-to-2ary x xs)
         (mapcar #'to-acl2s f)))
      (_ f))))

(to-acl2s '(and a b c d))
(to-acl2s '(iff a b c d))
(to-acl2s '(xor a b c d))

(defun pvars- (f)
  (match f
    ((type boolean) nil)
    ((type symbol) (list f))
    ((list* op args)
     (and (p-funp op)
          (reduce #'append (mapcar #'pvars- args))))))

(defun pvars (f) (remove-dups (pvars- f)))

(pvars '(and t (iff nil) (iff t nil t nil) p q))
(pvars '(iff p p q (foo t r) (foo s nil) (or p q)))
(pvars '(if p q (or r (foo t s) (and (not q)))))

(defun boolean-hyps (l)
  (reduce #'append
          (mapcar #'(lambda (x) `(,x :bool))
                  (mapcar #'to-acl2s l))))

(boolean-hyps '(p q r))

(defun acl2s-check-equal (f g)
  (let* ((iff `(iff ,f ,g))
         (siff (p-skeleton iff))
     (pvars (pvars siff))
     (aiff (to-acl2s siff))
         (af (second aiff))
         (ag (third aiff))
         (bhyps (boolean-hyps pvars)))
    (acl2s-query
     `(acl2s::property ,bhyps (acl2s::iff ,af ,ag)))))

;; And some simple examples.
(acl2s-check-equal 'p 'p)
(acl2s-check-equal 'p 'q)

; Here is how to check if the query succeeded
(assert (== (car (acl2s-check-equal 'p 'p)) nil))

; So, here's a useful function
(defun assert-acl2s-equal (f g)
  (assert (== (car (acl2s-check-equal f g)) nil)))

(assert-acl2s-equal 'p 'p)

(defun assert-equal (f g)
  (assert (== f g) (f g) "Formulas were not equal!~%F: ~A~%G: ~A" f g))

(defun assertf (f in out)
  (assert-equal (funcall f in) out))

#|

; This will lead to an error. Try it.
; In sbcl :top gets you out of the debugger.
(assert-acl2s-equal 'p 'q)

|#

; Here is how we can use ACL2s to check our code.
(let* ((x '(or (foo a (g a c)) (g a c) (not (foo a (g a c))))))
  (assert-acl2s-equal x t))

(let* ((x '(or (foo a (g a c)) (g a c) (not (foo a (g a c)))))
       (sx (p-skeleton x)))
  (assert-acl2s-equal sx t))


#|

 Question 1. (25 pts)

 Define function, p-simplify that given a propositional formula
 returns an equivalent propositional formula with the following
 properties.

 A. The skeleton of the returned formula is either a constant or does
 not include any constants. For example:

 (and p t (foo t nil) q) should be simplified to (and p (foo t nil) q)
 (and p t (foo t b) nil) should be simplified to nil

 B. Flatten expressions, e.g.:

 (and p q (and r s) (or u v)) is not flat, but this is
 (and p q r s (or u v))

 A formula of the form (op ...) where op is a Boolean operator of
 arbitrary arity (ie, and, or, iff) applied to 0 or 1 arguments is not
 flat. For example, replace (and) with t.

 A formula of the form (op ... (op ...)) where op is a Boolean
 operator of arbitrary arity is not flat. For example, replace (and p
 q (and r s)) with (and p q r s).

 C. If there is Boolean constant s s.t. If (op ... s ...) = s, then we
 say that s is a sink of op. For example t is a sink of or. A formula
 is sink-free if no such subformulas remain. The returned formula
 should be sink-free.

 D. Simplify your formulas so that no subexpressions of the following
 form remain

 (not (not f))
 (not (iff ...))
 (not (xor ...))

 E. Apply Shannon expansions in 61-67.

 For example

 (and (or p q) (or r q p) p) should be simplified to

 p because (and (or t q) (or r q t) p) is (and t t p) is p

 F. Simplify formulas so that no subexpressions of the form

 (op ... p ... q ...)

 where p, q are equal literals or  p = (not q) or q = (not p).

 For example

 (or x y (foo a b) z (not (foo a b)) w) should be simplified to

 t

 Make sure that your algorithm is as efficient as you can make
 it. The idea is to use this simplification as a preprocessing step,
 so it needs to be fast.

 You are not required to perform any other simplifications beyond
 those specified above. If you do, your simplifier must be guaranteed
 to always return something that is simpler that what would be
 returned if you just implemented the simplifications explicitly
 requested. Also, if you implement any other simplifications, your
 algorithm must run in comparable time (eg, no validity checking).
 Notice some simple consequences. You cannot transform the formula to
 an equivalent formula that uses a small subset of the
 connectives (such as not/and). If you do that, the formula you get
 can be exponentially larger than the input formula, as we have
 discussed in class. Notice that even negation normal form (NNF) can
 increase the size of a formula. Such considerations are important
 when you use Tseitin, because experience has shown that even
 transformations such as NNF are usually a bad idea when generating
 CNF, as they tend to result in CNF formulas that take modern solvers
 longer to analyze.

 Test your definition with assert-acl2s-equal using at least 10
 propositional formulas that include non-variable atoms, all of the
 operators, deeply nested formulas, etc.


|#

(defun partition (pred list)
  "Partition list into (values trues falses) based on pred"
  (loop for x in list
        if (funcall pred x) collect x into trues
        else collect x into falses
        finally (return (values trues falses))))

(defun p-simplify-implies (f)
  (match f
    ((list 'implies p q)
     (let ((sp (p-simplify-implies p))
           (sq (p-simplify-implies q)))
       `(or (not ,sp) ,sq)))
    ((list* op args)
     `(,op ,@(mapcar #'p-simplify-implies args)))
    (_ f)))

(defun p-simplify-const (f)
  (match f
    ((list 'not a)
     (let ((a (p-simplify-const a)))
       (match a
         ((type boolean) (not a))
         (_ `(not ,a)))))

    ((list 'if a b c)
     (let ((a (p-simplify-const a))
           (b (p-simplify-const b))
           (c (p-simplify-const c)))
        (cond ((== a t) b)
              ((== a nil) c)
              ((== b c) b)
              ((and (== b t) (== c nil)) a)
              ((and (== b nil) (== c t)) `(not ,a))
              ((== b t) `(or ,a ,c))
              ((== c nil) `(and ,a ,b))
              ((== b nil) `(and (not ,a) ,c))
              ((== c t) `(or (not ,a) ,b))
              (t `(if ,a ,b ,c)))))

    ((list* op as)
     (let ((as (mapcar #'p-simplify-const as)))
       (match op
         ((or 'iff 'xor)
          (let+ (((&values consts non-consts) (partition #'booleanp as))
                 (id (pfun-key->val op :identity))
                 (result (if (== op 'iff)
                             (evenp (count nil consts))
                             (oddp (count t consts)))))
            (if (== result id)
                (cond ((null non-consts) id)
                      ((null (cdr non-consts)) (car non-consts))
                      (t `(,op ,@non-consts)))
                (cond ((null non-consts) result)
                      ((null (cdr non-consts)) `(not ,(car non-consts)))
                      (t `(,op ,result ,@non-consts))))))

         ((or 'and 'or)
          (let* ((pop (key-alist->val op *p-ops*))
                 (id (key-list->val :identity pop))
                 (sink (key-list->val :sink pop)))
            (if (in sink as)
                sink
                `(,op
                  ,@(reduce
                     #'(lambda (a as)
                         (if (booleanp a)
                             (if (== a id) as `(,a ,@as))
                             `(,a ,@as)))
                     as
                     :from-end t
                     :initial-value nil)))))

         (_ `(,op ,@as)))))

    (_ f)))

(assertf #'p-simplify-const '(and x y t) '(and x y))
(assertf #'p-simplify-const '(or x y t) 't)
(assertf #'p-simplify-const '(and p t (foo t nil) q) '(and p (foo t nil) q))
(assertf #'p-simplify-const '(iff t nil p q) '(iff nil p q))
(assertf #'p-simplify-const '(iff nil p) '(not p))
(assertf #'p-simplify-const '(not (not p)) '(not (not p)))
(assertf #'p-simplify-const '(not (iff (iff) (or) q)) '(not (iff (or) q)))
(assertf #'p-simplify-const '(xor t nil q) '(not q))

(defun p-simplify-flatten (f)
  (match f
    ((list* op as)
     (if (p-funp op)
         (let* ((pop (key-alist->val op *p-ops*))
                (arity (key-list->val :arity pop)))
           (cond ((== arity '-)
                  (let ((sz (len as)))
                    (cond ((== sz 0) (key-list->val :identity pop))
                          ((== sz 1) (car as))
                          (t `(,op
                               ,@(reduce
                                  #'(lambda (a as)
                                      (match a
                                       ((list* op0 bs)
                                        (if (== op op0)
                                            `(,@bs ,@as)
                                            `(,a ,@as)))
                                        (_ `(,a ,@as))))
                                  (mapcar #'p-simplify-flatten as)
                                  :from-end t
                                  :initial-value nil))))))
                 (t `(,op ,@(mapcar #'p-simplify-flatten as)))))
         `(,op ,@(mapcar #'p-simplify-flatten as))))
    (_ f)))

(assertf #'p-simplify-flatten '(not (foo (and))) '(not (foo t)))
(assertf #'p-simplify-flatten '(not (foo (and p))) '(not (foo p)))
(assertf #'p-simplify-flatten '(and p q (and r s) (or u v)) '(and p q r s (or u v)))
(assertf #'p-simplify-flatten '(not (not p)) '(not (not p)))
(assertf #'p-simplify-flatten '(not (iff (iff) (and) (or) q)) '(not (iff t t nil q)))

(defun p-simplify-not (f)
  (match f
    ((list 'not a)
     (match a
       ((list 'not b) (p-simplify-not b))
       ((list* 'iff bs)
        (let ((bs (mapcar #'p-simplify-not bs)))
          (match bs
            (nil nil)  ; (not (iff)) -> nil
            ((list a) `(not ,a))  ; (not (iff a)) -> (not a)
            ((list a b) `(xor ,a ,b))  ; (not (iff a b)) -> (xor a b)
            ((list* a bs)  ; (not (iff a b c ...)) -> (xor a (iff b c ...))
             `(xor ,a (iff ,@bs))))))
       ((list* 'xor bs)
        (let ((bs (mapcar #'p-simplify-not bs)))
          (match bs
            (nil t)  ; (not (xor)) -> t
            ((list a) `(not ,a))  ; (not (xor a)) -> (not a)
            ((list a b) `(iff ,a ,b))  ; (not (xor a b)) -> (iff a b)
            ((list* a bs)  ; (not (xor a b c ...)) -> (iff a (xor b c ...))
             `(iff ,a (xor ,@bs))))))
       ((list* op bs) `(not (,op ,@(mapcar #'p-simplify-not bs))))
       (_ `(not ,a))))
    ((list* op as) `(,op ,@(mapcar #'p-simplify-not as)))
    (_ f)))

(assertf #'p-simplify-not '(not (not p)) 'p)
(assertf #'p-simplify-not '(not (iff t nil q)) '(xor t (iff nil q)))

(defun negate (f)
  "Get the negation of f"
  (match f
    ((list 'not a) a)
    (_ `(not ,f))))

(defun has-opposite (f args)
  (in (negate f) args))

(defun p-simplify-dup (f)
  "Simplify duplicated and opposite subformulas"
  (match f
    ((list* op as)
     (let ((as (mapcar #'p-simplify-dup as)))
       (cond
         ;; and/or: idempotent, check for p and (not p)
         ((in op '(and or))
          (let* ((pop (key-alist->val op *p-ops*))
                 (sink (key-list->val :sink pop)))
            ;; Check for opposite: p and (not p) => sink
            (if (some #'(lambda (a) (has-opposite a as)) as)
                sink
              ;; Remove duplicates (idempotent)
              `(,op ,@(remove-dups as)))))

         ;; iff: p iff p = t (identity), p iff (not p) = nil
         ((== op 'iff)
          (let* ((pairs (make-hash-table :test #'equal))
                 (seen (make-hash-table :test #'equal))
                 (neg-count 0)
                 (result nil))
            ;; Count occurrences
            (dolist (a as)
              (incf (gethash a pairs 0)))
            ;; Check for opposites and count odd occurrences
            (maphash #'(lambda (k v)
                         (let ((neg (negate k)))
                           (let+ (((&values neg-val neg-present?) (gethash neg pairs)))
                             (when (and neg-present? (not (gethash neg seen)))
                               ;; Mark both as seen
                               (setf (gethash k seen) t)
                               (setf (gethash neg seen) t)
                               ;; Reduce counts
                               (let ((n (min v neg-val)))
                                 (incf neg-count n)
                                 (decf (gethash k pairs) n)
                                 (decf (gethash neg pairs) n))))))
                     pairs)
            ;; Build result: keep odd occurrences
            (maphash #'(lambda (k v)
                         (when (oddp v)
                           (push k result)))
                     pairs)
            ;; Add nil for each opposite pair (nil is not identity for iff)
            (dotimes (i neg-count)
              (push nil result))
            (cond ((null result) t)
                  ((null (cdr result)) (car result))
                  (t `(iff ,@(reverse result))))))

         ;; xor: p xor p = nil (identity), p xor (not p) = t
         ((== op 'xor)
          (let* ((pairs (make-hash-table :test #'equal))
                 (seen (make-hash-table :test #'equal))
                 (neg-count 0)
                 (result nil))
            ;; Count occurrences
            (dolist (a as)
              (incf (gethash a pairs 0)))
            ;; Check for opposites
            (maphash #'(lambda (k v)
                         (let ((neg (negate k)))
                           (let+ (((&values neg-val neg-present?) (gethash neg pairs)))
                             (when (and neg-present? (not (gethash neg seen)))
                               ;; Mark both as seen
                               (setf (gethash k seen) t)
                               (setf (gethash neg seen) t)
                               ;; Reduce counts
                               (let ((n (min v neg-val)))
                                 (incf neg-count n)
                                 (decf (gethash k pairs) n)
                                 (decf (gethash neg pairs) n))))))
                     pairs)
            ;; Build result: keep odd occurrences
            (maphash #'(lambda (k v)
                         (when (oddp v)
                           (push k result)))
                     pairs)
            ;; Add t for each opposite pair
            (dotimes (i neg-count)
              (push t result))
            (cond ((null result) nil)
                  ((null (cdr result)) (car result))
                  (t `(xor ,@(reverse result))))))

         ;; if: check specific cases
         ((== op 'if)
          (match as
            ((list a b c)
             (cond ((equal b c) b)
                   ((equal a b) `(or ,a ,c))      ; (if a a c) = (or a c)
                   ((equal a c) `(and ,a ,b))     ; (if a b a) = (and a b)
                   ((equal a (negate b)) `(and ,b ,c))  ; (if a (not a) c) = (and (not a) c)
                   ((equal a (negate c)) `(or ,b ,c))   ; (if a b (not a)) = (or b (not a))
                   (t `(if ,@as))))
            (_ `(if ,@as))))

         (t `(,op ,@as)))))

    (_ f)))

(assertf #'p-simplify-dup '(iff nil p q) '(iff nil p q))
(assertf #'p-simplify-dup '(iff p q p) 'q)
(assertf #'p-simplify-dup '(xor p q p) 'q)
(assertf #'p-simplify-dup '(iff p q (not p)) '(iff q nil))

(defun extend (keys vals env)
  (if (endp keys)
      env
      (extend (cdr keys) (cdr vals)
              (acons (car keys) (car vals) env))))

(defun p-simplify-shannon (f &optional env)
  "Apply Shannon expansions to simplify formulas.
   env is an association list mapping variables to their values (t/nil).

   Pre: env should not contain duplicates or opposite literals. For example, it should not contain both p and (not p)."
  (match f
    ((type boolean) f)
    ((type symbol) (let+ (((&values v found) (key-alist->val f env)))
                     (if found v f)))
    ((list 'not a)
     (match a
       ((type symbol) (let+ (((&values v found) (key-alist->val a env)))
                        (if found (not v) f)))
       (_ `(not ,(p-simplify-shannon a env)))))

    ((list* op as)
     (cond ((in op '(and or))
            (let+ ((pop (key-alist->val op *p-ops*))
                   (id (key-list->val :identity pop))
                   (as (mapcar #'(lambda (a)
                                   (match a
                                       ((type symbol)
                                        (let+ (((&values v found) (key-alist->val a env)))
                                          (if found v a)))
                                     ((list 'not b)
                                      (match b
                                          ((type symbol) (let+ (((&values v found) (key-alist->val b env)))
                                                           (if found (not v) a)))
                                        (_ a)))
                                     (_ a)))
                               as))
                   ((&values vars nvars) (partition #'symbolp as))
                   ((&values nlits as) (partition
                                        #'(lambda (a)
                                            (match a
                                                ((list 'not (type symbol)) a)
                                              (_ nil)))
                                        nvars))
                   (nvars (mapcar #'(lambda (lit)
                                      (match lit
                                          ((list 'not v) v)
                                        (_ lit)))
                                  nlits))
                   (nenv (extend vars (mapcar #'(lambda (v) id) vars)
                                 (extend nvars (mapcar #'(lambda (v) (not id)) nvars)
                                         env))))
              `(,op ,@vars ,@nlits ,@(mapcar #'(lambda (a) (p-simplify-shannon a nenv)) as))))

           ((p-funp op) `(,op ,@(mapcar #'(lambda (a) (p-simplify-shannon a env)) as)))

           ;; Non-variable atom: keep as-is
           (t f)))))

(assertf #'p-simplify-shannon '(iff nil p q) '(iff nil p q))
(assertf #'p-simplify-shannon '(and (or p q) (or r q p) p) '(and p (or t q) (or r q t)))
(assertf #'p-simplify-shannon '(and (or p q) (or r q p) (not p)) '(and (not p) (or nil q) (or r q nil)))
(assertf #'p-simplify-shannon '(and (not p) q (or r q)) '(and q (not p) (or r t)))
(assertf #'p-simplify-shannon '(or (and p q) (and r q p) p) '(or p (and nil q) (and r q nil)))
(assertf #'p-simplify-shannon '(or p q (and r q)) '(or p q (and r nil)))
(assertf #'p-simplify-shannon '(or (and p q) (and r q p) (not p)) '(or (not p) (and t q) (and r q t)))
(assertf #'p-simplify-shannon '(or (not p) q (and r q)) '(or q (not p) (and r nil)))
(assertf #'p-simplify-shannon '(or a (foo a) (bar b)) '(or a (foo a) (bar b)))

(defun p-simplify-fixpoint (f)
  (let ((new-f (p-simplify-const
                (p-simplify-shannon
                 (p-simplify-dup
                  (p-simplify-not
                   (p-simplify-flatten f)))))))
    (if (equal new-f f)
        f
        (p-simplify-fixpoint new-f))))

(defun p-simplify (f)
  (p-simplify-fixpoint
    (p-simplify-implies f)))

;; Dup
(assertf #'p-simplify '(iff p q (not p)) '(not q))

;; Shannon
(assertf #'p-simplify '(and (or p q) (or r q p) p) 'p)
(assertf #'p-simplify '(and (or p q) (or r q p) (not p)) '(and q (not p)))
(assertf #'p-simplify '(or (and p q) (and r q p) p) 'p)
(assertf #'p-simplify '(or (and p q) (and r q p) (not p)) '(or q (not p)))

;; Non-variable atoms
(assertf #'p-simplify '(iff (foo a) (foo a) (bar b)) '(bar b))
(assertf #'p-simplify '(iff (foo a) (bar b) (not (foo a))) '(not (bar b)))
(assertf #'p-simplify '(or a (foo a) (bar b)) '(or a (foo a) (bar b)))

;; not + iff/xor
(assertf #'p-simplify '(iff (and) (or) q) '(not q))
(assertf #'p-simplify '(not (iff (and) (or) q)) 'q)
(assertf #'p-simplify '(xor (and) (or) q) '(not q))
(assertf #'p-simplify '(not (xor (and) (or) q)) 'q)

(defun test-simplify (f)
  (assert-acl2s-equal f (p-simplify f)))

;; Test cases generated by Claude
;; A. Constant simplification
(test-simplify '(and p t q))                    ; remove identity
(test-simplify '(and p nil q))                  ; sink
(test-simplify '(or p nil q))                   ; remove identity
(test-simplify '(or p t q))                     ; sink
(test-simplify '(and p t (foo t nil) q))        ; non-variable atoms with constants
(test-simplify '(iff t nil p q))                ; iff with constants
(test-simplify '(xor t t p))                    ; xor with constants

;; B. Flatten expressions
(test-simplify '(and p q (and r s) (or u v)))   ; nested and
(test-simplify '(or a (or b c) d))              ; nested or
(test-simplify '(iff p (iff q r)))              ; nested iff
(test-simplify '(xor a (xor b c)))              ; nested xor
(test-simplify '(and))                          ; 0 args
(test-simplify '(or))                           ; 0 args
(test-simplify '(and p))                        ; 1 arg
(test-simplify '(or q))                         ; 1 arg

;; C. Sink handling
(test-simplify '(and a b nil c))                ; nil is sink for and
(test-simplify '(or a b t c))                   ; t is sink for or

;; D. (not (not ...)), (not (iff ...)), (not (xor ...))
(test-simplify '(not (not p)))
(test-simplify '(not (xor p)))
(test-simplify '(not (xor p q)))
(test-simplify '(not (iff p q)))
(test-simplify '(not (iff (and) (or) q)))
(test-simplify '(not (iff (and) (or) q)))

;; E. Shannon expansion example from spec
(test-simplify '(and (or p q) (or r q p) p))    ; should simplify to p

;; F. Duplicate and opposite subformulas
(test-simplify '(and p p q))                    ; duplicate in and
(test-simplify '(or p p q))                     ; duplicate in or
(test-simplify '(and p (not p) q))              ; opposite in and -> nil
(test-simplify '(or p (not p) q))               ; opposite in or -> t
(test-simplify '(or x y (foo a b) z (not (foo a b)) w))  ; opposite with non-var atom
(test-simplify '(iff p p q))                    ; duplicate in iff
(test-simplify '(xor p p q))                    ; duplicate in xor
(test-simplify '(iff p (not p)))                ; opposite in iff -> nil
(test-simplify '(xor p (not p)))                ; opposite in xor -> t

;; implies handling
(test-simplify '(implies p q))
(test-simplify '(implies (implies a b) c))

;; if handling
(test-simplify '(if t a b))                     ; constant condition
(test-simplify '(if nil a b))
(test-simplify '(if p t nil))                   ; special cases
(test-simplify '(if p nil t))
(test-simplify '(if p a a))                     ; same branches

;; Deeply nested formulas
(test-simplify '(and (or (and p q) (not (not r))) (iff s (xor t u))))
(test-simplify '(implies (and a (or b c)) (iff (not d) e)))
(test-simplify '(if (and p q) (or r s) (iff t (not u))))

;; Non-variable atoms throughout
(test-simplify '(and (foo x) (bar y) (not (foo x))))
(test-simplify '(or (f a b) (g c) (not (g c))))
(test-simplify '(iff (foo a) (foo a) (bar b)))

#|

 Question 2. (20 pts)

 Define tseitin, a function that given a propositional formula,
 something that satisfies p-formulap, applies the tseitin
 transformation to generate a CNF formula that is equi-satisfiable.

 Remember that you have to deal with atoms such as

 (foo (if a b))

 You should simplify the formula first, using p-simplify, but do not
 perform any other simplifications. Any simpification you want to
 perform must be done in p-simplify.

 Test tseitin using with assert-acl2s-equal using at least 10
 propositional formulas.

|#

(defun tseitin-op (v op args)
  "Generate CNF clauses: v ↔ (op args...)"
  (case op
    (not
     (let ((a (car args)))
       `((or ,v ,a)
         (or (not ,v) (not ,a)))))

    (and
     ;; v ↔ (a1 ∧ ... ∧ an)
     ;; (¬v ∨ a1) ∧ ... ∧ (¬v ∨ an) ∧ (v ∨ ¬a1 ∨ ... ∨ ¬an)
     (append
      (mapcar #'(lambda (a) `(or (not ,v) ,a)) args)
      `((or ,v ,@(mapcar #'(lambda (a) `(not ,a)) args)))))

    (or
     ;; v ↔ (a1 ∨ ... ∨ an)
     ;; (¬v ∨ a1 ∨ ... ∨ an) ∧ (v ∨ ¬a1) ∧ ... ∧ (v ∨ ¬an)
     (append
      `((or (not ,v) ,@args))
      (mapcar #'(lambda (a) `(or ,v (not ,a))) args)))

    (iff
     ;; v ↔ (a ↔ b): both same polarity
     ;; (¬v ∨ ¬a ∨ b) ∧ (¬v ∨ a ∨ ¬b) ∧ (v ∨ ¬a ∨ ¬b) ∧ (v ∨ a ∨ b)
     (assert (= (length args) 2) () "iff must be binary after unchaining")
     (let ((a (first args))
           (b (second args)))
       `((or (not ,v) (not ,a) ,b)
         (or (not ,v) ,a (not ,b))
         (or ,v (not ,a) (not ,b))
         (or ,v ,a ,b))))

    (xor
     ;; v ↔ (a ⊕ b): different polarity
     ;; (¬v ∨ ¬a ∨ ¬b) ∧ (¬v ∨ a ∨ b) ∧ (v ∨ ¬a ∨ b) ∧ (v ∨ a ∨ ¬b)
     (assert (= (length args) 2) () "xor must be binary after unchaining")
     (let ((a (first args))
           (b (second args)))
       `((or (not ,v) (not ,a) (not ,b))
         (or (not ,v) ,a ,b)
         (or ,v (not ,a) ,b)
         (or ,v ,a (not ,b)))))

    (if
     ;; v ↔ (if a b c) ≡ v ↔ ((a ∧ b) ∨ (¬a ∧ c))
     ;; (¬v ∨ ¬a ∨ b) ∧ (¬v ∨ a ∨ c) ∧ (v ∨ ¬a ∨ ¬b) ∧ (v ∨ a ∨ ¬c)
     (assert (= (length args) 3) () "if must be ternary")
     (let ((a (first args))
           (b (second args))
           (c (third args)))
       `((or (not ,v) (not ,a) ,b)
         (or (not ,v) ,a ,c)
         (or ,v (not ,a) (not ,b))
         (or ,v ,a (not ,c)))))

    (otherwise
     (error "Unknown operator in Tseitin: ~A" op))))

(defun tseitin-unchain (f)
  "Recursively convert n-ary iff/xor to binary form.
   (iff a b c d) -> (iff (iff (iff a b) c) d)"
  (match f
    ((type boolean) f)
    ((type symbol) f)
    ((list* op args)
     (let ((args (mapcar #'tseitin-unchain args)))
       (if (and (in op '(iff xor)) (> (length args) 2))
           (reduce #'(lambda (acc x) `(,op ,acc ,x))
                   (cddr args)
                   :initial-value `(,op ,(first args) ,(second args)))
           `(,op ,@args))))
    (_ f)))

(defun tseitin-transform (f)
  "Transform formula f to CNF using Tseitin transformation.
   Returns CNF as (and clause1 clause2 ...)"
  (let ((clauses nil))
    (labels ((transform-subf (subf)
               "Transform subformula, return its representative variable"
               (match subf
                 ((type boolean) subf)
                 ((type symbol) subf)
                 ((list* op args)
                  (if (p-funp op)
                      (let* ((arg-vars (mapcar #'transform-subf args))
                             (v (gentemp "T"))
                             (new-clauses (tseitin-op v op arg-vars)))
                        (setf clauses (append new-clauses clauses))
                        v)
                      subf)))))
      (match f
        ((type boolean) f)
        ((type symbol) f)
        ((list 'not (type symbol)) f)
        ((list 'not (list* 'or args))
         (dolist (arg args)
           (let ((top-var (transform-subf `(not ,arg))))
             (push top-var clauses)))
         `(and ,@(reverse clauses)))

        ((list* 'and args)
         (dolist (arg args)
           (let ((top-var (transform-subf arg)))
             (push top-var clauses)))
         `(and ,@(reverse clauses)))

        ((list 'iff a b)
         (let ((va (transform-subf a))
               (vb (transform-subf b)))
           (push `(or (not ,va) ,vb) clauses)
           (push `(or (not ,vb) ,va) clauses)
           `(and ,@(reverse clauses))))

        ((list 'xor a b)
         (let ((va (transform-subf a))
               (vb (transform-subf b)))
           (push `(or (not ,va) (not ,vb)) clauses)
           (push `(or ,va ,vb) clauses)
           `(and ,@(reverse clauses))))

        (_
         (let ((top-var (transform-subf f)))
            (push top-var clauses)
           `(and ,@(reverse clauses))))))))

(defun tseitin (f)
  (let+ (((&values skeleton amap) (p-skeleton f))
         (simplified (p-simplify skeleton))
         (unchained (tseitin-unchain simplified))
         (cnf (tseitin-transform unchained))
         (simplified-cnf (p-simplify cnf))) ;; p-simplify preserves CNF
    (values simplified-cnf skeleton amap)))

(defun acl2s-valid? (f)
  "Check if f is valid (tautology) using ACL2s"
  (== (car (acl2s-check-equal f 't)) nil))

(defun acl2s-unsat? (f)
  "Check if f is unsatisfiable using ACL2s (f is UNSAT iff (negate f) is valid)"
  (acl2s-valid? (negate f)))

(defun literalp (f)
  (match f
    ((type boolean) t)
    ((type symbol) t)
    ((list 'not a) (or (symbolp a) (booleanp a)))
    (_ nil)))

(defun clausep (f)
  (match f
    ((type boolean) t)
    ((type symbol) t)
    ((list 'not a) (literalp f))
    ((list* 'or args) (every #'literalp args))
    (_ nil)))

(defun cnfp (f)
  (match f
    ((type boolean) t)
    ((type symbol) t)
    ((list 'not a) (literalp f))
    ((list* 'or args) (clausep f))
    ((list* 'and args) (every #'clausep args))
    (_ nil)))

(defun test-tseitin (f)
  "Test equisatisfiability: f is UNSAT iff (tseitin f) is UNSAT"
  (let* ((cnf (tseitin f))
         (f-unsat (acl2s-unsat? f))
         (cnf-unsat (acl2s-unsat? cnf)))
    (assert (cnfp cnf) () "Result not in CNF: ~A" cnf)
    (assert (eq f-unsat cnf-unsat) ()
            "Equisat failed for ~A: f-unsat=~A, cnf-unsat=~A" f f-unsat cnf-unsat)))

;; Tests generated with Claude
;; Basic tests
(test-tseitin 'p)
(test-tseitin 't)
(test-tseitin 'nil)
(test-tseitin '(not p))
(test-tseitin '(and p q))
(test-tseitin '(or p q))
(test-tseitin '(iff p q))
(test-tseitin '(xor p q))
(test-tseitin '(if p q r))

;; More complex formulas
(test-tseitin '(and p (or q r)))
(test-tseitin '(implies p (and q r)))
(test-tseitin '(iff (and p q) (or r s)))
(test-tseitin '(not (or (and p q) (and r s))))
(test-tseitin '(if (and p q) (or r s) (not t)))

;; Nested formulas
(test-tseitin '(and (or p (not q)) (iff r (xor s t))))
(test-tseitin '(or (and a b) (and c (or d e))))
(test-tseitin '(implies (or p q) (and r (not s))))

;; With non-variable atoms
(test-tseitin '(or (foo a b) (bar c)))
(test-tseitin '(and (f x) (g y) (not (h z))))


#|

 Question 3. (30 pts)

 Define DP, a function that given a propositional formula in CNF,
 applies the Davis-Putnam algorithm to determine if the formula is
 satisfiable.

 Remember that you have to deal with atoms such as

 (foo (if a b))

 If the formula is sat, DP returns 'sat and a satisfying assignment: an
 alist mapping each atom in the formula to t/nil. Use values to return
 multiple values.

 If it is usat, return 'unsat.

 Do some profiling

 Test DP using with assert-acl2s-equal using at least 10
 propositional formulas.

 It is easy to extend dp to support arbitrary formulas by using
 tseitin to generate CNF.

|#

;;; ============================================================
;;; Common SAT Representations for Variables, Clauses, and Assignments
;;; ============================================================

;;; ============================================================
;;; Hash Set API - Simple set abstraction over hash tables
;;; ============================================================

(defun make-hash-set ()
  "Create an empty hash set"
  (make-hash-table :test #'eql))

(defun hash-set-add (set elem)
  "Add element to hash set (mutates set)"
  (setf (gethash elem set) t))

(defun hash-set-contains? (set elem)
  "Check if element is in hash set"
  (gethash elem set))

(defun hash-set-size (set)
  "Return number of elements in hash set"
  (hash-table-count set))

(defun hash-set-map (fn set)
  "Apply function fn to each element in set"
  (maphash #'(lambda (k v) (declare (ignore v)) (funcall fn k)) set))

(defun hash-set->list (set)
  "Convert hash set to list"
  (let ((result nil))
    (hash-set-map #'(lambda (elem) (push elem result)) set)
    result))

(defun hash-set-copy-except (set elem)
  "Create a new hash set with all elements except elem"
  (let ((new-set (make-hash-set)))
    (hash-set-map #'(lambda (e)
                      (unless (equal e elem)
                        (hash-set-add new-set e)))
                  set)
    new-set))

;;; ============================================================
;;; Variable Manager - Maps between symbolic and numeric variables
;;; Encoding: variable n -> literal 2n (positive), literal 2n+1 (negative)
;;; ============================================================

(defstruct var-manager
  "Manages mapping between symbolic variables and numeric variables"
  (sym->num (make-hash-table :test #'equal))  ; symbol -> number
  (num->sym (make-hash-table :test #'eql))    ; number -> symbol
  (counter 0))                                ; next available variable number

(defun var-manager-get-num (vm sym)
  "Get or create numeric variable for symbolic variable"
  (let+ (((&values num present?) (gethash sym (var-manager-sym->num vm))))
    (if present?
        num
        (let ((new-num (var-manager-counter vm)))
          (setf (gethash sym (var-manager-sym->num vm)) new-num)
          (setf (gethash new-num (var-manager-num->sym vm)) sym)
          (setf (var-manager-counter vm) (1+ new-num))
          new-num))))

(defun var-manager-get-sym (vm num)
  "Get symbolic variable for numeric variable"
  (gethash num (var-manager-num->sym vm)))

(defun var-manager-sym-lit->num-lit (vm sym-lit)
  "Convert symbolic literal to numeric literal"
  (match sym-lit
    ((list 'not v)
     (let ((var-num (var-manager-get-num vm v)))
       (1+ (* 2 var-num))))  ; negative literal: 2n+1
    (_
     (let ((var-num (var-manager-get-num vm sym-lit)))
       (* 2 var-num)))))     ; positive literal: 2n

(defun var-manager-num-lit->sym-lit (vm num-lit)
  "Convert numeric literal to symbolic literal"
  (let* ((var-num (ash num-lit -1))         ; extract variable number
         (pos? (evenp num-lit))         ; check polarity
         (sym (var-manager-get-sym vm var-num)))
    (if pos?
        sym
        `(not ,sym))))

(defun var-manager->string (vm)
  "Convert variable manager mappings to string"
  (let ((pairs nil))
    (maphash #'(lambda (sym num)
                 (push (format nil "~A -> ~A" sym num) pairs))
             (var-manager-sym->num vm))
    (if pairs
        (format nil "Variable Mapping: ~%~{  ~A~%~}" (sort pairs #'string<))
        "Variable Mapping: (empty)")))

(defun var-manager-num-vars (vm)
  "Return number of variables in variable manager"
  (var-manager-counter vm))

;;; ============================================================
;;; Numeric Literal Operations
;;; Encoding: variable n -> literal 2n (positive), literal 2n+1 (negative)
;;; ============================================================

(declaim (inline lit-var lit-sign lit-negate make-lit))
(declaim (ftype (function (fixnum) fixnum) lit-var))
(declaim (ftype (function (fixnum) boolean) lit-sign))
(declaim (ftype (function (fixnum) fixnum) lit-negate))
(declaim (ftype (function (fixnum t) fixnum) make-lit))

(defun lit-var (lit)
  "Extract variable number from numeric literal"
  (declare (type fixnum lit))
  (the fixnum (ash lit -1)))

(defun lit-sign (lit)
  "Check if numeric literal is positive"
  (declare (type fixnum lit))
  (evenp lit))

(defun lit-negate (lit)
  "Negate numeric literal"
  (declare (type fixnum lit))
  (the fixnum (logxor lit 1)))

(defun make-lit (var-num pos?)
  "Create numeric literal from variable number and polarity"
  (declare (type fixnum var-num))
  (the fixnum
       (if pos?
           (* 2 var-num)
           (1+ (* 2 var-num)))))

(defun lit->string (lit &optional vm)
  "Convert numeric literal to string. If vm provided, use symbolic names."
  (let ((var (lit-var lit))
        (sign (lit-sign lit)))
    (if vm
        (let ((sym (var-manager-get-sym vm var)))
          (if sign
              (format nil "~A" sym)
              (format nil "~~~A" sym)))
        (if sign
            (format nil "~A" var)
            (format nil "~~~A" var)))))

;;; ============================================================
;;; Clause API - Abstraction over clause representation
;;; Current implementation: Hash sets with numeric literals
;;;
;;; This API provides a clean abstraction so that the clause
;;; representation can be easily changed (e.g., to use numeric
;;; variables or bit vectors) without modifying the DP algorithm.
;;;
;;; Current encoding: variable n -> literal 2n (positive), 2n+1 (negative)
;;; ============================================================

;; TODO: bit vectors for variable sets (pos/neg tracking)

(defun make-clause (&optional (lits nil))
  "Create a clause from a list of literals, lits"
  (let ((clause (make-hash-set)))
    (dolist (lit lits clause)
      (hash-set-add clause lit))))

(defun clause-has-lit? (cl lit)
  "Check if literal is in clause"
  (hash-set-contains? cl lit))

(defun clause-has-var? (cl var)
  "Check if variable (regardless of polarity) is in clause"
  (or (clause-has-lit? cl (make-lit var t))
      (clause-has-lit? cl (make-lit var nil))))

(defun clause-size (cl)
  "Return number of literals in clause"
  (hash-set-size cl))

(defun clause-empty? (cl)
  "Check if clause is empty"
  (zerop (hash-set-size cl)))

(defun clause-unit? (cl)
  "Check if clause is a unit clause (size 1)"
  (= 1 (hash-set-size cl)))

(defun clause-unit-lit (cl)
  "Get the single literal from a unit clause"
  (assert (clause-unit? cl) () "Not a unit clause")
  (hash-set-map #'(lambda (lit) (return-from clause-unit-lit lit)) cl))

(defun clause-two-lits (cl)
  "Get two literals from clause (for initialization of watches)"
  (assert (>= (hash-set-size cl) 2) () "Clause has fewer than 2 literals")
  (let ((lits nil))
    (clause-map #'(lambda (lit)
                    (push lit lits)
                    (when (= (length lits) 2)
                      (return-from clause-two-lits (values (first lits) (second lits)))))
                cl)
    (values nil nil)))  ; if clause has < 2 lits

(defun clause-map (fn cl)
  "Apply function fn to each literal in clause (for side effects only)"
  (hash-set-map fn cl))

(defun clause-negate (cl)
  "Negate a clause"
  (let ((new-cl (make-hash-set)))
    (clause-map #'(lambda (lit) (hash-set-add new-cl (lit-negate lit))) cl)
    new-cl))

(defun clause-any? (pred cl)
  "Return t if any literal in clause satisfies predicate pred"
  (block found
    (clause-map #'(lambda (lit)
                    (when (funcall pred lit)
                      (return-from found t)))
                cl)
    nil))

(defun clause-subsumes? (cl1 cl2)
  "Return t if cl1 subsumes cl2 (cl1 ⊆ cl2)"
  (and (<= (clause-size cl1) (clause-size cl2))
       (block check
         (clause-map #'(lambda (lit)
                             (unless (clause-has-lit? cl2 lit)
                               (return-from check nil)))
                         cl1)
         t)))

(defun clause-copy (cl)
  "Create a deep copy of a clause (copies the hash table)"
  (let ((new-cl (make-hash-set)))
    (clause-map #'(lambda (lit) (hash-set-add new-cl lit)) cl)
    new-cl))

(defun clause-remove-lit! (cl lit)
  "Destructively remove literal from clause (mutates clause)"
  (remhash lit cl))

(defun clause->string (cl &optional vm)
  "Convert clause to string (disjunction of literals)"
  (if (clause-empty? cl)
      "[]"
      (let ((lits nil))
        (clause-map #'(lambda (lit) (push (lit->string lit vm) lits)) cl)
        (format nil "[~{~A~^ v ~}]" (sort lits #'string<)))))

(defun clauses->string (cls &optional vm)
  "Convert list of clauses to string (conjunction of clauses)"
  (if (null cls)
      "TRUE"
      (format nil "~{~A~^ & ~}" (mapcar #'(lambda (cl) (clause->string cl vm)) cls))))

;;; ============================================================
;;; Assignment Hash Table API
;;; ============================================================

(defun make-assignment ()
  "Create an empty assignment hash table"
  (make-hash-table :test #'eql))

(defun assignment-set (asgn var val)
  "Set variable to value in assignment (mutates asgn)"
  (setf (gethash var asgn) val))

(defun assignment-get (asgn var)
  "Get variable's value from assignment. Returns (values val present-p)."
  (gethash var asgn))

(defun assignment->alist (asgn vm amap)
  "Convert numeric assignment hash table to symbolic alist using var-manager.
   asgn contains assigned variables in the original formula, tseitin-generated variables, and skeleton variables.
   The output includes assignments for all the original variables (excluding variables used in atoms) and atoms.
   Atoms not in asgn are assigned t arbitrarily."
  (let ((result nil))
    ;; First, process all variables in asgn
    (maphash #'(lambda (num-var val)
                 (let* ((sym-var (var-manager-get-sym vm num-var))
                        ;; Check if this generated var represents an atom
                        (orig-atom (and amap (car (rassoc sym-var amap :test #'equal))))
                        ;; Use original atom if found, otherwise use the variable
                        (key (or orig-atom sym-var)))
                   (when key
                     (push (cons key val) result))))
             asgn)

    ;; Add missing atoms from amap (assign t arbitrarily)
    ;; Note there no need to add missing vars coming from the non-variable atoms
    (when amap
      (dolist (pair amap)
        (let ((atom (car pair)))
          (unless (assoc atom result :test #'equal)
            (dbg "assignment->alist assigned atom ~A to t" atom)
            (push (cons atom t) result)))))

    result))

(defun assignment->string (asgn vm)
  "Convert assignment hash table to string"
  (let ((pairs nil))
    (maphash #'(lambda (num-var val)
                 (let ((sym-var (var-manager-get-sym vm num-var)))
                   (push (format nil "~A=~A" sym-var val) pairs)))
             asgn)
    (if pairs
        (format nil "{~{~A~^, ~}}" (sort pairs #'string<))
        "{}")))

;;; ============================================================
;;; Resolve Map String Conversion
;;; ============================================================

(defun resolve-map->string (resolve-map vm)
  "Convert resolve-map to string for debugging"
  (if (null resolve-map)
      "[]"
      (format nil "[~{~A~^, ~}]"
              (mapcar #'(lambda (entry)
                          (let ((var (car entry))
                                (cls (cdr entry)))
                            (format nil "~A: ~A"
                                    (var-manager-get-sym vm var)
                                    (clauses->string cls vm))))
                      resolve-map))))

;;; ============================================================
;;; CNF -> Clauses Conversion
;;; ============================================================

(defun cnf->clauses (f vm)
  "Convert a CNF formula to a list of clauses with numeric literals.
   vm: variable manager for symbol to number mapping"
  (labels ((unpack (cl)
             "Convert a clause formula to a list of symbolic literals"
             (match cl
               ((type boolean) (list cl))
               ((type symbol) (list cl))
               ((list 'not _) (list cl))
               ((list* 'or args) args)
               (_ (error "Not a clause: ~A" cl))))
           (convert-lits (sym-lits)
             "Convert symbolic literals to numeric literals"
             (mapcar #'(lambda (lit) (var-manager-sym-lit->num-lit vm lit)) sym-lits)))
    (match f
      ((type boolean) (if f nil (list (make-clause nil))))  ; t -> empty, nil -> empty clause
      ((type symbol) (list (make-clause (convert-lits (list f)))))
      ((list 'not _) (list (make-clause (convert-lits (list f)))))
      ((list* 'or args) (list (make-clause (convert-lits args))))
      ((list* 'and args) (mapcar #'(lambda (cl) (make-clause (convert-lits (unpack cl)))) args))
      (_ (error "Not in CNF: ~A" f)))))

;;; ============================================================
;;; Debug and Stats
;;; ============================================================

;; Mode: 'debug | 'stats | nil (default)
;; Note if we changed this, we should reload the file to recompile the definitions to include debugging/stats information
(defconstant +debug-mode+ 'nil)

(defmacro dbg (fmt &rest args)
  "Print debug message when +debug-mode+ is 'debug"
  `(when (eq +debug-mode+ 'debug)
     (pprint (format nil ,fmt ,@args))))

(defmacro dassert (test-form &optional format-string &rest format-args)
  "Assert that TEST-FORM is true, but only when +debug-mode+ is 'debug.
   If TEST-FORM is false and debug mode is enabled, signals an error with the optional message."
  `(when (eq +debug-mode+ 'debug)
     (assert ,test-form () ,@(when format-string (list* format-string format-args)))))

;;; ============================================================
;;; DP Stats
;;; ============================================================

;; Formula statistics
(defparameter *dp-stats-orig-vars* 0)       ; Variables in original skeleton formula
(defparameter *dp-stats-cnf-vars* 0)        ; Variables after Tseitin transformation
(defparameter *dp-stats-cnf-clauses* 0)     ; Clauses after Tseitin transformation
(defparameter *dp-stats-max-clause-size* 0) ; Maximum number of literals in a clause

;; Search statistics
(defparameter *dp-stats-unit-count* 0)      ; Number of unit propagations
(defparameter *dp-stats-pure-count* 0)      ; Number of pure literal eliminations
(defparameter *dp-stats-resolve-count* 0)   ; Number of resolution steps
(defparameter *dp-stats-max-clauses* 0)     ; Maximum clause count during solving

;; Timing statistics
(defparameter *dp-stats-time-unit* 0)       ; Time spent in unit propagation (internal-time-units)
(defparameter *dp-stats-time-pure* 0)       ; Time spent in pure literal elimination
(defparameter *dp-stats-time-resolve* 0)    ; Time spent in resolution
(defparameter *dp-stats-time-sat* 0)        ; Time spent in SAT solving (dp-sat)
(defparameter *dp-stats-time-total* 0)      ; Total time including preprocessing

(defmacro dp-stats-reset ()
  "Reset all stats counters"
  `(when (eq +debug-mode+ 'stats)
     (setf *dp-stats-orig-vars* 0
           *dp-stats-cnf-vars* 0
           *dp-stats-cnf-clauses* 0
           *dp-stats-max-clause-size* 0
           *dp-stats-unit-count* 0
           *dp-stats-pure-count* 0
           *dp-stats-resolve-count* 0
           *dp-stats-max-clauses* 0
           *dp-stats-time-unit* 0
           *dp-stats-time-pure* 0
           *dp-stats-time-resolve* 0
           *dp-stats-time-sat* 0
           *dp-stats-time-total* 0)))

(defmacro dp-stats-set-formula (orig-vars cnf-vars cnf-clauses max-clause-size)
  "Set formula statistics"
  `(when (eq +debug-mode+ 'stats)
     (setf *dp-stats-orig-vars* ,orig-vars
           *dp-stats-cnf-vars* ,cnf-vars
           *dp-stats-cnf-clauses* ,cnf-clauses
           *dp-stats-max-clause-size* ,max-clause-size)))

(defmacro dp-stats-inc-unit ()
  "Increment unit propagation count"
  `(when (eq +debug-mode+ 'stats)
     (incf *dp-stats-unit-count*)))

(defmacro dp-stats-inc-pure (n)
  "Increment pure literal count by n"
  `(when (eq +debug-mode+ 'stats)
     (incf *dp-stats-pure-count* ,n)))

(defmacro dp-stats-inc-resolve ()
  "Increment resolution count"
  `(when (eq +debug-mode+ 'stats)
     (incf *dp-stats-resolve-count*)))

(defmacro dp-stats-update-max-clauses (n)
  "Update max clauses if n is larger"
  `(when (eq +debug-mode+ 'stats)
     (setf *dp-stats-max-clauses* (max *dp-stats-max-clauses* ,n))))

(defmacro dp-stats-time (phase &body body)
  (let ((start (gensym "START")))
    `(if (eq +debug-mode+ 'stats)
         (let ((,start (get-internal-real-time)))
           (multiple-value-prog1 (progn ,@body)
             (incf ,(ecase phase
                      (:unit '*dp-stats-time-unit*)
                      (:pure '*dp-stats-time-pure*)
                      (:resolve '*dp-stats-time-resolve*)
                      (:sat '*dp-stats-time-sat*)
                      (:total '*dp-stats-time-total*))
                   (- (get-internal-real-time) ,start))))
         (progn ,@body))))

(defmacro stats-time->ms (time)
  "Convert internal time units to milliseconds"
  `(* 1000.0 (/ ,time internal-time-units-per-second)))

(defmacro dp-stats-report ()
  "Print stats report"
  `(when (eq +debug-mode+ 'stats)
     (format t "~%=== DP Statistics ===~%")
     (format t "--- Formula Info ---~%")
     (format t "Original vars:        ~A~%" *dp-stats-orig-vars*)
     (format t "After Tseitin:        ~A vars, ~A clauses~%" 
             *dp-stats-cnf-vars* *dp-stats-cnf-clauses*)
     (format t "Max clause size:      ~A~%" *dp-stats-max-clause-size*)
     (format t "--- Search Stats ---~%")
     (format t "Unit propagations:    ~A~%" *dp-stats-unit-count*)
     (format t "Pure literals:        ~A~%" *dp-stats-pure-count*)
     (format t "Resolution steps:     ~A~%" *dp-stats-resolve-count*)
     (format t "Max clauses:          ~A~%" *dp-stats-max-clauses*)
     (format t "--- Timing ---~%")
     (format t "Time (unit/sat):      ~,3F ms (~,1F%)~%"
             (stats-time->ms *dp-stats-time-unit*)
             (if (> *dp-stats-time-sat* 0) (* 100.0 (/ *dp-stats-time-unit* *dp-stats-time-sat*)) 0))
     (format t "Time (pure/sat):      ~,3F ms (~,1F%)~%"
             (stats-time->ms *dp-stats-time-pure*)
             (if (> *dp-stats-time-sat* 0) (* 100.0 (/ *dp-stats-time-pure* *dp-stats-time-sat*)) 0))
     (format t "Time (resolve/sat):   ~,3F ms (~,1F%)~%"
             (stats-time->ms *dp-stats-time-resolve*)
             (if (> *dp-stats-time-sat* 0) (* 100.0 (/ *dp-stats-time-resolve* *dp-stats-time-sat*)) 0))
     (format t "Time (sat/total):     ~,3F ms (~,1F%)~%" 
             (stats-time->ms *dp-stats-time-sat*)
             (if (> *dp-stats-time-total* 0) (* 100.0 (/ *dp-stats-time-sat* *dp-stats-time-total*)) 0))
     (format t "Time (total):         ~,3F ms~%" (stats-time->ms *dp-stats-time-total*))
     (format t "=====================~%")))

;;; ============================================================
;;; DP Algorithm
;;; ============================================================

(defun remove-satisfied-clauses (cls sat-lits)
  "Remove all clauses containing any literal in sat-lits"
  (remove-if #'(lambda (cl)
                 (some #'(lambda (lit) (clause-has-lit? cl lit)) sat-lits))
             cls))

;; Post: no more pure literals
(defun dp-pure (cls asgn)
  "Pure literal elimination. Returns simplified clauses, mutates asgn.
   A pure literal appears only in one polarity across all clauses."
  (let ((pos (make-hash-set))
        (neg (make-hash-set)))
    ;; Collect all literals using numeric literal operations
    (dolist (cl cls)
      (clause-map #'(lambda (lit)
                          (let ((var (lit-var lit))
                                (pos? (lit-sign lit)))
                            (if pos?
                                (hash-set-add pos var)
                                (hash-set-add neg var))))
                      cl))
    ;; Find pure literals and update assignment
    (let ((pure-pos nil)
          (pure-neg nil))
      (hash-set-map #'(lambda (v)
                        (unless (hash-set-contains? neg v)
                          (push v pure-pos)))
                    pos)
      (hash-set-map #'(lambda (v)
                        (unless (hash-set-contains? pos v)
                          (push v pure-neg)))
                    neg)
      (let ((pure-lits (append (mapcar #'(lambda (v) (make-lit v t)) pure-pos)
                               (mapcar #'(lambda (v) (make-lit v nil)) pure-neg))))
        (dp-stats-inc-pure (length pure-lits))
        (dolist (v pure-pos)
          (dbg "dp-pure assigned ~A to be T" v)
          (assignment-set asgn v t))
        (dolist (v pure-neg)
          (dbg "dp-pure assigned ~A to be NIL" v)
          (assignment-set asgn v nil))
        (if (null pure-lits)
            cls
            (remove-satisfied-clauses cls pure-lits))))))

;; Post: no more unit clauses
(defun dp-unit (cls asgn)
  "Unit propagation. Returns simplified clauses, mutates asgn.
   A unit clause has exactly one literal, which must be true."
  ;; Copy all clauses once, then destructively modify
  (labels ((unit-loop (cls)
             (let ((unit-cl (find-if #'clause-unit? cls)))
               (if (null unit-cl)
                   cls
                   (let* ((unit-lit (clause-unit-lit unit-cl))
                          (neg-lit (lit-negate unit-lit))
                          (var (lit-var unit-lit))
                          (val (lit-sign unit-lit)))
                     ;; Remove satisfied clauses
                     (setf cls (remove-satisfied-clauses cls (list unit-lit)))
                     ;; Destructively remove negated literal from remaining clauses
                     (dolist (cl cls) (clause-remove-lit! cl neg-lit))
                     (assignment-set asgn var val)
                     (dbg "dp-unit assigned ~A to be ~A" var val)
                     (dp-stats-inc-unit)
                     (unit-loop cls))))))
    (unit-loop (mapcar #'clause-copy cls))))

(defun dp-decide (cls)
  "Pick variable with minimum resolution blowup: m*n - m - n"
  (let ((var-counts (make-hash-table :test #'eql))) ; var -> (pos-count . neg-count)
    ;; Collect variable occurrences
    (dolist (cl cls)
      (clause-map #'(lambda (lit)
                      (let+ ((var (lit-var lit))
                             (pos? (lit-sign lit))
                             ((&values counts present?) (gethash var var-counts)))
                        (if present?
                            (if pos?
                                (incf (car counts))
                                (incf (cdr counts)))
                            (setf (gethash var var-counts)
                                  (if pos? (cons 1 0) (cons 0 1))))))
                  cl))
    ;; Find variable with minimum blowup: m*n - m - n
    ;; TODO: Early exit if blowup <= 0
    ;; TODO: Tie-breaking with MOMS heuristic (prefer variables in smaller clauses)
    (let ((best-var nil)
          (best-score 0))
      (maphash #'(lambda (var counts)
                   (let* ((m (car counts))
                          (n (cdr counts))
                          (score (- (* m n) m n)))
                     (when (or (null best-var) (< score best-score))
                       (setf best-var var
                             best-score score))))
               var-counts)
     best-var)))

;; TODO: use signatures to speed up subsumption
(defun remove-subsumed (cls)
  "Remove clauses that are subsumed by other clauses in the list.
   The value bound to cls shouldn't be used after the function call as it will be modified in place."
  ;; Sort by size - smaller clauses first (they subsume larger ones)
  (let* ((sorted (sort cls #'< :key #'clause-size))
         (result nil))
    (dolist (cl sorted)
      ;; If cl is not subsumed by anything in result (which are all smaller or equal), then add it
      (unless (some #'(lambda (r) (clause-subsumes? r cl)) result)
        (push cl result)))
    ;; Prefer smaller clauses in the front
    (nreverse result)))

(defun resolve-var (cls var)
  "Resolve on variable var, returning (values new-clause-set containing-clauses).
   containing-clauses is the list of clauses that contained var (pos-cls and neg-cls)."
  (let ((pos-lit (make-lit var t))
        (neg-lit (make-lit var nil))
        (pos-cls nil)
        (neg-cls nil)
        (other-cls nil))
    ;; Partition clauses
    (dolist (cl cls)
      (cond ((clause-has-lit? cl pos-lit) (push cl pos-cls))
            ((clause-has-lit? cl neg-lit) (push cl neg-cls))
            (t (push cl other-cls))))
    ;; Generate resolvents
    (let ((resolvents nil))
      (dolist (pcl pos-cls)
        (dolist (ncl neg-cls)
          ;; Build resolvent and detect tautologies on the fly
          (block next-resolvent
            (let ((resolvent (make-hash-set)))
              (clause-map #'(lambda (lit)
                                  (unless (= lit pos-lit)
                                    (hash-set-add resolvent lit)))
                              pcl)
              (clause-map #'(lambda (lit)
                                  (unless (= lit neg-lit)
                                    ;; Check for tautology as we add from ncl
                                    (when (clause-has-lit? resolvent (lit-negate lit))
                                      (return-from next-resolvent))
                                    (hash-set-add resolvent lit)))
                              ncl)
              (push resolvent resolvents)))))
      (values (append other-cls resolvents)
              (append pos-cls neg-cls)))))

(defun dp-resolve (cls var)
  "Resolve on variable var and apply subsumption to keep clause set small.
   Returns (values new-clause-set containing-clauses)."
  (let+ (((&values new-cls var-cls) (resolve-var cls var)))
    (values (remove-subsumed new-cls)
            var-cls)))

(defun dp-sat (cls asgn resolve-map)
  "Main DP loop: apply unit propagation, pure literal elimination, and resolution recursively.
   Returns (values result resolve-map) where resolve-map is an alist of (var . containing-clauses)."
  (dp-stats-update-max-clauses (length cls))
  (let ((cls (dp-stats-time :unit (dp-unit cls asgn))))
    (cond ((null cls) (values 'sat resolve-map))
          ((some #'clause-empty? cls) (values 'unsat resolve-map))
          (t (let ((cls (dp-stats-time :pure (dp-pure cls asgn))))
               (cond ((null cls) (values 'sat resolve-map))
                     ((some #'clause-empty? cls) (values 'unsat resolve-map))
                     (t (let* ((var (dp-decide cls)))
                          (dbg "dp-sat resolving on var ~A" var)
                          (dp-stats-inc-resolve)
                          (let+ (((&values new-cls var-cls) (dp-stats-time :resolve (dp-resolve cls var))))
                            (dp-sat new-cls asgn (cons (cons var var-cls) resolve-map)))))))))))

(defun dp-reconstruct (cls asgn resolve-map)
  "Reconstruct assignment for resolved variables by assigning them arbitrarily and propagating.
   Mutates asgn to add assignments for resolved variables.
   resolve-map is an alist of (var . containing-clauses)."
  (labels ((simplify-clauses (cls)
             (mapcar #'(lambda (cl)
                         ;; Copy clause and remove false literals
                         (let ((new-cl (make-hash-set)))
                           (clause-map #'(lambda (lit)
                                           (let+ ((var (lit-var lit))
                                                  (sign (lit-sign lit))
                                                  ((&values val assigned?) (assignment-get asgn var)))
                                             ;; Keep literal unless it's false (assigned opposite sign)
                                             (unless (and assigned? (not (eq val sign)))
                                               (hash-set-add new-cl lit))))
                                       cl)
                           new-cl))
                     ;; Remove satisfied clauses (where any literal is true)
                     (remove-if #'(lambda (cl)
                                    (clause-any? #'(lambda (lit)
                                                     (let+ ((var (lit-var lit))
                                                            (sign (lit-sign lit))
                                                            ((&values val assigned?) (assignment-get asgn var)))
                                                       ;; Clause satisfied if literal is true (assigned same sign)
                                                       (and assigned? (eq val sign))))
                                                 cl))
                                cls)))
           (get-unassigned-vars (cls target-var)
             "Get all unassigned variables in clauses except target-var"
             (let ((vars nil))
               (dolist (cl cls)
                 (clause-map #'(lambda (lit)
                                 (let+ ((var (lit-var lit))
                                        ((&values _ assigned?) (assignment-get asgn var)))
                                   (unless (or (= var target-var)
                                               assigned?
                                               (member var vars))
                                     (push var vars))))
                             cl))
               vars))
           (assign-companion-vars (cls target-var)
             "Assign companion variables (vars other than target) to reduce clauses to unit.
              Iteratively pick literals to satisfy clauses until only target-var remains."
             (loop
               (let ((simplified (simplify-clauses cls)))
                 ;; If empty or all unit with target-var, we're done
                 (when (or (null simplified)
                           (every #'(lambda (cl)
                                      (and (clause-unit? cl)
                                           (= (lit-var (clause-unit-lit cl)) target-var)))
                                  simplified))
                   (return simplified))
                 ;; Find a non-unit clause with unassigned vars other than target
                 (let ((companion-vars (get-unassigned-vars simplified target-var)))
                   (if (null companion-vars)
                       ;; No more companions, return what we have
                       (return simplified)
                       ;; Assign first companion to satisfy some clause
                       ;; Pick the first literal containing this var from any clause
                       (let ((var-to-assign (first companion-vars)))
                         (block found-lit
                           (dolist (cl simplified)
                             (clause-map #'(lambda (lit)
                                             (when (= (lit-var lit) var-to-assign)
                                               (assignment-set asgn var-to-assign (lit-sign lit))
                                               (return-from found-lit)))
                                         cl))))))))))
    (dolist (entry resolve-map)
      (let ((var (car entry))
            (var-cls (cdr entry)))
        ;; assign-companion-vars guarantees: nil OR all unit clauses with target-var
        (let ((cls (assign-companion-vars var-cls var)))
          (if (null cls)
              (assignment-set asgn var t)  ;; All clauses satisfied, assign arbitrarily
              ;; All unit clauses must have same sign and contain the same target var
              (assignment-set asgn var (lit-sign (clause-unit-lit (first cls))))))))))

(defun dp (f)
  "Main DP function: takes a formula f, converts to CNF, and applies DP algorithm.
   Returns 'sat or 'unsat with assignment alist."
  (dp-stats-time :total
    (let+ (((&values cnf skeleton amap) (tseitin f))
           (vm (make-var-manager))
           (cls (cnf->clauses cnf vm)) ;; mutates vm
           (asgn (make-assignment)))

      (dp-stats-set-formula (length (pvars skeleton))
                            (var-manager-num-vars vm)
                            (length cls)
                            (if cls (apply #'max (mapcar #'clause-size cls)) 0))

      (let+ (((&values result resolve-map) (dp-stats-time :sat (dp-sat cls asgn nil))) ;; mutates asgn
             (result-asgn (when (eq result 'sat)
                            (dp-reconstruct cls asgn resolve-map) ;; mutates asgn
                            (assignment->alist asgn vm amap))))
        (values result result-asgn)))))

(defun subst-formula (f asgn)
  "Substitute variables in formula f according to asgn (alist)"
  (match f
    ((type boolean) f)
    ((type symbol)
     (let ((val (assoc f asgn :test #'equal)))
       (if val (cdr val) f)))
    ((list* op args)
     (if (p-funp op)
         ;; Propositional operator - recurse into arguments
         `(,op ,@(mapcar #'(lambda (a) (subst-formula a asgn)) args))
         ;; Atom - look up in assignment like a symbol
         (let ((val (assoc f asgn :test #'equal)))
           (if val (cdr val) f))))
    (_ f)))

(defun verify-sat (f result asgn &optional expected)
  "Verify if result and asgn are correct for formula f.
   If expected is provided, assert that result matches expected.
   If result is 'sat, verify that substituting asgn makes f valid.
   If result is 'unsat, verify using ACL2s."
  ;; First check if result matches expected (if provided)
  (when expected
    (assert (eq result expected) ()
            "Result ~A does not match expected ~A for formula: ~A"
            result expected f))
  ;; Then verify the result is correct
  (case result
    (sat
     (let* ((subst-f (subst-formula f asgn)))
       ;; After substitution, remaining formula should be valid (tautology)
       (assert (acl2s-valid? subst-f) ()
               "Assignment does not make formula valid: ~A~%Assignment: ~A~%Result: ~A"
               f asgn subst-f)))
    (unsat
     (assert (acl2s-unsat? f) () "Formula is not UNSAT: ~A" f))
    (otherwise
     (error "Invalid result: ~A (expected 'sat or 'unsat)" result))))

(defun test-dp (f &optional (expected 'sat))
  "Test dp on formula f by verifying its result.
   Expected defaults to 'sat unless specified as 'unsat."
  (let+ (((&values result asgn) (dp f)))
    (verify-sat f result asgn expected)))

;; ================================================
;; Tests
;; ================================================

;; Adder circuit example
(defun halfsum (x y) `(xor ,x ,y))
(defun halfcarry (x y) `(and ,x ,y))
(defun carry (x y z) `(or (and ,x ,y) (and (or ,x ,y) ,z)))
(defun sum (x y z) (halfsum (halfsum x y) z))
(defun fa (x y z s c) `(and (iff ,s ,(sum x y z)) (iff ,c ,(carry x y z))))

(defun genvar (prefix n)
  "Generate a variable symbol of the form PREFIX_N"
  (intern (format nil "~A~D" prefix n)))

(defun genvars (prefix n)
  "Generate a list of variables (PREFIX0, PREFIX1, ..., PREFIXn)"
  (loop for i from 0 to n
        collect (genvar prefix i)))

(defun ripplecarry (x y c out n)
  "Generate ripple-carry adder for n bits.
   x y c out are functions that take an index i (0 ... n-1) and return the corresponding variable for that bit."
  (cons 'and
        (loop for i from 0 to (1- n)
              collect (fa (funcall x i)
                          (funcall y i)
                          (funcall c i)
                          (funcall out i)
                          (funcall c (1+ i))))))

(defun ripplecarry0 (x y c out n)
  (p-simplify
    (ripplecarry
      x y
      #'(lambda (i) (if (zerop i) nil (funcall c i)))
      out n)))

(defun rippleshift (u v c z w n)
  (ripplecarry0
     u v
     #'(lambda (i) (if (= i n) (funcall w (- n 1)) (funcall c (1+ i))))
     #'(lambda (i) (if (zerop i) z (funcall w (- i 1))))
     n))

;; Ramsey number example generated by Claude
(defun combinations (items k)
  "Returns all k-element combinations of ITEMS (a list or an integer N)."
  (let ((lst (if (integerp items)
                 (loop for i from 0 repeat items collect i)
                 items)))
    (cond ((zerop k) '(()))
          ((null lst) '())
          (t (append (mapcar (lambda (c) (cons (car lst) c))
                             (combinations (cdr lst) (1- k)))
                     (combinations (cdr lst) k))))))

;; Note this is an opposite formulation from the book.
;; SAT when n < R(s,k) - we CAN avoid monochromatic cliques
;; UNSAT when n ≥ R(s,k) - we CANNOT avoid them
(defun ramsey (s k n)
  "Generate a formula that is satisfiable iff there exists a red-blue coloring of the edges of K_n with no red K_s and no blue K_k."
  (let ((edges nil)
        (no-red-s nil)
        (no-blue-k nil))
    ;; Generate variables for each edge
    (dotimes (i n)
      (dotimes (j i)
        (push (genvar 'e (format nil "_~A_~A" i j)) edges)))
    ;; No red K_s: for every set of s vertices, at least one edge must be blue
    (dolist (subset (combinations n s))
      (let ((clause nil))
        (dolist (pair (combinations subset 2))
          (let* ((i (first pair))
                 (j (second pair))
                 (edge-var (genvar 'e (format nil "_~A_~A" i j))))
            ;; edge-var = true means red, so we want at least one to be false
            (push `(not ,edge-var) clause)))
        (push `(or ,@clause) no-red-s)))
    ;; No blue K_k: for every set of k vertices, at least one edge must be red
    (dolist (subset (combinations n k))
      (let ((clause nil))
        (dolist (pair (combinations subset 2))
          (let* ((i (first pair))
                 (j (second pair))
                 (edge-var (genvar 'e (format nil "_~A_~A" i j))))
            ;; edge-var = true means red, so we want at least one to be true
            (push edge-var clause)))
        (push `(or ,@clause) no-blue-k)))
    ;; Combine all constraints
    `(and ,@no-red-s ,@no-blue-k)))

(defun run-tests (test-sat &optional (time-out 40))
  "Run a suite of tests on the DP solver, using TEST-SAT to verify results.
   TIME-OUT is the maximum time in seconds for each test.
   The default time out is the same as in ACL2s."
  (labels ((test (f &optional (expected 'sat) (label nil))
             (format t "Testing: ~A~%"
                     (or label
                         (let ((s (write-to-string f)))
                           (if (> (length s) 80)
                               (concatenate 'string (subseq s 0 80) "...")
                               s))))
             (handler-case
                 (sb-ext:with-timeout time-out
                   (funcall test-sat f expected))
               (sb-ext:timeout ()
                 (format t "Solver timed out!~%")
                 :timeout))))
    (format t "Running tests...~%")

    ;; Basic SAT tests
    (test 'nil 'unsat)
    (test 't)
    (test 'p)                                    ; single var - SAT
    (test '(or p q))                             ; simple disjunction - SAT
    (test '(and p q))                            ; simple conjunction - SAT
    (test '(implies p q))                        ; implication - SAT
    (test '(iff p q))                            ; biconditional - SAT
    (test '(xor p q))

    ;; Basic UNSAT tests
    (test '(and p (not p)) 'unsat)              ; contradiction - UNSAT
    (test '(and (or p q) (not p) (not q)) 'unsat)  ; UNSAT
    (test '(and p q (or (not p) (not q)) (or p (not q)) (or (not p) q)) 'unsat)  ; UNSAT

    ;; More complex SAT formulas
    (test '(and (or p q) (or (not p) r)))        ; SAT
    (test '(and (or p q r) (or (not p) (not q)) (or (not r) p)))  ; SAT
    (test '(or (and p q) (and (not p) r)))       ; SAT
    (test '(iff (and p q) (or r s)))             ; SAT

    ;; With non-variable atoms
    (test '(or (foo a) (bar b)))                 ; SAT
    (test '(and (foo x) (not (foo x))) 'unsat)   ; UNSAT
    (test '(implies (f a b) (g c)))              ; SAT

    ;; Nested formulas
    (test '(and (or p (not q)) (or q (not r)) (or r (not p))))  ; SAT
    (test '(xor p q))                            ; SAT
    (test '(if p q r))                           ; SAT

    ;; Ripplecarry tests
    (test (ripplecarry0
           #'(lambda (i) (genvar 'x i))
           #'(lambda (i) (genvar 'y i))
           #'(lambda (i) (genvar 'c i))
           #'(lambda (i) (genvar 'z i))
           1))

    ;; Adder tests
    ;; Example 1: Single bit full adder
    (test (fa 'x0 'y0 'cin 's0 'cout))  ; SAT - unconstrained full adder

    ;; Example 2: 2-bit adder with constraint (checking 1+1=2 with carry-in=0)
    (test `(and ,(ripplecarry0
                  #'(lambda (i) (genvar 'x i))
                  #'(lambda (i) (genvar 'y i))
                  #'(lambda (i) (genvar 'c i))
                  #'(lambda (i) (genvar 's i))
                  2)
                x0 (not x1)    ; x = 01 (binary) = 1
                y0 (not y1)    ; y = 01 (binary) = 1
                (not s0) s1    ; s = 10 (binary) = 2
                (not c2)))     ; no overflow

    ;; Example 3: 3-bit adder checking 7+1=8 (overflow)
    (test `(and ,(ripplecarry0
                  #'(lambda (i) (genvar 'a i))
                  #'(lambda (i) (genvar 'b i))
                  #'(lambda (i) (genvar 'c i))
                  #'(lambda (i) (genvar 'sum i))
                  3)
                a0 a1 a2           ; a = 111 (binary) = 7
                b0 (not b1) (not b2)  ; b = 001 (binary) = 1
                (not sum0) (not sum1) (not sum2)  ; sum = 000 (mod 8)
                c3))               ; carry out = 1 (overflow)

    ;; Example 4: 4-bit adder unconstrained (always SAT)
    (test (ripplecarry0
           #'(lambda (i) (genvar 'x i))
           #'(lambda (i) (genvar 'y i))
           #'(lambda (i) (genvar 'c i))
           #'(lambda (i) (genvar 'z i))
           4))

    ;; UNSAT Examples
    ;; Example 5: 2-bit adder with impossible constraint (1+1=3, no overflow)
    (test `(and ,(ripplecarry0
                  #'(lambda (i) (genvar 'x i))
                  #'(lambda (i) (genvar 'y i))
                  #'(lambda (i) (genvar 'c i))
                  #'(lambda (i) (genvar 's i))
                  2)
                x0 (not x1)    ; x = 01 (binary) = 1
                y0 (not y1)    ; y = 01 (binary) = 1
                s0 s1          ; s = 11 (binary) = 3 (IMPOSSIBLE!)
                (not c2))      ; no overflow - UNSAT
          'unsat)

    ;; Example 6: 3-bit adder with overflow contradiction (7+1=8, but no carry)
    (test `(and ,(ripplecarry0
                  #'(lambda (i) (genvar 'a i))
                  #'(lambda (i) (genvar 'b i))
                  #'(lambda (i) (genvar 'c i))
                  #'(lambda (i) (genvar 'sum i))
                  3)
                a0 a1 a2           ; a = 111 (binary) = 7
                b0 (not b1) (not b2)  ; b = 001 (binary) = 1
                (not sum0) (not sum1) (not sum2)  ; sum = 000
                (not c3))          ; no carry - UNSAT (7+1 must overflow!)
          'unsat)

    ;; Example 7: 2-bit adder checking impossible result: 2+3=4 with carry
    (test `(and ,(ripplecarry0
                  #'(lambda (i) (genvar 'p i))
                  #'(lambda (i) (genvar 'q i))
                  #'(lambda (i) (genvar 'c i))
                  #'(lambda (i) (genvar 'r i))
                  2)
                (not p0) p1     ; p = 10 (binary) = 2
                q0 q1           ; q = 11 (binary) = 3
                (not r0) (not r1)  ; r = 00 (binary) = 0
                c2)             ; with carry - gives 0+4=4, but 2+3=5 - UNSAT
          'unsat)

    ;; Ramsey number tests
    ;; R(3,3) = 6 means any 2-coloring of K_6 must contain a monochromatic K_3
    (test (ramsey 3 3 5))      ; n < R(3,3), can avoid monochromatic triangles - SAT
    (test (ramsey 3 3 6) 'unsat) ; n >= R(3,3), cannot avoid monochromatic triangles - UNSAT
    ))

(defun run-test-dp ()
 "Run DP tests and report statistics."
 (dp-stats-reset)
 (run-tests #'test-dp)
 ;; Time out
 ;; (test-dp (ramsey 3 4 8))
 ;; (test-dp (ramsey 3 4 9) 'unsat)
 ;; (test-dp (ramsey 4 4 17)) ; n < R(4,4), can avoid monochromatic K_4 - SAT
 ;; (test-dp (ramsey 4 4 18) 'unsat) ; n >= R(4,4), cannot avoid monochromatic K_4 - UNSAT
 (dp-stats-report))

(run-test-dp)

#|

 Question 4.

 Part1: (25pts) Profile DP and make it as efficient as possible. If it
 meets the efficiency criteria of the evaluator, you get credit. The
 fastest submission will get 20 extra points, no matter how slow. To
 generate interesting problems, see your book.

 Part 2: (30pts) Define DPLL, a function that given a propositional
 formula in CNF, applies the DPLL algorithm to determine if the
 formula is satisfiable. You have to implement the iterative with
 backjumping version of DPLL from the book.

 Remember that you have to deal with atoms such as

 (foo (if a b))

 If the formula is sat, DPLL returns 'sat and a satisfying assignment:
 an alist mapping each atom in the formula to t/nil. Use values to
 return multiple values.

 If it is usat, return 'unsat.

 Test DPLL using with assert-acl2s-equal using at least 10
 propositional formulas.

 The fastest submission will get 20 extra points, no matter how
 slow. To generate interesting problems, see your book.

|#

;; ==============================================================
;; DPLL Statistics
;; ==============================================================

;; Formula statistics (computed once per problem)
(defparameter *dpll-stats-orig-vars* 0)        ; Variables in original skeleton formula
(defparameter *dpll-stats-cnf-vars* 0)         ; Variables after Tseitin transformation
(defparameter *dpll-stats-cnf-clauses* 0)      ; Clauses after Tseitin transformation
(defparameter *dpll-stats-max-clause-size* 0)  ; Maximum number of literals in a clause

;; Search statistics (accumulated during solving)
(defparameter *dpll-stats-decisions* 0)        ; Number of decisions made
(defparameter *dpll-stats-propagations* 0)     ; Number of unit propagations
(defparameter *dpll-stats-conflicts* 0)        ; Number of conflicts encountered
(defparameter *dpll-stats-learnt-clauses* 0)   ; Number of learnt clauses
(defparameter *dpll-stats-learnt-lits* 0)      ; Total literals in learnt clauses (for avg)
(defparameter *dpll-stats-max-level* 0)        ; Maximum decision level reached
(defparameter *dpll-stats-backjumps* 0)        ; Number of non-chronological backtracks

;; Timing statistics (internal time units)
(defparameter *dpll-stats-time-total* 0)       ; Total time including preprocessing
(defparameter *dpll-stats-time-sat* 0)         ; Time in SAT solving (init + solve)
(defparameter *dpll-stats-time-propagate* 0)   ; Time in unit propagation
(defparameter *dpll-stats-time-analyze* 0)     ; Time in conflict analysis
(defparameter *dpll-stats-time-backtrack* 0)   ; Time in backtracking
(defparameter *dpll-stats-time-decide* 0)      ; Time in decision making

(defmacro dpll-stats-reset ()
  "Reset all DPLL stats counters"
  `(when (eq +debug-mode+ 'stats)
     (setf *dpll-stats-orig-vars* 0
           *dpll-stats-cnf-vars* 0
           *dpll-stats-cnf-clauses* 0
           *dpll-stats-max-clause-size* 0
           *dpll-stats-decisions* 0
           *dpll-stats-propagations* 0
           *dpll-stats-conflicts* 0
           *dpll-stats-learnt-clauses* 0
           *dpll-stats-learnt-lits* 0
           *dpll-stats-max-level* 0
           *dpll-stats-backjumps* 0
           *dpll-stats-time-total* 0
           *dpll-stats-time-sat* 0
           *dpll-stats-time-propagate* 0
           *dpll-stats-time-analyze* 0
           *dpll-stats-time-backtrack* 0
           *dpll-stats-time-decide* 0)))

(defmacro dpll-stats-set-formula (orig-vars cnf-vars cnf-clauses max-clause-size)
  "Set formula statistics"
  `(when (eq +debug-mode+ 'stats)
     (setf *dpll-stats-orig-vars* ,orig-vars
           *dpll-stats-cnf-vars* ,cnf-vars
           *dpll-stats-cnf-clauses* ,cnf-clauses
           *dpll-stats-max-clause-size* ,max-clause-size)))

(defmacro dpll-stats-inc-decisions ()
  `(when (eq +debug-mode+ 'stats)
     (incf *dpll-stats-decisions*)))

(defmacro dpll-stats-inc-propagations ()
  `(when (eq +debug-mode+ 'stats)
     (incf *dpll-stats-propagations*)))

(defmacro dpll-stats-inc-conflicts ()
  `(when (eq +debug-mode+ 'stats)
     (incf *dpll-stats-conflicts*)))

(defmacro dpll-stats-add-learnt (clause-size)
  `(when (eq +debug-mode+ 'stats)
     (incf *dpll-stats-learnt-clauses*)
     (incf *dpll-stats-learnt-lits* ,clause-size)))

(defmacro dpll-stats-update-max-level (level)
  `(when (eq +debug-mode+ 'stats)
     (setf *dpll-stats-max-level* (max *dpll-stats-max-level* ,level))))

(defmacro dpll-stats-inc-backjumps ()
  `(when (eq +debug-mode+ 'stats)
     (incf *dpll-stats-backjumps*)))

(defmacro dpll-stats-time (phase &body body)
  "Time a phase of DPLL and accumulate to the corresponding counter"
  (let ((start (gensym "START")))
    `(if (eq +debug-mode+ 'stats)
         (let ((,start (get-internal-real-time)))
           (multiple-value-prog1 (progn ,@body)
             (incf ,(ecase phase
                      (:propagate '*dpll-stats-time-propagate*)
                      (:analyze '*dpll-stats-time-analyze*)
                      (:backtrack '*dpll-stats-time-backtrack*)
                      (:decide '*dpll-stats-time-decide*)
                      (:sat '*dpll-stats-time-sat*)
                      (:total '*dpll-stats-time-total*))
                   (- (get-internal-real-time) ,start))))
         (progn ,@body))))

(defmacro dpll-stats-report ()
  "Print DPLL statistics report"
  `(when (eq +debug-mode+ 'stats)
     (format t "~%=== DPLL Statistics ===~%")
     (format t "--- Formula Info ---~%")
     (format t "Original vars:        ~A~%" *dpll-stats-orig-vars*)
     (format t "After Tseitin:        ~A vars, ~A clauses~%" 
             *dpll-stats-cnf-vars* *dpll-stats-cnf-clauses*)
     (format t "Max clause size:      ~A~%" *dpll-stats-max-clause-size*)
     (format t "--- Search Stats ---~%")
     (format t "Decisions:            ~A~%" *dpll-stats-decisions*)
     (format t "Propagations:         ~A~%" *dpll-stats-propagations*)
     (format t "Conflicts:            ~A~%" *dpll-stats-conflicts*)
     (format t "Learnt clauses:       ~A~%" *dpll-stats-learnt-clauses*)
     (format t "Avg learnt size:      ~,2F~%" 
             (if (> *dpll-stats-learnt-clauses* 0) 
                 (/ *dpll-stats-learnt-lits* *dpll-stats-learnt-clauses*) 
                 0.0))
     (format t "Max decision level:   ~A~%" *dpll-stats-max-level*)
     (format t "Backjumps:            ~A~%" *dpll-stats-backjumps*)
     (format t "--- Timing ---~%")
     (format t "Time (propagate/sat): ~,3F ms (~,1F%)~%"
             (stats-time->ms *dpll-stats-time-propagate*)
             (if (> *dpll-stats-time-sat* 0) 
                 (* 100.0 (/ *dpll-stats-time-propagate* *dpll-stats-time-sat*)) 0))
     (format t "Time (analyze/sat):   ~,3F ms (~,1F%)~%"
             (stats-time->ms *dpll-stats-time-analyze*)
             (if (> *dpll-stats-time-sat* 0) 
                 (* 100.0 (/ *dpll-stats-time-analyze* *dpll-stats-time-sat*)) 0))
     (format t "Time (backtrack/sat): ~,3F ms (~,1F%)~%"
             (stats-time->ms *dpll-stats-time-backtrack*)
             (if (> *dpll-stats-time-sat* 0) 
                 (* 100.0 (/ *dpll-stats-time-backtrack* *dpll-stats-time-sat*)) 0))
     (format t "Time (decide/sat):    ~,3F ms (~,1F%)~%"
             (stats-time->ms *dpll-stats-time-decide*)
             (if (> *dpll-stats-time-sat* 0) 
                 (* 100.0 (/ *dpll-stats-time-decide* *dpll-stats-time-sat*)) 0))
     (format t "Time (sat/total):     ~,3F ms (~,1F%)~%" 
             (stats-time->ms *dpll-stats-time-sat*)
             (if (> *dpll-stats-time-total* 0) 
                 (* 100.0 (/ *dpll-stats-time-sat* *dpll-stats-time-total*)) 0))
     (format t "Time (total):         ~,3F ms~%" 
             (stats-time->ms *dpll-stats-time-total*))
     (format t "=======================~%")))

;; ==============================================================
;; Trail APIs
;;
;; Trail is a stack of trail entries
;; Trail entry is a triple of (lit reason . level)
;; where lit is the literal assigned (encodes both var and val),
;;       reason is the clause that implied this assignment (nil for decisions), and
;;       level is the decision level at which it was assigned.
;;
;; Well formed trail invariants:
;; 1) Decision levels are non-negative integers.
;; 2) Trail is ordered by non-increasing decision levels (newer entries have same or higher level than older entries).
;; 3) No variable is assigned more than once in the trail (i.e., no conflicting assignments).
;; 4) For any entry with a non-nil reason, all variables in the reason clause are assigned in the trail at levels less than or equal to the entry's level.
;; 5) For any entry with a non-nil reason, the reason clause is not satisfied by the trail at the time of assignment (i.e., the reason clause was unit under the trail when the literal was assigned).
;; ==============================================================

;; Trail entry
(defun make-trail-entry (lit level &optional reason)
  "Create a trail entry for literal LIT at decision level LEVEL with optional REASON clause."
  `(,lit ,reason . ,level))

(defun trail-entry-lit (entry) (car entry))
(defun trail-entry-var (entry) (lit-var (car entry)))
(defun trail-entry-val (entry) (lit-sign (car entry)))
(defun trail-entry-reason (entry) (cadr entry))
(defun trail-entry-level (entry) (cddr entry))

;; Trail
(defun empty-trail () nil)
(defun trail-empty? (trail) (null trail))

(defun trail-top (trail)
  (dassert (not (trail-empty? trail)) "Trail is empty, no top entry")
  (first trail))

(defun trail-pop (trail)
  (dassert (not (trail-empty? trail)) "Trail is empty, cannot pop")
  (rest trail))

(defun trail-push (trail lit level &optional reason)
  "Returns a new trail with literal LIT assigned at decision level LEVEL with optional REASON.

   Pre: the variable of LIT is not already assigned in TRAIL."
  (dassert (null (trail-get-var trail (lit-var lit)))
           "Variable ~A is already assigned in trail" (lit-var lit))

  (cons (make-trail-entry lit level reason) trail))

(defun trail-max-level (trail)
  "Returns the maximum decision level in the trail, or -1 if the trail is empty."
  (if (null trail) -1 (trail-entry-level (trail-top trail))))

(defun trail-get-var (trail var)
  "Returns entry for variable VAR in TRAIL, or nil if VAR is not assigned in TRAIL."
  (find var trail :key #'trail-entry-var))

(defun trail-get (trail lit)
  "Apply trail to lit.
   Return (val assigned?)"
  (let ((entry (trail-get-var trail (lit-var lit))))
    (if (null entry)
        (values nil nil)
        (values (eq (trail-entry-val entry) (lit-sign lit)) t))))

(defun trail-most-recent-two (trail level cl)
  "Returns (values entry1 entry2) for the two most recent entries at decision level LEVEL
   that are also in clause CL. entry1 is the most recent, entry2 is the second most recent.
   Returns (values nil nil) if fewer than two such entries exist."
  (let ((first nil)
        (second nil))
    (dolist (entry trail (values first second))
      (let ((entry-level (trail-entry-level entry)))
        (cond
          ((= entry-level level)
           (when (clause-has-var? cl (trail-entry-var entry))
             (if (null first)
                 (setf first entry)
                 (progn
                   (setf second entry)
                   (return (values first second))))))
          ((< entry-level level)
           (return (values first second)))
          (t nil))))))

(defun trail-backtrack (trail level)
  "Returns a new trail with all entries at decision levels greater than LEVEL removed.
   The top of new trail is a decision entry at LEVEL.

   Pre: LEVEL >= 0 and LEVEL <= (trail-max-level trail)
        The TRAIL is well-formed."
  (dassert (and (>= level 0) (<= level (trail-max-level trail)))
           "Invalid backtrack level ~A for trail with max level ~A" level (trail-max-level trail))
  (member-if #'(lambda (entry)
                 (<= (trail-entry-level entry) level))
             trail))

;; If we make trail stateful, we can bundle the assignment with the trail and avoid converting back and forth between trail and assignment.
(defun trail->assignment (trail)
  "Convert a trail to an assignment (hash table mapping var -> val).
   Inv: the trail is consistent (no variable is assigned both true and false)."
  (let ((asgn (make-assignment)))
    (dolist (entry trail)
      (let ((var (trail-entry-var entry))
            (val (trail-entry-val entry)))
        (dassert (let+ (((&values assigned-val assigned?) (assignment-get asgn var)))
                   (or (not assigned?) (eql assigned-val val)))
                 "Variable ~A assignment is inconsistent with values ~A and ~A" var assigned-val val)
        (assignment-set asgn var val)))
    asgn))

;; ==============================================================
;; Simple Queue APIs
;; ==============================================================

(defun make-queue () (cons nil nil))

(defun queue-empty? (queue)
  (null (car queue)))

(defun enqueue (item queue)
  (let ((new-cons (list item)))
    (if (car queue)
        (setf (cdr (cdr queue)) new-cons)
        (setf (car queue) new-cons))
    (setf (cdr queue) new-cons)))

(defun dequeue (queue)
  (pop (car queue)))

(defun clear-queue (queue)
  (setf (car queue) nil
        (cdr queue) nil))

;; ==============================================================
;; Two Literals Watching Scheme APIs
;; ==============================================================

;; Watch List: maps a literal to a list of clauses watching that literal
(defun make-watch-list ()
  "Create an empty watch list mapping literals to clauses watching them"
  (make-hash-table :test #'eql))

(defun watch-list-get (wl lit)
  "Get the list of clauses watching literal lit"
  (gethash lit wl nil))

(defun watch-list-add! (wl lit cl)
  "Add clause cl to the watch list for literal lit (destructive)"
  (push cl (gethash lit wl)))

(defun watch-list-remove! (wl lit cl)
  "Remove clause cl from the watch list for literal lit (destructive)"
  ;; Note the two gethash calls are necessary; the first is really a puthash, while the second is a gethash.
  (setf (gethash lit wl) (delete cl (gethash lit wl) :test #'eq :count 1)))

;; Clause Watches: maps a clause to its two watched literals (cons cell)
(defun make-clause-watches ()
  "Create an empty clause watches map (clause -> (lit1 . lit2))"
  (make-hash-table :test #'eq))

(defun clause-watches-get (cw cl)
  "Get the two watched literals for clause cl as (lit1 . lit2), or nil if not found"
  (gethash cl cw))

(defun clause-watches-set! (cw cl lit1 lit2)
  "Set the watched literals for clause cl to (lit1 . lit2) (destructive)"
  (setf (gethash cl cw) (cons lit1 lit2)))

(defun clause-watches-update! (cw cl old-lit new-lit)
  "Update one of the watched literals for clause cl: replace old-lit with new-lit (destructive)"
  (let ((watches (gethash cl cw)))
    (cond
      ((eql (car watches) old-lit) (setf (car watches) new-lit))
      ((eql (cdr watches) old-lit) (setf (cdr watches) new-lit))
      (t (error "Literal ~A not found in watches ~A for clause" old-lit watches)))))

(defun clause-watches-other (cw cl lit)
  "Get the other watched literal for clause cl (not lit)"
  (let ((watches (gethash cl cw)))
    (if (eql (car watches) lit)
        (cdr watches)
        (car watches))))

(defstruct (watches (:constructor make-watches-internal))
  "Combined watch structure containing both watch-list and clause-watches

   Valid watches invariants respect to a trail assignment:
   1. watches don't contain duplicate clauses under pointer equality, eq, and
   2. for any watched clause cl with watches (w1, w2),
      - cl doesn't contain duplicate literals,
      - w1 and w2 are negations of unique literals in cl,
      - w1 and w2 arenot falsified by the trail assignment"

  (lit->clauses (make-watch-list) :type hash-table)      ; lit -> list of clauses
  (clause->lits (make-clause-watches) :type hash-table)) ; clause -> (lit1 . lit2)

(defun make-watches ()
  "Create a new combined watches structure"
  (make-watches-internal))

(defun watches-get-clauses (w lit)
  "Get clauses watching literal lit"
  (watch-list-get (watches-lit->clauses w) lit))

(defun watches-get (w cl)
  "Get watched literals for clause cl as (lit1 . lit2)"
  (clause-watches-get (watches-clause->lits w) cl))

(defun watches-get-other-watch (w cl watch)
  "Get the other watched literal for clause cl"
  (clause-watches-other (watches-clause->lits w) cl watch))

(defun watches-add! (w cl lit1 lit2)
  "Add clause cl with watched literals lit1 and lit2 (destructive)"
  (watch-list-add! (watches-lit->clauses w) lit1 cl)
  (watch-list-add! (watches-lit->clauses w) lit2 cl)
  (clause-watches-set! (watches-clause->lits w) cl lit1 lit2))

(defun watches-update! (w cl old-lit new-lit)
  "Update a watch: clause cl stops watching old-lit and starts watching new-lit (destructive)"
  (watch-list-remove! (watches-lit->clauses w) old-lit cl)
  (watch-list-add! (watches-lit->clauses w) new-lit cl)
  (clause-watches-update! (watches-clause->lits w) cl old-lit new-lit))

;;; ============================================================
;;; VSIDS Strategy: Literal-Level Granularity
;;; ============================================================

;; Standard VSIDS parameters from literature (can be tuned for better performance)
(defparameter *literal-decay-factor* 0.95d0)
(defparameter *rescale-threshold* 1e100)
(defparameter *rescale-factor* 1e-100)

(defstruct (activities (:constructor %make-activities))
  scores  ; A simple array: index 2n = +x_n, 2n+1 = -x_n
  inc)    ; The current "value" of a conflict bump (grows exponentially)

(defun make-activities (num-vars)
  "Initializes scores for 2 * num-vars literals with subtle random noise."
  (let* ((num-lits (* 2 num-vars))
         (arr (make-array num-lits :element-type 'double-float)))
    (dotimes (i num-lits)
      ;; Small random noise (0.0, 1.0) allows VSIDS to override
      ;; initial hunches after the very first conflict.
      (setf (aref arr i) (random 1.0d0)))
    (%make-activities :scores arr :inc 1.0d0)))

(defun activities-num-vars (act)
  "Returns the number of variables tracked in activities ACT."
  (ash (length (activities-scores act)) -1))

(defun bump-lit-activity! (act lit)
  "Increment activity for literal 'lit'.
   No overflow check here for speed."
  (incf (aref (activities-scores act) lit) (activities-inc act)))

(defun rescale-activities! (act)
  "Normalizes all scores and the 'inc' factor to prevent IEEE 754 overflow."
  (let ((scores (activities-scores act)))
    (dotimes (i (length scores))
      (setf (aref scores i) (* (aref scores i) *rescale-factor*)))
    ;; Scale the 'inc' down so future bumps remain proportional to old scores
    (setf (activities-inc act) (* (activities-inc act) *rescale-factor*))))

(defun decay-activities! (act)
  "Effectively decays past activities by increasing the future increment.
   This is called exactly once per conflict."
  (setf (activities-inc act)
        (/ (activities-inc act) *literal-decay-factor*))
  ;; Check overflow of the global 'inc' rather than checking every literal
  (when (> (activities-inc act) *rescale-threshold*)
    (rescale-activities! act)))

(defun select-literal (act asgn)
  "Linear scan for the unassigned literal with the highest score.
   Naturally chooses variable and polarity simultaneously.

   If all variables assigned, returns nil (caller should check for this case and handle it as a SAT solution)."
  (let ((best-lit nil)
        (max-score -1.0d0)
        (scores (activities-scores act))
        (num-vars (activities-num-vars act)))
    ;; Iterate through all variables and check scores for unassigned ones
    (dotimes (var num-vars)
      (let+ (((&values _ assigned?) (assignment-get asgn var)))
        (unless assigned?
          (let* ((pos-lit (* 2 var))
                 (neg-lit (1+ pos-lit))
                 (pos-score (aref scores pos-lit))
                 (neg-score (aref scores neg-lit)))
            (when (> pos-score max-score)
              (setf max-score pos-score best-lit pos-lit))
            (when (> neg-score max-score)
              (setf max-score neg-score best-lit neg-lit))))))
    best-lit))

;; ============================================================
;; DPLL Algorithm
;; ===========================================================

(defun dpll-try-enqueue (lit trail propQ level &optional reason)
  "Enqueue unit literal lit for propagation if it is not already satisfied by the trail.
   Returns (values conflict? new-trail)
   where conflict? is true if lit is falsified by the trail (conflict), and
         new-trail is the updated trail with lit assigned if no conflict, or nil if conflict.

   Inv: any lit in propQ is in trail with no conflicts

   Pre: level >= 0
        reason is the clause that caused this propagation (nil for decisions and initial unit clauses)
   Post: if conflict? = nil then propQ has lit enqueued and new-trail is trail extended with lit's assignment at level LEVEL with reason REASON.
         else propQ and new-trail are unchanged (caller should handle the conflict)."
  (dassert (>= level 0) "Decision level must be non-negative, got ~A" level)
  (let+ (((&values val assigned?) (trail-get trail lit)))
    (if assigned?
        (if val
            (values nil trail) ;; satisfied
            (values t nil)) ;; conflict
        (progn ;; not assigned, assign it and enqueue for propagation
          (when reason (dpll-stats-inc-propagations)) ;; Count propagations (not decisions)
          (enqueue lit propQ)
          (values nil (trail-push trail lit level reason))))))

(defun dpll-init (cls num-vars)
  "Preprocess the clauses cls by computing the watch lists and initializing the propagation queue.
   Returns (values conflict? new-cls trail activities watches propQ)
   where conflict? if cls are unsat,
         if conflict? = nil, then
            new-cls is a list of simplified clauses or nil if the cls are sat,
            trail is the initial trail propagated from unit clauses with level 0, nil if no unit clauses,
            activities is the initial activity scores (randomly determined) for variables,
            watches is the initialized watches structure, and
            propQ is the initialized queue of unit literals to propagate.
          else
            new-cls, trail, activities, watches, and propQ are all nil.

  Pre: each cl in cls doesn't contain duplicate literals

  Post: any lit in propQ is in trail with no conflicts and is treated as a decision (no reason clause),
        watches are valid with respect to trail,
        propQ is empty."

  (let ((trail nil)
        (new-cls nil)
        (watches (make-watches))
        (propQ (make-queue)))
    (dolist (cl cls)
      (cond
        ;; If clause is satisfied, skip it
        ((null cl) nil)
        ;; If clause is empty, we have a conflict - UNSAT
        ((clause-empty? cl) (return-from dpll-init (values t nil nil nil nil)))
        ;; If clause is unit, propagate it immediately; treat it as a decision!
        ((clause-unit? cl)
         (let+ (((&values conflict? new-trail) (dpll-try-enqueue (clause-unit-lit cl) trail propQ 0)))
           (if conflict?
               (return-from dpll-init (values t nil nil nil nil nil)) ;; conflict from unit clause - UNSAT
               (setf trail new-trail))))
        ;; Otherwise, add watches and keep the clause
        (t (push cl new-cls)
           (let+ (((&values lit1 lit2) (clause-two-lits cl)))
             ;; The watches are negated because we want to watch for them when they become false under the trail assignment
             (watches-add! watches cl (lit-negate lit1) (lit-negate lit2))))))
    (values nil new-cls trail (make-activities num-vars) watches propQ)))

(defun dpll-find-new-unassigned (cl trail old-lit other-lit)
  "Find an unassigned literal in clause cl to watch that is not falsified by the trail, excluding old-lit and other-lit.
   Returns the unassigned literal if found, or nil if no such literal exists.

   Pre: old-lit and other-lit are the current watched literals for cl, and cl doesn't contain duplicate literals.
        old-lit and other-lit are not falsified by trail."
  (clause-map #'(lambda (lit)
                  (unless (or (eql lit old-lit) (eql lit other-lit))
                    (let+ (((&values val assigned?) (trail-get trail lit)))
                      ;; Return lit if unassigned or satisfied
                      (when (or (not assigned?) val)
                        (return-from dpll-find-new-unassigned lit)))))
              cl)
  nil)

(defun dpll-unit (trail watches propQ)
  "Apply two literal watching scheme to unit propagate under the current trail assignment.
   Returns (values conflict-cl new-trail)
   where conflict-cl is the clause that caused a conflict, or nil if no conflict
         new-trail is the updated trail after propagation.

   Pre: watches are valid with respect to trail.
        if trail is nil, then propQ must be empty by invariant 2

   Inv: 1. for any clause, the two watched literals are not falsified by the current trail assignment.
        2. for any lit in propQ, lit is in trail with no conflicts.
        3. watches are valid with respect to new-trail.

   Post: 1. if conflict-cl != nil, then new-trail != nil.
            else new-trail can be nil or a valid trail without conflicts.
         2. propQ is empty.
         3. watches are valid with respect to new-trail."
  (if (queue-empty? propQ)
      (values nil trail)  ; No more units to propagate, return current trail
      (let ((new-trail trail)
            (watch (dequeue propQ)))
        ;; Get clauses that are affected by watch being true
        (let ((watching-clauses (watches-get-clauses watches watch)))
          (loop for cl in (copy-list watching-clauses) ;; Need to copy since we may modify the watch list during iteration
                do (let* ((other-watch (watches-get-other-watch watches cl watch))
                          ;; the two literals in cl
                          (watch-lit (lit-negate watch))
                          (other-lit (lit-negate other-watch)))
                     (let+ (((&values other-val other-assigned?) (trail-get trail other-lit)))
                       (if (and other-assigned? other-val)
                           nil ;; other-watch is satisfied, cl is satisfied
                           ;; other-watch is unassigned, so try to find a new literal to watch in cl that is not falsified
                           (let ((unassigned-lit (dpll-find-new-unassigned cl new-trail watch-lit other-lit)))
                             (if unassigned-lit
                                 ;; Found a new watch, update the watches
                                 ;; Note invariant 3 holds since cl is not already a watch for new-watch
                                 (let ((new-watch (lit-negate unassigned-lit)))
                                   (watches-update! watches cl watch new-watch))
                                 ;; No new watch found, other-lit is a unit
                                 ;; So try enqueue other-lit with cl as the reason
                                 (let+ (((&values conflict? result-trail) (dpll-try-enqueue other-lit new-trail propQ (trail-max-level new-trail) cl))) ;; trail-max-level cannot be < 0 by invariant 2
                                   (if conflict?
                                       (progn
                                         (clear-queue propQ)
                                         (return-from dpll-unit (values cl new-trail))) ;; conflict found - return with conflict clause and current trail
                                       (setf new-trail result-trail)))))))))
         (dpll-unit new-trail watches propQ)))))

(defun dpll-decide (activities trail propQ)
  "Decide the next variable to assign based on the current cls and trail.
   Returns (values decide? new-trail)
   where decide? is true if a new decision variable was chosen, false if no more decisions possible (all variables assigned), and
         new-trail is the updated trail with the new decision if decide? is true, or the same trail if decide? is false.

   Pre: cls is either nil or contains no unit clauses under the current trail assignment.

   Post: if decide? = true, then new-trail is extended with a new decision variable assigned to true at the new decision level (level), and propQ is updated.
         else new-trail and propQ remain the same."
  (let ((asgn (trail->assignment trail)))
    (let ((lit (select-literal activities asgn)))
      (if (null lit)
          (values nil trail) ;; No unassigned variables left, SAT
          (let* ((new-level (1+ (trail-max-level trail))))
            (dpll-stats-inc-decisions)
            (dpll-stats-update-max-level new-level)
            (let+ (((&values conflict? new-trail) (dpll-try-enqueue lit trail propQ new-level)))
              (dassert (not conflict?) "Conflict cannot occur when making a new decision, got ~A for literal ~A" conflict? lit)
              (values t new-trail)))))))

(defun dpll-analyze (conflict-cl activities trail)
  "Analyze the conflict clause at the current trail.
   Return (values learnt-cl bt-level)
   where learnt-clause is a new clause derived from the conflict that will be added to the learnt clause set.
         bt-level is the backtracking level to jump back to, or -1 if unsat.

   Pre: conflict-cl != nil and is a clause that is falsified by the current trail assignment (i.e., all its literals are falsified under the current trail).
        trail != nil and there is a conflict (empty clause) in cls under the current trail assignment."

  (labels ((find-first-uip (working-cl trail seen)
             "Find the first Unique Implication Point (1UIP) in the conflict clause with respect to the current trail.
              While finding the UIP via resolution, the working clause can become:
              Returns the clause containing the first UIP if found, or nil if no UIP exists.

              Pre: working-cl != nil and is falsified by the current trail assignment.
                   working-cl is non-empty,
                   trail != nil and there is a conflict (empty clause) in cls under the current trail assignment.
                   (trail-max-level trail) > 0."

             (dassert working-cl "Working clause cannot be nil when finding UIP")
             (dassert (not (clause-empty? working-cl)) "Working clause cannot be empty when finding UIP")
             (dassert trail "Trail cannot be nil when finding UIP")
             (dassert (> (trail-max-level trail) 0) "Trail must have at least one decision level when finding UIP")

             (let+ (((&values most-recent second-most-recent) (trail-most-recent-two trail (trail-max-level trail) working-cl)))
              (dassert most-recent "There must be at least one entry from current level in trail for conflict clause ~A" working-cl)
              (if (null second-most-recent)
                  ;; Only one literal from current level, this is the UIP
                  working-cl
                  ;; More than one literal from current level, resolve with reason of most recent entry and continue searching
                  (let ((reason-cl (trail-entry-reason most-recent)))
                    (dassert reason-cl "Reason clause cannot be nil for non-decision entries in trail")

                    ;; Add literals from the reason clause to 'seen'
                    (clause-map #'(lambda (lit) (hash-set-add seen lit)) reason-cl)

                    (let ((resolved-cls (resolve-var (list working-cl reason-cl) (trail-entry-var most-recent))))
                      (dassert resolved-cls "Resolution must produce at least one clause")
                      (find-first-uip (first resolved-cls) trail seen))))))

           (backtrack-level (learnt-cl trail)
             "Returns the second highest level in the learnt clause to jump back to, or -1 if unsat."
             (let ((levels nil))
                ;; Collect unique decision levels from literals in learnt-cl
                (clause-map #'(lambda (lit)
                                (let ((entry (trail-get-var trail (lit-var lit))))
                                  (when entry
                                    (pushnew (trail-entry-level entry) levels))))
                           learnt-cl)
                ;; Sort levels in descending order and get second highest
                (setf levels (sort levels #'>))
                (cond ((null levels) -1)           ; UNSAT
                      ((null (cdr levels)) 0)      ; Unit, backtrack to 0
                      (t (second levels))))))      ; Return second highest level

    (if (zerop (trail-max-level trail))
        (values nil -1)
        (let* ((seen (clause-copy conflict-cl)) ;; 'seen' is a COPY of conflict-cl
               (learnt-cl (find-first-uip conflict-cl trail seen)))
          (dassert learnt-cl "Learnt clause cannot be nil after analysis")

          ;; Stats: track conflict and learnt clause
          (dpll-stats-inc-conflicts)
          (dpll-stats-add-learnt (clause-size learnt-cl))

          ;; BUMP: Reward all involved literals exactly once.
          (hash-set-map (lambda (lit) (bump-lit-activity! activities lit)) seen)
          ;; DECAY: Increase the 'inc' value for the next conflict.
          (decay-activities! activities)

          (values learnt-cl (backtrack-level learnt-cl trail))))))

(defun dpll-backtrack (learnt-cl trail watches propQ bt-level)
   "Backtrack the trail to the given backtracking level.
    Update the propagation queue propQ to reflect the new trail after backtracking.
    Returns the new trail after backtracking.

    Watches are updated by adding the new learnt clause (if not unit) during backtracking.
    For other clauses, the watches remain valid since the watch invariant still holds before and after backtracking.
    Any stale watches will be corrected lazily at the next propagation when we enqueue the flipped literal.

    Pre: bt-level >= 0, trail != nil, and bt-level < current max decision level in trail.
         propQ is empty before backtracking.
         learnt-cl != nil

    Post: the returned trail != nil and its top entry is a decision at bt-level with the opposite assignment.
          propQ contains the unit literal with the flipped assignment."

  (dassert learnt-cl "Learnt clause cannot be nil for backtracking")
  (dassert trail "Trail cannot be empty when backtracking")
  (dassert (>= bt-level 0) "Backtracking level must be non-negative: ~A" bt-level)
  (let ((max-level (trail-max-level trail)))
    (dassert (< bt-level max-level) "Backtracking level ~A must be less than current max decision level ~A in trail" bt-level max-level))
  (dassert (queue-empty? propQ) "Propagation queue must be empty before backtracking")

  ;; Stats: track non-chronological backtracks (backjumps)
  (when (< bt-level (1- (trail-max-level trail)))
    (dpll-stats-inc-backjumps))

  (let ((bt-trail (trail-backtrack trail bt-level)))
    (dassert bt-trail "Trail cannot be nil after backtracking")
    (if (clause-unit? learnt-cl)
        ;; If the learnt clause is unit, we can directly enqueue it without adding watches since it will be propagated immediately after backtracking
        (progn
          (dassert (zerop bt-level) "Learnt unit clause can only be propagated at level 0 during backtracking, got ~A" bt-level)
          (let+ (((&values conflict? new-trail) (dpll-try-enqueue (clause-unit-lit learnt-cl) bt-trail propQ bt-level)))
            (dassert (not conflict?) "Learnt unit clause cannot cause a conflict during backtracking, got ~A for literal ~A" conflict? (clause-unit-lit learnt-cl))
            new-trail))
        ;; Otherwise, use the asserting lit (unassigned) and the decision literal (falsified) at bt-level as watching literals for learnt-clause
        (labels ((find-watch-literals (learnt-cl bt-trail bt-level)
                   (let ((asserting-lit nil)
                         (bt-lit nil))
                     (clause-map #'(lambda (lit)
                                     (let ((entry (trail-get-var bt-trail (lit-var lit))))
                                       (if (or (null entry)
                                               (= (trail-entry-level entry) bt-level))
                                           (if (null entry)
                                               (setf asserting-lit lit) ;; not assigned
                                               (setf bt-lit lit)))
                                       (when (and asserting-lit bt-lit)
                                         (return-from find-watch-literals (values asserting-lit bt-lit)))))
                                 learnt-cl)
                     ;; unreached
                     (values nil nil))))
          (let+ (((&values asserting-lit bt-lit) (find-watch-literals learnt-cl bt-trail bt-level)))
            (dassert asserting-lit "Asserting literal has to exist.")
            (dassert bt-lit "A literal with backtrack level has to exist.")
            (watches-add! watches learnt-cl (lit-negate asserting-lit) (lit-negate bt-lit))

            (let+ (((&values conflict? new-trail) (dpll-try-enqueue asserting-lit bt-trail propQ bt-level learnt-cl)))
              (dassert (not conflict?) "Asserting literal cannot cause a conflict during backtracking, got ~A for literal ~A" conflict? asserting-lit)
              new-trail))))))

(defun dpll-sat (trail activities watches propQ)
  "Main DPLL loop: apply unit propagation, then either analyze conflict or decide next variable.
   Returns (values result new-trail)
   where result is 'sat or 'unsat
         new-trail is the final trail after backtracking if needed.

   propQ is updated in-place during propagation, decision, and backtracking."

  (let+ (((&values conflict-cl trail0) (dpll-stats-time :propagate (dpll-unit trail watches propQ))))
    (if conflict-cl
        ;; Analyze conflict and backtrack
        (let+ (((&values learnt-cl bt-level) (dpll-stats-time :analyze (dpll-analyze conflict-cl activities trail0))))
          (if (< bt-level 0)
              (values 'unsat nil)  ; No more backtracking possible, UNSAT
              (let ((trail1 (dpll-stats-time :backtrack (dpll-backtrack learnt-cl trail0 watches propQ bt-level))))
                (dpll-sat trail1 activities watches propQ))))
        ;; Decide
        (let+ (((&values decide? trail1) (dpll-stats-time :decide (dpll-decide activities trail0 propQ))))
          (if (not decide?)
              (values 'sat trail0)  ; No more decisions possible, SAT with current assignment
              (dpll-sat trail1 activities watches propQ))))))

(defun dpll (f)
  "Main DPLL function: takes a formula f, converts to CNF, and applies DPLL algorithm.
   Returns 'sat with assignment alist or 'unsat with nil."
  (dpll-stats-time :total
    (let+ (((&values cnf skeleton amap) (tseitin f))
           (vm (make-var-manager))
           (cls (cnf->clauses cnf vm))) ;; mutates vm

      (dpll-stats-set-formula (length (pvars skeleton)) 
                              (var-manager-num-vars vm)
                              (length cls)
                              (if cls (apply #'max (mapcar #'clause-size cls)) 0))
      (dbg "After init~%")
      (let+ (((&values conflict? cls trail activities watches propQ) (dpll-stats-time :sat (dpll-init cls (var-manager-num-vars vm)))))
        (if conflict?
            (values 'unsat nil)  ; Conflict with initial unit propagation, UNSAT
            (let+ (((&values result trail) (dpll-stats-time :sat (dpll-sat trail activities watches propQ)))
                    (result-asgn (when (eq result 'sat)
                                  (let ((asgn (trail->assignment trail)))
                                    (assignment->alist asgn vm amap)))))
              (values result result-asgn)))))))

(defun test-dpll (f &optional (expected 'sat))
  "Test dpll on formula f by verifying its result.
   Expected defaults to 'sat unless specified as 'unsat."
  (let+ (((&values result asgn) (dpll f)))
    (verify-sat f result asgn expected)))

(defun run-test-dpll ()
  "Run DPLL tests and report statistics."
  (dpll-stats-reset)
  (run-tests #'test-dpll)
  (test-dpll (ramsey 3 4 8))
  ;; ACL2s cannot prove the case to be unsat (but no counter examples).
  (test-dpll (ramsey 3 4 9) 'unsat)
  ;; Time out:
  ;; (test-dpll (ramsey 4 4 17)) ; n < R(4,4), can avoid monochromatic K_4 - SAT
  ;; (test-dpll (ramsey 4 4 18) 'unsat) ; n >= R(4,4), cannot avoid monochromatic K_4 - UNSAT
  (dpll-stats-report))

(run-test-dpll)
