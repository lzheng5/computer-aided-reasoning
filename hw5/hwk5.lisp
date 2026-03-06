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

(let ((f '(not (foo (and)))))
  (assert-equal (p-simplify-flatten f) '(not (foo t))))

(let ((f '(not (foo (and p)))))
  (assert-equal (p-simplify-flatten f) '(not (foo p))))

(let ((f '(and p q (and r s) (or u v))))
  (assert-equal (p-simplify-flatten f) '(and p q r s (or u v))))

(assertf #'p-simplify-flatten '(not (not p)) '(not (not p)))

(defun p-simplify-not (f)
  (match f
    ((list 'not a)
     (match a
       ((list 'not b) (p-simplify-not b))
       ((list* 'iff bs) `(xor ,@(mapcar #'p-simplify-not bs)))
       ((list* 'xor bs) `(iff ,@(mapcar #'p-simplify-not bs)))
       ((list* op bs) `(not (,op ,@(mapcar #'p-simplify-not bs))))
       (_ `(not ,a))))
    ((list* op as) `(,op ,@(mapcar #'p-simplify-not as)))
    (_ f)))

(assertf #'p-simplify-not '(not (not p)) 'p)

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
                 (neg-count 0)
                 (result nil))
            ;; Count occurrences
            (dolist (a as)
              (incf (gethash a pairs 0)))
            ;; Check for opposites and count odd occurrences
            (maphash #'(lambda (k v)
                         (let ((neg (negate k)))
                           (when (and (gethash neg pairs)
                                      (not (gethash (list :seen k neg) pairs)))
                             (setf (gethash (list :seen k neg) pairs) t)
                             (setf (gethash (list :seen neg k) pairs) t)
                             (let ((n (min (gethash k pairs) (gethash neg pairs))))
                               (incf neg-count n)
                               (decf (gethash k pairs) n)
                               (decf (gethash neg pairs) n)))))
                     pairs)
            ;; Build result: keep odd occurrences
            (maphash #'(lambda (k v)
                         (unless (and (listp k) (eq (car k) :seen))
                           (when (oddp v)
                             (push k result))))
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
                 (neg-count 0)
                 (result nil))
            ;; Count occurrences
            (dolist (a as)
              (incf (gethash a pairs 0)))
            ;; Check for opposites
            (maphash #'(lambda (k v)
                         (let ((neg (negate k)))
                           (when (and (gethash neg pairs)
                                      (not (gethash (list :seen k neg) pairs)))
                             (setf (gethash (list :seen k neg) pairs) t)
                             (setf (gethash (list :seen neg k) pairs) t)
                             (let ((n (min (gethash k pairs) (gethash neg pairs))))
                               (incf neg-count n)
                               (decf (gethash k pairs) n)
                               (decf (gethash neg pairs) n)))))
                     pairs)
            ;; Build result: keep odd occurrences
            (maphash #'(lambda (k v)
                         (unless (and (listp k) (eq (car k) :seen))
                           (when (oddp v)
                             (push k result))))
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

(defun lit->var (lit)
  (match lit
    ((list 'not v) v)
    (_ lit)))

(defun lit->val (lit)
  (match lit
    ((list 'not _) nil)
    (_ t)))

;; pre: no duplicates and opposites
(defun p-simplify-shannon (f &optional env)
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
     (if (in op '(and or))
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
                (nvars (mapcar #'lit->var nlits)) 
                (nenv (extend vars (mapcar #'(lambda (v) id) vars)
                              (extend nvars (mapcar #'(lambda (v) (not id)) nvars)
                                      env))))
           `(,op ,@vars ,@nlits ,@(mapcar #'(lambda (a) (p-simplify-shannon a nenv)) as)))
         `(,op ,@(mapcar #'(lambda (a) (p-simplify-shannon a env)) as))))))

(assertf #'p-simplify-shannon '(iff nil p q) '(iff nil p q))
(assertf #'p-simplify-shannon '(and (or p q) (or r q p) p) '(and p (or t q) (or r q t)))
(assertf #'p-simplify-shannon '(and (or p q) (or r q p) (not p)) '(and (not p) (or nil q) (or r q nil)))
(assertf #'p-simplify-shannon '(and (not p) q (or r q)) '(and q (not p) (or r t)))
(assertf #'p-simplify-shannon '(or (and p q) (and r q p) p) '(or p (and nil q) (and r q nil)))
(assertf #'p-simplify-shannon '(or p q (and r q)) '(or p q (and r nil)))
(assertf #'p-simplify-shannon '(or (and p q) (and r q p) (not p)) '(or (not p) (and t q) (and r q t)))
(assertf #'p-simplify-shannon '(or (not p) q (and r q)) '(or q (not p) (and r nil)))

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

(defun test-simplify (f)
  (assert-acl2s-equal f (p-simplify f)))

;; Used Claude to generate tests
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
     (let ((a (first args))
           (b (second args)))
       `((or (not ,v) (not ,a) ,b)
         (or (not ,v) ,a (not ,b))
         (or ,v (not ,a) (not ,b))
         (or ,v ,a ,b))))

    (xor
     ;; v ↔ (a ⊕ b): different polarity
     ;; (¬v ∨ ¬a ∨ ¬b) ∧ (¬v ∨ a ∨ b) ∧ (v ∨ ¬a ∨ b) ∧ (v ∨ a ∨ ¬b)
     (let ((a (first args))
           (b (second args)))
       `((or (not ,v) (not ,a) (not ,b))
         (or (not ,v) ,a ,b)
         (or ,v (not ,a) ,b)
         (or ,v ,a (not ,b)))))

    (if
     ;; v ↔ (if a b c) ≡ v ↔ ((a ∧ b) ∨ (¬a ∧ c))
     ;; (¬v ∨ ¬a ∨ b) ∧ (¬v ∨ a ∨ c) ∧ (v ∨ ¬a ∨ ¬b) ∧ (v ∨ a ∨ ¬c)
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
        ((list* 'and args)
         (dolist (arg args)
           (let ((top-var (transform-subf arg)))
             (push top-var clauses)))
         `(and ,@(reverse clauses)))
        (_
         (let ((top-var (transform-subf f)))
            (push top-var clauses)
           `(and ,@(reverse clauses))))))))

(defun tseitin (f)
  (let+ ((simplified (p-simplify f))
         ((&values skeleton amap) (p-skeleton simplified))
         (unchained (tseitin-unchain skeleton))
         (cnf (tseitin-transform unchained))
         (cnf (p-simplify cnf)))
    (values cnf amap)))

(defun acl2s-valid? (f)
  "Check if f is valid (tautology) using ACL2s"
  (== (car (acl2s-check-equal f 't)) nil))

(defun acl2s-unsat? (f)
  "Check if f is unsatisfiable using ACL2s (f is UNSAT iff (negate f) is valid)"
  (acl2s-valid? (negate f)))

(defun test-tseitin (f)
  "Test equisatisfiability: f is UNSAT iff (tseitin f) is UNSAT"
  (let* ((cnf (tseitin f))
         (f-unsat (acl2s-unsat? f))
         (cnf-unsat (acl2s-unsat? cnf)))
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

(defun clause->list (c)
  "Convert a clause to a list of literals"
  (match c
    ((type boolean) (list c))
    ((type symbol) (list c))
    ((list 'not _) (list c))
    ((list* 'or args) args)
    (_ (error "Not a clause: ~A" c))))

(defun cnf->clauses (f)
  "Convert a CNF formula to a list of clauses (each clause is a list of literals)"
  (match f
    ((type boolean) (if f nil (list nil)))  ; t -> empty, nil -> (())
    ((type symbol) (list (list f)))
    ((list 'not _) (list (list f)))
    ((list* 'or args) (list args))
    ((list* 'and args) (mapcar #'clause->list args))
    (_ (error "Not in CNF: ~A" f))))

(defun remove-satisfied-clauses (clauses satisfied-lits)
  "Remove all clauses containing any literal in satisfied-lits."
  (remove-if #'(lambda (c)
                 (some #'(lambda (lit) (in lit satisfied-lits)) c))
             clauses))

(defun remove-lit-from-clauses (clauses lit)
  "Remove lit from all clauses."
  (mapcar #'(lambda (c) (remove lit c :test #'equal)) clauses))

;; Post: no more pure literals
(defun dp-pure (clauses)
  "Pure literal elimination. Returns (values new-clauses assignment).
   A pure literal appears only in one polarity across all clauses."
  (let ((pos (make-hash-table :test #'equal))   
        (neg (make-hash-table :test #'equal)))
    ;; Collect all literals using lit->var/lit->val
    (dolist (c clauses)
      (dolist (lit c)
        (let ((var (lit->var lit))
              (val (lit->val lit)))
          (if val
              (setf (gethash var pos) t)
              (setf (gethash var neg) t)))))
    ;; Find pure literals and build assignment
    (let ((pure-pos nil)
          (pure-neg nil))
      (maphash #'(lambda (v _)
                   (unless (gethash v neg)
                     (push v pure-pos)))
               pos)
      (maphash #'(lambda (v _)
                   (unless (gethash v pos)
                     (push v pure-neg)))
               neg)
      (let ((assignment (append (mapcar #'(lambda (v) (cons v t)) pure-pos)
                                (mapcar #'(lambda (v) (cons v nil)) pure-neg)))
            (pure-lits (append pure-pos
                               (mapcar #'(lambda (v) `(not ,v)) pure-neg))))
        (if (null pure-lits)
            (values clauses nil)
            (values (remove-satisfied-clauses clauses pure-lits)
                    assignment))))))

;; Post: no more unit clauses
(defun dp-unit (clauses &optional acc-assignment)
  "Unit propagation. Returns (values new-clauses assignment).
   A unit clause has exactly one literal, which must be true."
  (let ((unit-lit (some #'(lambda (c) (and (== (length c) 1) (car c))) clauses)))
    (if (null unit-lit)
        (values clauses acc-assignment)
        (let* ((neg-lit (negate unit-lit))
               (var (lit->var unit-lit))
               (val (lit->val unit-lit))
               (new-clauses
                (remove-lit-from-clauses
                 (remove-satisfied-clauses clauses (list unit-lit))
                 neg-lit)))
          (dp-unit new-clauses (acons var val acc-assignment))))))

;; TODO: better ways to pick variables 
(defun dp-decide (cls) 
  (some #'(lambda (c) (some #'lit->var c)) cls))

(defun clause->set (clause)
  "Convert a clause (list of literals) to a hash set for O(1) lookup."
  (let ((ht (make-hash-table :test #'equal)))
    (dolist (lit clause ht)
      (setf (gethash lit ht) t))))

(defun subsumes-set? (c1 c2-set c2-len)
  "Return t if c1 subsumes c2 (c1 ⊆ c2).
   c2-set is a hash table, c2-len is the length of c2."
  (and (<= (length c1) c2-len)
       (every #'(lambda (lit) (gethash lit c2-set)) c1)))

(defun remove-subsumed (clauses)
  "Remove clauses that are subsumed by other clauses in the list.
   Keep smaller clauses that subsume larger ones.
   Uses hash tables for O(1) literal lookup."
  ;; Sort by length - shorter clauses first (they subsume longer ones)
  (let* ((sorted (sort (copy-list clauses) #'< :key #'length))
         (result nil))
    (dolist (c sorted)
      (let ((c-set (clause->set c))
            (c-len (length c)))
        ;; Check if c is subsumed by anything in result (which are all shorter or equal)
        ;; r subsumes c means r ⊆ c, so check if every lit in r is in c-set
        (unless (some #'(lambda (r) (subsumes-set? r c-set c-len)) result)
          ;; c is not subsumed; add it (no need to check if c subsumes result
          ;; since result only contains shorter/equal clauses processed before c)
          (push c result))))
    (nreverse result)))

(defun dp-resolve (clauses var)
  (let ((pos-lit var)
        (neg-lit `(not ,var))
        (pos-clauses nil)
        (neg-clauses nil)
        (other-clauses nil))
    ;; Partition clauses
    (dolist (c clauses)
      (cond ((in pos-lit c) (push c pos-clauses))
            ((in neg-lit c) (push c neg-clauses))
            (t (push c other-clauses))))
    ;; Generate resolvents
    (let ((resolvents nil))
      (dolist (pc pos-clauses)
        (dolist (nc neg-clauses)
          (let ((resolvent (remove-dups
                            (append (remove pos-lit pc :test #'equal)
                                    (remove neg-lit nc :test #'equal)))))
            ;; Skip clauses containing both p and (not p)
            (unless (some #'(lambda (lit) (has-opposite lit resolvent)) resolvent)
              (push resolvent resolvents)))))
      ;; Remove subsumed clauses to keep clause set small
      (remove-subsumed (append other-clauses resolvents)))))

(defun dp-sat (cls &optional acc-assignment) 
  (let+ (((&values cls unit-asgn) (dp-unit cls)))
    ;; Early termination after unit propagation
    (cond ((null cls) (values 'sat (append unit-asgn acc-assignment)))
          ((member nil cls :test #'equal) (values 'unsat nil))
          (t
           (let+ (((&values cls pure-asgn) (dp-pure cls))
                  (asgn (append unit-asgn pure-asgn acc-assignment)))
             ;; Early termination after pure literal elimination
             (cond ((null cls) (values 'sat asgn))
                   ((member nil cls :test #'equal) (values 'unsat nil))
                   (t
                    (let* ((var (dp-decide cls))
                           (new-cls (dp-resolve cls var)))
                      (dp-sat new-cls asgn)))))))))

(defun dp (f) 
  (let* ((cnf (tseitin f))
         (clauses (cnf->clauses cnf)))
    (dp-sat clauses)))

(defun subst-formula (f assignment)
  "Substitute variables in formula f according to assignment alist"
  (match f
    ((type boolean) f)
    ((type symbol)
     (let ((val (assoc f assignment :test #'equal)))
       (if val (cdr val) f)))
    ((list* op args) `(,op ,@(mapcar #'(lambda (a) (subst-formula a assignment)) args)))
    (_ f)))

(defun verify-sat (f result assignment)
  "Verify if result and assignment are correct for formula f.
   If result is 'sat, verify that substituting assignment makes f valid.
   If result is 'unsat, verify using ACL2s."
  (case result
    (sat
     (let* ((subst-f (subst-formula f assignment)))
       ;; After partial substitution, remaining formula should be valid (tautology)
       (assert (acl2s-valid? subst-f) () 
               "Partial assignment does not make formula valid: ~A~%Assignment: ~A~%Result: ~A" 
               f assignment subst-f)))
    (unsat
     (assert (acl2s-unsat? f) () "Formula is not UNSAT: ~A" f))
    (otherwise
     (error "Invalid result: ~A (expected 'sat or 'unsat)" result))))

(defun test-dp (f)
  "Test dp on formula f by verifying its result"
  (let+ (((&values result assignment) (dp f)))
    (verify-sat f result assignment)))

;; Tests generated with Claude
;; Basic SAT tests
(test-dp 'p)                                    ; single var - SAT
(test-dp '(or p q))                             ; simple disjunction - SAT
(test-dp '(and p q))                            ; simple conjunction - SAT
(test-dp '(implies p q))                        ; implication - SAT
(test-dp '(iff p q))                            ; biconditional - SAT

;; Basic UNSAT tests
(test-dp '(and p (not p)))                      ; contradiction - UNSAT
(test-dp '(and (or p q) (not p) (not q)))       ; UNSAT
(test-dp '(and p q (or (not p) (not q)) (or p (not q)) (or (not p) q)))  ; UNSAT

;; More complex SAT formulas
(test-dp '(and (or p q) (or (not p) r)))        ; SAT
(test-dp '(and (or p q r) (or (not p) (not q)) (or (not r) p)))  ; SAT
(test-dp '(or (and p q) (and (not p) r)))       ; SAT
(test-dp '(iff (and p q) (or r s)))             ; SAT

;; With non-variable atoms
(test-dp '(or (foo a) (bar b)))                 ; SAT
(test-dp '(and (foo x) (not (foo x))))          ; UNSAT
(test-dp '(implies (f a b) (g c)))              ; SAT

;; Nested formulas
(test-dp '(and (or p (not q)) (or q (not r)) (or r (not p))))  ; SAT
(test-dp '(xor p q))                            ; SAT
(test-dp '(if p q r))                           ; SAT

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

(defun dpll (f) ...)
