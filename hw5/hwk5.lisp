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

;; TODO: fix
(let ((f '(not (foo (and)))))
  (assert-equal (p-simplify-flatten f) '(not (foo t))))

(let ((f '(not (foo (and p)))))
  (assert-equal (p-simplify-flatten f) '(not (foo p))))

(let ((f '(and p q (and r s) (or u v))))
  (assert-equal (p-simplify-flatten f) '(and p q r s (or u v))))

(assertf #'p-simplify-flatten '(not (not p)) '(not (not p)))
(assertf #'p-simplify-flatten '(not (iff (iff) (and) (or) q)) '(not (iff t t nil q)))

;; TODO: iff/xor associative so (not (iff a b c ...)) -> (xor a (iff b c ...))
;; TODO: last + butlast in one shot?
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
            (_ ; (not (iff a b ... c)) -> (xor (iff a b ...) c)
             (let ((butlast (butlast bs))
                   (last-elem (car (last bs))))
               `(xor (iff ,@butlast) ,last-elem))))))
       ((list* 'xor bs)
        (let ((bs (mapcar #'p-simplify-not bs)))
          (match bs
            (nil t)  ; (not (xor)) -> t
            ((list a) `(not ,a))  ; (not (xor a)) -> (not a)
            ((list a b) `(iff ,a ,b))  ; (not (xor a b)) -> (iff a b)
            (_ ; (not (xor a b ... c)) -> (iff (xor a b ...) c)
             (let ((butlast (butlast bs))
                   (last-elem (car (last bs))))
               `(iff (xor ,@butlast) ,last-elem))))))
       ((list* op bs) `(not (,op ,@(mapcar #'p-simplify-not bs))))
       (_ `(not ,a))))
    ((list* op as) `(,op ,@(mapcar #'p-simplify-not as)))
    (_ f)))

(assertf #'p-simplify-not '(not (not p)) 'p)
(assertf #'p-simplify-not '(not (iff t nil q)) '(xor (iff t nil) q))

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
                (nvars (mapcar #'(lambda (lit)
                                   (match lit
                                     ((list 'not v) v)
                                     (_ lit)))
                               nlits))
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

;; TODO: handle top-level iff
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
        (_
         (let ((top-var (transform-subf f)))
            (push top-var clauses)
           `(and ,@(reverse clauses))))))))

(defun tseitin (f)
  (let+ ((simplified (p-simplify f))
         ((&values skeleton amap) (p-skeleton simplified))
         (unchained (tseitin-unchain skeleton))
         (cnf (tseitin-transform unchained))
         (simplified-cnf (p-simplify cnf))) ;; p-simplify preserves CNF
    (values simplified-cnf amap)))

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
  (counter 0))                                 ; next available variable number

(defun var-manager-get-num (vm sym)
  "Get or create numeric variable for symbolic variable"
  (or (gethash sym (var-manager-sym->num vm))
      (let ((num (var-manager-counter vm)))
        (setf (gethash sym (var-manager-sym->num vm)) num)
        (setf (gethash num (var-manager-num->sym vm)) sym)
        (setf (var-manager-counter vm) (1+ num))
        num)))

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

(defun make-clause (lits)
  "Create a clause from a list of literals, lits"
  (let ((clause (make-hash-set)))
    (dolist (lit lits clause)
      (hash-set-add clause lit))))

(defun clause-has-lit? (cl lit)
  "Check if literal is in clause"
  (hash-set-contains? cl lit))

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

(defun clause-map (fn cl)
  "Apply function fn to each literal in clause (for side effects only)"
  (hash-set-map fn cl))

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

(defun assignment->alist (asgn vm vars amap)
  "Convert numeric assignment hash table to symbolic alist using var-manager.
   asgn contains assigned variables in the original formula, tseitin-generated variables, and skeleton variables.
   The output includes assignments for all the original variables and atoms.
   Variables/atoms not in asgn are assigned t arbitrarily."
  (let ((result nil))
    ;; First, process all variables in asgn
    (maphash #'(lambda (num-var val)
                 (let* ((sym-var (var-manager-get-sym vm num-var))
                        ;; Check if this generated var represents an atom
                        (orig-atom (and amap (car (rassoc sym-var amap :test #'equal))))
                        ;; Use original atom if found, otherwise use the variable
                        (key (or orig-atom sym-var)))
                   (when (or (null vars)
                             (in key vars)
                             orig-atom)  ;; Include atoms even if not in vars
                     (push (cons key val) result))))
             asgn)

    ;; Add missing variables from vars (assign t arbitrarily)
    (when vars
      (dolist (var vars)
        (unless (assoc var result :test #'equal)
          (pprint (format nil "assignment->alist assigned var ~A to t" var))
          (push (cons var t) result))))

    ;; Add missing atoms from amap (assign t arbitrarily)
    (when amap
      (dolist (pair amap)
        (let ((atom (car pair)))
          (unless (assoc atom result :test #'equal)
            (pprint (format nil "assignment->alist assigned atom ~A to t" atom))
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
             (mapcar #'(lambda (lit)
                         (let ((n (var-manager-sym-lit->num-lit vm lit)))
                           (pprint (format nil "variable mapping ~A to ~A" lit n))
                           n))
                     sym-lits)))
    (match f
      ((type boolean) (if f nil (list (make-clause nil))))  ; t -> empty, nil -> empty clause
      ((type symbol) (list (make-clause (convert-lits (list f)))))
      ((list 'not _) (list (make-clause (convert-lits (list f)))))
      ((list* 'or args) (list (make-clause (convert-lits args))))
      ((list* 'and args) (mapcar #'(lambda (cl) (make-clause (convert-lits (unpack cl)))) args))
      (_ (error "Not in CNF: ~A" f)))))

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
        (dolist (v pure-pos)
          (assignment-set asgn v t))
        (dolist (v pure-neg)
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
                     (pprint (format nil "dp-unit assigned ~A to be ~A" var val))
                     (unit-loop cls))))))
    (unit-loop (mapcar #'clause-copy cls))))

(defun dp-decide (cls)
  "Pick variable with minimum resolution blowup: m*n - m - n"
  (let ((var-counts (make-hash-table :test #'eql))) ; var -> (pos-count . neg-count)
    ;; Collect variable occurrences
    (dolist (cl cls)
      (clause-map #'(lambda (lit)
                      (let* ((var (lit-var lit))
                             (pos? (lit-sign lit))
                             (counts (gethash var var-counts)))
                        (if counts
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
  (let ((cls (dp-unit cls asgn)))
    (cond ((null cls) (values 'sat resolve-map))
          ((some #'clause-empty? cls) (values 'unsat resolve-map))
          (t
           (let ((cls (dp-pure cls asgn)))
             (cond ((null cls) (values 'sat resolve-map))
                   ((some #'clause-empty? cls) (values 'unsat resolve-map))
                   (t
                    (let* ((var (dp-decide cls)))
                      (let+ (((&values new-cls var-cls) (dp-resolve cls var)))
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
                                           (let ((var (lit-var lit))
                                                 (sign (lit-sign lit)))
                                             (unless (and (gethash var asgn)
                                                          (not (eq (gethash var asgn) sign)))
                                               (hash-set-add new-cl lit))))
                                       cl)
                           new-cl))
                     ;; Remove satisfied clauses (where any literal is true)
                     (remove-if #'(lambda (cl)
                                    (clause-any? #'(lambda (lit)
                                                     (let ((var (lit-var lit))
                                                           (sign (lit-sign lit)))
                                                       (and (gethash var asgn)
                                                            (eq (gethash var asgn) sign))))
                                                 cl))
                                cls)))))
    (dolist (entry resolve-map)
      (let ((var (car entry))
            (var-cls (cdr entry)))
        (let ((cls (simplify-clauses var-cls)))
          (cond ((null cls) (assignment-set asgn var t))  ;; If all clauses are satisfied, assign arbitrarily
                ((every #'clause-unit? cls)
                 ;; All remaining clauses must be unit clauses with the same literal
                 (let* ((first-unit (clause-unit-lit (first cls)))
                        (expected-sign (lit-sign first-unit)))
                   (assert (= (lit-var first-unit) var) () 
                           "Expected unit clause to contain variable ~A, but got ~A" var (clause->string (first cls)))
                   (assert (every #'(lambda (cl)
                                      (let ((lit (clause-unit-lit cl)))
                                        (and (= (lit-var lit) var)
                                             (eq (lit-sign lit) expected-sign))))
                                  cls)
                           () "Inconsistent unit clauses during reconstruction for var ~A: ~A" 
                           var (mapcar #'clause->string cls))
                   (assignment-set asgn var expected-sign)))
                (t (error "Unexpected non-unit clauses during reconstruction for var ~A: ~A" 
                          var (mapcar #'clause->string cls))))))))

(defun dp (f)
  "Main DP function: takes a formula f, converts to CNF, and applies DP algorithm.
   Returns 'sat or 'unsat with assignment alist."
  (let* ((vm (make-var-manager)))
    (let+ (((&values cnf amap) (tseitin f))
           (cls (cnf->clauses cnf vm)) ;; mutates vm
           (asgn (make-assignment))
           ((&values result resolve-map) (dp-sat cls asgn nil)) ;; mutates asgn
           (result-asgn (when (eq result 'sat)
                          (dp-reconstruct cls asgn resolve-map) ;; mutates asgn
                          (assignment->alist asgn vm (pvars f) amap))))
      (values result result-asgn))))

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

(dp '(xor p q))

(tseitin (ripplecarry0
          #'(lambda (i) (genvar 'x i))
          #'(lambda (i) (genvar 'y i))
          #'(lambda (i) (genvar 'c i))
          #'(lambda (i) (genvar 'z i))
          1))

(test-dp (ripplecarry0
          #'(lambda (i) (genvar 'x i))
          #'(lambda (i) (genvar 'y i))
          #'(lambda (i) (genvar 'c i))
          #'(lambda (i) (genvar 'z i))
          1))

;; Tests generated with Claude
;; Basic SAT tests
(test-dp 'p)                                    ; single var - SAT
(test-dp '(or p q))                             ; simple disjunction - SAT
(test-dp '(and p q))                            ; simple conjunction - SAT
(test-dp '(implies p q))                        ; implication - SAT
(test-dp '(iff p q))                            ; biconditional - SAT

;; Basic UNSAT tests
(test-dp '(and p (not p)) 'unsat)              ; contradiction - UNSAT
(test-dp '(and (or p q) (not p) (not q)) 'unsat)  ; UNSAT
(test-dp '(and p q (or (not p) (not q)) (or p (not q)) (or (not p) q)) 'unsat)  ; UNSAT

;; More complex SAT formulas
(test-dp '(and (or p q) (or (not p) r)))        ; SAT
(test-dp '(and (or p q r) (or (not p) (not q)) (or (not r) p)))  ; SAT
(test-dp '(or (and p q) (and (not p) r)))       ; SAT
(test-dp '(iff (and p q) (or r s)))             ; SAT

;; With non-variable atoms
(test-dp '(or (foo a) (bar b)))                 ; SAT
(test-dp '(and (foo x) (not (foo x))) 'unsat)   ; UNSAT
(test-dp '(implies (f a b) (g c)))              ; SAT

;; TODO: fix shannon?
(dp '(or a (foo a) (bar b)))

;; Nested formulas
(test-dp '(and (or p (not q)) (or q (not r)) (or r (not p))))  ; SAT
(test-dp '(xor p q))                            ; SAT
(test-dp '(if p q r))                           ; SAT

;; Adder circuit example
(defun halfsum (x y) `(xor ,x ,y))
(defun halfcarry (x y) `(and ,x ,y))
(defun carry (x y z) `(or (and ,x ,y) (and (or ,x ,y) ,z)))
(defun sum (x y z) (halfsum (halfsum x y) z))
(defun fa (x y z s c) `(and (iff ,s ,(sum x y z)) (iff ,c ,(carry x y z))))

;; TODO: use genvar for tseitin
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

;; Adder tests generated by Claude
;; Example 1: Single bit full adder
(test-dp (fa 'x0 'y0 'cin 's0 'cout))  ; SAT - unconstrained full adder

;; Example 2: 2-bit adder with constraint (checking 1+1=2 with carry-in=0)
(test-dp `(and ,(ripplecarry0
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
(test-dp `(and ,(ripplecarry0
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
(test-dp (ripplecarry0
          #'(lambda (i) (genvar 'x i))
          #'(lambda (i) (genvar 'y i))
          #'(lambda (i) (genvar 'c i))
          #'(lambda (i) (genvar 'z i))
          4))

;; UNSAT Examples
;; Example 5: 2-bit adder with impossible constraint (1+1=3, no overflow)
(test-dp `(and ,(ripplecarry0
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
(test-dp `(and ,(ripplecarry0
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
;; (Actually 2+3=5, so with carry c2=1 and result r=00, we'd get 4, which is wrong)
(test-dp `(and ,(ripplecarry0
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

;; Ramsey number example generated by Claude
;; Note this is an opposite formulation from the book.
;; SAT when n < R(s,t) - we CAN avoid monochromatic cliques
;; UNSAT when n ≥ R(s,t) - we CANNOT avoid them
(defun ramsey (s t n)
  "Generate a formula that is satisfiable iff there exists a red-blue coloring of the edges of K_n with no red K_s and no blue K_t."
  (let ((edges nil))
    ;; Generate variables for each edge
    (dotimes (i n)
      (dotimes (j i)
        (push (genvar 'e (format nil "_~A_~A" i j)) edges)))
    ;; No red K_s: for every set of s vertices, at least one edge must be blue
    (let ((no-red-s nil))
      (dolist (subset (combinations n s))
        (let ((clause nil))
          (dolist (pair (combinations subset 2))
            (let* ((i (first pair))
                   (j (second pair))
                   (edge-var (genvar 'e (format nil "_~A_~A" i j))))
              ;; edge-var = true means red, so we want at least one to be false
              (push `(not ,edge-var) clause)))
          (push `(or ,@clause) no-red-s))))
    ;; No blue K_t: for every set of t vertices, at least one edge must be red
    (let ((no-blue-t nil))
      (dolist (subset (combinations n t))
        (let ((clause nil))
          (dolist (pair (combinations subset 2))
            (let* ((i (first pair))
                   (j (second pair))
                   (edge-var (genvar 'e (format nil "_~A_~A" i j))))
              ;; edge-var = true means red, so we want at least one to be true
              (push edge-var clause)))
          (push `(or ,@clause) no-blue-t))))
    ;; Combine all constraints
    `(and ,@no-red-s ,@no-blue-t)))

;; Ramsey number tests
;; R(3,3) = 6 means any 2-coloring of K_6 must contain a monochromatic K_3
(test-dp (ramsey 3 3 5))      ; n < R(3,3), can avoid monochromatic triangles - SAT
(test-dp (ramsey 3 3 6) 'unsat) ; n >= R(3,3), cannot avoid monochromatic triangles - UNSAT
(test-dp (ramsey 4 4 17)) ; n < R(4,4), can avoid monochromatic K_4 - SAT
(test-dp (ramsey 4 4 18) 'unsat) ; n >= R(4,4), cannot avoid monochromatic K_4 - UNSAT

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
