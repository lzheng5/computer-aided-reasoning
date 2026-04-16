#|

 Copyright © 2026 by Pete Manolios
 CS 4820 Fall 2026

 Homework 7.
 Due: 4/18 (Midnight)

 For this assignment, work in groups of 1-3. Send me and the grader
 exactly one solution per team and make sure to follow the submission
 instructions on the course Web page. In particular, make sure that
 the subject of your email submission is "CS 4820 HWK 7".

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

 Here are some examples you can try.

 acl2s-compute is the form you use when you are using ACL2s to compute
 something, e.g., running a function on some input.

 (acl2s-compute '(+ 1 2))

 acl2s-query is the form you use when you are querying ACL2s, e.g., a
 property without a name. If the property has a name, then that is not
 a query, but an event and you have to use acl2s-event.

 (acl2s-query 'acl2s::(property (p q :all)
                        (iff (=> p q)
                             (v (! p) q))))

 acl2s-arity is a function that determines if f is a function defined
 in ACL2s and if so, its arity (number of arguments). If f is not a
 function, then the arity is nil. Otherwise, the arity is a natural
 number. Note that f can't be a macro.

 (acl2s-arity 'acl2s::app)     ; is nil since app is a macro
 (acl2s-arity 'acl2s::bin-app) ; is 2

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

(import 'acl2s::(acl2s-compute acl2s-query))
(import 'acl2s-interface-extras::(acl2s-arity))


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
    (or      :arity - :identity nil :idem t   :sink t  )
    (not     :arity 1 :identity -   :idem nil :sink -  )
    (implies :arity 2 :identity -   :idem nil :sink -  )
    (iff     :arity - :identity t   :idem nil :sink -  )
    (if      :arity 3 :identity -   :idem nil :sink -  )))

#|

 mapcar is like map. See the common lisp manual.
 In general if you have questions about lisp, ask on Piazza.

|#

(defparameter *p-funs* (mapcar #'car *p-ops*))
(defparameter *fo-quantifiers* '(forall exists))
(defparameter *booleans* '(t nil))
(defparameter *fo-keywords*
  (append *p-funs* *booleans* *fo-quantifiers*))

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

(defun get-alist (k l)
  (cdr (assoc k l :test #'equal)))

(defun get-key (k l)
  (cadr (member k l :test #'equal)))

(defun remove-dups (l)
  (remove-duplicates l :test #'equal))

(defmacro == (x y) `(equal ,x ,y))
(defmacro != (x y) `(not (equal ,x ,y)))

(defun booleanp (x)
  (in x *booleans*))

(defun no-dupsp (l)
  (or (endp l)
      (and (not (in (car l) (cdr l)))
           (no-dupsp (cdr l)))))

(defun pfun-argsp (pop args)
  (and (p-funp pop)
       (let ((arity (get-key :arity (get-alist pop *p-ops*))))
         (and (or (== arity '-)
                  (== (len args) arity))
              (every #'p-formulap args)))))


#|

 Next we have some utilities for converting propositional formulas to
 ACL2s formulas.

|#

(defun to-acl2s (f)
  (match f
    ((type symbol) (intern (symbol-name f) "ACL2S"))
    ((list 'iff) t)
    ((list 'iff p) (to-acl2s p))
    ((list* 'iff args)
     (acl2s::xxxjoin 'acl2s::iff
                     (mapcar #'to-acl2s args)))
    ((cons x xs)
     (mapcar #'to-acl2s f))
    (_ f)))

#|

 A FO term is either a

 constant symbol: a symbol whose name starts with "C" and is
 optionally followed by a natural number with no leading 0's, e.g., c0,
 c1, c101, c, etc are constant symbols, but c00, c0101, c01, etc are
 not. Notice that (gentemp "C") will create a new constant. Notice
 that symbol names  are case insensitive, so C1 is the same as c1.

 quoted constant: anything of the form (quote object) for any object

 constant object: a rational, boolean, string, character or keyword

 variable: a symbol whose name starts with "X", "Y", "Z", "W", "U" or
 "V" and is optionally followed by a natural number with no leading
 0's (see constant symbol). Notice that (gentemp "X") etc will create
 a new variable.

 function application: (f t1 ... tn), where f is a
 non-constant/non-variable/non-boolean/non-keyword symbol. The arity
 of f is n and every occurrence of (f ...)  in a term or formula has
 to have arity n. Also, if f is a defined function in ACL2s, its arity
 has to match what ACL2s expects. We allow functions of 0-arity.

|#

(defun char-nat-symbolp (s chars)
  (and (symbolp s)
       (let ((name (symbol-name s)))
         (and (<= 1 (len name))
              (in (char name 0) chars)
              (or (== 1 (len name))
                  (let ((i (parse-integer name :start 1 :junk-allowed t)))
                    (and (integerp i)
                         (<= 0 i)
                         (string= (format nil "~a~a" (char name 0) i)
                                  name))))))))

(defun constant-symbolp (s)
  (char-nat-symbolp s '(#\C)))

(defun variable-symbolp (s)
  (char-nat-symbolp s '(#\X #\Y #\Z #\W #\U #\V)))

(defun quotep (c)
  (and (consp c)
       (== (car c) 'quote)))

(defun constant-objectp (c)
  (typep c '(or boolean rational simple-string standard-char keyword)))

#|

Examples

(constant-objectp #\a)
(constant-objectp 0)
(constant-objectp 1/221)
(constant-objectp "hi there")
(constant-objectp t)
(constant-objectp nil)
(constant-objectp :hi)
(constant-objectp 'a)

(quotep '1)  ; recall that '1 is evaluated first
(quotep ''1) ; but this works
(quotep '(1 2 3))  ; similar to above
(quotep ''(1 2 3)) ; similar to above
(quotep (list 'quote (list 1 2 3))) ; verbose version of previous line

|#

(defun function-symbolp (f)
  (and (symbolp f)
       (not (in f *fo-keywords*))
       (not (keywordp f))
       (not (constant-symbolp f))
       (not (variable-symbolp f))))

#|

(function-symbolp 'c)
(function-symbolp 'c0)
(function-symbolp 'c00)
(function-symbolp 'append)
(function-symbolp '+)

|#

(defmacro mv-and (a b &optional (fsig 'fsig) (rsig 'rsig))
  `(if ,a ,b (values nil ,fsig ,rsig)))

(defmacro mv-or (a b &optional (fsig 'fsig) (rsig 'rsig))
  `(if ,a (values t ,fsig ,rsig) ,b))

(defun fo-termp (term &optional (fsig nil) (rsig nil))
  (match term
    ((satisfies constant-symbolp) (values t fsig rsig))
    ((satisfies variable-symbolp) (values t fsig rsig))
    ((satisfies quotep) (values t fsig rsig))
    ((satisfies constant-objectp) (values t fsig rsig))
    ((list* f args)
     (mv-and
      (and (function-symbolp f) (not (get-alist f rsig)))
      (let* ((fsig-arity (get-alist f fsig))
             (acl2s-arity
              (or fsig-arity
                  (acl2s-arity (to-acl2s f))))
             (arity (or acl2s-arity (len args)))
             (fsig (if fsig-arity fsig (acons f arity fsig))))
        (mv-and (== arity (len args))
                (fo-termsp args fsig rsig)))))
    (_ (values nil fsig rsig))))

(defun fo-termsp (terms fsig rsig)
  (mv-or (endp terms)
         (let+ (((&values res fsig rsig)
                 (fo-termp (car terms) fsig rsig)))
           (mv-and res
                   (fo-termsp (cdr terms) fsig rsig)))))

#|

Examples

(fo-termp '(f d 2))
(fo-termp '(f c 2))
(fo-termp '(f c0 2))
(fo-termp '(f c00 2))
(fo-termp '(f '1 '2))
(fo-termp '(f (f '1 '2)
              (f v1 c1 '2)))


(fo-termp '(binary-append '1 '2))
(fo-termp '(binary-append '1 '2 '3))
(fo-termp '(binary-+ '1 '2))
(fo-termp '(+ '1 '2))
(fo-termp '(- '1 '2))

|#

#|

 A FO atomic formula is either an

 atomic equality: (= t1 t2), where t1, t2 are FO terms.

 atomic relation: (P t1 ... tn), where P is a
 non-constant/non-variable symbol. The arity of P is n and every
 occurrence of (P ...) has to have arity n. Also, if P is a defined
 function in ACL2s, its arity has to match what ACL2s expects.  We do
 not check that if P is a defined function then it has to return a
 Boolean. Make sure that you do not use such examples.

|#

(defun relation-symbolp (f)
  (function-symbolp f))

#|

Examples

(relation-symbolp '<)
(relation-symbolp '<=)
(relation-symbolp 'binary-+)

|#

(defun fo-atomic-formulap (f &optional (fsig nil) (rsig nil))
  (match f
    ((list '= t1 t2)
     (fo-termsp (list t1 t2) fsig rsig))
    ((list* r args)
     (mv-and
      (and (relation-symbolp r) (not (get-alist r fsig)))
      (let* ((rsig-arity (get-alist r rsig))
             (acl2s-arity
              (or rsig-arity
                  (acl2s::acl2s-arity (to-acl2s r))))
             (arity (or acl2s-arity (len args)))
             (rsig (if rsig-arity rsig (acons r arity rsig))))
        (mv-and (== arity (len args))
                (fo-termsp args fsig rsig)))))
    (_ (values nil fsig rsig))))

#|

 Here is the definition of a propositional formula. We allow
 Booleans.

|#

(defun pfun-fo-argsp (pop args fsig rsig)
  (mv-and (p-funp pop)
          (let ((arity (get-key :arity (get-alist pop *p-ops*))))
            (mv-and (or (== arity '-)
                        (== (len args) arity))
                    (fo-formulasp args fsig rsig)))))

(defun p-fo-formulap (f fsig rsig)
  (match f
    ((type boolean) (values t fsig rsig))
    ((list* pop args)
     (if (p-funp pop)
         (pfun-fo-argsp pop args fsig rsig)
       (values nil fsig rsig)))
    (_ (values nil fsig rsig))))

#|

 Here is the definition of a quantified formula.

 The quantified variables can be a variable
 or a non-empty list of variables with no duplicates.
 Examples include

 (exists w (P w y z x))
 (exists (w) (P w y z x))
 (forall (x y z) (exists w (P w y z x)))

 But this does not work

 (exists c (P w y z x))
 (forall () (exists w (P w y z x)))
 (forall (x y z x) (exists w (P w y z x)))

|#

(defun quant-fo-formulap (f fsig rsig)
  (match f
    ((list q vars body)
     (mv-and (and (in q *fo-quantifiers*)
                  (or (variable-symbolp vars)
                      (and (consp vars)
                           (no-dupsp vars)
                           (every #'variable-symbolp vars))))
             (fo-formulap body fsig rsig)))
    (_ (values nil fsig rsig))))

(defun mv-seq-first-fun (l)
  (if (endp (cdr l))
      (car l)
    (let ((res (gensym))
          (f (gensym))
          (r (gensym)))
      `(multiple-value-bind (,res ,f ,r)
           ,(car l)
         (if ,res
             (values t ,f ,r)
           ,(mv-seq-first-fun (cdr l)))))))

(defmacro mv-seq-first (&rest rst)
  (mv-seq-first-fun rst))

(defun fo-formulap (f &optional (fsig nil) (rsig nil))
  (mv-seq-first
   (fo-atomic-formulap f fsig rsig)
   (p-fo-formulap f fsig rsig)
   (quant-fo-formulap f fsig rsig)
   (values nil fsig rsig)))

(defun fo-formulasp (fs fsig rsig)
  (mv-or (endp fs)
         (let+ (((&values res fsig rsig)
                 (fo-formulap (car fs) fsig rsig)))
           (mv-and res
                   (fo-formulasp (cdr fs) fsig rsig)))))

#|

FOL Syntax

t := <constant symbol>
   | <quoted constant>
   | <constant object>
   | <variable>
   | (<f-symbol> t1 ... tn)
a := (<R-symbol> t1 ... tn)
   | (= t1 t2)
p := <bool>
   | (<p-op> f1 ... fn)
f := a | p
   | (<fo-quant> xs f)
l := a | (not a)

|#

#|

 We can use fo-formulasp to find the function and relation
 symbols in a formula as follows.

|#

(defun fo-f-symbols (f)
  (let+ (((&values res fsig rsig)
          (fo-formulap f)))
    (mapcar #'car fsig)))

(defun fo-r-symbols (f)
  (let+ (((&values res fsig rsig)
          (fo-formulap f)))
    (mapcar #'car rsig)))

#|

Examples

(fo-formulap
 '(forall (x y z) (exists w (P w y z x))))

(fo-formulap
 '(forall (x y z x) (exists w (P w y z x))))

(quant-fo-formulap
 '(forall (x y z) (exists y (P w y z x))) nil nil)

(fo-formulap
 '(exists w (P w y z x)))

(fo-atomic-formulap
 '(exists w (P w y z x)) nil nil)

(quant-fo-formulap
 '(exists w (P w y z x)) nil nil)

(fo-formulap
 '(P w y z x))

(fo-formulap
 '(and (forall (x y z) (or (not (= (q z) (r z))) nil (p '1 x y)))
       (exists w (implies (forall x1 (iff (= (p1 x1 w) c2) (q c1) (r c2)))
                          (p '2 y w)))))

(fo-formulap
 '(forall (x y z) (or (not (= (q z) (r z))) nil (p '1 x y))))

(fo-formulap
 '(exists w (implies (forall x1 (iff (= (p1 x1 w) c2) (q c1) (r c2)))
                          (p '2 y w))))

(fo-formulap
 '(exists w (implies (forall x1 (iff (p1 x1 w) (q c1) (r c2)))
                     (p '2 y w))))

(fo-formulap
 '(and (forall (x y z) (or (not (= (q2 z) (r2 z))) nil (p '1 x y)))
       (exists w (implies (forall x1 (iff (= (p1 x1 w) c2) (q c1) (r c2)))
                          (p '2 y w)))))

(fo-formulap
 '(forall x1 (iff (p1 x1 w) (q c1) (r c2))))

(fo-formulap
 '(iff (p1 x1 w) (q c1) (r c2)))

(fo-atomic-formulap
 '(p1 x1 w))

(variable-symbolp 'c1)
(fo-termp 'x1)
(fo-termp 'w1)
(fo-termp '(x1 w) nil nil)
(fo-termsp '(x1 w) nil nil)

|#

#|

 Where appropriate, for the problems below, modify your solutions from
 homework 4. For example, you already implemented most of the
 simplifications in Question 1 in homework 4.

|#


#|

 Question 1. (25 pts)

 Define function fo-simplify that given a first-order (FO) formula
 returns an equivalent FO formula with the following properties.

 A. The returned formula is either a constant or does not include any
 constants. For example:

 (and (p x) t (q t y) (q y z)) should be simplified to
 (and (p x) (q t y) (q y z))

 (and (p x) t (q t b) nil) should be simplified to nil

 B. Expressions are flattened, e.g.:

 (and (p c) (= c '1) (and (r) (s) (or (r1) (r2)))) is not flat, but this is
 (and (p c) (= c '1) (r) (s) (or (r1) (r2)))

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
 form remain (where f is a formula)

 (not (not f))

 E. Simplify formulas so that no subexpressions of the following form
 remain

 (op ... p ... q ...)

 where p, q are equal literals or  p = (not q) or q = (not p).

 For example

 (or (f) (f1) (p a b) (not (p a b)) (= w z)) should be simplified to

 t

 F. Simplify formulas so there are no vacuous quantified formulas.
 For example,

 (forall (x w) (P y z))  should be simplified to

 (P y z)

 and

 (forall (x w) (P x y z))  should be simplified to

 (forall (x) (P x y z))

 G. Simplify formulas by using ACL2s to evaluate, when possible, terms
 of the form (f ...) where f is an ACL2s function all of whose
 arguments are either constant-objects or quoted objects.

 For example,

 (P (binary-+ 4 2) 3)

 should be simplified to

 (P 6 3)

 Hint: use acl2s-compute and to-acl2s. For example, consider

 (acl2s-compute (to-acl2s '(binary-+ 4 2)))

 On the other hand,

 (P (binary-+ 'a 2) 3)

 does not get simplified because

 (acl2s-compute (to-acl2s '(binary-+ 'a 2)))

 indicates an error (contract/guard violation). See the definition of
 acl2s-compute to see how to determine if an error occurred.

 H. Test your definitions using at least 10 interesting formulas.  Use
 the acl2s code, if you find it useful.  Include deeply nested
 formulas, all of the Boolean operators, quantified formulas, etc.

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
 increase the size of a formula.

|#

;;; ============================================================
;;; Debug and Stats
;;; ============================================================

;; Mode: 'debug | 'stats | nil (default)
;; Note if we changed this, we should reload the file to recompile the definitions to include debugging/stats information
(defconstant +debug-mode+ 'debug)

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
;;; Hash Set API - Simple set abstraction over hash tables
;;; ============================================================

(defun make-hash-set (&optional (eq #'eql))
  "Create an empty hash set"
  (make-hash-table :test eq))

(defun hash-set-add (set elem)
  "Add element to hash set (mutates set)"
  (setf (gethash elem set) t))

(defun hash-set-contains? (set elem)
  "Check if element is in hash set"
  (gethash elem set))

(defun hash-set-size (set)
  "Return number of elements in hash set"
  (hash-table-count set))

(defun hash-set-empty? (set)
  "Check if hash set is empty"
  (= (hash-set-size set) 0))

(defun hash-set-map (fn set)
  "Apply function fn to each element in set"
  (maphash #'(lambda (k v) (declare (ignore v)) (funcall fn k)) set))

(defun hash-set->list (set)
  "Convert hash set to list"
  (let ((result nil))
    (hash-set-map #'(lambda (elem) (push elem result)) set)
    result))

(defun list->hash-set (lst)
  "Build a fresh hash set containing every element of LST."
  (let ((s (make-hash-set)))
    (dolist (v lst s)
      (hash-set-add s v))))

(defun hash-set-copy-except (set elem)
  "Create a new hash set with all elements except elem"
  (let ((new-set (make-hash-set)))
    (hash-set-map #'(lambda (e)
                      (unless (equal e elem)
                        (hash-set-add new-set e)))
                  set)
    new-set))

(defun hash-set-union! (set1 set2)
  "Add all elements of set2 to set1 (mutates set1)"
  (hash-set-map #'(lambda (elem) (hash-set-add set1 elem)) set2))

(defun hash-set-remove! (set1 set2)
  "Remove all elements of set2 from set1 (mutates set1)"
  (hash-set-map #'(lambda (elem)
                    (when (hash-set-contains? set2 elem)
                      (setf (gethash elem set1) nil)))
                set1))

;;; ============================================================
;;; General Utilities
;;; ============================================================

(defun assertf (f in out)
  (== (funcall f in) out))

(defun filter (pred lst)
  "Return a new list containing only elements of LST satisfying PRED."
  (loop for x in lst when (funcall pred x) collect x))

(defun partition (pred list)
  "Partition list into (values trues falses) based on pred"
  (loop for x in list
        if (funcall pred x) collect x into trues
        else collect x into falses
        finally (return (values trues falses))))

(defun subsets (lst)
  "Return a list of all subsets of LST."
  (if (null lst)
      (list nil)
      (let ((rest (subsets (cdr lst))))
        (append rest
                (mapcar (lambda (s) (cons (car lst) s)) rest)))))

(defun negate (f)
  "Get the negation of f"
  (match f
    ((list 'not a) a)
    (_ `(not ,f))))

(defun has-opposite (f args)
  (in (negate f) args))

(defun fo-quantifierp (q)
  (in q *fo-quantifiers*))

(defun subst-term (tm var-map)
  "Substitute variables in tm according to var-map, which is an alist mapping variables to terms"
  (match tm
    ((satisfies constant-symbolp) tm)
    ((satisfies variable-symbolp) (or (get-alist tm var-map) tm))
    ((satisfies quotep) tm)
    ((satisfies constant-objectp) tm)
    ((list* F args)
     `(,F ,@(mapcar #'(lambda (a) (subst-term a var-map)) args)))
    (_ tm)))

(defun subst-terms (tms var-map)
  "Substitute variables in each term in tms according to var-map, which is an alist mapping variables to terms"
  (mapcar #'(lambda (tm) (subst-term tm var-map)) tms))

(defun term-vars (term &optional (vars (make-hash-set)))
  "Return a hash set of the variables in term"
  (labels ((walk (tm)
             (match tm
               ((satisfies variable-symbolp) (hash-set-add vars tm))
               ((list* F args) (mapc #'walk args))
               (_ nil))))
    (walk term)
    vars))

(defun terms-vars (terms &optional (vars (make-hash-set)))
  "Return a hash set of the variables in the list of terms"
  (mapc #'(lambda (tm) (term-vars tm vars)) terms)
  vars)

(defun free-vars (f)
  "Return a set (list) of the free variables in f"
  (dassert (fo-formulap f) "Input formula is not well-formed")
  (match f  
    ;; < quant-fo-formulap >
    ((list (guard q (fo-quantifierp q)) vars body)
     (let ((vars (if (variable-symbolp vars) (list vars) vars)))
       (set-difference (free-vars body) vars)))
       
    ;; < p-fo-formulap >
    ((type boolean) nil)
    ((list* (guard op (p-funp op)) args)
     (apply #'union (mapcar #'free-vars args)))

    ;; < fo-atomic-formulap >
    ((list* R ts)
     (hash-set->list (terms-vars ts)))))

;;; ============================================================
;;; Variables Utilities
;;; ============================================================

(defun genvarn (prefix n)
  "Generate a variable symbol of the form PREFIX_N"
  (intern (format nil "~A~D" prefix n)))

;; Prefix counter map: a hash map of prefix symbol -> next counter value.
(defparameter *var-gen-cnt-map* (make-hash-table :test #'eq))
;; Exclusion set: a hash set of variable symbols that genvar should skip to avoid capturing existing variables.
(defparameter *var-gen-exclusion-set* (make-hash-set))

(defun genvar (prefix)
  "Generate a new variable symbol of the form PREFIX_N,
   where PREFIX is a symbol and N is a per-prefix natural number counter.
   Skips any name that appears in *var-gen-exclusion-set* to avoid
   capturing existing variables."
  (loop
    (let* ((n   (gethash prefix *var-gen-cnt-map* 0))
           (var (genvarn prefix n)))
      (setf (gethash prefix *var-gen-cnt-map*) (1+ n))
      (unless (hash-set-contains? *var-gen-exclusion-set* var)
        (return var)))))

(defun genvars (prefix n)
  (loop for i from 0 below n
        collect (genvar prefix)))

(defmacro with-free-vars (fvars &body body)
  "Execute BODY with a fresh per-prefix counter map and *var-gen-exclusion-set*
   pre-populated from fvars (a list of variable symbols, e.g. from free-vars).
   Prevents genvar from generating names that clash with the given variables."
  `(let ((*var-gen-cnt-map*       (make-hash-table :test #'eq))
         (*var-gen-exclusion-set* (list->hash-set ,fvars)))
     ,@body))

(defun assertv (f in out)
  (dassert (fo-formulap in) "Input formula is not well-formed")
  (with-free-vars (free-vars in)
    (== (funcall f in) out)))

;;; ============================================================
;;; Preprocessing
;;; ============================================================

(defun fo-cannonicalize-quant-vars (f)
  "Turn the quantified variables into a standard list form."
  (match f
    ;; < quant-fo-formulap >
    ((list (guard q (fo-quantifierp q)) vars body)
     (let ((vars (if (variable-symbolp vars) (list vars) vars)))
      `(,q ,vars ,(fo-cannonicalize-quant-vars body))))

    ;; < p-fo-formulap >
    ((type boolean) f)
    ((list* (guard op (p-funp op)) args)
     `(,op ,@(mapcar #'fo-cannonicalize-quant-vars args)))

    ;; < fo-atomic-formulap >
    (_ f)))

(defun fo-simplify-implies (f)
  (match f
    ;; < quant-fo-formulap >
    ((list (guard q (fo-quantifierp q)) vars body)
     `(,q ,vars ,(fo-simplify-implies body)))

    ;; < p-fo-formulap >
    ((type boolean) f)
    ((list 'implies p q)
     (let ((sp (fo-simplify-implies p))
           (sq (fo-simplify-implies q)))
       `(or (not ,sp) ,sq)))

    ((list* (guard op (p-funp op)) args)
     `(,op ,@(mapcar #'fo-simplify-implies args)))

    ;; < fo-atomic-formulap >
    (_ f)))

;; Tests for fo-simplify-implies
(assertf #'fo-simplify-implies '(implies p q) '(or (not p) q))
(assertf #'fo-simplify-implies '(implies (implies a b) c) '(or (not (or (not a) b)) c))
(assertf #'fo-simplify-implies '(forall (x) (implies (P x) (Q x))) '(forall (x) (or (not (P x)) (Q x))))
(assertf #'fo-simplify-implies '(exists (x) (implies (R x) (S x))) '(exists (x) (or (not (R x)) (S x))))
(assertf #'fo-simplify-implies '(and (implies a b) (implies c d)) '(and (or (not a) b) (or (not c) d)))

(defun fo-preprocess (f)
  "Apply preprocessing to f.

   Pre: (fo-formulap f)"
  (fo-simplify-implies
    (fo-cannonicalize-quant-vars f)))

;;; ============================================================
;;; Simplification
;;; ============================================================

(defun fo-simplify-const (f)
  (match f
    ;; < quant-fo-formulap >
    ((list (guard q (fo-quantifierp q)) vars body)
     `(,q ,vars ,(fo-simplify-const body)))

    ;; < p-fo-formulap >
    ((type boolean) f)

    ((list 'not a)
     (let ((a (fo-simplify-const a)))
       (match a
         ((type boolean) (not a))
         (_ `(not ,a)))))

    ((list 'if a b c)
     (let ((a (fo-simplify-const a))
           (b (fo-simplify-const b))
           (c (fo-simplify-const c)))
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

    ((list* (guard op (p-funp op)) as)
     (let ((as (mapcar #'fo-simplify-const as)))
       (match op
         ((or 'iff)
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

    ;; < fo-atomic-formulap >
    (_ f)))

(assertf #'fo-simplify-const '(and x y t) '(and x y))
(assertf #'fo-simplify-const '(or x y t) 't)
(assertf #'fo-simplify-const '(and p t (foo t nil) q) '(and p (foo t nil) q))
(assertf #'fo-simplify-const '(iff t nil p q) '(iff nil p q))
(assertf #'fo-simplify-const '(iff nil p) '(not p))
(assertf #'fo-simplify-const '(not (not p)) '(not (not p)))
(assertf #'fo-simplify-const '(not (iff (iff) (or) q)) '(not (iff (or) q)))

(assertf #'fo-simplify-const '(and (p x) t (q t y) (q y z)) '(and (p x) (q t y) (q y z)))
(assertf #'fo-simplify-const '(and (p x) t (q t y) nil) 'nil)

(assertf #'fo-simplify-const '(forall (x y) (and (p x) t (q t y) (q y z))) '(forall (x y) (and (p x) (q t y) (q y z))))
(assertf #'fo-simplify-const '(exists (x y) (and (p x) t (q t y) nil)) '(exists (x y) nil))

(defun fo-simplify-flatten (f)
  (match f
    ;; < quant-fo-formulap >
    ((list (guard q (fo-quantifierp q)) vars body)
     `(,q ,vars ,(fo-simplify-flatten body)))

    ;; < p-fo-formulap >
    ((type boolean) f)
    ((list* (guard op (p-funp op)) as)
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
                              (mapcar #'fo-simplify-flatten as)
                              :from-end t
                              :initial-value nil))))))
             (t `(,op ,@(mapcar #'fo-simplify-flatten as))))))

    ;; < fo-atomic-formulap >
    (_ f)))

(assertf #'fo-simplify-flatten '(not (foo x)) '(not (foo x)))
(assertf #'fo-simplify-flatten '(and p q (and r s) (or u v)) '(and p q r s (or u v)))
(assertf #'fo-simplify-flatten '(not (not p)) '(not (not p)))
(assertf #'fo-simplify-flatten '(not (iff (iff) (and) (or) q)) '(not (iff t t nil q)))

(assertf #'fo-simplify-flatten '(and (p c) (= c '1) (and (r) (s) (or (r1) (r2)))) '(and (p c) (= c '1) (r) (s) (or (r1) (r2))))
(assertf #'fo-simplify-flatten '(and) 't)
(assertf #'fo-simplify-flatten '(and p q (and r s)) '(and p q r s))
;; Quantified formula tests
(assertf #'fo-simplify-flatten '(forall (x) (and (P x) (and (Q x) (R x)))) '(forall (x) (and (P x) (Q x) (R x))))
(assertf #'fo-simplify-flatten '(exists (x) (or (P x))) '(exists (x) (P x)))
(assertf #'fo-simplify-flatten '(forall (x) (or)) '(forall (x) nil))
(assertf #'fo-simplify-flatten '(forall (x) (iff (P x))) '(forall (x) (P x)))

(defun fo-simplify-not (f)
  (match f
    ;; < quant-fo-formulap >
    ((list (guard q (fo-quantifierp q)) vars body)
     `(,q ,vars ,(fo-simplify-not body)))

    ;; < p-fo-formulap >
    ((type boolean) f)

    ((list 'not f)
     (match f
       ((list 'not b) (fo-simplify-not b))
       (_ `(not ,(fo-simplify-not f)))))

    ((list* (guard op (p-funp op)) fs)
     `(,op ,@(mapcar #'fo-simplify-not fs)))

    ;; < fo-atomic-formulap >
    (_ f)))

(assertf #'fo-simplify-not '(not (not p)) 'p)
(assertf #'fo-simplify-not '(not (not (not p))) '(not p))
(assertf #'fo-simplify-not '(and (not (not p)) q) '(and p q))
(assertf #'fo-simplify-not '(forall (x) (not (not (P x)))) '(forall (x) (P x)))
(assertf #'fo-simplify-not '(exists (x) (or (not (not p)) (not (not q)))) '(exists (x) (or p q)))

(defun fo-simplify-dup (f)
  "Simplify duplicated and opposite subformulas"
  (match f
    ;; < quant-fo-formulap >
    ((list (guard q (fo-quantifierp q)) vars body)
     `(,q ,vars ,(fo-simplify-dup body)))

    ;; < p-fo-formulap >
    ((type boolean) f)
    ((list* (guard op (p-funp op)) as)
     (let ((as (mapcar #'fo-simplify-dup as)))
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

    ;; < fo-atomic-formulap >
    (_ f)))

(assertf #'fo-simplify-dup '(iff nil p q) '(iff nil p q))
(assertf #'fo-simplify-dup '(iff p q p) 'q)
(assertf #'fo-simplify-dup '(iff p q (not p)) '(iff q nil))
;; Quantified formula tests
(assertf #'fo-simplify-dup '(forall (x) (and (P x) (P x))) '(forall (x) (and (P x))))
(assertf #'fo-simplify-dup '(exists (x) (or (P x) (not (P x)))) '(exists (x) t))
(assertf #'fo-simplify-dup '(forall (x) (and (P x) (not (P x)))) '(forall (x) nil))
(assertf #'fo-simplify-dup '(forall (x y) (iff (R x y) (R x y))) '(forall (x y) t))
;; Deeply nested tests
(assertf #'fo-simplify-dup '(and p q p r q) '(and p q r))
(assertf #'fo-simplify-dup '(or (P x) (Q y) (P x)) '(or (P x) (Q y)))

(defun fo-simplify-trivially-quantified (f)
  (labels ((walk (f)
             (match f
               ;; < quant-fo-formulap >
               ((list (guard q (fo-quantifierp q)) vars body)
                (let+ (((&values new-body fvars) (walk body)))
                  (let* ((used (remove-if-not (lambda (v) (hash-set-contains? fvars v)) vars))
                         (new-fvars (let ((s (make-hash-set)))
                                      (hash-set-map (lambda (v)
                                                      (unless (member v vars :test #'equal)
                                                        (hash-set-add s v)))
                                                    fvars)
                                      s)))
                    (if (null used)
                        (values new-body new-fvars)
                        (values `(,q ,used ,new-body) new-fvars)))))

               ;; < p-fo-formulap >
               ((type boolean) (values f (make-hash-set)))
               ((list* (guard op (p-funp op)) fs)
                (let ((all-fvars (make-hash-set))
                      (new-fs (loop for sub in fs
                                  collect (let+ (((&values nf fv) (walk sub)))
                                            (hash-set-union! all-fvars fv)
                                            nf))))
                  (values `(,op ,@new-fs) all-fvars)))

               ;; < fo-atomic-formulap >
               (_ (values f (if (consp f) (terms-vars (cdr f)) (make-hash-set)))))))
    (let+ (((&values new-f fvars) (walk f)))
      new-f)))

;; Vacuous quantifier removal tests
(assertf #'fo-simplify-trivially-quantified '(forall (x w) (P y z)) '(P y z))
(assertf #'fo-simplify-trivially-quantified '(forall (x w) (P x y z)) '(forall (x) (P x y z)))
(assertf #'fo-simplify-trivially-quantified '(exists (x) (and (P y) (Q z))) '(and (P y) (Q z)))
(assertf #'fo-simplify-trivially-quantified '(forall (x y z) (exists (w) (R x w))) '(forall (x) (exists (w) (R x w))))
(assertf #'fo-simplify-trivially-quantified '(exists (x) (forall (y) (P x y))) '(exists (x) (forall (y) (P x y))))
(assertf #'fo-simplify-trivially-quantified '(forall (x) t) 't)

(defun term-partial-eval (term)
  "Apply partial evaluation to term if possible."
  (match term
    ((satisfies constant-symbolp) term)
    ((satisfies variable-symbolp) term)
    ((satisfies quotep) term)
    ((satisfies constant-objectp) term)
    ((list* F args)
     (let ((new-args (mapcar #'term-partial-eval args)))
       (if (every #'(lambda (a) (or (constant-objectp a) (quotep a))) new-args)
           (let ((res (acl2s-compute (to-acl2s (cons F new-args)))))
             (if (null (car res))
                 (cdr res) ;; success
                 `(,F ,@new-args))) ;; error
           `(,F ,@new-args))))))

(defun fo-simplify-partial-eval (f)
  "Apply partial evaluation to terms in f if possible."
  (match f
    ;; < quant-fo-formulap >
    ((list (guard q (fo-quantifierp q)) vars body)
     `(,q ,vars ,(fo-simplify-partial-eval body)))

    ;; < p-fo-formulap >
    ((type boolean) f)
     ((list* (guard op (p-funp op)) fs)
      `(,op ,@(mapcar #'fo-simplify-partial-eval fs)))

    ;; < fo-atomic-formulap >
    ((list* R args)
     `(,R ,@(mapcar #'term-partial-eval args)))))

;; Partial evaluation tests
(assertf #'fo-simplify-partial-eval '(P (binary-+ 4 2) 3) '(P 6 3))
(assertf #'fo-simplify-partial-eval '(forall (x) (= x (binary-+ 1 2))) '(forall (x) (= x 3)))
(assertf #'fo-simplify-partial-eval '(and (P (binary-* 2 3)) (Q y)) '(and (P 6) (Q y)))

(defun fo-simplify-fixpoint (f)
  (let ((new-f (fo-simplify-partial-eval
                (fo-simplify-trivially-quantified
                 (fo-simplify-dup
                  (fo-simplify-const
                   (fo-simplify-not
                    (fo-simplify-flatten f))))))))
    (if (equal new-f f)
        f
        (fo-simplify-fixpoint new-f))))

(defun fo-simplify (f)
  "Apply simplification to f.

   Pre: (fo-formulap f)"

  (dassert (fo-formulap f) "Input must be a FO formula")

  (fo-simplify-fixpoint
   (fo-preprocess f)))

;; Preprocessing
(assertf #'fo-simplify '(implies a b) '(or (not a) b))
(assertf #'fo-simplify '(forall x (P y z)) '(forall (x) (P y z)))

;; Simplification
;; Implies with constants simplifies
(assertf #'fo-simplify '(implies t nil) 'nil)
;; Vacuous quantifier dropped
(assertf #'fo-simplify '(forall (x w) (P y z)) '(P y z))
;; Partially vacuous quantifier trimmed
(assertf #'fo-simplify '(forall (x w) (P x y z)) '(forall (x) (P x y z)))
;; Double negation eliminated
(assertf #'fo-simplify '(not (not (P x))) '(P x))
;; Sink: nil in and
(assertf #'fo-simplify '(and (P x) nil (Q y)) 'nil)
;; Sink: t in or
(assertf #'fo-simplify '(or (P x) t (Q y)) 't)
;; Flatten nested and
(assertf #'fo-simplify '(and (P x) (and (Q y) (R z))) '(and (P x) (Q y) (R z)))
;; Duplicate elimination in and
(assertf #'fo-simplify '(and (P x) (Q y) (P x)) '(and (P x) (Q y)))
;; Complementary pair in or => t
(assertf #'fo-simplify '(or (P x) (not (P x))) 't)
;; Deep: quantifier + constants + implies
(assertf #'fo-simplify '(forall (x y) (implies t (and (P x) nil))) 'nil)

#|

 Question 2. (10 pts)

 Define nnf, a function that given a FO formula, something that
 satisfies fo-formulap, puts it into negation normal form (NNF).

 The resulting formula cannot contain any of the following
 propositional connectives: implies, iff, if.

 Test nnf using at least 10 interesting formulas. Make sure you
 support quantification.

|#

(defun nnf (f)
  "Convert f to NNF. Eliminates implies, iff, if.

   Pre: (fo-formulap f)"

  (dassert (fo-formulap f) "Input must be a FO formula")

  (labels ((walk (f neg)
             (match f
               ;; < quant-fo-formulap >
               ;; quantifiers: (not (forall x P)) = (exists x (not P))
               ;;              (not (exists x P)) = (forall x (not P))
               ((list (guard q (fo-quantifierp q)) vars body)
                (let ((new-q (if neg (if (eq q 'forall) 'exists 'forall) q)))
                  `(,new-q ,vars ,(walk body neg))))

               ;; < p-fo-formulap >
               ((type boolean) (if neg (not f) f))

               ;; not: flip negation flag
               ((list 'not a) (walk a (not neg)))

               ;; implies: p => q = (or (not p) q)
               ((list 'implies p q)
                (if neg
                    ;; not (p => q) = (and p (not q))
                    `(and ,(walk p nil) ,(walk q t))
                    `(or ,(walk p t) ,(walk q nil))))

               ;; if: (if a b c) = (or (and a b) (and (not a) c))
               ;;     (not (if a b c)) = (and (or (not a) (not b)) (or a (not c)))
               ((list 'if a b c)
                (if neg
                    `(and (or ,(walk a t) ,(walk b t))
                          (or ,(walk a nil) ,(walk c t)))
                    `(or (and ,(walk a nil) ,(walk b nil))
                         (and ,(walk a t) ,(walk c nil)))))

               ;; iff: ACL2s defines n-ary iff as right-fold, so we reduce to binary
               ;; chains before applying the binary iff NNF rule.
               ;; (iff) = t (identity element)
               ((list 'iff) (if neg nil t))
               ;; (iff p) = p
               ((list 'iff p) (walk p neg))
               ;; binary (iff p q):
               ;;   positive: (or (and p q) (and (not p) (not q)))
               ;;   negated:  (and (or (not p) (not q)) (or p q))
               ((list* 'iff args)
                (let ((binary (reduce (lambda (a acc) `(iff ,a ,acc))
                                      args :from-end t)))
                  (match binary
                    ((list 'iff p q)
                     (if neg
                         `(and (or ,(walk p t) ,(walk q t))
                               (or ,(walk p nil) ,(walk q nil)))
                         `(or (and ,(walk p nil) ,(walk q nil))
                              (and ,(walk p t) ,(walk q t)))))
                    (_ (walk binary neg)))))

               ;; and/or: de morgan
               ((list* 'and args)
                (if neg
                    `(or ,@(mapcar (lambda (a) (walk a t)) args))
                    `(and ,@(mapcar (lambda (a) (walk a nil)) args))))

               ((list* 'or args)
                (if neg
                    `(and ,@(mapcar (lambda (a) (walk a t)) args))
                    `(or ,@(mapcar (lambda (a) (walk a nil)) args))))

               ;; < fo-atomic-formulap >
               (_ (if neg `(not ,f) f)))))
    (walk f nil)))

;; Test cases generated by Claude
;; Basic: atomic pass-through
(assertf #'nnf '(P x y) '(P x y))
;; Simple not: pushed in
(assertf #'nnf '(not (P x y)) '(not (P x y)))
;; Double negation eliminated
(assertf #'nnf '(not (not (P x))) '(P x))
;; implies eliminated
(assertf #'nnf '(implies p q) '(or (not p) q))
;; not-implies
(assertf #'nnf '(not (implies p q)) '(and p (not q)))
;; De Morgan: not-and
(assertf #'nnf '(not (and p q r)) '(or (not p) (not q) (not r)))
;; De Morgan: not-or
(assertf #'nnf '(not (or p q)) '(and (not p) (not q)))
;; iff elimination (binary)
;; (iff p q) -> (or (and p q) (and (not p) (not q)))
(assertf #'nnf '(iff p q)
         '(or (and p q) (and (not p) (not q))))
;; n-ary iff is right-folded before NNF:
;; (iff p q r) = (iff p (iff q r))
;;   (iff q r) -> (or (and q r) (and (not q) (not r))) [call it B]
;;   (iff p B) -> (or (and p B) (and (not p) (not B)))
;;              = (or (and p (or (and q r) (and (not q) (not r))))
;;                   (and (not p) (and (or (not q) (not r)) (or q r))))
(assertf #'nnf '(iff p q r)
         '(or (and p (or (and q r) (and (not q) (not r))))
              (and (not p) (and (or (not q) (not r)) (or q r)))))
;; not-iff: (not (iff p q)) = (and (or (not p) q) (or p (not q)))
;;    i.e. p XOR q
(assertf #'nnf '(not (iff p q))
         '(and (or (not p) (not q)) (or p q)))
;; forall: quantifier preserved
(assertf #'nnf '(forall (x) (implies (P x) (Q x)))
         '(forall (x) (or (not (P x)) (Q x))))
;; not-forall flips to exists
(assertf #'nnf '(not (forall (x) (P x)))
         '(exists (x) (not (P x))))
;; not-exists flips to forall
(assertf #'nnf '(not (exists (x) (P x)))
         '(forall (x) (not (P x))))
;; if eliminated
(assertf #'nnf '(if a b c)
         '(or (and a b) (and (not a) c)))
;; nested iff — exponential blowup:
;;     (iff (iff a b) (iff c d))
;;     Right-fold: it's already binary — p=(iff a b), q=(iff c d)
;;     positive: (or (and P Q) (and (not P) (not Q))), substituting nnf of p and q:
;;       P_pos = (or (and a b) (and (not a) (not b)))
;;       Q_pos = (or (and c d) (and (not c) (not d)))
;;       P_neg = (and (or (not a) (not b)) (or a b))
;;       Q_neg = (and (or (not c) (not d)) (or c d))
;;     result: (or (and P_pos Q_pos) (and P_neg Q_neg))
;; Each sub-iff is duplicated once => 2x blowup at each nesting level
(assertf #'nnf '(iff (iff a b) (iff c d))
         '(or (and (or (and a b) (and (not a) (not b)))
                   (or (and c d) (and (not c) (not d))))
              (and (and (or (not a) (not b)) (or a b))
                   (and (or (not c) (not d)) (or c d)))))
;; (iff) = t
(assertf #'nnf '(iff) t)
;; (not (iff)) = nil
(assertf #'nnf '(not (iff)) nil)
;; (iff p) = p
(assertf #'nnf '(iff p) 'p)
;; (not (iff p)) = (not p)
(assertf #'nnf '(not (iff p)) '(not p))

#|

 Question 3. (25 pts)

 Define simp-skolem-pnf-cnf, a function that given a FO formula,
 simplifies it using fo-simplify, then puts it into negation normal
 form, applies skolemization, then puts the formula in prenex normal
 form and finally transforms the matrix into an equivalent CNF
 formula.

 To be clear: The formula returned should be equi-satisfiable with the
 input formula, should contain no existential quantifiers, and if it
 has quantifiers it should be of the form

 (forall (...) matrix)

 where matrix is quantifier-free and in CNF.

 The fewer quantified variables, the better.
 The fewer Skolem functions, the better.
 The smaller the arity of Skolem functions, the better.
 Having said that, correctness should be your primary consideration.

 Test your functions using at least 10 interesting formulas.

 CNF Matrix Form Syntax 

 f := m | (forall (v1 ... vn) m)
 m := <bool> | l 
    | (and c1 ... cn)
 c := l | (or l1 ... ln)

|#

(defun fo-rename (f)
  "Rename all the bound variables in f.
   The temporary variables generated have prefix 'X.

   Pre: fo-cannonicalize-quant-vars has already been applied to f.
   Post: all bound variables in f are unique and free variables are kept intact."

  (labels ((rename-vars (vars var-map)
             (let ((new-vars (mapcar #'(lambda (var)
                                         (let ((new-var (genvar 'X)))

                                               (setf var-map (acons var new-var var-map))
                                               new-var))
                                     vars)))
               (values new-vars var-map)))
           (rename (f var-map)
             (match f
               ;; < quant-fo-formulap >
               ((list (guard q (fo-quantifierp q)) vars body)
                (let+ (((&values new-vars new-var-map) (rename-vars vars var-map)))
                  `(,q ,new-vars ,(rename body new-var-map))))

               ;; < p-fo-formulap >
               ((type boolean) f)
               ((list* (guard op (p-funp op)) fs)
                `(,op ,@(mapcar #'(lambda (f) (rename f var-map)) fs)))

               ;; < fo-atomic-formulap >
               ((list* R ts)
                `(,R ,@(mapcar #'(lambda (tm) (subst-term tm var-map)) ts)))))
           (rename f nil))))

(defun skolemize (f)
  "Skolemize f.
   New function symbols generated have prefix SK.

   Pre: f is in NNF."
  (labels
      ((walk (f forall-vars exists-map)
         "forall-vars: universally quantified variables currently in scope (outermost first).
          exists-map: alist mapping existential variable -> its full Skolem term."
         (match f
           ;; < quant-fo-formulap >
           ((list (guard q (fo-quantifierp q)) vars body)
            (cond
              ;; universal: extend scope and recurse
              ((eq q 'forall)
               `(forall ,vars ,(walk body (append vars forall-vars) exists-map)))
              ;; existential: build Skolem terms capturing current forall-vars,
              ((eq q 'exists)
               (let ((new-exist-map
                       (reduce (lambda (m v)
                                 (acons v `(,(genvar 'SK) ,@forall-vars) m))
                               vars
                               :initial-value exists-map)))
                 (walk body forall-vars new-exist-map)))))

           ;; < p-fo-formulap >
           ((type boolean) f)
           ((list* (guard op (p-funp op)) fs)
            `(,op ,@(mapcar (lambda (x) (walk x forall-vars exists-map)) fs)))

           ;; < fo-atomic-formulap >
           ((list* R args)
            `(,R ,@(mapcar (lambda (a) (subst-term a exists-map)) args))))))
    (walk f nil nil)))

(defun pnf (f)
  "Convert f to prenex normal form.
   The variable ordering of the resulting prenex quantifier is the traversal order.

   Pre: f has been simplified and skolemized (so all bound variables are unique)."
  (labels ((walk (f)
             "Return the unquantified formula and all forall-bound variables."
             (match f
               ;; < quant-fo-formulap >
               ((list (guard q (fo-quantifierp q)) vars body)
                (let+ (((&values new-body bound-vars) (walk body)))
                  (values new-body (append vars bound-vars))))

               ;; < p-fo-formulap >
               ((type boolean) (values f nil))
               ((list* (guard op (p-funp op)) fs)
                (let (all-new-fs all-bound-vars)
                  (dolist (sub-f fs)
                    (let+ (((&values new-body bound-vars) (walk sub-f)))
                      (push new-body all-new-fs)
                      (setf all-bound-vars (append all-bound-vars bound-vars))))
                  (values `(,op ,@(nreverse all-new-fs)) all-bound-vars)))

               ;; < fo-atomic-formulap >
               (_ (values f nil)))))
    (let+ (((&values new-f bound-vars) (walk f)))
       (if (null bound-vars)
           new-f
           ;; TODO: remove remove-dups after fo-rename
           `(forall ,(remove-dups bound-vars) ,new-f)))))

(defun tseitin-op (v op args)
  "Generate CNF clauses: v ↔ (op args...)
   Pre: v is a 0-arity predicate application (TS), op is a propositional operator,
        args are 0-arity predicate applications or boolean constants."
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

    (otherwise
     (error "Unknown operator in Tseitin: ~A" op))))

(defun tseitin-transform (f)
  "Transform unquantified NNF formula f to CNF using Tseitin transformation"
  (let ((clauses nil))
    (labels ((transform-subf (subf)
               "Transform subformula; return a 0-arity predicate (TSn) as its representative.
                TSn starts with T so it is a relational symbol, not a variable symbol. Note (TSn) is valid FO.
                
                Since after simplification and nnf, the subformula can either be a literal, and, or. "
               
               (dassert (not (booleanp subf)) "Subformula should not be a boolean constant due to simplification")
               (match subf
                 ((satisfies literalp) subf)
                 ((list* (guard op (p-funp op)) args)
                  (let* ((arg-vars (mapcar #'transform-subf args))
                         (v `(,(genvar 'TS)))  ; 0-arity predicate application: (TS0), (TS1), ...
                         (new-clauses (tseitin-op v op arg-vars)))
                    (setf clauses (append new-clauses clauses))
                    v))
                  (_ (dassert nil "Unexpected subformula type in Tseitin transform: ~A" subf)))))
      (match f
        ;; < p-fo-formulap >
        ((type boolean) f)

        ;; already a literal 
        ((satisfies literalp) f)

        ;; (and ...) = each conjunct must hold independently
        ((list* 'and args)
         (dolist (arg args)
           (let ((top-var (transform-subf arg)))
             ;; top-var is (TSn) already a valid 0-arity atomic unit clause
             (push top-var clauses)))
         `(and ,@(reverse clauses)))

        ;; any other propositional formula: introduce one top-level Tseitin var
        ((list* (guard op (p-funp op)) args)
         (let ((top-var (transform-subf f)))
           ;; top-var is (TSn) already a valid 0-arity atomic unit clause
           (push top-var clauses)
           `(and ,@(reverse clauses))))

        ;; < fo-atomic-formulap >: already a unit clause
        (_ f)))))

(defun tseitin (f)
  "Convert f to CNF using Tseitin transformation.
   Returns CNF as (and clause1 clause2 ...)
   New Tseitin relational symbols generated have prefix TS.

   Pre: f has been simplified, skolemized, and is in prenex normal form."

  (match f
    ;; < quant-fo-formulap >
    ((list (guard q (fo-quantifierp q)) vars body)
     (dassert (eq q 'forall) "Only universal quantifiers should remain after skolemization and prenex normal form conversion")
     `(forall ,vars ,(tseitin-transform body)))

    (_ (tseitin-transform f))))

;; TODO: after nnf, fo-rename, minimize-scope, merge-existentials, skolemize, merge-universals, pnf, tseitin 

(defun simp-skolem-pnf-cnf (f)
  "Apply simplification, skolemization, prenex normal form conversion, and CNF transformation to f.
   Variables are NOT renamed here; clauses are renamed apart lazily during resolution.

   Pre: (fo-formulap f)"
  (dassert (fo-formulap f) "Input must be a FO formula")

  (tseitin
   (pnf
    (skolemize
     (nnf
      (fo-simplify f))))))

;; Some example problems
(defconstant *mortal* '(and (forall x (implies (man x) (mortal x)))
                            (man c0)
                            (not (mortal c0))))

(defconstant *pet* '(and (forall x (implies (pet x) (exists y (cares y x))))
                         (forall (y z) (implies (and (pet z) (cares y z)) (kind y)))
                         (pet c0)
                         (not (forall w (not (kind w))))))

(defconstant *barb*
  '(not (exists x (forall y (iff (shaves x y) (not (shaves y y)))))))

;; Atomic formula: passthrough, wrapped in (and ...)
(assertv #'simp-skolem-pnf-cnf '(P x) '(P x))

;; Conjunction of atomics: each conjunct pushed as unit clause, no new vars
(assertv #'simp-skolem-pnf-cnf '(and (P x) (Q x)) '(and (P x) (Q x)))

;; Disjunction: Tseitin introduces (TS0), definitional clauses
;; (TS0) <-> (P x) v (Q x):
;;   unit: (TS0)
;;   forward: (or (not (TS0)) (P x) (Q x))
;;   backward: (or (TS0) (not (P x))), (or (TS0) (not (Q x)))
(assertv #'simp-skolem-pnf-cnf '(or (P x) (Q x))
         '(and (TS0)
               (or (not (TS0)) (P x) (Q x))
               (or (TS0) (not (P x)))
               (or (TS0) (not (Q x)))))

;; Negated atomic: already a literal, returned as-is
(assertv #'simp-skolem-pnf-cnf '(not (P x)) '(not (P x)))

;; 0-arity Skolem: (exists (y) (R c0 y)) => y -> (SK0), no quantifier in result
(assertv #'simp-skolem-pnf-cnf '(exists (y) (R c0 y))
         '(R c0 (SK0)))

;; 1-arity Skolem: (forall (x) (exists (y) (R x y))) => y -> (SK0 x)
(assertv #'simp-skolem-pnf-cnf '(forall (x) (exists (y) (R x y)))
         '(forall (x) (R x (SK0 x))))

(defun literalp (l)
  (match l
    ((list 'not a) (let+ (((&values ok) (fo-atomic-formulap a nil nil))) ok))
    (_ (let+ (((&values ok) (fo-atomic-formulap l nil nil))) ok))))

(defun cnf-clausep (c)
  (match c
    ((type boolean) t)
    ((list* 'or lits) (every #'literalp lits))
    (_ (literalp c))))

(defun cnf-matrixp (f)
  (match f
    ((type boolean) t)
    ((list* 'and clauses) (every #'cnf-clausep clauses))
    (_ (cnf-clausep f))))

(defun pnf-cnf-p (f)
  "check that result is (forall (...) cnf-matrix) or cnf-matrix"
  (match f
    ((list 'forall vars body) (cnf-matrixp body))
    (_ (cnf-matrixp f))))

;; Simple propositional implies
(assert (pnf-cnf-p (simp-skolem-pnf-cnf '(implies p q))))
;; Already propositional CNF
(assert (pnf-cnf-p (simp-skolem-pnf-cnf '(and (or p q) (or (not p) r)))))
;; Tautology
(assert (pnf-cnf-p (simp-skolem-pnf-cnf '(or p (not p)))))
;; Contradiction
(assert (pnf-cnf-p (simp-skolem-pnf-cnf '(and p (not p)))))
;; Mortal Socrates
(assert (pnf-cnf-p (simp-skolem-pnf-cnf *mortal*)))
;; Pet example
(assert (pnf-cnf-p (simp-skolem-pnf-cnf *pet*)))
;; iff with quantifiers
(assert (pnf-cnf-p (simp-skolem-pnf-cnf '(forall (x) (iff (P x) (Q x))))))
;; Deeply nested: implies + quantifiers
(assert (pnf-cnf-p (simp-skolem-pnf-cnf
                    '(forall (x) (implies (and (P x) (Q x))
                                          (exists (y) (R x y)))))))

#|

 Question 4. (15 pts)

 Define unify, a function that given an a non-empty list of pairs,
 where every element of the pair is FO-term, returns an mgu (most
 general unifier) if one exists or the symbol 'fail otherwise.

 An assignment is a list of conses, where car is a variable, the cdr
 is a term and the variables (in the cars) are unique.

 Test your functions using at least 10 interesting inputs.

|#

(defun occurs (var term)
  "Returns t if variable var appears anywhere in term."
  (match term
     ((satisfies constant-symbolp) nil)
     ((satisfies variable-symbolp) (eql var term))
     ((satisfies quotep) nil)
     ((satisfies constant-objectp) nil)
     ((list* F args) (some (lambda (a) (occurs var a)) args))
     (_ nil)))

(defun term-unify (sigma l)
  "Given initial substitution sigma and a list of term pairs (conses (s . t)),
   return an MGU extending sigma, or 'fail if no unifier exists."
  (match l
    (nil sigma)
    ((cons pair rest)
     (let ((s (subst-term (car pair) sigma))
           (u (subst-term (cdr pair) sigma)))
       (match (cons s u)
         ;; Already equal after substitution: skip
         ((guard _ (equal s u))
          (term-unify sigma rest))
         ;; s is a variable: bind s -> u
         ((cons (satisfies variable-symbolp) _)
          (if (occurs s u)
              'fail
              (let ((b `((,s . ,u))))
                (term-unify (cons (cons s u)
                                  (mapcar (lambda (e) (cons (car e) (subst-term (cdr e) b)))
                                          sigma))
                            rest))))
         ;; u is a variable: bind u -> s
         ((cons _ (satisfies variable-symbolp))
          (if (occurs u s)
              'fail
              (let ((b `((,u . ,s))))
                (term-unify (cons (cons u s)
                                  (mapcar (lambda (e) (cons (car e) (subst-term (cdr e) b)))
                                          sigma))
                            rest))))
         ;; Both compound with same functor and arity: decompose
         ((cons (list* f1 a1) (list* f2 a2))
          (if (and (eq f1 f2) (= (length a1) (length a2)))
              (term-unify sigma (append (mapcar #'cons a1 a2) rest))
              'fail))
         ;; Clash
         (_ 'fail))))))

(defun unify (l)
  "Given a non-empty list of terms, return an MGU
   alist mapping variables to terms in solved forms, or 'fail if no unifier exists."
  (term-unify nil l))

(defun subst-valid? (l sigma)
  "Returns t if applying sigma to both sides of each pair in l yields equal terms."
  (every (lambda (pair)
           (equal (subst-term (car pair) sigma)
                  (subst-term (cdr pair) sigma)))
         l))

;; Trivial: single variable unified with a constant
(assertf #'unify '((x . c0)) '((x . c0)))
;; Identical constants: empty substitution
(assertf #'unify '((c0 . c0)) nil)
;; Constant clash: fail
(assertf #'unify '((c0 . c1)) 'fail)
;; Variable unified with a function term
(assertf #'unify '((x . (f c0))) '((x . (f c0))))
;; Two variables unified
(assertf #'unify '((x . y)) '((x . y)))
;; Function term decomposed to single variable binding
(assertf #'unify '(((f x) . (f c0))) '((x . c0)))
;; Occurs check: x cannot unify with (f x)
(assertf #'unify '((x . (f x))) 'fail)
;; Different functor heads: fail
(assertf #'unify '(((f x) . (g x))) 'fail)
;; Two-arg decomposition
(assertf #'unify '(((f x y) . (f c0 c1))) '((y . c1) (x . c0)))
;; Chain: x=y, y=c0 -> both x and y bound to c0
(assertf #'unify '((x . y) (y . c0)) '((y . c0) (x . c0)))
;; Cross-pair: two pairs that share a variable are consistent
(assertf #'unify '(((f x) . (f y)) (x . c0)) '((y . c0) (x . c0)))
;; Complex: nested function term
;; (f (g x) y) = (f (g c0) c1) -> x=c0, y=c1
(assert (let ((sigma (unify '(((f (g x) y) . (f (g c0) c1))))))
          (and (not (eq sigma 'fail))
               (subst-valid? '(((f (g x) y) . (f (g c0) c1))) sigma))))
;; Most general: (f x y) = (f y x) -> x=y (no occurs issue)
;; bind x->y: sigma=((x.y)), then (y.x) -> apply sigma: y=y, x->y gives y=y, equal. done
(assertf #'unify '(((f x y) . (f y x))) '((x . y)))
;; Arity mismatch: fail
(assertf #'unify '(((f x) . (f c0 c1))) 'fail)

#|

 Question 5. (25 pts)

 Define fo-no=-val, a function that given a FO formula, without equality,
 checks if it is valid using U-Resolution.

 If it is valid, return 'valid.

 Your code should use positive resolution and must implement
 subsumption and replacement.

 Test your functions using at least 10 interesting inputs
 including the formulas from the following pages of the book: 178
 (p38, p34), 179 (ewd1062), 180 (barb), and 198 (the Los formula).

 Clausal Form Syntax: 
 cls := (cl ...)
 cl := (l ...)

 Note cls includes () and (())
|#

;; ==============================================================
;; Simple Queue APIs
;; ==============================================================

(defun make-queue (&optional (items nil))
  "Create a queue, optionally pre-filled with ITEMS in list order."
  (let ((q (cons nil nil)))
    (dolist (item items q)
      (enqueue item q))))

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

(defun queue->list (queue)
  "Return the contents of QUEUE as a list (non-destructive)."
  (car queue))

(defun queue-remove-if! (pred queue)
  "Remove all elements satisfying PRED from QUEUE (mutates queue in-place)."
  (let ((new-list (remove-if pred (car queue))))
    (setf (car queue) new-list
          (cdr queue) (last new-list))))

(defun queue-update-and-remove-if! (pred new-val queue)
  "Replace the first element in QUEUE satisfying PRED with NEW-VAL,
   and remove all subsequent elements satisfying PRED.
   Returns t if any element was found satisfying PRED, nil otherwise."
  (let ((found nil)
        (new-list nil))
    (dolist (x (car queue))
      (cond ((funcall pred x)
             (unless found
               (push new-val new-list)
               (setf found t)))
            (t
             (push x new-list))))
    (when found
      (let ((reversed (nreverse new-list)))
        (setf (car queue) reversed
              (cdr queue) (last reversed))))
    found))

;; ==============================================================
;; To Clausal Form 
;; ==============================================================

(defun to-clauses-m (m)
  "Convert a CNF matrix m to a list of clauses satisfying the Clausal Form Syntax.

   Pre: m satisfies the CNF Matrix Form Syntax:
        m := <bool> | l | (and c1 ... cn)  
        c := l | (or l1 ... ln)"
  (flet ((clause-of (c)
           (match c
             ((satisfies literalp) (list c))
             ((list* 'or lits) lits))))
    (match m
      ((type boolean) (if m nil (list nil)))
      ((satisfies literalp) (list (list m)))
      ((list* 'and conjuncts) (mapcar #'clause-of conjuncts)))))

(defun to-clauses (f)
  "Convert f (output of simp-skolem-pnf-cnf) to a list of clauses satisfying the Clausal Form Syntax for resolution.
   Each clause is a list of literals.

   Pre: f satisfies the CNF Matrix Form Syntax:
        f := m | (forall (v1 ... vn) m)"
  (match f
    ((list 'forall vars m) (to-clauses-m m))
    (_ (to-clauses-m f))))

;; ==============================================================
;; Resolution, Subsumption, and Replacement
;; ==============================================================

(defun rename-clause (cl)
  "Return a copy of CL with all variables renamed to fresh ones.
   Called before each resolution step to ensure two clauses being resolved
   have disjoint variable sets."
  (let* ((vars (hash-set->list (terms-vars (mapcar (lambda (l)
                                                      (match l
                                                        ((list 'not a) a)
                                                        (_ l)))
                                                    cl))))
         (renaming (mapcar (lambda (v) (cons v (genvar 'X))) vars)))
    (mapcar (lambda (l) (subst-term l renaming)) cl)))

(defun unifiable? (l1 l2)
  "Return t if literals l1 and l2 are unifiable, nil otherwise."
  (not (eq (unify `((,l1 . ,l2))) 'fail)))

(defun unify-seq (lits)
  "Given a list of literals, return an MGU that unifies all of them, or 'fail if no such unifier exists."
  (if (null lits)
      nil
      (let ((eqs nil))
        (dolist (l (cdr lits))
          (push (cons l (car lits)) eqs))
        (unify eqs))))

(defun term-match (theta t1 t2)
  "Match a single pair: return extended theta if t1 matches t2, or 'fail."
  (match t1
    ;; t1 is a variable: look up in theta
    ((satisfies variable-symbolp)
     (let ((binding (assoc t1 theta :test #'equal)))
       (cond
         ;; already bound: check consistency with t2
         (binding (if (equal (cdr binding) t2) theta 'fail))
         ;; not yet bound: extend theta
         (t (acons t1 t2 theta)))))
    ;; t1 is a compound term: decompose if t2 has same functor and arity
    ((list* f1 args1)
     (match t2
       ((list* (guard f2 (eq f1 f2)) args2)
        (if (/= (length args1) (length args2))
            'fail
            (terms-match theta args1 args2)))
       (_ 'fail)))
    ;; t1 is a constant/quoted/constant-object: must literally equal t2
    (_ (if (equal t1 t2) theta 'fail))))

(defun terms-match (theta ts1 ts2)
  "Given substitution theta and two lists of terms ts1 and ts2,
   return an extended theta matching ts1 against ts2 pairwise, or 'fail on failure.
   Matching is one-directional: only variables on the ts1 side may be bound.

   Pre: ts1 and ts2 have the same length."
  (dassert (= (length ts1) (length ts2)) "ts1 and ts2 must have the same length")
  (if (null ts1)
      theta
      (let ((new-theta (term-match theta (car ts1) (car ts2))))
        (if (eq new-theta 'fail) 'fail (terms-match new-theta (cdr ts1) (cdr ts2))))))

(defun clause-subsumes? (cl1 cl2)
  "cl1 subsumes cl2 if there exists some substitution θ such that θ(cl1) ⊆ cl2.
   If this is the case, then cl1 => cl2.
   Return t if cl1 subsumes cl2, nil otherwise.

   Pre: cl1 and cl2 are non-empty clauses (lists of literals)."
  (dassert (not (null cl1)) "cl1 should be non-empty for subsumption check")
  (dassert (not (null cl2)) "cl2 should be non-empty for subsumption check")
  (labels ((try-match (remaining-cl1 theta)
             ;; For each literal in cl1, try to match it to some literal in cl2.
             ;; Backtrack if a choice leads to a dead end.
             (if (null remaining-cl1)
                 t ;; all literals matched — return t (not theta, which may be nil)
                 (let ((l1 (car remaining-cl1)))
                   (dolist (l2 cl2)
                     (let ((new-theta (term-match theta l1 l2)))
                       (unless (eq new-theta 'fail)
                         (let ((result (try-match (cdr remaining-cl1) new-theta)))
                           (when result (return-from try-match result))))))
                   nil))))
    (try-match cl1 nil)))

(defun trivial? (cl)
  "Return t if CL is a tautological clause (contains a complementary pair of literals), nil otherwise."
  (some (lambda (l) (member (negate l) cl :test #'equal)) cl))

(defun replace (cl unusedQ)
  "Replace the first unused clause in unusedQ subsumed by cl (cl ⇒ unused-cl) with cl.
   Remove all other unused clauses in unusedQ subsumed by cl.
   If no such unused-cl exists, enqueue cl into unusedQ.
   This way preserves the relative ordering of clauses in unusedQ.
   
   Pre: cl and all clauses in unusedQ are non-empty (since trivial clauses should never be enqueued)."

  (dassert (not (null cl)) "cl should be non-empty for replacement")
  (unless (queue-update-and-remove-if! ;; better than the book
             (lambda (unused-cl) (clause-subsumes? cl unused-cl))
             cl unusedQ)
    (enqueue cl unusedQ)))

(defun incorporate (used cl unusedQ)
  "If cl is non-trivial and not subsumed by any clause in used or unusedQ, enqueue cl into unusedQ."
  (unless (or (trivial? cl)
              (let ((found nil)) ;; better than the book
                (hash-set-map (lambda (used-cl)
                                (when (clause-subsumes? used-cl cl)
                                  (setf found t)))
                              used)
                found)
              (some (lambda (unused-cl) (clause-subsumes? unused-cl cl)) (queue->list unusedQ)))
    (replace cl unusedQ)))

(defun resolve-clauses (cl1 cl2 used unusedQ)
  "Compute resolvants by considering all pairs of literals (l1, l2) where l1 in cl1, l2 in cl2, and l1 is the negation of l2 
   Push the resolvants derived from resolving cl1 and cl2 into unusedQ.
   Return nil if empty clause is derived, otherwise return the updated unusedQ.
   
   Pre: both cl1 and cl2 are already in used."
   (dassert (hash-set-contains? used cl1) "cl1 should already be in used for presolve")
   (dassert (hash-set-contains? used cl2) "cl2 should already be in used for presolve")

   (let ((new-cl1 (rename-clause cl1))
         (new-cl2 (rename-clause cl2)))
      (dolist (l1 new-cl1)
        (let ((ps2 (filter #'(lambda (l) (unifiable? l1 (negate l))) new-cl2)))
          (if (null ps2) 
              nil 
              (let ((ps1 (filter #'(lambda (l) (and (not (equal l1 l)) (unifiable? l1 l))) new-cl1)))
                ;; try all possible subsets of ps1 and ps2 to resolve with l1 and enqueue the valid resolvants 
                (dolist (pl1 (subsets ps1))
                  (let ((s1 `(,l1 . ,pl1)))
                    (dolist (s2 (subsets ps2))
                      (if (null s2)
                          nil
                          (let ((U (unify-seq (append s1 (mapcar #'negate s2)))))
                            (if (eq U 'fail)
                                nil
                                (let* ((R (union (set-difference new-cl1 s1 :test #'equal)
                                                 (set-difference new-cl2 s2 :test #'equal)
                                                 :test #'equal))
                                       (resolvant (subst-terms R U)))
                                  (if (null resolvant)
                                      (return-from resolve-clauses nil) ;; empty clause derived
                                      (incorporate used resolvant unusedQ))))))))))))))
   unusedQ)

(defun positive-clause? (cl)
  "Returns t if CL is a positive clause (contains no negated literals)."
  (every (lambda (l) (not (and (listp l) (eq (car l) 'not)))) cl))

(defun presolve-clauses (cl1 cl2 used unusedQ)
  "Apply positive resolution to CL1 and CL2 if they contain complementary literals.
   Push the resolvants derived from resolving cl1 and cl2 into unusedQ.
   Return nil if empty clause is derived, otherwise return the updated unusedQ. 
   
   Pre: both cl1 and cl2 are already in used."
  (dassert (hash-set-contains? used cl1) "cl1 should already be in used for presolve")
  (dassert (hash-set-contains? used cl2) "cl2 should already be in used for presolve")

  (if (or (positive-clause? cl1) (positive-clause? cl2))
      (resolve-clauses cl1 cl2 used unusedQ)
      unusedQ))

(defun solve (used unusedQ)
  "Apply positive resolution until the empty clause is derived (return 'valid) or no new clauses can be derived (return nil).

   used: a set of clauses that have already been used for resolution
   unusedQ: a queue of clauses that have not yet been used for resolution"
  (if (queue-empty? unusedQ)
      nil 
      (progn 
        (dbg "used: ~A, unused: ~A" (hash-set-size used) (length (queue->list unusedQ)))
        (let* ((cl (dequeue unusedQ)))
          (hash-set-add used cl) ;; necessary to handle factoring
          (hash-set-map #'(lambda (used-cl)
                            (let ((new-unusedQ (presolve-clauses cl used-cl used unusedQ))) ;; mutates unusedQ
                              (if (null new-unusedQ)
                                  (return-from solve 'valid)
                                  nil)))
                        used)
          (solve used unusedQ)))))

(defun fo-no=-val (f) 
  "Check if f is valid using U-Resolution without equality, 
   where for a FO sequent (Γ ⊢ φ), f = Γ ∧ ¬φ. 

   Returns 'valid if f is valid (always true) or nil if f is unsatisfiable (always false). 
   Loops if f is satisfiable but not valid (sometimes true but sometimes false).

   Pre: f is a FO formula without equality."

  (dassert (fo-formulap f) "Input must be a FO formula")
  (with-free-vars (free-vars f)
   (solve 
    (make-hash-set #'equal)  
    (make-queue (to-clauses (simp-skolem-pnf-cnf f)))))) 

#|

 Question 6. Extra Credit (20 pts)

 Define fo-val, a function that given a FO formula, checks if it is
 valid using U-Resolution.

 If it is valid, return 'valid.

 Your code should use positive resolution and must implement
 subsumption and replacement. This is an extension of question 5,
 where you replace equality with a new relation symbol and add
 the appropriate equivalence and congruence hypotheses.

|#

(defun fo-val (f) ...)
