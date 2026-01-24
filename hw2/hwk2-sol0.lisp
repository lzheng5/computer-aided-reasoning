;; hwk2.lisp is the homework submission

(in-package "ACL2S")

;(modeling-admit-all)

;; debugging
;(acl2s-defaults :set testing-enabled t)
;(acl2s-defaults :set testing-enabled nil)
;(set-gag-mode t)
;(set-gag-mode nil)

(defdata uoper (enum (list '- '/)))

(defdata boper (enum (list '+ '- '* '/ '^)))

(defdata
  (saexpr (or rational  ; or is the same as oneof
              var
              usaexpr   ; unary sael expression
              bsaexpr)) ; binary sael expression
  (usaexpr (list uoper saexpr))
  (bsaexpr (list saexpr boper saexpr)))

(defdata assignment (alistof var rational))

(definec lookup (v :var a :assignment) :rational
  (match a
    (() 1)
    (((u . r) . tl)
     (if (== u v)
         r
         (lookup v tl)))))

(defdata er 'error)

(defconst *er* (nth-er-builtin 0))

(defdata rat-err (or rational er))

(definec non-negative-integerp (r :all) :boolean
  (and (integerp r)
       (not (< r 0))))

(defthm rat-err-non-er-is-rational
  (implies (and (rat-errp x)
                (not (erp x)))
           (rationalp x))
  :rule-classes (:rewrite :forward-chaining))

;; Apply a unary operator to a value
(definec apply-uoper (op :uoper v :rational) :rat-err
  (match op
    ('- (- v))
    ('/ (if (== v 0) *er* (/ v)))))

;; Apply a binary operator to two values
(definec apply-boper (op :boper v0 :rational v1 :rational) :rat-err
  (match op
    ('+ (+ v0 v1))
    ('- (- v0 v1))
    ('* (* v0 v1))
    ('/ (if (== v1 0) *er* (/ v0 v1)))
    ('^ (if (== v0 0)
            *er*
            (if (non-negative-integerp v1)
                (expt v0 v1)
                *er*)))))

(definec saeval (e :saexpr a :assignment) :rat-err
  (match e
    (:rational e)
    (:var (lookup e a))
    (:usaexpr
     ((op e0) (match (saeval e0 a)
                (:er *er*)
                (v0 (apply-uoper op v0)))))
    (:bsaexpr
     ((e0 op e1) (match (saeval e0 a)
                   (:er *er*)
                   (v0 (match (saeval e1 a)
                         (:er *er*)
                         (v1 (apply-boper op v0 v1)))))))))

(property (a :assignment)
  (== (saeval 'x a) (saeval 'x a)))

(property (x :var a :assignment)
  (== (saeval x a) (saeval x a)))

(property double-negation (x :saexpr a :assignment)
  (== (saeval '(- (- x)) a)
      (saeval 'x a)))

(property (a :assignment)
    (== (saeval '(- x) a)
     (saeval '(- (- (- x))) a)))

(property (a :assignment)
    (== (saeval '(- (- (- x))) a)
     (saeval '(- x) a))
  ;; [TODO] ??
  ;; :hints (("Goal" :use (double-negation)))
  )

(property (x y :var a :assignment)
    (== (saeval `(,x + (- ,y)) a)
     (saeval `(,x - ,y) a)))

(property (x y z :saexpr a :assignment)
    (== (saeval `(,x * (,y + ,z)) a)
        (saeval `((,x * ,y) + (,x * ,z)) a)))

(property recip (x y :saexpr a :assignment)
    (=> (not (== (saeval y a) 0))
     (== (saeval `(1 / (,x / ,y)) a)
         (saeval `(,y / ,x) a))))

(property zero-exponent-err (x :saexpr a :assignment)
    (== (saeval `(0 ^ ,x) a) *er*))

(property non-zero-divide-cancel (x :rational y :saexpr a :assignment)
  (let ((v (saeval y a)))
      (=> (and (not (== v 0))
               (not (erp v)))
          (== (saeval `((,x * ,y) / ,y) a)
              x))))

;; [TODO] how to speed up?
(property (x y :saexpr a :assignment)
  (let ((v (saeval y a)))
    (=> (and (not (== v 0))
             (not (erp v)))
        (== (saeval `(,x ^ ((2 * ,y) / ,y)) a)
            (saeval `(,x ^ 2) a))))
  :hints (("Goal" :use (non-zero-divide-cancel))))

(defdata baoper (enum (list '+ '- '* '/ 'expt)))

(defdata
  (aaexpr (or rational  ; or is the same as oneof
              var
              uaaexpr   ; unary aael expression
              baaexpr)) ; binary aael expression
  (uaaexpr (list uoper aaexpr))
  (baaexpr (list aaexpr baoper aaexpr)))

(definec sael->aa (e :saexpr) :aaexpr
  (match e
    (:usaexpr
     (('- e0) `(- ,(sael->aa e0)))
     (('/ e0) `(/ ,(sael->aa e0))))
    (:bsaexpr
     ((e0 '+ e1) `(,(sael->aa e0) + ,(sael->aa e1)))
     ((e0 '- e1) `(,(sael->aa e0) - ,(sael->aa e1)))
     ((e0 '* e1) `(,(sael->aa e0) * ,(sael->aa e1)))
     ((e0 '/ e1) `(,(sael->aa e0) / ,(sael->aa e1)))
     ((e0 '^ e1) `(,(sael->aa e0) expt ,(sael->aa e1))))
    (& e)))

(definec aa->sael (e :aaexpr) :saexpr
  (match e
    (:uaaexpr
     (('- e0) `(- ,(aa->sael e0)))
     (('/ e0) `(/ ,(aa->sael e0))))
    (:baaexpr
     ((e0 '+ e1) `(,(aa->sael e0) + ,(aa->sael e1)))
     ((e0 '- e1) `(,(aa->sael e0) - ,(aa->sael e1)))
     ((e0 '* e1) `(,(aa->sael e0) * ,(aa->sael e1)))
     ((e0 '/ e1) `(,(aa->sael e0) / ,(aa->sael e1)))
     ((e0 'expt e1) `(,(aa->sael e0) ^ ,(aa->sael e1))))
    (& e)))

(property sael-aa-id (e :aaexpr)
    (== (sael->aa (aa->sael e)) e))

(property aa-sael-id (e :saexpr)
    (== (aa->sael (sael->aa e)) e))

;; Apply a unary operator to a value 
(definec aapply-uoper (op :uoper v :rational) :rational
  (match op
    ('- (- v))
    ('/ (if (== v 0) 0 (/ v)))))

;; Apply a binary AA operator to two values
(definec aapply-baoper (op :baoper v0 :rational v1 :rational) :rational
  (match op
    ('+ (+ v0 v1))
    ('- (- v0 v1))
    ('* (* v0 v1))
    ('/ (if (== v1 0) 0 (/ v0 v1)))
    ('expt (if (== v0 0)
               0
               (if (non-negative-integerp v1)
                   (expt v0 v1)
                   1)))))

(set-guard-checking nil)
(definec aaeval (e :aaexpr a :assignment) :rational
   (match e
     (:rational e)
     (:var (lookup e a))
     (:uaaexpr
      ((op e0) (aapply-uoper op (aaeval e0 a))))
     (:baaexpr
      ((e0 op e1) (aapply-baoper op (aaeval e0 a) (aaeval e1 a))))))

(property (e :saexpr a :assignment)
    (let ((v (saeval e a)))
      (=> (not (erp v))
          (== (aaeval (sael->aa e) a) v))))

(property (e :aaexpr a :assignment)
    (let* ((s (aa->sael e))
           (v (saeval s a)))
      (=> (not (erp v))
          (== (aaeval e a) v))))
