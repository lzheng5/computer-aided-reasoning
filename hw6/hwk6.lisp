#|

 Copyright © 2026 by Pete Manolios and Andrew Walter
 CS 4820 Spring 2026

 Homework 6
 Due: 3/28 (Midnight)

 For this assignment, work in groups of 1-2. Send me and the grader
 exactly one solution per team and make sure to follow the submission
 instructions on the course Web page. In particular, make sure that
 the subject of your email submission is "CS 4820 HWK 6".

 The group members are:

 Ling Zheng

|#

#|

 In this homework, you will learn how to use Z3, a modern
 SMT (satisfiability modulo theories) solver from inside of
 ACL2s. Andrew has developed API bindings that provide a (property
 ...)-like interface to Z3. There are Z3 bindings for most languages,
 including Python, OCaml, Haskell, etc.

 You'll develop a simple Sudoku solver using the Z3 bindings. You will
 also explore different ways of encoding problems and how that affects
 performance.

 SMT solvers combine SAT solvers with solvers for additional
 theories (for example, the theory of uninterpreted functions, or real
 arithmetic with addition and multiplication). In this way, SMT
 solvers can check the satisfiability of expressions that contain
 variables and functions from several different theories at once.

 Consider the following example:
 Let x and y be two strings. Is the following satisfiable?
 (^ (< (length x) 3)
    (< (length y) 3)
    (> (length (string-append x y)) 6))
 It is not - the length of (string-append x y) is at most (length x) + (length y).

 We can state this as an ACL2s property:
 (property (x :string y :string)
           (=> (^ (< (length x) 3)
                  (< (length y) 3))
               (not (> (length (string-append x y)) 6))))

 For an SMT solver to be able to report that this statement is UNSAT,
 it needs to understand how length and string-append relate to each
 other. If we ask our DP implementation from Homework 4 whether the
 propositional skeleton is satisfiable, it will report that it is SAT
 because it doesn't reason about length, <, >, string-append, etc.

 As you'll learn, we can ask Z3 to check the satisfiability of this
 statement using the following query (after setting up dependencies):

 (z3-assert (x :string y :string)
            (and (< (str.len x) 3)
                 (< (str.len y) 3)
                 (> (str.len (str.++ x y)) 6)))
 (check-sat)

 Z3 reports :UNSAT.

 Let's get started by first going through some setup instructions for
 the Z3-Lisp API.
|#

#|
=====================================
=            Z3 Setup               =
=====================================

You first need to install Z3 onto your system. Many package managers
offer a prepackaged version of Z3, so it is likely easiest to install
Z3 using your package manager rather than building it from source. If
you're on macOS, Homebrew provides prebuilt Z3 packages as well.

If using Windows Subsystem for Linux to run ACL2s, you should install
Z3 into WSL rather than in "regular" Windows.

Depending on your operating system, you may also need to install
a "z3-dev" package. On Ubuntu, this package is called `libz3-dev`.

You will also need a working C compiler to use the interface. On
Ubuntu, the `build-essential` package should include everything you
need, though it is fairly large and contains some unneeded
software. One could also try just installing `gcc` or `clang`.

After getting Z3 installed, you should be able to run it through the
command line. To test this, execute `z3 --version` in your terminal
and verify that it reports something along the lines of `Z3 version
4.15.4 - 64 bit` (your version or architecture may be different,
that's OK).

To install the z3 bindings, follow the instructions at
https://github.com/mister-walter/cl-z3.  If you run into any issues,
ask questions on Piazza.

|#

;; Exit out of ACL2s into raw Lisp
:q

(load "~/quicklisp/setup.lisp")
(ql:register-local-projects)
(ql:quickload :cl-z3)

(defpackage :hwk6
  (:use :cl :z3))
(in-package :hwk6)

;; Before we do anything, we must start Z3.
(solver-init)

;; ===========================
;;           Basics
;; ===========================
;; To use Z3, one adds one or more assertions to Z3 and then uses
;; (check-sat) to ask Z3 to perform a satisfiability check.
;; Let's try something simple first.
;; We want to know if the formula `x ^ y` is satisfiable. Let's add it
;; to Z3's stack:
(z3-assert (x :bool y :bool)
           (and x y))
;; We can see the contents of the solver using print-solver.
;;(print-solver)

;; Now, we can ask Z3 to check satisfiability:
(check-sat)
(get-model-as-assignment)
;; We get an assignment: ((X T) (Y T)). This indicates that the set of
;; assertions we've added to Z3's stack is satisfiable, and provides a
;; satisfying assignment.

;; Note that Z3 still contains the stack of assertions; if we call
;; check-sat again, we'll get another satisfying assignment.
(check-sat)
(get-model-as-assignment)
;; In this case the satisfying assignment is the same (since there is
;; only one distinct satisfying assignment for the formula `x ^ y`),
;; but in general the assignment may be different.

;; To clear the set of assignments, we can use `(solver-reset)`.
(solver-reset)

;; =========================
;;    The Assertion Stack
;; =========================
;; Sometimes, it may be useful to be able to remove just a subset of
;; assertions instead of resetting all of them. Z3 supports this with
;; the concept of scopes.
;; When a scope `S` is created, Z3 saves the set of assertions that
;; exist at that time. When `S` is popped, Z3 will return its set of
;; assertions to its state at the time `S` was created.

;; Let's see an example.

;; Create an initial scope that we can return to when we want an empty
;; set of assertions
(solver-push)

(z3-assert (x :bool y :int)
           (and x (>= y 5)))
;; This is SAT.
(check-sat)
(get-model-as-assignment)

;; There is currently 1 assertion.
(print-solver)

;; Let's create another scope, one that contains the above assertion.
(solver-push)

;; We'll add an assertion that forces x to be false.
(z3-assert (x :bool)
           (not x))

;; Now the set of assertions is UNSAT!
(check-sat)

;; There are now 2 assertions.
(print-solver)

;; Let's pop off the top scope. This will remove the assertion we just
;; added.
(solver-pop)

;; As expected, check-sat returns a satisfying assignment again.
(check-sat)
(get-model-as-assignment)

;; We're back to the same set of assertions that we had when we ran
;; (solver-push) the second time.
(print-solver)

;; We can pop back to the empty set of assertions that we had after we
;; reset the solver.
(solver-pop)
(print-solver)

;; ==================
;;       Sorts
;; ==================
;; Z3 supports many variable types, which it calls "sorts".
;; We've already seen booleans and integers.
(solver-push)
(z3-assert (x :bool y :int z :string)
           (and x (> y 5) (= (str.len z) 3)))
(check-sat)
(get-model-as-assignment)

;; Z3 also supports sequence types, including strings.
(solver-reset)
(solver-push)
(z3-assert (x (:seq :int) y :string)
           (and (> (seq.len x) 3)
                (> (str.len y) 3)))
(check-sat)
(get-model-as-assignment)
(solver-pop)

;; Here's another example showing more of the sequence operators.
(solver-reset)
(solver-push)
(z3-assert (x (:seq :int) y (:seq :int) z (:seq :int))
           (and (> (seq.len x) 3)
                (> (seq.len y) 1)
                ;; x contains the subsequence consisting of the 0th element of y
                ;; this is equivalent to saying that x contains the 0th element of y
                (seq.contains x (seq.at y 0))
                ;; z equals the concatenation of x and y
                (= z (seq.++ x y))))
(check-sat)
(get-model-as-assignment)
(solver-pop)

;; You can define enumeration sorts as follows:
(register-enum-sort :my-sort (a b c))
;; this sort consists of one of the three values a, b, and c.

;; Now you can use this sort in assertions!
(solver-push)
(z3-assert (x :my-sort y :my-sort)
           (and (not (= x y))
                ;; To represent an element of an enum, you need to use
                ;; `enumval` as shown here.
                (not (= x (enumval :my-sort a)))
                (not (= y (enumval :my-sort b)))))
(check-sat)
(get-model-as-assignment)
(solver-pop)

#|
 Note that operations that may cause exceptions in other languages
 (like division by zero) are underspecified in Z3. This means that Z3
 treats `(/ x 0)` as an uninterpreted function that it may assign any
 value to. This can lead to unexpected behavior if you're not careful.

 For example, Z3 reports that the following is satisfiable, since it
 can assign `x` and `y` different values, and has the flexibility to
 have division by 0 for the value of `x` return 3, and division by 0
 for the value of `y` return 4.
|#
(solver-push)
(z3-assert (x :int y :int)
           (and (= (/ x 0) 3)
                (= (/ y 0) 4)))
(check-sat)
(get-model-as-assignment)
(solver-pop)

;; There are many more operators and a few more sorts supported by Z3
;; and the lisp-z3 interface. See the operators.md file in
;; <ql-local-projects>/lisp-z3 for more information. The operator
;; documentation is also available on the course website (right next
;; to the HWK 6 link). Feel free to ask on Piazza if anything is
;; unclear.

;; One final note: sometimes, `check-sat` may not return an assignment
;; for some of the input variables provided to `z3-assert`. This often
;; is because Z3 is able to determine that the value of those
;; variables does not affect the satisfiability of the set of
;; assertions being checked, so it returns a partial assignment. If
;; you get a partial assignment, then all possible ways of extending
;; the partial assignment to total assignments are also assignments.

(solver-reset)

;; ==========================
;;            Q1
;; ==========================
;; 15 pts (3 pts each)
;;
;; For each of the following statements, encode the statement into a
;; SMT problem that Z3 can handle using `z3-assert` and report whether
;; the statement is satisfiable or not.
;;
;; As noted above, the list of operators supported by the Lisp-Z3
;; interface is available in HTML format on the course website <link>,
;; as well as in Markdown format in
;; <ql-local-projects>/lisp-z3/operators.md.

;; 1a:
;; x, y, and z are boolean variables.
;; if x is true, then both y and z are true.
;; if y is true, then x is not true and z is not true.
;; if z is false, then y is false

(solver-push)
(z3-assert (x :bool y :bool z :bool)
           (and (implies x (and y z))
                (implies y (and (not x) (not z)))
                (implies (not z) (not y))))
(check-sat)
(get-model-as-assignment)
(solver-pop)

;; 1b:
;; x,y,z,p and q are all string variables.
;; the concatenation of x y and z is equal to the concatenation of p and q
;; all of the strings have at least length 2
;; y starts with "ab"
;; p ends with "ba"

(solver-push)
(z3-assert (x y z p q :string)
           (and (= (str.++ x y z) (str.++ p q))
                (and (>= (str.len x) 2)
                     (>= (str.len y) 2)
                     (>= (str.len z) 2)
                     (>= (str.len p) 2)
                     (>= (str.len q) 2))
                (str.prefixof "ab" y)
                (= (seq-last-index p "ba") (- (str.len p) 2))))
(check-sat)
(get-model-as-assignment)
(solver-pop)


;; 1c:
;; x is a sequence of booleans
;; y is an integer variable
;; y is between 0 and 32 inclusive
;; x has length equal to y
;; if x has at least one element and the first element of x is true,
;; then the length of x is even. Otherwise, the length of x is odd.

(solver-push)
(z3-assert (x (:seq :bool) y :int)
           (and (and (<= 0 y) (<= y 32))
                (= (seq.len x) y)
                (ite (and (> (seq.len x) 0)
                          (seq.nth x 0))
                     (= (mod (seq.len x) 2) 0)
                     (not (= (mod (seq.len x) 2) 0)))))
(check-sat)
(get-model-as-assignment)
(solver-pop)

;; Now, we'll have some fun by encoding logic puzzles as SMT problems.

;; 1d:
;; (adapted from "What is the Name of This Book?" by Raymond Smullyan)

;; An island is inhabited by "knights" who always tell the truth, and
;; "knaves" who always lie. A stranger comes across three inhabitants
;; of this island standing together (Alice, Bob, and Clara) and asks
;; Alice "How many knights are among you?". Alice answers
;; indistinctly, and the stranger then asks Bob what Alice said. Bob
;; responds "Alice said there is one knight among us." Clara
;; interjects, saying "Don't believe Bob, he's lying!"
;; Is Bob a knight or a knave? Is Clara a knight or a knave?

;; consulted AI for the direct encoding
;; "Person X is a Knight if and only if their statement is true" is written as (= X S)
(solver-push)
(z3-assert (A B C ASaid1 :bool)
           (and (= B ASaid1)
                (= C (not B))
                (=> ASaid1 (= (+ (ite A 1 0) (ite B 1 0) (ite C 1 0)) 1))))
(check-sat)
(get-model-as-assignment)
(solver-pop)

;; with a little manual reasoning
(solver-push)
(z3-assert (B C :bool)
           (and ;; B, C have different identities
                (= C (not B))
                ;; if A knight,
                ;; then B cannot be knight, otherwise, it forces count of knights to be 2
                ;; else B cannot be knight, otherwise, it forces count of knights to be 0, 2, or 3 but C has to be knave.
                (not B)))
(check-sat)
(get-model-as-assignment)
(solver-pop)

;; 1e:
;; (adapted from from "My best puzzles in logic and reasoning" by
;; Hubert Phillips, now public domain)
#|
Mr. Fireman, Mr. Guard, and Mr. Driver are (not necessarily
respectively) the fireman, guard, and driver of an express
train. Exactly one of the following statements is true:
- Mr. Driver is not the guard
- Mr. Fireman is not the driver
- Mr. Driver is the driver
- Mr. Fireman is not the guard

Is the above set of constraints consistent? If so, who has what job?

(hint: an enumeration sort might be helpful here)
|#

(register-enum-sort :job (F G D))

(solver-push)
(z3-assert (MF MG MD :job)
           (and ((_ at-most 1)
                 (!= MD (enumval :job G))
                 (!= MF (enumval :job D))
                 (= MD (enumval :job D))
                 (!= MF (enumval :job G)))
                ((_ at-least 1)
                 (!= MD (enumval :job G))
                 (!= MF (enumval :job D))
                 (= MD (enumval :job D))
                 (!= MF (enumval :job G)))
                (distinct MF MG MD)))
(check-sat)
(get-model-as-assignment)
;; Mr. Fireman is the Driver.
;; Mr. Guard is the Fireman.
;; Mr. Driver is the Guard.
(solver-pop)

;; ===========================
;;    Generating Constraints
;; ===========================
;;
;; It can get tedious to manually generate the constraints that encode
;; a particular problem. Since constraints are written using
;; S-expressions, we can use Lisp to generate constraints
;; programmatically.

;; Let's take a look at a very simple problem: we want to use Z3 to
;; find a normal semimagic square of order 3. A non-trivial semimagic
;; square of order `n` is an `n` x `n` grid of integers between 1 and
;; n^2 inclusive such that all of the rows and columns sum to the same
;; value. Since we did not specify that the magic square is
;; non-trivial, more than one cell in the square may have the same
;; value.

;; First, let's think about the constraints that we will need to
;; generate for this problem. We will likely want to encode each
;; square in the grid as an integer variable, and then add constraints
;; that state that the sums of the integer variables for each row and
;; column all equal the same value.

;; Let's consider an order-2 semimagic square. For this square, we
;; need 4 integer variables. I'll call them X0, X1, X2, and X3. They
;; need to have values between 1 and 4 inclusive, e.g. the following
;; conjunction must hold:
#|
(and (> X0 0) (<= X0 4)
     (> X1 0) (<= X1 4)
     (> X2 0) (<= X2 4)
     (> X3 0) (<= X3 4))
|#

;; Our square will look like this:
#|
+---------+
| X0 | X1 |
+---------+
| X2 | X3 |
+---------+
|#
;; Now, we need to encode that the sums of the rows and columns are
;; the same. I'll introduce another integer variable, S, to represent
;; the sum of the rows and columns.
;; The constraints are:
;; (= (+ X0 X1) S) ;; row 0
;; (= (+ X2 X3) S) ;; row 1
;; (= (+ X0 X2) S) ;; col 0
;; (= (+ X1 X3) S) ;; col 1

;; To write this in a form that `z3-assert` can understand, we need to
;; take the conjunction of the row and column constraints, and
;; generate a list defining each variable and its sort. We also need
;; to add in the constraints on the range of each variable.
;; In this case, we would generate:

(z3-assert (X0 :int X1 :int X2 :int X3 :int S :int)
           (and (> X0 0) (<= X0 4) ;; x0 is within the appropriate range
                (> X1 0) (<= X1 4) ;; ditto for x1
                (> X2 0) (<= X2 4)
                (> X3 0) (<= X3 4)
                (= (+ X0 X1) S) ;; row 0
                (= (+ X2 X3) S) ;; row 1
                (= (+ X0 X2) S) ;; col 0
                (= (+ X1 X3) S))) ;; col 1
;; We can use Z3 to determine if any such magic square exists:
(check-sat)
;; Indeed, one exists: all of the squares are 1. Boring, but it works.
(solver-reset)

;; Now, let's generate those constraints for an order-3 semimagic
;; square programmatically.

;; When dealing with a grid of variables, it is often useful to have a
;; way of transforming a pair of a row and column indices into the
;; variable at that location. I'll define such a function below.
(defun get-3x3-magic-square-var (row col)
  ;; See the Common Lisp HyperSpec for more information about any
  ;; Common Lisp function.
  ;; For example, the documentation for `concatenate` can be found at
  ;; http://clhs.lisp.se/Body/f_concat.htm
  ;; You can also ask SBCL for documentation for a function
  ;; by running (describe #'<function-name>) in the REPL.
  ;; e.g. (describe #'concatenate)
  (intern (concatenate 'string "X" (write-to-string (+ col (* row 3))))))
;;

;; This should give us the variable for the first cell, X0
(get-3x3-magic-square-var 0 0)
;; Don't worry if it prints out :INTERNAL afterwards - `intern`
;; actually returns multiple values (see the HyperSpec for more info)

;; Now, let's define a function that will generate the constraint that
;; states that the sum of a particular row should be equal to some variable.
(defun 3x3-magic-square-row-sum (row sum-var)
  ;; I'm going to use the loop macro here. This is a very powerful
  ;; macro that allows us to avoid writing helper functions just to
  ;; perform basic loops.
  ;; See the HyperSpec and
  ;; https://gigamonkeys.com/book/loop-for-black-belts.html for more
  ;; information.
  ;; We want to first generate the variables corresponding to each
  ;; cell in this row.
  (let ((row-squares
         (loop for col below 3
               collect (get-3x3-magic-square-var row col))))
    ;; Then, we want to say that the sum of the squares is equal to
    ;; whatever the sum-var is.
    `(= ,sum-var (+ . ,row-squares))))

;; Just as a sanity check, let's generate the constraint for the first row.
(3x3-magic-square-row-sum 0 'S)
;; great, exactly as we expected.

;; Now, let's define a similar function for columns.
(defun 3x3-magic-square-col-sum (col sum-var)
  (let ((col-squares
         (loop for row below 3
               collect (get-3x3-magic-square-var row col))))
    `(= ,sum-var (+ . ,col-squares))))
;; Another sanity check...
(3x3-magic-square-col-sum 0 'S)
;; looks good.

;; Now, let's put it all together. We want to generate the constraints
;; for all of the rows and all of the columns and take the conjunction
;; of them.
(defun 3x3-magic-square-row-col-constraints (sum-var)
  (let ((row-constraints (loop for row below 3 collect (3x3-magic-square-row-sum row sum-var)))
        (col-constraints (loop for col below 3 collect (3x3-magic-square-col-sum col sum-var))))
    ;; ,@ splices a list into an S-expression. e.g. `(1 ,@(list 2 3)) = '(1 2 3)
    `(and ,@row-constraints ,@col-constraints)))
;; Great, this is a conjunction of equalities, which is what we expect.
(3x3-magic-square-row-col-constraints 'S)

;; Finally, we need to generate the list of variables and their sorts.
(defun 3x3-magic-square-var-specs (sum-var)
  (let ((cell-vars (loop for row below 3 append
                         (loop for col below 3 append
                               `(,(get-3x3-magic-square-var row col) :int)))))
    `(,sum-var :int ,@cell-vars)))

(3x3-magic-square-var-specs 'S)

;; We also need to assert that all of the values are between 1 and 9.
(defun 3x3-magic-square-vars-between-1-and-9 ()
  (cons 'and (loop for row below 3 append
                   (loop for col below 3 append
                         `((>= ,(get-3x3-magic-square-var row col) 1)
                           (<= ,(get-3x3-magic-square-var row col) 9))))))

;; Now, we just need to pass this information into `z3-assert`.
;; `z3-assert` is just a macro that calls `z3-assert-fn` on its quoted
;; input. All this means is that we can skip some shenanigans with
;; backquote and just pass the constraints and variable specifications
;; directly into `z3-assert-fn`.

(solver-push)
(z3-assert-fn (3x3-magic-square-var-specs 'S)
              (3x3-magic-square-row-col-constraints 'S))
(z3-assert-fn (3x3-magic-square-var-specs 'S)
              (3x3-magic-square-vars-between-1-and-9))
(check-sat)
;; We get our satisfying assignment, still boring (all 1s) but correct.
(solver-pop)

;; You'll expand upon this in Q2 below.

(solver-reset)

;; ==========================
;;            Q2
;; ==========================
;; 25 pts

;; Use Z3 to find a normal non-trivial magic square of order 3.

;; You should use a similar approach to that shown above to
;; programmatically generate the constraints and pass them into
;; `z3-assert-fn`.

;; A magic square is a semimagic square that also satisfies the
;; property that all diagonals also sum to the same value as all of
;; the rows and columns.
;; A non-trivial magic square is a magic square such that no two cells
;; have the same value.

(defun 3x3-magic-square-diagonal (sum-var)
  (let ((diag1 (loop for i below 3 collect (get-3x3-magic-square-var i i)))
        (diag2 (loop for i below 3 collect (get-3x3-magic-square-var i (- 2 i)))))
    `(and (= (+ . ,diag1) ,sum-var)
          (= (+ . ,diag2) ,sum-var))))

(defun 3x3-magic-square-distinct ()
  (cons 'distinct
        (loop for row below 3 append
             (loop for col below 3
                   collect (get-3x3-magic-square-var row col)))))

(solver-push)
(z3-assert-fn (3x3-magic-square-var-specs 'S)
              (3x3-magic-square-row-col-constraints 'S))
(z3-assert-fn (3x3-magic-square-var-specs 'S)
              (3x3-magic-square-vars-between-1-and-9))
(z3-assert-fn (3x3-magic-square-var-specs 'S)
              (3x3-magic-square-diagonal 'S))
(z3-assert-fn (3x3-magic-square-var-specs 'S)
              (3x3-magic-square-distinct))
(check-sat)
(get-model-as-assignment)
;; ((X2 4) (X3 1) (S 15) (X5 9) (X4 5) (X0 8) (X1 3) (X8 2) (X6 6) (X7 7))
(solver-pop)

;; You'll expand upon this in Q2 below.

(solver-reset)


;; ==========================
;;            Q3
;; ==========================
;; 30 pts
;;
;; Develop a Sudoku solver that uses an approach similar to that
;; described above to use Z3 to generate solutions to a given starting
;; board. The top-level function should be called `solve-sudoku`, and
;; should take a starting board as an argument. The format of the
;; starting board will be defined below. `solve-sudoku` should return
;; either 'UNSAT (if no valid Sudoku board also satisfies the starting
;; board) or an assignment (a list of 2-element lists, similar to a
;; let binding, where the first element is the variable name and the
;; second is the assignment) that represents a filled-in Sudoku board
;; that satisfies the starting board's assignments.
;;
;; A valid Sudoku board is a 3x3 grid of 3x3 boxes. The 9 cells in
;; each box must all be integers from 1 to 9 inclusive, and must all
;; be different. Every row and column of the 9x9 Sudoku grid must
;; contain every integer from 1 to 9 inclusive exactly once.
;;
;; You will first use a bit-blasting encoding for this problem,
;; similar to the approach that I used to generate the example Sudoku
;; problems that I evaluated your DP algorithms using.  What I mean by
;; this is that each Sudoku square will be represented by 9 variables,
;; one for each possible value it may have.
;;
;; A starting board consists of a standard 3x3 Sudoku board with only
;; a subset of cells having specified values. We will use _ to denote
;; unspecified values. The starting board will be represented by a
;; list of 81 elements, where each element can be an integer between 1
;; and 9 inclusive or _.
;;
;; `solve-sudoku` should return an alist mapping Sudoku cell variables
;; (see `sudoku-cell-var` below) to booleans depending on whether the
;; cell represented by the cell variable has the value represented by
;; the cell variable.
;;
;; I have provided the function that generates a variable
;; corresponding to the Sudoku cell at a given row and column having a
;; particular value.
;; row and col should both be integers from 0 to 8, inclusive.
;; val should be an integer from 1 to 9, inclusive.
(defun sudoku-cell-var (row col val)
  (intern (concatenate 'string "X" (write-to-string (+ col (* row 9))) "_" (write-to-string val))))

;; I have provided some utilities for pretty-printing Sudoku solutions
;; below.

(defun assoc-equal (x a)
  (assoc x a :test #'equal))

;; Given a solution that is an alist from cell vars to booleans, get
;; the assigned value for the cell at the given row and column, or nil
;; if it is unassigned.
(defun get-square-value-bool (soln row col)
  (block outer
    (loop for i from 1 to 9
          do (when (and (cdr (assoc-equal (sudoku-cell-var row col i) soln))
                        (cadr (assoc-equal (sudoku-cell-var row col i) soln)))
               (return-from outer i)))
    nil))

;; Default: uses bool encoding (Q3). Callers may setf this to get-square-value-int.
(defun get-square-value (soln row col)
  (get-square-value-bool soln row col))

;; This pretty-prints a Sudoku solution, using `get-square-value` to
;; handle the task of getting the value of a cell from the solution
;; representation used.
(defun pretty-print-3x3-sudoku-solution (soln)
  (loop for row below 9
        do (progn (terpri)
                  (loop for col below 9
                        do (progn (format t "~A " (get-square-value soln row col))
                                  (when (equal (mod col 3) 2) (format t "  "))))
                  (when (equal (mod row 3) 2) (terpri)))))

;; Here's an example starting board. It has a unique solution.
(defconstant *sudoku-example-board*
  '(7 _ _   _ 1 _   _ _ _
    _ 1 _   _ _ 3   7 _ 8
    _ 5 3   _ _ _   _ _ 4

    5 _ 9   3 _ _   _ _ 2
    4 _ 1   2 6 _   3 7 _
    _ _ 7   _ 8 5   9 4 _

    2 7 _   _ 9 4   _ 3 _
    8 _ _   5 _ 1   _ 6 _
    _ 3 _   _ _ 2   4 5 _))

;; Here's its solution.
#|
 7 4 8   9 1 6   5 2 3
 6 1 2   4 5 3   7 9 8
 9 5 3   7 2 8   6 1 4

 5 6 9   3 4 7   1 8 2
 4 8 1   2 6 9   3 7 5
 3 2 7   1 8 5   9 4 6

 2 7 5   6 9 4   8 3 1
 8 9 4   5 3 1   2 6 7
 1 3 6   8 7 2   4 5 9
|#

(defun exactly-one (vars)
  `(((_ at-least 1) ,@vars)
    ((_ at-most  1) ,@vars)))

(defun sudoku-var-specs ()
  (loop for row below 9 append
        (loop for col below 9 append
              (loop for val from 1 to 9 append
                    `(,(sudoku-cell-var row col val) :bool)))))

(defun sudoku-initial (input-grid)
  (let ((specs (loop for row below 9 append
                     (loop for col below 9 append
                           (let ((cell-val (nth (+ col (* row 9)) input-grid)))
                             (if (not (equal cell-val '_))
                                 `((= ,(sudoku-cell-var row col cell-val) t))
                                 nil))))))
    (if (null specs)
        'true
        `(and ,@specs))))

(defun sudoku-each-cell-has-one-value ()
  (cons 'and
        (loop for row below 9 append
             (loop for col below 9 append
                   (let ((vars (loop for val from 1 to 9
                                    collect (sudoku-cell-var row col val))))
                     (exactly-one vars))))))

(defun sudoku-box-cell-all-different (box-row box-col)
  (loop for val from 1 to 9 append
        (let ((vars (loop for r from (* box-row 3) below (+ (* box-row 3) 3) append
                         (loop for c from (* box-col 3) below (+ (* box-col 3) 3)
                               collect (sudoku-cell-var r c val)))))
          (exactly-one vars))))

(defun sudoku-each-box-all-different ()
  (cons 'and
        (loop for box-row below 3 append
             (loop for box-col below 3 append
                   (sudoku-box-cell-all-different box-row box-col)))))

(defun sudoku-all-row-col-different ()
  (cons 'and
        (append
         (loop for row below 9 append
              (loop for val from 1 to 9 append
                    (let ((vars (loop for col below 9
                                     collect (sudoku-cell-var row col val))))
                      (exactly-one vars))))
         (loop for col below 9 append
              (loop for val from 1 to 9 append
                    (let ((vars (loop for row below 9
                                     collect (sudoku-cell-var row col val))))
                      (exactly-one vars)))))))

(solver-reset)

(defun solve-sudoku (input-grid)
  (let ((var-specs (sudoku-var-specs)))
    (solver-push)
    (z3-assert-fn var-specs (sudoku-initial input-grid))
    (z3-assert-fn var-specs (sudoku-each-cell-has-one-value))
    (z3-assert-fn var-specs (sudoku-each-box-all-different))
    (z3-assert-fn var-specs (sudoku-all-row-col-different))
    (let ((sol (if (equal (check-sat) :UNSAT)
                   'UNSAT
                   (get-model-as-assignment))))
      (solver-pop)
      sol)))

(defun benchmark-solve-sudoku (grid name)
  (format t "~%=== ~A (bit-blasting) ===~%" name)
  (solver-reset)
  (let ((soln (time (solve-sudoku grid))))
    (if (equal soln 'UNSAT)
        (format t "UNSAT~%")
        (progn
          (setf (fdefinition 'get-square-value) #'get-square-value-bool)
          (pretty-print-3x3-sudoku-solution soln)))
    (z3::get-solver-stats)
    soln))

;; This should print out the solution given above.
(benchmark-solve-sudoku *sudoku-example-board* "*sudoku-example-board*")

;; ==========================
;;            Q4
;; ==========================
;; 30 pts
;;
;; 4a. (15 pts)
;;
;; Experiment with a different encoding for Sudoku cells. For example,
;; you could use integers to represent each square, or enumeration
;; sorts. You should define `solve-sudoku-alternate` below to behave
;; like `solve-sudoku` as described in Q3, except that it must use a
;; different encoding to represent the value of each Sudoku cell.
;;
;; You likely will want to define your own version of
;; `sudoku-cell-var`, perhaps omitting the `val` parameter if it is
;; not necessary for your cell value representation.
;;
;; You can continue to use the `pretty-print-3x3-sudoku-solution`
;; function I provided if you redefine `get-square-value` to work with
;; your variable encoding.

(defun sudoku-cell-var-alt (row col)
  (intern (concatenate 'string "X" (write-to-string (+ col (* row 9))))))

(defun sudoku-var-specs-alt ()
  (loop for row below 9 append
        (loop for col below 9 append
              `(,(sudoku-cell-var-alt row col) :int))))

(defun sudoku-initial-alt (input-grid)
  (let ((specs (loop for row below 9 append
                     (loop for col below 9 append
                           (let ((cell-val (nth (+ col (* row 9)) input-grid)))
                             (if (not (equal cell-val '_))
                                 `((= ,(sudoku-cell-var-alt row col) ,cell-val))
                                 nil))))))
    (if (null specs)
        'true
        `(and ,@specs))))

(defun sudoku-var-range ()
  (cons 'and
        (loop for row below 9 append
             (loop for col below 9 append
                   `((and (> ,(sudoku-cell-var-alt row col) 0)
                          (<= ,(sudoku-cell-var-alt row col) 9)))))))

(defun sudoku-box-cell-all-different-alt (box-row box-col)
  `(distinct ,@(loop for r from (* box-row 3) below (+ (* box-row 3) 3) append
                      (loop for c from (* box-col 3) below (+ (* box-col 3) 3)
                            collect (sudoku-cell-var-alt r c)))))

(defun sudoku-each-box-all-different-alt ()
  (cons 'and
        (loop for box-row below 3 append
             (loop for box-col below 3 collect
                   (sudoku-box-cell-all-different-alt box-row box-col)))))

(defun sudoku-all-row-col-different-alt ()
  (cons 'and
        (append
         (loop for row below 9 collect
              (cons 'distinct
                    (loop for col below 9
                          collect (sudoku-cell-var-alt row col))))
         (loop for col below 9 collect
              (cons 'distinct
                    (loop for row below 9
                          collect (sudoku-cell-var-alt row col)))))))

(defun solve-sudoku-alternative (input-grid)
  (let ((var-specs (sudoku-var-specs-alt)))
    (solver-push)
    (z3-assert-fn var-specs (sudoku-initial-alt input-grid))
    (z3-assert-fn var-specs (sudoku-var-range))
    (z3-assert-fn var-specs (sudoku-each-box-all-different-alt))
    (z3-assert-fn var-specs (sudoku-all-row-col-different-alt))
    (let ((sol (if (equal (check-sat) :UNSAT)
                   'UNSAT
                   (get-model-as-assignment))))
      (solver-pop)
      sol)))

(solver-reset)

;; Integer encoding: the cell variable holds its value directly.
(defun get-square-value-int (soln row col)
  (cadr (assoc-equal (sudoku-cell-var-alt row col) soln)))

(defun benchmark-solve-sudoku-alternative (grid name)
  (format t "~%=== ~A (integer encoding) ===~%" name)
  (solver-reset)
  (let ((soln (time (solve-sudoku-alternative grid))))
    (if (equal soln 'UNSAT)
        (format t "UNSAT~%")
        (progn
          (setf (fdefinition 'get-square-value) #'get-square-value-int)
          (pretty-print-3x3-sudoku-solution soln)))
    (z3::get-solver-stats)
    soln))

;; This should print out the solution given above.
(benchmark-solve-sudoku-alternative *sudoku-example-board* "*sudoku-example-board*")

;; 4b. (15 pts)
;;
;; Compare the performance of `solve-sudoku` and
;; `solve-sudoku-alternate`. Come up with the hardest Sudoku grid you
;; can find for each solver and explain why you think it is hard.
;;
;; Note that Z3 uses a variant of DPLL called DPLL(T) for solving SMT
;; problems.
;;
;; You may find it useful to see internal statistics that Z3 collects
;; during SMT solving. These statistics are cumulative, so you should
;; re-initialize Z3 before each query that you want to measure.
;; These statistics can be printed by calling `(z3::get-solver-stats)`.
;;
;; Unfortunately there is no single resource that describes what all
;; of the returned statistics means, but some statistics of note are:
;; - :conflicts: the number of conflicts found during DPLL
;; - :decisions: the number of DPLL decisions made
;; - :propagations: the number of times unit propagation was performed
;; - :restarts: the number of times that Z3 decided to restart DPLL
;;   from the beginning, retaining learned conflict clauses (recall
;;   nonchronological backtracking)

(defun benchmark-sudoku (grid name)
  (benchmark-solve-sudoku grid name)
  (benchmark-solve-sudoku-alternative grid name))

;; Tests taken from https://github.com/mister-walter/cl-z3/blob/main/examples/sudoku.lisp

;; Formatted for readability.
(defconstant a-hard-sudoku-grid
  '(6 _ _   3 _ 1   _ 8 4
    _ _ _   _ 6 9   _ _ 7
    _ _ _   _ _ 7   _ 1 3

    4 _ _   6 9 _   _ _ 8
    _ _ _   _ 1 5   _ _ _
    _ _ 8   _ _ _   _ 6 _

    _ _ _   _ _ _   _ _ _
    _ _ _   1 _ _   7 _ _
    2 _ 4   _ _ 3   1 _ _))

(benchmark-sudoku a-hard-sudoku-grid "a-hard-sudoku-grid")
;; 0.025s
;; 0.062s

(defconstant a-very-hard-sudoku-grid
  '(_ _ _   _ _ _   _ 1 2
    _ _ _   _ _ _   _ _ 3
    _ _ 2   3 _ _   4 _ _

    _ _ 1   8 _ _   _ _ 5
    _ 6 _   _ 7 _   8 _ _
    _ _ _   _ _ 9   _ _ _

    _ _ 8   5 _ _   _ _ _
    9 _ _   _ 4 _   5 _ _
    4 7 _   _ _ 6   _ _ _))

(benchmark-sudoku a-very-hard-sudoku-grid "a-very-hard-sudoku-grid")
;; 0.028s
;; 0.407s

(defconstant only-first-row-defined-grid
  '(1 2 3   4 5 6   7 8 9
    _ _ _   _ _ _   _ _ _
    _ _ _   _ _ _   _ _ _

    _ _ _   _ _ _   _ _ _
    _ _ _   _ _ _   _ _ _
    _ _ _   _ _ _   _ _ _

    _ _ _   _ _ _   _ _ _
    _ _ _   _ _ _   _ _ _
    _ _ _   _ _ _   _ _ _))

(benchmark-sudoku only-first-row-defined-grid "only-first-row-defined-grid")
;; 0.027s
;; 31.176s

(defconstant only-first-col-defined-grid
  '(1 _ _   _ _ _   _ _ _
    2 _ _   _ _ _   _ _ _
    3 _ _   _ _ _   _ _ _

    4 _ _   _ _ _   _ _ _
    5 _ _   _ _ _   _ _ _
    6 _ _   _ _ _   _ _ _

    7 _ _   _ _ _   _ _ _
    8 _ _   _ _ _   _ _ _
    9 _ _   _ _ _   _ _ _))

(benchmark-sudoku only-first-col-defined-grid "only-first-col-defined-grid")
;; 0.027s
;; 5.958s

(defconstant only-diag-defined-grid
  '(1 _ _   _ _ _   _ _ _
    _ 2 _   _ _ _   _ _ _
    _ _ 3   _ _ _   _ _ _

    _ _ _   4 _ _   _ _ _
    _ _ _   _ 5 _   _ _ _
    _ _ _   _ _ 6   _ _ _

    _ _ _   _ _ _   7 _ _
    _ _ _   _ _ _   _ 8 _
    _ _ _   _ _ _   _ _ 9))

(benchmark-sudoku only-diag-defined-grid "only-diag-defined-grid")
;; 0.032s
;; 5.725s

(defconstant only-first-row-defined-reverse-grid
  '(9 8 7   6 5 4   3 2 1
    _ _ _   _ _ _   _ _ _
    _ _ _   _ _ _   _ _ _

    _ _ _   _ _ _   _ _ _
    _ _ _   _ _ _   _ _ _
    _ _ _   _ _ _   _ _ _

    _ _ _   _ _ _   _ _ _
    _ _ _   _ _ _   _ _ _
    _ _ _   _ _ _   _ _ _))

(benchmark-sudoku only-first-row-defined-reverse-grid "only-first-row-defined-reverse-grid")
;; 0.028s
;; 12.273s

(defconstant blank-sudoku-grid
  '(_ _ _   _ _ _   _ _ _
    _ _ _   _ _ _   _ _ _
    _ _ _   _ _ _   _ _ _

    _ _ _   _ _ _   _ _ _
    _ _ _   _ _ _   _ _ _
    _ _ _   _ _ _   _ _ _

    _ _ _   _ _ _   _ _ _
    _ _ _   _ _ _   _ _ _
    _ _ _   _ _ _   _ _ _))

(benchmark-solve-sudoku blank-sudoku-grid "blank-sudoku-grid")
;; 0.038s
;; (benchmark-solve-sudoku-alternative blank-sudoku-grid "blank-sudoku-grid")
;; timeout after 1 min

;; Generated by Claude

;; -----------------------------------------------
;; Example A (SAT): Arto Inkala's 2010 "AI Escargot" — one of the hardest known Sudoku puzzles.
(defconstant *inkala-2010*
  '(8 _ _   _ _ _   _ _ _
    _ _ 3   6 _ _   _ _ _
    _ 7 _   _ 9 _   2 _ _

    _ 5 _   _ _ 7   _ _ _
    _ _ _   _ 4 5   7 _ _
    _ _ _   1 _ _   _ 3 _

    _ _ 1   _ _ _   _ 6 8
    _ _ 8   5 _ _   _ 1 _
    _ 9 _   _ _ _   4 _ _))

(benchmark-sudoku *inkala-2010* "*inkala-2010*")
;; 0.027s (bit-blasting)
;; 0.423s (integer)
;;
;; Note: Inkala 2010 was designed to be hard for *humans*, not SAT solvers.
;; It has 24 given clues — these immediately seed strong unit propagation in
;; CDCL, quickly narrowing the search space. Human hardness comes from the
;; clues being placed to block standard human pencil-mark strategies (naked
;; singles, hidden pairs, etc.), which are irrelevant to CDCL.

;; -----------------------------------------------
;; Example B (SAT): Moderate puzzle — baseline comparison.
(defconstant *moderate-board*
  '(_ _ _   2 6 _   7 _ 1
    6 8 _   _ 7 _   _ 9 _
    1 9 _   _ _ 4   5 _ _

    8 2 _   1 _ _   _ 4 _
    _ _ 4   6 _ 2   9 _ _
    _ 5 _   _ _ 3   _ 2 8

    _ _ 9   3 _ _   _ 7 4
    _ 4 _   _ 5 _   _ 3 6
    7 _ 3   _ 1 8   _ _ _))

(benchmark-sudoku *moderate-board* "*moderate-board*")
;; 0.026s
;; 0.007s

;; -----------------------------------------------
;; Example C (UNSAT): Value 1 appears twice in row 0 — direct contradiction.
(defconstant *unsat-board*
  '(1 _ _   _ _ _   _ _ 1
    _ _ _   _ _ _   _ _ _
    _ _ _   _ _ _   _ _ _

    _ _ _   _ _ _   _ _ _
    _ _ _   _ _ _   _ _ _
    _ _ _   _ _ _   _ _ _

    _ _ _   _ _ _   _ _ _
    _ _ _   _ _ _   _ _ _
    _ _ _   _ _ _   _ _ _))

(benchmark-sudoku *unsat-board* "*unsat-board*")
;; 0.008s
;; 0s

;; The hardest Sudoku board for your `solve-sudoku` implementation.
(define-symbol-macro *hardest-sudoku-board* blank-sudoku-grid)

;; The hardest Sudoku board for your `solve-sudoku-alternate`
;; implementation.
(defconstant *hardest-sudoku-board-alternate* blank-sudoku-grid)

;; ==========================
;;       Extra Credit
;; ==========================
;; 25pts each

;; ==========================
;;            E1
;; ==========================
;;
;; Extend your Sudoku solver to support arbitrary-size Sudoku
;; puzzles. For n>3, the input and output of your solver should still
;; be numeric (as opposed to e.g. taking in and returning symbols that
;; somehow encode numeric values for cell values greater than 9).

(defun arb-sudoku-var-specs (n^2)
  (loop for row below n^2 append
        (loop for col below n^2 append
              (loop for val from 1 to n^2 append
                    `(,(sudoku-cell-var row col val) :bool)))))

(defun arb-sudoku-initial (input-grid n^2)
  (cons 'and
        (loop for row below n^2 append
             (loop for col below n^2 append
                   (let ((cell-val (nth (+ col (* row n^2)) input-grid)))
                     (if (not (equal cell-val '_))
                         `((= ,(sudoku-cell-var row col cell-val) t))
                         nil))))))

(defun arb-sudoku-each-cell-has-one-value (n^2)
  (cons 'and
        (loop for row below n^2 append
             (loop for col below n^2 append
                   (let ((vars (loop for val from 1 to n^2
                                    collect (sudoku-cell-var row col val))))
                     (exactly-one vars))))))

(defun arb-sudoku-box-cell-all-different (box-row box-col n)
  (loop for val from 1 to (* n n) append
        (let ((vars (loop for r from (* box-row n) below (+ (* box-row n) n) append
                         (loop for c from (* box-col n) below (+ (* box-col n) n)
                               collect (sudoku-cell-var r c val)))))
          (exactly-one vars))))

(defun arb-sudoku-each-box-all-different (n)
  (cons 'and
        (loop for box-row below n append
             (loop for box-col below n append
                   (arb-sudoku-box-cell-all-different box-row box-col n)))))

(defun arb-sudoku-all-row-col-different (n^2)
  (cons 'and
        (append
         (loop for row below n^2 append
              (loop for val from 1 to n^2 append
                    (let ((vars (loop for col below n^2
                                     collect (sudoku-cell-var row col val))))
                      (exactly-one vars))))
         (loop for col below n^2 append
              (loop for val from 1 to n^2 append
                    (let ((vars (loop for row below n^2
                                     collect (sudoku-cell-var row col val))))
                      (exactly-one vars)))))))

(defun arb-solve-sudoku (n input-grid)
  "Arbitrary-size Sudoku solver. n is the size of the boxes in the Sudoku grid, so the grid is of size n^2 x n^2 and contains values from 1 to n^2.

  Pre: n > 0"

  (assert (> n 0) nil "n must be greater than 0")

  (let* ((n^2 (* n n))
         (var-specs (arb-sudoku-var-specs n^2)))
    (solver-push)
    (z3-assert-fn var-specs
                  (arb-sudoku-initial input-grid n^2))

    (z3-assert-fn var-specs
                  (arb-sudoku-each-cell-has-one-value n^2))

    (z3-assert-fn var-specs
                  (arb-sudoku-each-box-all-different n))

    (z3-assert-fn var-specs
                  (arb-sudoku-all-row-col-different n^2))

    (let ((sol (if (equal (check-sat) :UNSAT)
                  'UNSAT
                  (get-model-as-assignment))))
      (solver-pop)
      sol)))

(defun pretty-print-sudoku-solution (n soln)
  (loop for row below n
        do (progn (terpri)
                  (loop for col below n
                        do (progn (format t "~A " (get-square-value soln row col))
                                  (when (equal (mod col n) 2) (format t "  "))))
                  (when (equal (mod row n) 2) (terpri)))))

(defun benchmark-arb-solve-sudoku (n grid name)
  (format t "~%=== ~A (arb ~Ax~A bit-blasting) ===~%" name (* n n) (* n n))
  (solver-reset)
  (let ((soln (time (arb-solve-sudoku n grid))))
    (if (equal soln 'UNSAT)
        (format t "UNSAT~%")
        (progn
          (setf (fdefinition 'get-square-value) #'get-square-value-bool)
          (pretty-print-sudoku-solution n soln)))
    (z3::get-solver-stats)))

;; This should print out the solution given above.
(benchmark-arb-solve-sudoku 3 *sudoku-example-board* "*sudoku-example-board*")
;; 0.030s

;; -----------------------------------------------
;; 16x16 Sudoku (n=4): 4x4 boxes, values 1-16
;; -----------------------------------------------

;; A 16x16 Sudoku puzzle with some clues (SAT)
(defconstant *sudoku-16x16-example*
  '( 1  2  _  _    _  _  7  8    9 10  _  _   13 14  _  _
     _  _  5  6    _  _  _  _    _  _  _  _   _  _  _  _
     _  _  _  _   11 12  _  _    _  _  _  _   _  _  _  _
    13 14  _  _   15 16  _  _    _  _  _  _   _  _  _  _

     _  _  _  _    _  _  _  _    _  _  _  _   _  _  _  _
     _  _  _  _    _  _  _  _    _  _  _  _   _  _  _  _
     _  _  _  _    _  _  _  _    _  _  _  _   _  _  _  _
     _  _  _  _    _  _  _  _    _  _  _  _   _  _  _  _

     _  _  _  _    _  _  _  _    _  _  _  _   _  _  _  _
     _  _  _  _    _  _  _  _    _  _  _  _   _  _  _  _
     _  _  _  _    _  _  _  _    _  _  _  _   _  _  _  _
     _  _  _  _    _  _  _  _    _  _  _  _   _  _  _  _

     _  _  _  _    _  _  _  _    _  _  _  _   _  _  _  _
     _  _  _  _    _  _  _  _    _  _  _  _   _  _  _  _
     _  _  _  _    _  _  _  _    _  _  _  _   _  _  _  _
     _  _  _  _    _  _  _  _    _  _  _  _   _  _  _  _))

(benchmark-arb-solve-sudoku 4 *sudoku-16x16-example* "*sudoku-16x16-example*")

;; -----------------------------------------------
;; 25x25 Sudoku (n=5): 5x5 boxes, values 1-25
;; -----------------------------------------------

;; A 25x25 Sudoku puzzle with first row defined (SAT)
;; This is a large puzzle - may take significant time to solve
(defconstant *sudoku-25x25-first-row*
  (append '( 1  2  3  4  5    6  7  8  9 10   11 12 13 14 15   16 17 18 19 20   21 22 23 24 25)
          (loop repeat (* 24 25) collect '_)))

;; Warning: 25x25 puzzles are very large and may take minutes to solve
;; (benchmark-arb-solve-sudoku 5 *sudoku-25x25-first-row* "*sudoku-25x25-first-row*")

;; ==========================
;;            E2
;; ==========================
;;
;; Develop a solver for another logic puzzle by encoding it as
;; Z3 assertions using the Lisp-Z3 interface.
;; Any of the logic puzzles here are allowed:
;; https://www.chiark.greenend.org.uk/~sgtatham/puzzles/
;; Any puzzle that is NP-hard is OK.
;;
;; You should provide a short description of the selected logic puzzle
;; and the input encoding you use, as well as a few (2-3) example
;; instances of your chosen puzzle encoded using your input encoding.

;; Unequal [https://www.chiark.greenend.org.uk/~sgtatham/puzzles/js/unequal.html]
;; Fill in the grid with numbers from 1 to the grid size, so that every number appears exactly once in each row and column, and so that all the < signs represent true inequalities
;; (i.e. the number at the pointed end is smaller than the number at the open end).
;; This is basically Sudoku with some additional constraints, so we can use a similar encoding to the one we used for Sudoku.
;; We can reuse the same variable encoding as in `solve-sudoku-alternative`, and then add additional constraints for the inequalities.

(defun unequal-cell-var (n row col)
  (intern (concatenate 'string "X" (write-to-string (+ col (* row n))))))

(defun unequal-var-specs (n)
  (loop for row below n append
        (loop for col below n append
              `(,(unequal-cell-var n row col) :int))))

;; Helper to get element from the (2n-1) x (2n-1) expanded grid
(defun unequal-grid-ref (grid n expanded-row expanded-col)
  (let ((width (- (* 2 n) 1)))
    (nth (+ expanded-col (* expanded-row width)) grid)))

;; Parse the (2n-1) x (2n-1) grid to extract:
;; - Value assignments (numbers at positions (2*row, 2*col))
;; - Horizontal inequalities (symbols at positions (2*row, 2*col+1))
;; - Vertical inequalities (symbols at positions (2*row+1, 2*col))
(defun unequal-initial (input-grid n)
  (let ((specs (append
                ;; Value assignments from positions (2*row, 2*col)
                (loop for row below n append
                      (loop for col below n append
                            (let ((cell-val (unequal-grid-ref input-grid n (* 2 row) (* 2 col))))
                              (if (and (not (equal cell-val '_)) (numberp cell-val))
                                  `((= ,(unequal-cell-var n row col) ,cell-val))
                                  nil))))
                ;; Horizontal inequalities at positions (2*row, 2*col+1)
                ;; Between cell (row, col) and cell (row, col+1)
                (loop for row below n append
                      (loop for col below (- n 1) append
                            (let ((ineq-sym (unequal-grid-ref input-grid n (* 2 row) (+ (* 2 col) 1))))
                              (cond
                                ((equal ineq-sym '<)
                                 `((< ,(unequal-cell-var n row col) ,(unequal-cell-var n row (+ col 1)))))
                                ((equal ineq-sym '>)
                                 `((> ,(unequal-cell-var n row col) ,(unequal-cell-var n row (+ col 1)))))
                                (t nil)))))
                ;; Vertical inequalities at positions (2*row+1, 2*col)
                ;; Between cell (row, col) and cell (row+1, col)
                ;; ^ means top < bottom, v means top > bottom
                (loop for row below (- n 1) append
                      (loop for col below n append
                            (let ((ineq-sym (unequal-grid-ref input-grid n (+ (* 2 row) 1) (* 2 col))))
                              (cond
                                ((equal ineq-sym '^)
                                 `((< ,(unequal-cell-var n row col) ,(unequal-cell-var n (+ row 1) col))))
                                ((equal ineq-sym 'v)
                                 `((> ,(unequal-cell-var n row col) ,(unequal-cell-var n (+ row 1) col))))
                                (t nil))))))))
    (if (null specs)
        'true
        `(and ,@specs))))

(defun unequal-var-range (n)
  (cons 'and
        (loop for row below n append
             (loop for col below n append
                   `((and (> ,(unequal-cell-var n row col) 0)
                          (<= ,(unequal-cell-var n row col) ,n)))))))

(defun unequal-all-row-col-different (n)
  (cons 'and
        (append
         (loop for row below n collect
              (cons 'distinct
                    (loop for col below n
                          collect (unequal-cell-var n row col))))
         (loop for col below n collect
              (cons 'distinct
                    (loop for row below n
                          collect (unequal-cell-var n row col)))))))

(defun solve-unequal (n input-grid)
  (let ((var-specs (unequal-var-specs n)))
    (solver-push)
    (z3-assert-fn var-specs (unequal-initial input-grid n))
    (z3-assert-fn var-specs (unequal-var-range n))
    (z3-assert-fn var-specs (unequal-all-row-col-different n))
    (let ((sol (if (equal (check-sat) :UNSAT)
                   'UNSAT
                   (get-model-as-assignment))))
      (solver-pop)
      sol)))

(defun get-unequal-value (soln n row col)
  (cadr (assoc-equal (unequal-cell-var n row col) soln)))

;; Pretty-print an Unequal solution of size n x n, showing inequalities from the original grid.
;; Output format is (2n-1) x (2n-1) with values and inequality symbols.
(defun pretty-print-unequal-solution (soln n &optional input-grid)
  (format t "~%")
  (let ((expanded-size (- (* 2 n) 1)))
    (loop for exp-row below expanded-size
          do (progn
               (loop for exp-col below expanded-size
                     do (cond
                          ;; Value cell at even row/col
                          ((and (evenp exp-row) (evenp exp-col))
                           (let ((val (get-unequal-value soln n (/ exp-row 2) (/ exp-col 2))))
                             (format t "~2D " val)))
                          ;; Horizontal inequality at even row, odd col
                          ((and (evenp exp-row) (oddp exp-col))
                           (let ((sym (if input-grid
                                          (unequal-grid-ref input-grid n exp-row exp-col)
                                          '_)))
                             (format t "~A  " (if (eq sym '_) " " sym))))
                          ;; Vertical inequality at odd row, even col
                          ((and (oddp exp-row) (evenp exp-col))
                           (let ((sym (if input-grid
                                          (unequal-grid-ref input-grid n exp-row exp-col)
                                          '_)))
                             (format t "~A  " (if (eq sym '_) " " sym))))
                          ;; Unused position at odd row, odd col
                          (t (format t "   "))))
               (terpri)))
    (terpri)))

(defun benchmark-solve-unequal (n grid name)
  (format t "~%=== ~A (~Ax~A integer encoding) ===~%" name n n)
  (solver-reset)
  (let ((soln (time (solve-unequal n grid))))
    (if (equal soln 'UNSAT)
        (format t "UNSAT~%")
        (pretty-print-unequal-solution soln n grid))
    (z3::get-solver-stats)))

;; ========================================
;; Example 4x4 Unequal Grid Representation
;;
;; Documentation Generated by Claude
;; ========================================
;;
;; For an n x n Unequal puzzle, we use a (2n-1) x (2n-1) grid:
;; - Value cells at even row/col positions: (2i, 2j)
;; - Horizontal inequalities at: (2i, 2j+1) — between cell (i,j) and (i,j+1)
;; - Vertical inequalities at: (2i+1, 2j) — between cell (i,j) and (i+1,j)
;; - Odd row/odd col positions are unused (use _ as placeholder)
;;
;; Inequality symbols:
;;   Horizontal: < means left < right, > means left > right, _ means no constraint
;;   Vertical:   ^ means top < bottom, v means top > bottom, _ means no constraint
;;
;; Visual layout for a 4x4 grid (represented as 7x7):
;;
;;   V h V h V h V      ; row 0: values at col 0,2,4,6; h-ineq at col 1,3,5
;;   v _ v _ v _ v      ; row 1: v-ineq at col 0,2,4,6; _ at odd cols
;;   V h V h V h V      ; row 2
;;   v _ v _ v _ v      ; row 3
;;   V h V h V h V      ; row 4
;;   v _ v _ v _ v      ; row 5
;;   V h V h V h V      ; row 6

;; Example 4x4 Unequal puzzle (SAT):
;; Solution should be a Latin square with all inequalities satisfied.
(defconstant *unequal-4x4-example*
  '(
;; value h-ineq value  h-ineq  value h-ineq value
    _      <      _      _      _      >      _
;; v-ineq  _   v-ineq    _   v-ineq    _    v-ineq
    ^      _      _      _      v      _      _
    _      _      _      <      _      _      _
    _      _      ^      _      _      _      v
    _      >      _      _      _      <      _
    v      _      _      _      ^      _      _
    _      _      _      _      _      _      _))

;; Example 4x4 Unequal puzzle with some givens (SAT):
(defconstant *unequal-4x4-with-givens*
  '(1      _      _      _      _      _      _
    _      _      _      _      _      _      _
    _      <      _      _      _      >      _
    ^      _      _      _      _      _      v
    _      _      _      _      _      _      _
    _      _      v      _      ^      _      _
    _      _      _      _      _      _      4))

;; Example 4x4 Unequal puzzle (UNSAT - contradictory constraints):
;; Cell (0,0) must be both < cell (0,1) and > cell (0,1)
(defconstant *unequal-4x4-unsat*
  '(1      <      1      _      _      _      _
    _      _      _      _      _      _      _
    _      _      _      _      _      _      _
    _      _      _      _      _      _      _
    _      _      _      _      _      _      _
    _      _      _      _      _      _      _
    _      _      _      _      _      _      _))

;; Run the benchmarks
(benchmark-solve-unequal 4 *unequal-4x4-example* "*unequal-4x4-example*")
(benchmark-solve-unequal 4 *unequal-4x4-with-givens* "*unequal-4x4-with-givens*")
(benchmark-solve-unequal 4 *unequal-4x4-unsat* "*unequal-4x4-unsat*")

;; ==========================
;;            E3
;; ==========================
;;
;; Develop your own solver for arbitrary-size Sudoku puzzles.  Try to
;; beat the Z3 version you wrote. There are a lot of Sudoku-specific
;; reasoning shortcuts you can use and you should think carefully
;; about how to manage search. Compare your solver with the Z3 version
;; on a number of interesting examples.
