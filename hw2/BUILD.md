# Build and Test Instructions for Coq Translation

## Prerequisites

1. **Install Coq**: Version 8.14 or later
   ```bash
   # On Ubuntu/Debian
   sudo apt-get install coq

   # On macOS with Homebrew
   brew install coq

   # On Windows: Download from https://coq.inria.fr/
   ```

2. **Install QuickChick**:
   ```bash
   opam install coq-quickchick
   ```

3. **Install CoqHammer**:
   ```
   opam install coq-hammer
   ```

## Building the Coq File

### Option 1: Interactive Development (Recommended)
Use CoqIDE, VSCode with VSCoq, or Proof General:
```bash
coqide saexpr.v
```

### Option 2: Compile from Command Line
```bash
coqc saexpr.v
```

## Running QuickChick Tests

To run the property-based tests, you need to:

1. Uncomment the QuickChick directives at the bottom of `saexpr.v`:
   ```coq
   QuickChick prop_triple_negation.
   QuickChick prop_minus_as_plus.
   QuickChick prop_distributivity.
   ```

2. Compile and run:
   ```bash
   coqc saexpr.v
   ```

## Example Verification Session

Here's a typical workflow:

1. **Test properties first** (QuickChick finds counterexamples quickly)
2. **Prove verified examples** (the `Example` definitions)
3. **Attempt formal proofs** of properties that passed testing

### Sample Proof Session

```coq
(* After the definitions in saexpr.v *)

(* Prove a simple lemma *)
Lemma lookup_correct : forall v q a,
  lookup v ((v, q) :: a) = q.
Proof.
  intros. simpl.
  rewrite String.eqb_refl.
  reflexivity.
Qed.

(* Prove property 1 formally *)
Theorem triple_negation_correct : forall a,
  prop_triple_negation a = true.
Proof.
  intros a.
  unfold prop_triple_negation.
  simpl.
  (* Continue proof... *)
Admitted.
```

## Known Issues and Limitations

1. **Rational arithmetic in Coq** is more cumbersome than ACL2s
2. **QuickChick generators** may need tuning for better coverage
3. **Structural equality** for inversions needs proper decidable equality
4. **Power function** only handles non-negative integer exponents

## Extending the Translation

To make this more complete, consider:

1. **Add Show instances** for pretty-printing:
   ```coq
   Instance showSaexpr : Show saexpr := { ... }.
   ```

2. **Improve generators** for better test coverage:
   ```coq
   Definition genBalancedSaexpr : G saexpr := ...
   ```

3. **Prove formal theorems** that QuickChick validated:
   ```coq
   Theorem distributivity : forall x y z a,
     (* formal statement *)
   ```

4. **Add Shrinking** for better counterexample minimization:
   ```coq
   Instance shrinkSaexpr : Shrink saexpr := { ... }.
   ```

## Comparison with ACL2s Workflow

| Task | ACL2s | Coq + QuickChick |
|------|-------|------------------|
| Load file | `(include-book "hwk2")` | `coqc saexpr.v` |
| Test property | Automatic in `property` | `QuickChick prop_name` |
| Prove property | Increase rigor level | Write `Theorem` + tactics |
| Counterexamples | Automatic | QuickChick finds them |
| Extract code | ACL2 runtime | `Extraction "file.ml"` |

## Further Reading

- **QuickChick Tutorial**: https://softwarefoundations.cis.upenn.edu/qc-current/
- **Coq QArith**: https://coq.inria.fr/library/Coq.QArith.QArith.html
- **ACL2s Documentation**: https://www.cs.utexas.edu/users/moore/acl2/
