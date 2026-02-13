# Measure Function for `if-flat`

## The Problem

The `if-flat` function normalizes if-expressions by flattening nested ifs in the condition position:

```lisp
(if (if d e f) b c)  -->  (if d (if e b c) (if f b c))
```

The challenge: branches `b` and `c` are **duplicated** during this transformation, growing exponentially with nesting depth.

## The Correct Measure

```lisp
(definec m-if-flat (x :if-expr)
  :pos
  (match x
    (:if-atom 1)
    (('if a b c)
     (* (m-if-flat a)
        (+ 1 (m-if-flat b) (m-if-flat c))))))
```

```
m(atom)       = 1
m(if a b c)   = m(a) * (1 + m(b) + m(c))
```

## Why It Works

### Case 1: Condition is an atom

```lisp
(if a b c)  where a is an atom
```

Recurses on `b` and `c`. Since `m(a) = 1`:

```
m(if a b c) = 1 * (1 + m(b) + m(c)) = 1 + m(b) + m(c) > m(b)
```

**Result:** Measure decreases when recursing on branches.

### Case 2: Condition is a nested if

```lisp
(if (if d e f) b c)  -->  (if d (if e b c) (if f b c))
```

Let `B = 1 + m(b) + m(c)`, `E = 1 + m(e) + m(f)`, and `D = m(d)`.

**Before:**

```
m(if d e f) = D * E
m_orig      = m(if d e f) * B = D * E * B
```

**After:**

```
m(if e b c) = m(e) * B
m(if f b c) = m(f) * B
m_new       = D * (1 + m(e)*B + m(f)*B)
            = D * (1 + (m(e) + m(f)) * B)
```

**Difference:**

```
m_orig - m_new = D * E * B - D * (1 + (m(e) + m(f)) * B)
               = D * (E * B - 1 - (m(e) + m(f)) * B)
               = D * ((1 + m(e) + m(f)) * B - 1 - (m(e) + m(f)) * B)
               = D * (B - 1)
```

Since atoms have measure 1, `B = 1 + m(b) + m(c) >= 3`, so `B - 1 >= 2 > 0`.

```
m_orig - m_new = D * (B - 1) >= 1 * 2 = 2 > 0
```

**Result:** Measure strictly decreases!

## Why Other Measures Fail

### Why not `2^(nesting level)`?

Only looks at the condition—ignores branch complexity.

When recursing on branches (Case 1):
- `(if a b c)` with atom `a` has nesting = 0, measure = 1
- But `b` might have nesting = 1, measure = 2

**Problem:** `m(b) > m(if a b c)` — measure increases!

### Why not `m(a) * (m(b) + m(c))` (without the +1)?

For `(if (if d e f) b c)` with all atoms:

```
m_orig = 2 * (1 + 1) = 4
m_new  = 1 * (2 + 2) = 4
```

**Problem:** No decrease!

## Intuition

The measure answers: **"How much total work to flatten everything, accounting for all future duplications?"**

| Term | Meaning |
|------|---------|
| `m(a)` | Number of paths through condition = how many times branches will be duplicated |
| `m(b) + m(c)` | Work to process each branch |
| `+1` | Cost of processing this if-node itself |

The **multiplication** captures: total work = (copies) * (work per copy).

When we flatten `(if (if d e f) b c)`:
- We reduce the condition's complexity (`m(if d e f)` --> `m(d)`)
- We duplicate branches (but only once)
- The **reduced multiplier** outweighs the duplication

## Summary

| Measure | Case 1 (a is atom) | Case 2 (a is if) |
|---------|-------------------|------------------|
| `2^nesting` | Fails | Works |
| `m(a) * (m(b) + m(c))` | Works | No decrease |
| `m(a) * (1 + m(b) + m(c))` | Works | Works |

The +1 is a **technical trick** to ensure strict decrease—it accounts for the "structural work" of removing a nesting level.
