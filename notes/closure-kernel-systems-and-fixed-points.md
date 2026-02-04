# Closure Systems and Least Fixed Points

## Closure Systems

### Definition

A **closure system** (or Moore family) on a set $X$ is a collection $\mathcal{C} \subseteq \mathcal{P}(X)$ such that:

1. **Contains the top:** $X \in \mathcal{C}$
2. **Closed under arbitrary intersections:** $\mathcal{S} \subseteq \mathcal{C} \land \mathcal{S} \neq \emptyset \implies \bigcap \mathcal{S} \in \mathcal{C}$

### Example: Reflexive Relations Form a Closure System

Let $A$ be a set. The family of all reflexive relations on $A$:
$$\mathcal{R} = \{R \subseteq A \times A \mid R \text{ is reflexive on } A\}$$

**Verification:**

1. **Top element:** $A \times A$ is reflexive, so $A \times A \in \mathcal{R}$ ✓

2. **Closed under intersections:** Let $\mathcal{S} \subseteq \mathcal{R}$ be non-empty. For any $a \in A$:
   - For each $R \in \mathcal{S}$: $R$ is reflexive, so $(a, a) \in R$
   - Therefore $(a, a) \in \bigcap \mathcal{S}$
   - So $\bigcap \mathcal{S}$ is reflexive ✓

### Note on Reflexivity

A relation $R$ on $A$ is **reflexive** iff $\forall a \in A.\ (a, a) \in R$.

This means: "every element is related to itself" — it does **NOT** mean "elements can only be related to themselves."

| Relation on $\{1,2\}$ | Reflexive? |
|----------------------|------------|
| $\{(1,1), (2,2)\}$ | ✓ Yes |
| $\{(1,1), (2,2), (1,2)\}$ | ✓ Yes (extra pairs are fine!) |
| $\{(1,1), (1,2)\}$ | ✗ No (missing $(2,2)$) |

---

## Closure Operators

### From Closure System to Closure Operator

Given a closure system $\mathcal{C}$ on $X$, for any set $S \subseteq X$, define its **closure**:
$$\text{cl}(S) = \bigcap \{C \in \mathcal{C} \mid S \subseteq C\}$$

This is well-defined because:
1. **Non-empty intersection:** $X \in \mathcal{C}$ and $S \subseteq X$, so there's always at least one $C$ containing $S$
2. **Result is in $\mathcal{C}$:** Intersection of members of $\mathcal{C}$ is in $\mathcal{C}$
3. **Smallest:** It's the intersection of *all* closed sets containing $S$

### Example: Reflexive Closure

$$\text{refl}(R) = \bigcap \{S \supseteq R \mid S \text{ is reflexive}\} = R \cup \Delta_A$$

where $\Delta_A = \{(a,a) \mid a \in A\}$ is the diagonal relation.

### Properties of Closure Operators

A closure operator $\text{cl}: \mathcal{P}(X) \to \mathcal{P}(X)$ satisfies:
- **Extensive:** $S \subseteq \text{cl}(S)$
- **Monotone:** $S \subseteq T \Rightarrow \text{cl}(S) \subseteq \text{cl}(T)$
- **Idempotent:** $\text{cl}(\text{cl}(S)) = \text{cl}(S)$

### Key Theorems for Closure

```
closure_in_system:  R ⊆ A × A ⟹ closure_system A Ps ⟹ cl(R) ∈ Ps
closure_contains:   R ⊆ A × A ⟹ closure_system A Ps ⟹ R ⊆ cl(R)  
closure_minimal:    R ⊆ S ⟹ S ∈ Ps ⟹ cl(R) ⊆ S
```

---

## Connection to Least Fixed Points

### The Key Insight

A closure operator **is** a least fixed point operator for a specific class of monotone functions.

### Knaster-Tarski Theorem

In a complete lattice, every monotone function $f$ has a least fixed point:
$$\text{lfp}(f) = \bigcap \{x \mid f(x) \leq x\}$$

### The Equivalence

For closure operators:
- The lattice is $(\mathcal{P}(A \times A), \subseteq)$
- $f(X) = R \cup F(X)$ where $F$ captures the closure "rules"
- $\{x \mid f(x) \leq x\} = \{x \mid R \subseteq x \land F(x) \subseteq x\}$
- These are exactly the "closed" sets containing $R$!

### Examples

| Closure | Closure System View | Fixed Point View |
|---------|---------------------|------------------|
| Reflexive | $\bigcap \{T \supseteq R \mid \text{refl}(T)\}$ | $\text{lfp}(\lambda X.\ R \cup \Delta)$ |
| Symmetric | $\bigcap \{T \supseteq R \mid \text{sym}(T)\}$ | $\text{lfp}(\lambda X.\ R \cup X^{-1})$ |
| Transitive | $\bigcap \{T \supseteq R \mid \text{trans}(T)\}$ | $\text{lfp}(\lambda X.\ R \cup X \circ X)$ |

### Transitive Closure Example

**As closure operator:**
$$R^+ = \bigcap \{T \supseteq R \mid T \text{ is transitive}\}$$

**As least fixed point:**
$$R^+ = \text{lfp}(\lambda X.\ R \cup (X \circ X))$$

where $X \circ X = \{(a,c) \mid \exists b.\ (a,b) \in X \land (b,c) \in X\}$

### Perspectives Comparison

| Closure System View | Fixed Point View |
|---------------------|------------------|
| **What:** Intersection of all closed sets containing $R$ | **How:** Iteratively apply rules until stable |
| Declarative / denotational | Operational / computational |
| Good for proving properties | Good for computing/implementing |
| $\bigcap \{C \in \mathcal{C} \mid R \subseteq C\}$ | $R \cup F(R) \cup F(F(R)) \cup \cdots$ |

---

## Non-Closure Systems

Not all properties form closure systems. For example:

- **Irreflexive relations:** Intersection may not be irreflexive
- **Asymmetric relations:** Intersection may not be asymmetric

So there's no "irreflexive closure" or "asymmetric closure."

---

## Dual: Kernel Systems and Greatest Fixed Points

### The Duality

| Closure System | Kernel System (Dual) |
|----------------|----------------------|
| Closed under **intersections** | Closed under **unions** |
| Contains **top** ($X$) | Contains **bottom** ($\emptyset$) |
| **Closure** operator (lfp) | **Interior/Kernel** operator (gfp) |
| $\text{cl}(S) = \bigcap \{C \supseteq S \mid C \in \mathcal{C}\}$ | $\text{int}(S) = \bigcup \{K \subseteq S \mid K \in \mathcal{K}\}$ |
| Smallest closed set **containing** $S$ | Largest kernel set **contained in** $S$ |

### Definition: Kernel System

A **kernel system** (or **interior system**) on $X$ is a collection $\mathcal{K} \subseteq \mathcal{P}(X)$ such that:

1. $\emptyset \in \mathcal{K}$ (contains bottom)
2. Closed under arbitrary **unions**: $\mathcal{S} \subseteq \mathcal{K} \implies \bigcup \mathcal{S} \in \mathcal{K}$

### Interior Operator

Given a kernel system $\mathcal{K}$:
$$\text{int}(S) = \bigcup \{K \in \mathcal{K} \mid K \subseteq S\}$$

This is the **largest** "open" set contained in $S$.

### Properties of Interior Operators

- **Contractive:** $\text{int}(S) \subseteq S$
- **Monotone:** $S \subseteq T \Rightarrow \text{int}(S) \subseteq \text{int}(T)$
- **Idempotent:** $\text{int}(\text{int}(S)) = \text{int}(S)$

(Compare: closure is **extensive**, interior is **contractive**)

### Connection to Greatest Fixed Point

$$\text{int}(S) = \text{gfp}(\lambda X.\ S \cap F(X))$$

where $F$ captures the "interior rules."

### Example: Topology

In topology:
- **Closed sets** form a closure system → **closure** of a set
- **Open sets** form a kernel system → **interior** of a set

$$\text{cl}(S) = \bigcap \{C \supseteq S \mid C \text{ closed}\}$$
$$\text{int}(S) = \bigcup \{U \subseteq S \mid U \text{ open}\}$$

And they're related by complement: $\text{int}(S) = X \setminus \text{cl}(X \setminus S)$

### Fixed Point Duality

| Least Fixed Point (lfp) | Greatest Fixed Point (gfp) |
|-------------------------|---------------------------|
| $\bigcap \{x \mid f(x) \leq x\}$ | $\bigcup \{x \mid x \leq f(x)\}$ |
| Pre-fixed points | Post-fixed points |
| Inductive definitions | Coinductive definitions |
| Finite/terminating | Infinite/non-terminating |
| "Must eventually" | "Can forever" |

### Example: Reachability vs Safety

- **Reachable states** = lfp of "initial ∪ successors" = closure
- **Safe states** = gfp of "goal ∩ predecessors" = interior/kernel

---

## Isabelle/HOL Definitions

```isabelle
definition P_sets :: "'a set ⇒ ('a set ⇒ 'a rel ⇒ bool) ⇒ ('a rel) set" where 
  "P_sets A P = { R ∈ Pow (A × A). P A R }"

definition closure_system :: "'a set ⇒ ('a rel) set ⇒ bool" where 
  "closure_system A Ps = ((A × A) ∈ Ps ∧ (∀ S. S ⊆ Ps ∧ S ≠ {} ⟶ ⋂ S ∈ Ps))" 

definition P_closure :: "'a set ⇒ 'a rel ⇒ ('a rel) set ⇒ 'a rel" where 
  "P_closure A R Ps = ⋂ { P ∈ Ps . R ⊆ P }"
```
