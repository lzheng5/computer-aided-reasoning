# HW3 Solutions

## Ex 11.

**Theorem [Two Relations Case]:** If $R_1$, $R_2$ are well-founded, then $R_{lex}$ on $A \times B$ is well-founded.

**Proof:** Suppose not. Let $(a\_0,b\_0) >\_{lex} (a\_1,b\_1) >\_{lex} \cdots$ be infinite descending.

Since $R_1$ is WF, then $\exists N.\ \forall i \geq N.\ a_i = a_N$.

Then for $i \geq N$: $b\_i >\_{R\_2} b\_{i+1}$, giving an infinite descending chain in $R\_2$. Contradiction. ∎

**Remark:** Consulted AI for proof ideas. And for an alternative direct proof, see [hw3.thy](hw3.thy). 

**Theorem [Lex Order WF]:** If $R_1$, $R_2$, ... $R_n$ are well-founded, then $R_{lex}$ on $A\_1 \times A\_2 \times ... \times A\_n$ is well-founded.

**Proof:** By induction on `n` and the two case lemma ∎

## Ex 12.

**Definition [Dictionary Order]:** Given relations $R_1, \ldots, R_n$ on sets $A_1, \ldots, A_n$, define $<_{dict}$ on $\bigcup\_{k=1}^{n} (A\_1 \times \cdots \times A\_k)$ by:

$$[] <_{dict} (b:bs)$$
$$(a:as) <\_{dict} (b:bs) \iff (a <\_{{R}\_1} b) \lor (a = b \land as <\_{dict'} bs)$$

where $<\_{dict'}$ is the dictionary order on the tail using $R_2, \ldots, R_n$.

**Theorem [Two Relations Case]:** If $R_1$, $R_2$ are well-founded, then $R_{dict}$ for $R_1$ and $R_2$ is well-founded.

**Proof:** Similar to the two relations case for lex ordering. ∎

**Theorem [Dictionary Order WF]:** If $R_1, R_2, \ldots, R_n$ are well-founded, then $R_{dict}$ on $\bigcup\_{k=1}^{n} (A\_1 \times \cdots \times A\_k)$ is well-founded.

**Proof:** Let $(a\_1, a\_2, ..., a\_i)$ and $(a\_1', a\_2', ..., a\_j')$ be in the domain for arbitrary $i$ and $j$, where $i \leq j$.

By induction on $i$ and the two case lemma for the dictionary ordering. ∎

**Remark:** Consulted AI for definitions. 

## Ex 13.

**Theorem:** $f$ defined by well-founded recursion is uniquely defined.

**Proof:** Suppose $f$ and $g$ both satisfy the recursive equation.
  Show $f(x) = g(x)$ for all $x$ by WF induction:
- **IH:** $f(y) = g(y)$ for all $y < x$, then
  
  $$ \lbrace(y, f y) : y \leq x\rbrace = \lbrace(y, g y) : y \leq x\rbrace $$

- Since $f, g$ satisfy the same equation, then
  
  $$f(x) = G(x, \lbrace(y, f y) : y \leq x\rbrace) = G(x, \lbrace(y, g y) : y \leq x\rbrace) = g(x)$$
  ∎

**Remark:** Consulted AI for proof ideas. 

## Lemma 5

**Definition [Transset]:** A set $\alpha$ is a transset if $\forall \beta \in \alpha. \beta \subseteq \alpha$.

Note this is the property given in Definition 3.

**Lemma [Transset iff Pred]:** $\alpha$ is a transset iff $\forall \beta \in \alpha, \beta = s.\beta$.

**Proof:** See `Transset_iff_pred ` in [hw3-ord.thy](hw3-ord.thy).∎

**Lemma [Transset iff Transitive]:** $\alpha$ is a transset iff $\alpha$ is transitive.

**Proof:** See `Transset_iff_trans ` in [hw3-ord.thy](hw3-ord.thy).∎

**Theorem [Ord iff trans and well-ordered]:** $x$ is an ordinal iff $x$ is transitive and well-ordered by $\in$.

**Proof:** By definition of ordinals and above lemmas. ∎

## Lemma 10

**Theorem:** A woset is not isomorphic to any initial segment

**Proof:** Let $\langle S, A \rangle$ be a woset and $x \in S$. We prove the claim by contradiction.

Assume $\langle S, A \rangle \cong \langle pred(x, A), res(A, x) \rangle$, i.e., there is some $f : S \to pred(x, A)$ such that $f$ is bijective and $f$ preserves ordering.
Now consider the set $B = \lbrace y \in S \mid f(y) \neq y\rbrace$.

- Case: $B = \emptyset$. Then $\forall y \in S. f y = y$. But $f x = x \notin pred(x, A)$. Contradiction. 
- Case: $B \neq \emptyset$. Then, $B$ has a least element, $m$. Note
  - Since $m \in S$, we have $f m \in pred(x, A)$ or $f(m) \in S$. [*]  
  - Since $m \in B$, $f m \neq m$. 
    By totality of $A$, we have two other scenarios for $f m$ and $m$. 
    - Case: $mAf(m)$. Since $f$ preserves the ordering and [*], $f(m)Af(f(m))$, and note we can continue to apply $f$, leaving us an infinite decreasing sequence. Contradicting well-foundedness of $A$. 
    - Case: $f(m)Am$. Note $f m \notin B$. Now $f m = m$ since $m$ is the least element in $B$. Then $mAm$. Contradicting the irreflexiveness of $A$. 
 ∎

**Remark:** Consulted AI for proof ideas. 

## Lemma 15

**Proof:** By Exercise 5.2, we have $\forall B \subseteq S. B \neq \emptyset \implies \exists m \in B . \forall b \in B . m \neq b \implies m A b$ [*]. 

Then we get a mapping $f$ from $S$ to some ordinal $\alpha$ by the following construction.

- Let $S\_0 = S$ and instantiate [*] with $S\_0$, we get some $m\_0$ that's the least element in $S\_0$. Let $f(m\_0) = 0$. 
- Next, let $S\_1 = S\_0 - \lbrace m\_0 \rbrace$ and we instantiate [*] with $S\_1$. Then we get some $m\_1$ that's the least in $S\_0$. Let $f(m\_1) = 1$. 
- ...

Since $f$ maps each element of $S$ deterministically, $f$ is a function from $S$ to $\alpha$.
And consequently, the ordinal $\alpha$ is also uniquely determined to be the least ordinal containing the image of $f$.

Next, we show $f$ is bijective.
- $f$ is surjective as it can always map any $\beta \in \alpha$ to $\beta$ itself, which is a woset under $\in$. 
- $f$ is injective, i.e., $\forall m\_i, m\_j \in S.\ f(m\_i) = f(m\_j) \implies m\_i = m\_j$.  
  Let $m\_i, m\_j \in S$ and $f(m\_i) = f(m\_j)$. We prove by contradiction.  
  Suppose $m\_i \neq m\_j$, and WLOG, $m\_i\ A\ m\_j$, as $A$ is total on $S$.  
  By the way we have constructed $f$, $f(m\_i) < f(m\_j)$, contradiction. 

Then, we show $f$ preserves ordering, i.e., $\forall x, y \in S. x A y \iff f(x) \in f(y)$.
  Let $x, y \in S$. 
- Assume $xAy$, then by the construction of $f$, $f(x) < f(y)$, or $f(x) \in f(y)$. 
- Assume $f(x) \in f(y)$, we show the claim by contradiction.    
  Suppose $\lnot xAy$, then either $x = y$ or $y A x$ by totality of $A$.  
  * Case: $x = y$. By injectivity, $f(x) = f(y)$, contradiction.  
  * Case: $y A x$. Then $f(y) \in f(x)$, contradiction. ∎