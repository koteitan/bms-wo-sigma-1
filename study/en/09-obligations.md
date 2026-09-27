[← Back](README.md) | [English](09-obligations.md) | [Japanese](../09-obligations.md)

# Proofs of the label interface and the final theorems

Prerequisites

| Note | Terms used here |
|---|---|
| [01 Ordinals and ω₁](01-ordinals.md) | $`\lt`$ on ordinals is a well-order, there is no infinite descending sequence (§1), $`\omega_1`$ |
| [02 Well-founded relations and well-founded recursion](02-well-founded.md) | well-founded, well-founded induction (§1, §2) |
| [03 Structures and Σ₁-elementary substructures](03-sigma1-elementary.md) | atomic diagram, bit (§3), 5-tuples for $`\Sigma_1`$ formulas and the matrix (§7), visible bits and Lemma 2 on setting invisible bits to false (§8) |
| [05 The Bashicu Matrix System](05-bms.md) | array with $`r`$ rows, column, parent, ancestor, expansion $`A[N]`$, the empty array $`()`$, expansion sequence, one-step expansion $`\triangleleft`$, $`E_r`$, BM4 |
| [06 Stable labels and the descent of the height](06-stable-labels.md) | the label interface, $`\mathrm{rel}_k`$, finite reflection, stable label, height $`\mathrm{ht}`$, DH's Proposition 19.1 (descent of the height) |
| [07 The relation R](07-relation-r.md) | $`R(k, a, b)`$, layer, the structure $`\mathfrak A^{\gamma}_{k}`$ of layer $`k`$, formula of layer $`k`$, $`\mathrm{Rel}_j`$, $`\mathrm{Top}_j`$, $`\mathrm{Elem}`$, the defining equation, the theorems of strictness and transitivity (§7) |
| [08 Closure below ω₁ and the chain](08-closure-chain.md) | $`\mathfrak B`$, $`\mathfrak B{\restriction}\gamma`$, Good, closure point, the chain $`c_t`$ and Properties 9–11 |

This note explains how the relation $`R`$ satisfies the label interface. Then it gives every array a stable label and derives the final theorems. The main parts are finite reflection (§3) and the labels given by the chain (§4–§6).

## 1. List of the conditions

Fix the number of rows $`r \in \mathbb N`$. The labels are the ordinals, and the order on labels is $`\lt`$ on ordinals. The relations are $`\mathrm{rel}_k(a, b) :\iff R(k, a, b)`$.

| Condition ([06](06-stable-labels.md)) | Content | Section |
|---|---|---|
| well-order | $`\lt`$ on labels is a well-order | §2 |
| strictness | $`R(k, a, b) \implies a \lt b`$ | §2 |
| transitivity | $`R(k, a, b) \land R(k, b, c) \implies R(k, a, c)`$ | §2 |
| finite reflection | from $`n \lt r`$ and $`R(n, \alpha, \beta)`$, move finitely many points of $`[\alpha, \beta)`$ below $`\alpha`$ | §3 |

Besides the conditions, the final theorems need a stable label on the first array. It is built in §4–§6.

## 2. Well-order, strictness, transitivity

- Well-order: $`\lt`$ on ordinals is a well-order ([01](01-ordinals.md) §1).
- Strictness: the theorem (strictness) of [07](07-relation-r.md) §7. It is the first condition on the right side of the defining equation.
- Transitivity: the theorem (transitivity) of [07](07-relation-r.md) §7. It joins two $`\Sigma_1`$-elementarity steps through the same middle structure $`\mathfrak A^{b}_{k}`$.

## 3. Finite reflection

**Goal.** Assume the following.

- $`n \lt r`$ and $`R(n, \alpha, \beta)`$.
- $`X`$ is a finite set of ordinals, and every element of $`X`$ is $`\lt \alpha`$.
- $`s \gt 0`$ and $`\alpha \le y_0 \lt y_1 \lt \cdots \lt y_{s-1} \lt \beta`$.

Then build $`y'_0 \lt y'_1 \lt \cdots \lt y'_{s-1} \lt \alpha`$ that satisfy the following four. Here $`x \in X`$, $`i, j \lt s`$, $`k \lt r`$ and $`m \lt n`$.

- (a) $`x \lt y'_0`$.
- (b) $`R(k, x, y_i) \implies R(k, x, y'_i)`$.
- (c) $`R(k, y_i, y_j) \implies R(k, y'_i, y'_j)`$.
- (d) $`R(m, y_i, \beta) \implies R(m, y'_i, \alpha)`$.

**Proof.**

1. List the elements of $`X`$ as $`x_0, \ldots, x_{|X|-1}`$. $`|X|`$ is the number of elements of $`X`$. The order of the list does not matter.
2. Let the list of variables be $`z = (x_0, \ldots, x_{|X|-1}, y_0, \ldots, y_{s-1})`$. Its length is $`|X| + s`$.
3. Let $`d`$ be the atomic diagram of $`z`$ in the structure $`\mathfrak A^{\beta}_{n}`$ of layer $`n`$ and height $`\beta`$. The bound on symbols is $`r`$. $`d`$ consists of the following bits, for $`i, j \lt |X| + s`$.
   - The order bits $`[z_i \lt z_j]`$.
   - The $`\mathrm{Rel}_k`$ bits $`[R(k, z_i, z_j)]`$ ($`k \lt r`$).
   - The $`\mathrm{Top}_m`$ bits $`[R(m, z_i, \beta)]`$ ($`m \lt n`$). Since $`m \lt n \lt r`$, they fit in the bound on symbols $`r`$. The $`\mathrm{Top}_m`$ bits with $`n \le m \lt r`$ are invisible at layer $`n`$, so they are false.
4. Build the following $`\Sigma_1`$ formula $`\Phi`$. The parameters are $`x_0, \ldots, x_{|X|-1}`$ and the witnesses are $`y_0, \ldots, y_{s-1}`$.

```math
\Phi(x_0, \ldots, x_{|X|-1}) :\equiv \exists y_0 \cdots \exists y_{s-1}\ \ \mathrm{diag}(x_0, \ldots, x_{|X|-1}, y_0, \ldots, y_{s-1}) \in \{d\}
```

5. $`\Phi`$ is a formula of layer $`n`$. As a 5-tuple of [03](03-sigma1-elementary.md) §7, the bound on symbols is $`r`$, the number of variables is $`|X| + s`$, the matrix is $`\{d\}`$, the number of witnesses is $`s`$ and the number of parameters is $`|X|`$. The matrix has only one atomic diagram. So $`\Phi`$ says "there are witnesses whose whole atomic diagram equals $`d`$".
6. $`\Phi`$ is true at height $`\beta`$. The witnesses are $`y_0, \ldots, y_{s-1}`$ themselves, and all are $`\lt \beta`$. Their atomic diagram is $`d`$ by the definition in step 3.
7. By the defining equation ([07](07-relation-r.md)), $`\mathrm{Elem}(n, \alpha, \beta)`$. The parameters $`x_0, \ldots, x_{|X|-1}`$ are all $`\lt \alpha`$. So $`\Phi`$ is also true at height $`\alpha`$. Let $`y'_0, \ldots, y'_{s-1}`$ be its witnesses. All are $`\lt \alpha`$. The atomic diagram of $`(x_0, \ldots, x_{|X|-1}, y'_0, \ldots, y'_{s-1})`$ in the structure $`\mathfrak A^{\alpha}_{n}`$ of height $`\alpha`$ is $`d`$.
8. The two atomic diagrams are equal, so each bit about $`y`$ carries over to $`y'`$.
   - Order bits: for $`i \lt j`$, $`y_i \lt y_j`$, so $`y'_i \lt y'_j`$. Since $`x \lt \alpha \le y_0`$, $`x \lt y'_0`$. The latter is (a).
   - $`\mathrm{Rel}_k`$ bits: $`\mathrm{Rel}_k`$ is $`R(k, \cdot, \cdot)`$ at every height. So $`R(k, x, y_i) \iff R(k, x, y'_i)`$ and $`R(k, y_i, y_j) \iff R(k, y'_i, y'_j)`$. These are (b) and (c).
   - $`\mathrm{Top}_m`$ bits: at height $`\beta`$, $`\mathrm{Top}_m(y_i)`$ is $`R(m, y_i, \beta)`$. At height $`\alpha`$, $`\mathrm{Top}_m(y'_i)`$ is $`R(m, y'_i, \alpha)`$. So $`R(m, y_i, \beta) \iff R(m, y'_i, \alpha)`$. This is (d). $`\square`$

**Remarks.**

- The proof gives (b)–(d) as equivalences. The conditions ask only for the direction $`\implies`$.
- $`\Phi`$ also contains the false bits. So relations that do not hold also carry over to $`y'`$.
- (d) moves a relation to $`\beta`$ to a relation to $`\alpha`$. Since the top predicate $`\mathrm{Top}_m`$ is a symbol of the language, one $`\Sigma_1`$ formula can say this ([04](04-patterns-of-resemblance.md) §5).
- Not used: that $`\alpha`$ or $`\beta`$ is a limit ordinal, that they are closure points.

**Example (written by hand, shape only).** Let $`r = 2`$, $`n = 1`$, $`X = \{x_0\}`$ ($`|X| = 1`$) and $`s = 2`$. Then $`z = (x_0, y_0, y_1)`$. Assume that the true bits at height $`\beta`$ are only the following six. These six were chosen so that they do not break transitivity.

```math
x_0 \lt y_0,\quad x_0 \lt y_1,\quad y_0 \lt y_1,\quad R(0, x_0, y_0),\quad R(1, x_0, y_0),\quad R(0, y_1, \beta)
```

Then $`\Phi`$ has the following form.

```math
\exists y_0\ \exists y_1\ \bigl[\ x_0 \lt y_0 \land x_0 \lt y_1 \land y_0 \lt y_1 \land \mathrm{Rel}_0(x_0, y_0) \land \mathrm{Rel}_1(x_0, y_0) \land \mathrm{Top}_0(y_1) \land \Psi\ \bigr]
```

$`\Psi`$ is the conjunction of the negations of all other bits (for example $`\mathrm{Rel}_0(y_0, y_1)`$, $`\mathrm{Top}_0(y_0)`$, $`y_1 \lt y_0`$). Reflection gives $`y'_0, y'_1`$ with $`x_0 \lt y'_0 \lt y'_1 \lt \alpha`$ that satisfy the following.

```math
R(0, x_0, y'_0),\quad R(1, x_0, y'_0),\quad R(0, y'_1, \alpha),\quad \neg R(0, y'_0, y'_1),\quad \neg R(0, y'_0, \alpha)
```

## 4. Absoluteness of the top predicates

**Theorem (absoluteness of the top predicates).** Let $`\mathrm{Good}(\delta)`$ and $`\delta \lt \omega_1`$. For every $`j \in \mathbb N`$ and $`x \lt \delta`$,

```math
R(j, x, \delta) \iff R(j, x, \omega_1)
```

**Proof.** Well-founded induction on $`j`$ with $`\lt`$ on natural numbers ([02](02-well-founded.md) §2).

1. Open both sides with the defining equation ([07](07-relation-r.md)). Both $`x \lt \delta`$ and $`x \lt \omega_1`$ hold. What remains is that every formula $`\psi`$ of layer $`j`$ (parameters $`\lt x`$) has the same truth value at height $`\delta`$ and at height $`\omega_1`$.
2. The top-predicate bits that $`\psi`$ reads at height $`\delta`$ are $`\mathrm{Top}_i(u)`$ ($`i \lt j`$, $`u \lt \delta`$). Its meaning is $`R(i, u, \delta)`$. By the induction hypothesis, this is equivalent to $`R(i, u, \omega_1)`$.
3. So $`\mathfrak A^{\delta}_{j}`$ agrees with $`\mathfrak B{\restriction}\delta`$ on visible bits. With Lemma 2 of [03](03-sigma1-elementary.md) §8, translate $`\psi`$ into the all-symbol formula $`\psi^*`$ whose invisible bits are set to false.
4. By $`\mathrm{Good}(\delta)`$, $`\mathfrak B{\restriction}\delta \models \psi^* \iff \mathfrak B \models \psi^*`$.
5. $`\mathfrak A^{\omega_1}_{j}`$ is $`\mathfrak B`$ with the top predicates of $`i \ge j`$ made invisible. Translating back with Lemma 2 gives the truth value in $`\mathfrak A^{\omega_1}_{j}`$. $`\square`$

In summary, for parameters $`\vec p \lt x`$ the proof chains these equivalences.

```math
\mathfrak A^{\delta}_{j} \models \psi(\vec p) \iff \mathfrak B{\restriction}\delta \models \psi^*(\vec p) \iff \mathfrak B \models \psi^*(\vec p) \iff \mathfrak A^{\omega_1}_{j} \models \psi(\vec p)
```

Step 2 uses "visibility depends only on the layer number" ([03](03-sigma1-elementary.md) §8). So the induction only needs to run over the layer $`j`$.

## 5. Two points of the chain are related by R

**Theorem (two points of the chain are related by R).** For natural numbers $`i \lt j`$ and every layer $`k \in \mathbb N`$, $`R(k, c_i, c_j)`$.

**Proof.** By Property 10 of [08](08-closure-chain.md) §7, $`c_i \lt c_j`$. For a formula $`\psi`$ of layer $`k`$ and parameters $`\vec p \lt c_i`$, chain these equivalences.

```math
\mathfrak A^{c_i}_{k} \models \psi \iff \mathfrak B{\restriction}c_i \models \psi^* \iff \mathfrak B \models \psi^* \iff \mathfrak B{\restriction}c_j \models \psi^* \iff \mathfrak A^{c_j}_{k} \models \psi
```

The first and fourth use the theorem of §4 (at $`c_i`$ and at $`c_j`$) and Lemma 2 of [03](03-sigma1-elementary.md) §8. The hypotheses of the theorem of §4 are Properties 9 and 11 of [08](08-closure-chain.md) §7. The second and third are $`\mathrm{Good}(c_i)`$ and $`\mathrm{Good}(c_j)`$ ($`\vec p \lt c_i \lt c_j`$). So $`\mathrm{Elem}(k, c_i, c_j)`$, and by the defining equation $`R(k, c_i, c_j)`$. $`\square`$

## 6. A stable label on every array

**Theorem (a stable label on every array).** Let $`r \in \mathbb N`$ and let $`A`$ be any array with $`r`$ rows. Then $`f(t) := c_t`$ ($`t \in \mathbb N`$) is a stable label on $`A`$.

**Proof.** Check the two conditions of a stable label ([06](06-stable-labels.md)).

- $`f`$ is strictly increasing (Property 10 of [08](08-closure-chain.md) §7).
- Let $`k \lt r`$ and let column $`i`$ be a $`k`$-ancestor of column $`j`$. An ancestor lies to the left, so $`i \lt j`$. By the theorem of §5, $`R(k, c_i, c_j)`$. $`\square`$

$`f`$ depends neither on $`A`$ nor on $`r`$. $`f`$ does not look at the entries of the array. Any two columns $`i \lt j`$ are related by $`R`$ at every layer. This is more than a stable label asks for. So every array gets a label, not only the arrays obtained from $`E_r`$ by expansion.

**Example (computed by computer).** Let $`r = 2`$ and $`A = (0,0)(2,1)(1,1)`$. The parents and ancestors were computed by a small Python program.

| Row | Parent of column 1 | Parent of column 2 | Ancestor pairs |
|---|---|---|---|
| 0 | column 0 | column 0 | (0, 1), (0, 2) |
| 1 | column 0 | column 0 | (0, 1), (0, 2) |

A pair $`(i, j)`$ means "column $`i`$ is an ancestor of column $`j`$". A stable label asks for $`c_0 \lt c_1 \lt c_2`$ and the following four.

```math
R(0, c_0, c_1),\quad R(0, c_0, c_2),\quad R(1, c_0, c_1),\quad R(1, c_0, c_2)
```

All follow from the theorem of §5. The theorem of §5 also gives $`R(0, c_1, c_2)`$ and $`R(1, c_1, c_2)`$, but this array does not ask for them.

## 7. The final theorems

For an array $`A`$ with $`r`$ rows and a function $`n : \mathbb N \to \mathbb N`$, define the expansion sequence ([05](05-bms.md) §7) by

```math
A^{(0)} = A, \qquad A^{(t+1)} = A^{(t)}[n(t)]
```

$`()`$ denotes the empty array (the array of length 0; [05](05-bms.md) §1).

**Theorem 1 (termination).** For every $`r \in \mathbb N`$, every array $`A`$ with $`r`$ rows and every $`n : \mathbb N \to \mathbb N`$,

```math
\exists T \in \mathbb N\ \ A^{(T)} = ()
```

**Proof.** Assume that no $`A^{(t)}`$ is empty. Choose, by recursion on $`t`$, a stable label $`g_t`$ on $`A^{(t)}`$.

- $`g_0(i) := c_i`$ (§6).
- If $`g_t`$ is a stable label on $`A^{(t)}`$, then by DH's Proposition 19.1 ([06](06-stable-labels.md)) there is a stable label $`g_{t+1}`$ on $`A^{(t+1)}`$ with $`\mathrm{ht}(g_{t+1}) \lt \mathrm{ht}(g_t)`$. Choose one with the axiom of choice. Proposition 19.1 uses that $`A^{(t)}`$ and $`A^{(t+1)}`$ are nonempty, and the label interface of §2 and §3.

This gives the following infinite descending sequence of ordinals.

```math
\mathrm{ht}(g_0) \gt \mathrm{ht}(g_1) \gt \mathrm{ht}(g_2) \gt \cdots
```

This contradicts [01](01-ordinals.md) §1. $`\square`$

**Theorem 2 (well-foundedness on all arrays).** Define the relation $`\triangleleft_r`$ on all arrays with $`r`$ rows by the following formula. It is the one-step expansion $`\triangleleft`$ of [05](05-bms.md) §7, with the row count written as a subscript.

```math
A \triangleleft_r B :\iff B \ne () \land \exists N \in \mathbb N\ \ A = B[N]
```

$`\triangleleft_r`$ is well-founded.

**Proof.** Assume that there is an infinite descending sequence $`C_0 \triangleright_r C_1 \triangleright_r \cdots`$ of $`\triangleleft_r`$. Then $`C_{t+1} = C_t[N_t]`$, and no $`C_t`$ is empty. This contradicts Theorem 1 (with $`A = C_0`$ and $`n(t) = N_t`$). $`\square`$

**Theorem 3 (well-foundedness on the $`r`$-row part of BM4).** Let $`\mathrm{BM4}_r`$ be the set of arrays obtained from $`E_r = (0, \ldots, 0)(1, \ldots, 1)`$ by finitely many expansions. The restriction of $`\triangleleft_r`$ to $`\mathrm{BM4}_r`$ is well-founded.

**Proof.** The restriction of a well-founded relation to a subset is well-founded. It follows from Theorem 2. $`\square`$

**Theorem 4 (well-foundedness on all of BM4).** Let BM4 be the set of pairs $`(r, A)`$ of a number of rows $`r`$ and $`A \in \mathrm{BM4}_r`$. Define the relation by

```math
(r', A) \triangleleft (r, B) :\iff r' = r \land A \triangleleft_r B
```

$`\triangleleft`$ is well-founded on BM4.

**Proof.** Expansion does not change the number of rows. So an infinite descending sequence of $`\triangleleft`$ lies in a single $`\mathrm{BM4}_r`$. This contradicts Theorem 3. $`\square`$

**Strength.** The proof uses the axiom of choice and the regularity of $`\omega_1`$. The labels are closure points below $`\omega_1`$ whose values are not known. No ordinal bound or notation system is obtained. It uses neither the constructible universe $`L`$ nor admissible ordinals. The only model-theoretic notion it uses is $`\Sigma_1`$-elementarity.

## 8. Where this repository uses it

| Place | Use |
|---|---|
| [README](../../README-en.md) "Where the label interface goes" | the table of the conditions and the summary of finite reflection and the labels on all arrays |
| [README](../../README-en.md) "What is proved" | the four final theorems (§7) |
| [notes/01-design.md](../../notes/01-design.md) §4.5, §4.7, §4.8, §4.9 (Japanese) | the proof of each condition, the absoluteness of the top predicates, the chain, the final theorems |
