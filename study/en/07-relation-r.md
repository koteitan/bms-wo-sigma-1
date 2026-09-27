[← Back](README.md) | [English](07-relation-r.md) | [Japanese](../07-relation-r.md)

# The relation R

Prerequisites

| Note | Terms used here |
|---|---|
| [01 Ordinals and ω₁](01-ordinals.md) | ordinal, $`\mathrm{Ord}`$ |
| [02 Well-founded relations and recursion](02-well-founded.md) | lexicographic order, well-founded recursion, guarded recursion |
| [03 Structures and Σ₁-elementary substructures](03-sigma1-elementary.md) | height, point, witness, 5-tuples for $`\Sigma_1`$ formulas and the matrix, top, top predicate (§7), visible bits and the way two structures are compared (§8) |
| [04 Patterns of resemblance](04-patterns-of-resemblance.md) | the idea of making top predicates atomic symbols |
| [06 Stable labels and the descent of the height](06-stable-labels.md) | the label interface, the relations $`\mathrm{rel}_k`$, among them strictness and transitivity |

This note explains the definition of the label relation $`R`$ of this repository and the properties that follow directly from it.

## 1. Notation

- $`\mathrm{Ord}`$: all ordinals.
- $`R(k, a, b)`$: layer $`k \in \mathbb N`$, lower point $`a \in \mathrm{Ord}`$, upper point $`b \in \mathrm{Ord}`$. The **layer** $`k`$ corresponds to the index $`k`$ of the label relation $`\mathrm{rel}_k`$ of [06](06-stable-labels.md). $`R`$ is defined in §4. §2 and §3 use $`R`$ in the interpretations of symbols. As §5 explains, this use is not circular.
- Lexicographic order on $`\mathrm{Ord} \times \mathbb N`$: $`(b', j) \lhd (b, k) \iff b' \lt b \lor (b' = b \land j \lt k)`$. It is used in the recursion of §5.

## 2. The language

There are three kinds of symbols.

| Symbol | Arity | Meaning (in the structure of height $`\gamma`$) |
|---|---|---|
| $`\lt`$ | 2 | order of ordinals |
| $`\mathrm{Rel}_j`$ ($`j \in \mathbb N`$) | 2 | $`\mathrm{Rel}_j(x, y) :\iff R(j, x, y)`$ |
| $`\mathrm{Top}_j`$ ($`j \in \mathbb N`$) | 1 | $`\mathrm{Top}_j(x) :\iff R(j, x, \gamma)`$ |

$`\mathrm{Rel}_j`$ relates points to points, and $`\mathrm{Top}_j`$ relates a point to the top $`\gamma`$ (a top predicate) ([03](03-sigma1-elementary.md) §7). $`\gamma`$ itself is not in the domain.

We call the interpretations of the table the **true interpretations**, to distinguish them from the stage interpretations of §5. The true interpretation of the top predicates depends on the height $`\gamma`$.

## 3. The structure of layer k

**Definition (the structure of layer k).** For an ordinal $`\gamma`$, the structure of height $`\gamma`$ and layer $`k`$ is the following. Its domain is $`\{x \mid x \lt \gamma\}`$.

```math
\mathfrak A^{\gamma}_{k} = \bigl(\gamma;\ \lt,\ (\mathrm{Rel}_j)_{j \in \mathbb N},\ (\mathrm{Top}_j)_{j \lt k}\bigr)
```

- $`\mathrm{Rel}_j`$ is present for every layer $`j`$.
- $`\mathrm{Top}_j`$ is present only for $`j \lt k`$. There are no top predicates with $`j \ge k`$.

A **formula of layer $`k`$** is a $`\Sigma_1`$ formula of the language of this structure.

**Visible bits.** The visible bits ([03](03-sigma1-elementary.md) §8) of a formula of layer $`k`$ are the $`\lt`$ bits, the bits of every $`\mathrm{Rel}_j`$, and the bits of $`\mathrm{Top}_j`$ for $`j \lt k`$. The bits of $`\mathrm{Top}_j`$ for $`j \ge k`$ are invisible. Invisible bits are read as false. Whether a bit is visible depends only on the layer number $`j`$, not on the values of the points.

**Example.** At layer 2, consider

```math
\exists y\ \bigl(p_0 \lt y \land \mathrm{Rel}_3(p_0, y) \land \mathrm{Top}_1(y)\bigr)
```

- $`\mathrm{Rel}_3(p_0, y)`$ can be written. $`\mathrm{Rel}_j`$ can be written for every $`j`$.
- $`\mathrm{Top}_1(y)`$ can be written ($`1 \lt 2`$).
- $`\mathrm{Top}_2(y)`$ and $`\mathrm{Top}_3(p_0)`$ cannot be written at this layer (reading them gives false).

## 4. The definition

**Definition (R).**

```math
R(k, a, b) \iff a \lt b \ \land\ \mathfrak A^{a}_{k} \preccurlyeq_{\Sigma_1} \mathfrak A^{b}_{k}
```

Here $`\mathfrak A^{a}_{k} \preccurlyeq_{\Sigma_1} \mathfrak A^{b}_{k}`$ means that for every $`\Sigma_1`$ formula $`\varphi`$ of layer $`k`$ and all parameters $`\vec p \lt a`$,

```math
\mathfrak A^{a}_{k} \models \varphi(\vec p) \iff \mathfrak A^{b}_{k} \models \varphi(\vec p)
```

We write $`\mathrm{Elem}(k, a, b)`$ for this comparison (with the true interpretations). The top predicates of the two structures are different ($`R`$ to $`a`$ and $`R`$ to $`b`$) (Difference 1 of [03](03-sigma1-elementary.md) §8).

## 5. The recursion

The right side reads $`R`$ itself. We use well-founded recursion on the lexicographic order $`\lhd`$ of keys $`(b, k)`$ (§1, [02](02-well-founded.md) §3), defining all $`a`$ at once.

**What the right side reads.** Only three kinds, all with smaller keys. In the table, $`\mathfrak A^{a}`$ and $`\mathfrak A^{b}`$ abbreviate $`\mathfrak A^{a}_{k}`$ and $`\mathfrak A^{b}_{k}`$.

| What is read | Key | Why smaller |
|---|---|---|
| $`\mathrm{Rel}_j(x, y)`$ | $`(y, j)`$ | the points are below the height ($`a`$ or $`b`$), so $`y \lt b`$ |
| a top predicate $`\mathrm{Top}_j(x)`$ of $`\mathfrak A^{a}`$ | $`(a, j)`$ | $`a \lt b`$ |
| a visible top predicate $`\mathrm{Top}_j(x)`$ of $`\mathfrak A^{b}`$ | $`(b, j)`$ | $`j \lt k`$ |

**Guarded recursion.** The value at key $`t = (b, k)`$ is the set of $`a`$ with $`R(k, a, b)`$. It is defined with the following interpretations, used in the one recursion step at key $`t`$. We call them the **stage interpretations**. The superscript $`\mathrm{st}`$ marks a stage interpretation. Each of the three contains, as a guard, the condition that the key is smaller ([02](02-well-founded.md) §5).

| Stage interpretation | Formula |
|---|---|
| $`\mathrm{Rel}^{\mathrm{st}}_j(x, y)`$ | $`y \lt b \land R(j, x, y)`$ |
| $`\mathrm{Top}^{\mathrm{st},a}_j(x)`$ | $`a \lt b \land R(j, x, a)`$ |
| $`\mathrm{Top}^{\mathrm{st},b}_j(x)`$ | $`j \lt k \land R(j, x, b)`$ |

Write $`\mathrm{Elem}^{\mathrm{st}}(k, a, b)`$ for $`\Sigma_1`$-elementarity with the stage interpretations. The stage interpretations read $`R`$ only at smaller keys, so the well-founded recursion of [02](02-well-founded.md) §4 determines $`R`$. The defining equation is the following guarded equation.

```math
R(k, a, b) \iff a \lt b \land \mathrm{Elem}^{\mathrm{st}}(k, a, b)
```

## 6. Removing the guards

**Lemma (removing the guards).** If $`a \lt b`$, then $`\mathrm{Elem}^{\mathrm{st}}(k, a, b) \iff \mathrm{Elem}(k, a, b)`$. That is, $`\Sigma_1`$-elementarity for the stage interpretations is equivalent to $`\Sigma_1`$-elementarity for the true interpretations.

**Proof.** Show that the guards are true on every bit a formula of layer $`k`$ reads.

1. $`\mathrm{Rel}`$ bits: the points are parameters ($`\lt a`$) or witnesses ($`\lt`$ height $`\le b`$). So $`y \lt b`$.
2. Top predicates at height $`a`$: the guard is $`a \lt b`$, which is the assumption.
3. Visible top predicates at height $`b`$: only $`\mathrm{Top}_j`$ with $`j \lt k`$ is visible (§3). The guard is $`j \lt k`$, which is then always true.

Invisible bits are false in both interpretations. So by Lemma 1 of [03](03-sigma1-elementary.md) §8 the atomic diagrams are equal and so are the truth values. $`\square`$

**Theorem (defining equation).**

```math
R(k, a, b) \iff a \lt b \land \mathrm{Elem}(k, a, b)
```

**Proof.** Apply the lemma (removing the guards) under $`a \lt b`$ to the guarded equation of §5. $`\square`$

## 7. Properties that follow directly

**Theorem (strictness).** $`R(k, a, b)`$ implies $`a \lt b`$. This is the first condition on the right side of the defining equation. It is the strictness in the label interface of [06](06-stable-labels.md) ($`\mathrm{rel}_k(a, b) \implies a \lt b`$).

**Theorem (transitivity).** If $`R(k, a, b)`$ and $`R(k, b, c)`$, then $`R(k, a, c)`$. This is the transitivity in the label interface of [06](06-stable-labels.md).

**Proof.** By the defining equation, $`a \lt b`$ and $`b \lt c`$, so $`a \lt c`$. Take a formula $`\varphi`$ of layer $`k`$ and parameters $`\vec p \lt a`$. Since $`\vec p \lt a \lt b`$, both assumptions apply.

```math
\mathfrak A^{a}_{k} \models \varphi(\vec p) \iff \mathfrak A^{b}_{k} \models \varphi(\vec p) \iff \mathfrak A^{c}_{k} \models \varphi(\vec p)
```

The first $`\iff`$ follows from $`R(k, a, b)`$, the second from $`R(k, b, c)`$. So $`\mathrm{Elem}(k, a, c)`$. By the defining equation, $`R(k, a, c)`$. $`\square`$

In this proof the middle structure of the two assumptions is the same $`\mathfrak A^{b}_{k}`$. Both assumptions are at layer $`k`$ and interpret the top predicates as "$`R`$ to $`b`$". So the two equivalences can be chained as they are.

**Property (visible top predicates agree).** Let $`R(k, a, b)`$, $`x \lt a`$ and $`j \lt k`$. Then

```math
R(j, x, a) \iff R(j, x, b)
```

**Reason.** Use the quantifier-free formula $`\mathrm{Top}_j(p_0)`$ with parameter $`x`$. Since $`j \lt k`$, it is a formula of layer $`k`$. At height $`a`$ it means the left side, at height $`b`$ the right side. The proof does not use this property. It uses the theorem (absoluteness of the top predicates) of [09](09-obligations.md), which has a similar form: the top predicates agree between a Good point and $`\omega_1`$.

**Property (the lower point is a limit ordinal).** $`R(k, a, b)`$ implies that $`a`$ is a nonzero limit ordinal.

**Reason.** As in the example of [03](03-sigma1-elementary.md) §5.

- If $`a = 0`$: $`\exists y\ \neg(y \lt y)`$ ($`m = 0`$, $`n = 1`$, $`\mathit{bb} = 1`$, $`\mathit{np} = 0`$, the matrix is the set of complete atomic diagrams with $`[v_0 \lt v_0] = 0`$) is true at height $`b`$ and false at height 0.
- If $`a = \gamma + 1`$: $`\exists y\ (\gamma \lt y)`$ with parameter $`\gamma \lt a`$ is true at height $`b`$ ($`y = \gamma + 1 \lt b`$) and false at height $`a`$.

Both contradict $`\mathrm{Elem}`$. The combinatorial layer does not use this property.

## 8. Properties that are not used

The proof does not use the following two properties.

- Monotonicity in the layer: if $`j \le k`$ and $`R(k, a, b)`$, then $`R(j, a, b)`$. A formula of layer $`j`$ is also a formula of layer $`k`$, and the two layers interpret the visible symbols in the same way, so this holds.
- Locality: $`R`$ with top $`\le \delta`$ is determined by the recursion at keys smaller than $`(\delta + 1, 0)`$. This is expected to hold but is not proved here.

## 9. Where this repository uses it

| Place | Use |
|---|---|
| [README](../../README-en.md) "The relation R" | the defining equation and the three kinds of reads in the recursion |
| [README](../../README-en.md) "Where the label interface goes" | strictness and transitivity follow from the two theorems of §7 |
| [notes/01-design.md](../../notes/01-design.md) §3.3, §3.4, §4.1, §4.3, §4.4 (Japanese) | definition of the relation R, recursion, defining equation, strictness, transitivity |
