[← Back](README.md) | [English](01-ordinals.md) | [Japanese](../01-ordinals.md)

# Ordinals and ω₁

Prerequisites: none

This note explains ordinals and $`\omega_1`$. Later notes attach ordinals to the columns of arrays in the proof that expansion terminates ([06 Stable labels and the descent of the height](06-stable-labels.md)). The facts that are used are the regularity in §5 and the enumeration in §6.

## 1. Well-orders and ordinals

**Definition (well-order).** A linear order $`\lt`$ on a set $`X`$ is a **well-order** if every nonempty subset of $`X`$ has a least element.

**Definition (infinite descending sequence).** A sequence $`(x_n)_{n \in \mathbb N}`$ with $`x_0 \gt x_1 \gt x_2 \gt \cdots`$ is an **infinite descending sequence**.

A linear order is a well-order if and only if it has no infinite descending sequence. The direction "no infinite descending sequence implies well-order" uses a weak form of the axiom of choice (dependent choice).

| Order | Well-order? | Reason |
|---|---|---|
| $`(\mathbb N, \lt)`$ | yes | every nonempty subset has a least element |
| $`(\mathbb Z, \lt)`$ | no | $`0 \gt -1 \gt -2 \gt \cdots`$ |
| $`(\mathbb Q_{\ge 0}, \lt)`$ | no | $`1 \gt 1/2 \gt 1/4 \gt \cdots`$ |

**Definition (ordinal).** An **ordinal** is the order type of a well-order. We identify an ordinal $`\alpha`$ with the set $`\{\beta \mid \beta \lt \alpha\}`$ of smaller ordinals.

In increasing order:

```math
0,\ 1,\ 2,\ \ldots,\ \omega,\ \omega+1,\ \omega+2,\ \ldots,\ \omega \cdot 2,\ \ldots,\ \omega^2,\ \ldots
```

- $`\omega`$ is the order type of the natural numbers. $`\omega = \{0, 1, 2, \ldots\}`$.
- The ordinals are well-ordered by $`\lt`$. Every nonempty collection of ordinals has a least element.
- We write $`\mathrm{Ord}`$ for the class of all ordinals.

## 2. Successors and limits

**Definition (successor).** $`\alpha + 1`$ is the ordinal right after $`\alpha`$. An ordinal of the form $`\alpha + 1`$ is a **successor ordinal**.

**Definition (limit ordinal).** An ordinal that is neither 0 nor a successor ordinal is a **limit ordinal**.

| Ordinal | Kind |
|---|---|
| $`0`$ | neither |
| $`5`$, $`\omega+1`$, $`\omega \cdot 2 + 3`$ | successor |
| $`\omega`$, $`\omega \cdot 2`$, $`\omega^2`$ | limit |

**Property.** If $`\alpha`$ is a limit ordinal and $`\beta \lt \alpha`$, then $`\beta + 1 \lt \alpha`$. So above $`\beta`$ there are infinitely many elements below $`\alpha`$.

This property is used in an example of [03 Structures and Σ₁-elementary substructures](03-sigma1-elementary.md).

## 3. Suprema

**Definition (supremum).** The **supremum** $`\sup S`$ of a set $`S`$ of ordinals is the least ordinal that is $`\ge`$ every element of $`S`$.

- If $`S`$ has a largest element, $`\sup S`$ is that element. This is always the case for a nonempty finite set. The supremum of the empty set is $`0`$.
- If $`S`$ has no largest element, $`\sup S`$ is not in $`S`$.

| $`S`$ | $`\sup S`$ |
|---|---|
| $`\{2, 5, 3\}`$ | $`5`$ |
| $`\{0, 1, 2, \ldots\}`$ | $`\omega`$ |
| $`\{\omega, \omega+1, \omega+2, \ldots\}`$ | $`\omega \cdot 2`$ |

To get an ordinal strictly above all $`y_i`$, use $`\sup_{i} (y_i + 1)`$. Indeed $`y_i \lt y_i + 1 \le \sup_i (y_i + 1)`$. The "height of witnesses" defined in [08 Closure and chain below ω₁](08-closure-chain.md) has this form.

## 4. Countability and ω₁

**Definition (countable).** A set $`X`$ is **countable** if $`X`$ is empty or there is a surjection $`\mathbb N \to X`$.

**Definition (countable ordinal).** An ordinal $`\alpha`$ is **countable** if $`\{\beta \mid \beta \lt \alpha\}`$ is countable.

$`0, 1, \omega, \omega+1, \omega \cdot 2, \omega^2, \omega^\omega, \varepsilon_0`$ are all countable.

**Definition (ω₁).** $`\omega_1`$ is the least uncountable ordinal. So the ordinals below $`\omega_1`$ are exactly the countable ordinals.

```math
\alpha \lt \omega_1 \iff \alpha \text{ is countable}
```

Three facts are used.

- $`0 \lt \omega_1`$.
- $`\alpha \lt \omega_1 \implies \alpha + 1 \lt \omega_1`$.
- $`\gamma \lt \omega_1 \implies \{\beta \mid \beta \lt \gamma\}`$ is countable.

Reason for the second: $`\{\beta \mid \beta \lt \alpha + 1\} = \{\beta \mid \beta \lt \alpha\} \cup \{\alpha\}`$, and a countable set with one more point is countable. In other words, $`\omega_1`$ is a limit ordinal.

## 5. Regularity of ω₁

**Theorem (regularity of ω₁).** If $`\alpha_n \lt \omega_1`$ for every $`n \in \mathbb N`$, then

```math
\sup_{n \in \mathbb N} \alpha_n \lt \omega_1
```

The index set need not be $`\mathbb N`$. Any countable index set works.

**Proof.** Let $`\sigma := \sup_n \alpha_n`$. If $`\beta \lt \sigma`$, then $`\beta \lt \alpha_n`$ for some $`n`$. So

```math
\{\beta \mid \beta \lt \sigma\} = \bigcup_{n} \{\beta \mid \beta \lt \alpha_n\}
```

The right side is a countable union of countable sets. The terms with $`\alpha_n = 0`$ add nothing to the union, so drop them. For each remaining $`n`$ choose a surjection $`e_n : \mathbb N \to \alpha_n`$. Then $`(n, t) \mapsto e_n(t)`$ is a surjection from $`\mathbb N \times \mathbb N`$ onto the union. Since $`\mathbb N \times \mathbb N`$ is countable, so is the union. Hence $`\sigma`$ is countable and $`\sigma \lt \omega_1`$. $`\square`$

- Choosing countably many surjections $`e_n`$ at once uses the axiom of choice (countable choice).
- The statement fails for an uncountable index set. For example $`\sup_{\alpha \lt \omega_1} \alpha = \omega_1`$.

## 6. Enumerating a countable ordinal

If $`0 \lt \gamma \lt \omega_1`$, the set $`\{\beta \mid \beta \lt \gamma\}`$ is nonempty and countable, so there is a surjection $`e_\gamma : \mathbb N \to \gamma`$. Choose one with the axiom of choice and call it $`e_\gamma`$. For $`\gamma = 0`$ there is no surjection, so let $`e_0`$ be the function $`\mathbb N \to \mathrm{Ord}`$ whose value is always $`0`$.

**Theorem (enumeration).** If $`\gamma \lt \omega_1`$ and $`a \lt \gamma`$, then $`e_\gamma(t) = a`$ for some $`t \in \mathbb N`$.

With this, finitely many ordinals below $`\gamma`$ can be written as a finite list of natural numbers. These ordinals are later used as parameters of formulas (defined in [03](03-sigma1-elementary.md) §2), so we call them parameters here too.

**Definition (coding parameters).** For a list of natural numbers $`l = (l_0, l_1, \ldots)`$, let $`\mathrm{params}_\gamma(l)(i) := e_\gamma(l_i)`$ (outside the list, read $`l_i := 0`$).

**Theorem (existence of a code).** If $`\gamma \lt \omega_1`$, $`k \in \mathbb N`$ and $`p_0, \ldots, p_{k-1} \lt \gamma`$, then there is a list $`l`$ of natural numbers with $`\mathrm{params}_\gamma(l)(i) = p_i`$ for all $`i \lt k`$.

**Example.** Let $`\gamma = \omega + 1`$, and suppose the chosen enumeration is $`e_\gamma(0) = \omega`$, $`e_\gamma(t+1) = t`$. The parameters $`(3, \omega, 0)`$ are given by $`l = (4, 0, 1)`$.

**Why it is needed.** In [08 Closure and chain below ω₁](08-closure-chain.md) we take a supremum over all formulas (defined in [03](03-sigma1-elementary.md) §2) with parameters below $`\gamma`$. Instead of running over tuples of ordinals, we run over lists $`l`$ of natural numbers. Then the index set is the set of all pairs of a formula and a finite list of natural numbers. This set does not depend on $`\gamma`$ and is countable ([08](08-closure-chain.md)). So the theorem of §5 applies directly.

## 7. Where this repository uses it

| Place | Use |
|---|---|
| [README](../../README-en.md) "The relation R" | the values attached to columns (labels) are ordinals, the order is $`\lt`$ |
| [README](../../README-en.md) "Where the label interface goes" | the order $`\lt`$ of ordinals is a well-order (§1) |
| [notes/01-design.md](../../notes/01-design.md) §3.6, §4.6 (Japanese) | $`\omega_1`$, the enumeration $`e_\gamma`$, closure points ([08](08-closure-chain.md)) lie below $`\omega_1`$ (regularity of §5) |
