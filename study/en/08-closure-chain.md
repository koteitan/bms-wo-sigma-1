[← Back](README.md) | [English](08-closure-chain.md) | [Japanese](../08-closure-chain.md)

# Closure below ω₁ and the chain

Prerequisites

| Note | Terms used here |
|---|---|
| [01 Ordinals and ω₁](01-ordinals.md) | $`\omega_1`$, regularity, the enumeration $`e_\gamma`$, coding parameters $`\mathrm{params}_\gamma`$ |
| [03 Structures and Σ₁-elementary substructures](03-sigma1-elementary.md) | witness, Tarski–Vaught test, 5-tuples for $`\Sigma_1`$ formulas and the matrix, complete atomic diagram (§7), visible bits (§8) |
| [07 The relation R](07-relation-r.md) | $`R`$, layer, the symbols $`\mathrm{Rel}_j`$, $`\mathrm{Top}_j`$ and their true interpretations |

This note explains how to build points below $`\omega_1`$ that are closed under $`\Sigma_1`$ witnesses. The idea is the one of the Löwenheim–Skolem theorem: add witnesses and take the supremum. The chain of these points gives the labels in [09](09-obligations.md).

## 1. The ambient structure and Good

**Definition (ambient structure).** Let $`\mathfrak B`$ be the structure of height $`\omega_1`$ with all symbols.

```math
\mathfrak B = \bigl(\omega_1;\ \lt,\ (\mathrm{Rel}_j)_{j \in \mathbb N},\ (\mathrm{Top}^{\omega_1}_j)_{j \in \mathbb N}\bigr), \qquad \mathrm{Top}^{\omega_1}_j(x) :\iff R(j, x, \omega_1)
```

It has the top predicates of every layer. All bits are visible ([03](03-sigma1-elementary.md) §8).

**Definition (Good).** For an ordinal $`\gamma \le \omega_1`$, let $`\mathfrak B{\restriction}\gamma`$ be $`\mathfrak B`$ with its domain restricted to $`\{x \mid x \lt \gamma\}`$. The top predicates remain those toward $`\omega_1`$.

```math
\mathrm{Good}(\gamma) :\iff \mathfrak B{\restriction}\gamma \preccurlyeq_{\Sigma_1} \mathfrak B
```

That is, $`\mathfrak B{\restriction}\gamma \models \varphi(\vec p) \iff \mathfrak B \models \varphi(\vec p)`$ for every $`\Sigma_1`$ formula $`\varphi`$ and all $`\vec p \lt \gamma`$.

$`\mathfrak B{\restriction}\gamma`$ is a genuine substructure of $`\mathfrak B`$ (same interpretations, smaller domain). So the Tarski–Vaught test of [03](03-sigma1-elementary.md) §6 applies directly.

## 2. There are countably many formulas

**Definition (the set of formulas).** Let $`\mathcal F`$ be the set of all 5-tuples $`(m, n, D, \mathit{bb}, \mathit{np})`$ of [03](03-sigma1-elementary.md) §7. $`D`$ is a subset of the set of complete atomic diagrams determined by $`m, n`$.

**Why it is countable.** Once $`m, n`$ are fixed, there are only finitely many complete atomic diagrams ([03](03-sigma1-elementary.md) §3, §7), so there are finitely many subsets $`D`$. $`m, n, \mathit{bb}, \mathit{np}`$ are natural numbers. So $`\mathcal F`$ is countable. The set $`\mathbb N^{\lt\omega}`$ of finite lists of natural numbers is countable too, so $`\mathcal F \times \mathbb N^{\lt\omega}`$ is countable.

This is why a formula uses finitely many symbols (bound $`m`$). If formulas could use infinitely many symbols, the set of all formulas would not be countable.

## 3. Height of witnesses

**Definition (height of witnesses).** For a formula $`\varphi = (m, n, D, \mathit{bb}, \mathit{np}) \in \mathcal F`$ and a list $`\vec p`$ of parameters below $`\omega_1`$ ($`\varphi`$ reads the first $`\mathit{np}`$ of them, $`p_0, \ldots, p_{\mathit{np}-1}`$):

- if $`\mathfrak B \models \varphi(\vec p)`$, choose one tuple of witnesses $`y_0, \ldots, y_{\mathit{bb}-1} \lt \omega_1`$ with the axiom of choice and let $`h(\varphi, \vec p) := \sup_{i \lt \mathit{bb}} (y_i + 1)`$;
- otherwise let $`h(\varphi, \vec p) := 0`$.

**Theorem (the height of witnesses is below ω₁).** $`h(\varphi, \vec p) \lt \omega_1`$.

**Proof.** It is the maximum of finitely many $`y_i + 1`$, each below $`\omega_1`$ ([01](01-ordinals.md) §4). $`\square`$

All chosen witnesses lie below $`h(\varphi, \vec p)`$.

## 4. One closure step

**Definition (one closure step).**

```math
\mathrm{next}(\gamma) := \max\Bigl(\gamma,\ \sup_{(\varphi, l)} h\bigl(\varphi, \mathrm{params}_\gamma(l)\bigr)\Bigr) + 1
```

The supremum runs over all $`(\varphi, l) \in \mathcal F \times \mathbb N^{\lt\omega}`$. $`\mathrm{params}_\gamma(l)`$ is the parameter tuple coded by a list of natural numbers, as in [01](01-ordinals.md) §6.

| Property | Statement | Reason |
|---|---|---|
| Property 1 | $`\gamma \lt \mathrm{next}(\gamma)`$ | the $`+1`$ |
| Property 2 | $`\gamma \lt \omega_1 \implies \mathrm{next}(\gamma) \lt \omega_1`$ | supremum of countably many ([01](01-ordinals.md) §5) |
| Property 3 | if $`\gamma \lt \omega_1`$, $`\vec p \lt \gamma`$ and $`\mathfrak B \models \varphi(\vec p)`$, then witnesses can be taken below $`\mathrm{next}(\gamma)`$ | proof below |

**Proof of Property 3.** By the theorem (existence of a code) of [01](01-ordinals.md) §6 there is a list $`l`$ with $`\vec p = \mathrm{params}_\gamma(l)`$. The witnesses chosen for $`(\varphi, l)`$ lie below $`h(\varphi, \mathrm{params}_\gamma(l))`$. This is one of the terms of the supremum, so they lie below $`\mathrm{next}(\gamma)`$. $`\square`$

## 5. λ

**Definition (λ).**

```math
\mathrm{next}^0(\gamma) := \gamma, \quad \mathrm{next}^{t+1}(\gamma) := \mathrm{next}\bigl(\mathrm{next}^t(\gamma)\bigr), \qquad \lambda(\gamma) := \sup_{t \in \mathbb N} \mathrm{next}^t(\gamma)
```

Here $`t \in \mathbb N`$. An ordinal of the form $`\lambda(\gamma)`$ is called a **closure point**.

| Property | Statement |
|---|---|
| Property 4 | $`\gamma \lt \omega_1 \implies \mathrm{next}^t(\gamma) \lt \omega_1`$ |
| Property 5 | $`t \le t' \implies \mathrm{next}^t(\gamma) \le \mathrm{next}^{t'}(\gamma)`$ |
| Property 6 | $`\gamma \lt \omega_1 \implies \lambda(\gamma) \lt \omega_1`$ (supremum of countably many) |
| Property 7 | $`\gamma \lt \lambda(\gamma)`$ |
| Property 8 | if $`k \in \mathbb N`$ and $`p_0, \ldots, p_{k-1} \lt \lambda(\gamma)`$, then all are $`\lt \mathrm{next}^t(\gamma)`$ for some $`t`$ |

Property 8 is proved by induction on $`k`$. Each $`p_i`$ is below the supremum, so $`p_i \lt \mathrm{next}^{t_i}(\gamma)`$ for some $`t_i`$. Take $`t := \max_i t_i`$.

## 6. λ(γ) is Good

**Theorem (λ(γ) is Good).** If $`\gamma \lt \omega_1`$, then $`\mathrm{Good}(\lambda(\gamma))`$.

**Proof.** In the form of the Tarski–Vaught test ([03](03-sigma1-elementary.md) §6). Let $`\vec p \lt \lambda(\gamma)`$.

- $`\Rightarrow`$: witnesses below $`\lambda(\gamma)`$ are also witnesses below $`\omega_1`$ (Property 6). The matrix is evaluated in the same way.
- $`\Leftarrow`$: by Property 8, $`\vec p \lt \mathrm{next}^t(\gamma)`$ for some $`t`$. Applying Property 3 at $`\mathrm{next}^t(\gamma)`$, the witnesses can be taken below $`\mathrm{next}^{t+1}(\gamma) \le \lambda(\gamma)`$. $`\square`$

**Example (only the shape).** Let $`\gamma = 0`$. $`\lambda(0)`$ contains witnesses of every true $`\Sigma_1`$ statement of $`\mathfrak B`$ whose parameters lie below $`\lambda(0)`$. The actual value of $`\lambda(0)`$ is not known. The proof never uses the value, only $`\lambda(0) \lt \omega_1`$ and $`\mathrm{Good}(\lambda(0))`$.

**About the set of Good points.** We neither show nor use that the set of Good points is closed in $`\omega_1`$. That is why it is not called a club (closed unbounded set).

## 7. The chain

**Definition (the chain).**

```math
c_0 := \lambda(0), \qquad c_{t+1} := \lambda(c_t)
```

| Property | Statement |
|---|---|
| Property 9 | $`c_t \lt \omega_1`$ |
| Property 10 | $`c_0 \lt c_1 \lt c_2 \lt \cdots`$ |
| Property 11 | $`\mathrm{Good}(c_t)`$ |

All follow from §5 and §6 by induction on $`t`$.

Any two points of this chain are related by $`R`$ at every layer. That is, if $`i \lt j`$, then $`R(k, c_i, c_j)`$ for every $`k`$. The proof needs that at a Good point $`\alpha \lt \omega_1`$ the top predicates agree with the top predicates of $`\omega_1`$ (for $`x \lt \alpha`$, $`R(j, x, \alpha) \iff R(j, x, \omega_1)`$). This agreement is proved by induction on the layer $`j`$. Both are explained in [09](09-obligations.md).

## 8. Where this repository uses it

| Place | Use |
|---|---|
| [README](../../README-en.md) "Where the label interface goes" | the labels of all arrays are built from a chain of closure points below $`\omega_1`$ |
| [notes/01-design.md](../../notes/01-design.md) §3.6, §4.6 (Japanese) | ambient structure, Good, next, λ, chain, the proof that λ(γ) is Good |
