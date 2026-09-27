[← Back](README.md) | [English](04-patterns-of-resemblance.md) | [Japanese](../04-patterns-of-resemblance.md)

# Patterns of resemblance

Prerequisites

| Note | Terms used here |
|---|---|
| [01 Ordinals and ω₁](01-ordinals.md) | ordinal, limit ordinal, $`\mathrm{Ord}`$ |
| [02 Well-founded relations and recursion](02-well-founded.md) | well-founded recursion, key, lexicographic order, label |
| [03 Structures and Σ₁-elementary substructures](03-sigma1-elementary.md) | structures $`(\gamma; \ldots)`$, point, $`\Sigma_1`$ formulas, $`\preccurlyeq_{\Sigma_1}`$, top, top predicate (§7) |

This note explains the idea of Carlson's patterns of resemblance. It then says how [bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) used it for BMS. Finally it says how this repository changes that, and why BMS needs no root index.

## 1. A relation whose language contains itself

**Definition (Carlson's ≤₁).** Define a relation $`\le_1`$ on ordinals by

```math
\alpha \le_1 \beta \iff \alpha \le \beta \ \land\ (\alpha; \le, \le_1) \preccurlyeq_{\Sigma_1} (\beta; \le, \le_1)
```

$`\alpha \lt_1 \beta`$ means $`\alpha \lt \beta \land \alpha \le_1 \beta`$.

**Reading.** "The shape of the ordinals below $`\alpha`$ cannot be told apart by $`\Sigma_1`$ formulas from the shape below $`\beta`$." Here the shape consists of the order and of the relation $`\le_1`$ itself.

The right side uses the relation $`\le_1`$ being defined. This looks circular, but it is a well-founded recursion on $`\beta`$.

- The domain of $`(\beta; \le, \le_1)`$ is $`\{x \mid x \lt \beta\}`$. The only $`\le_1`$ facts read there are $`x \le_1 y`$ with $`x, y \lt \beta`$.
- The truth value of $`x \le_1 y`$ has been decided at the earlier stage with key $`y \lt \beta`$.
- The same holds for $`(\alpha; \ldots)`$, since $`\alpha \le \beta`$.

Carlson studied the extension to $`\le_1, \ldots, \le_N`$ ($`\Sigma_1, \ldots, \Sigma_N`$-elementarity).

```math
\mathcal R_N = (\mathrm{Ord}; \le, \le_1, \ldots, \le_N)
```

- $`N \ge 1`$ is a natural number.
- $`\alpha \le_i \beta`$ is obtained from the definition of $`\le_1`$ by replacing $`\preccurlyeq_{\Sigma_1}`$ with elementarity for $`\Sigma_i`$ formulas. A $`\Sigma_i`$ formula starts with a block of existential quantifiers, has $`i`$ alternating blocks of existential and universal quantifiers, and then a quantifier-free formula.
- Each of the relations $`\le_1, \ldots, \le_N`$ is called a **level** of $`\mathcal R_N`$.

Reference: T. J. Carlson, Elementary patterns of resemblance, Annals of Pure and Applied Logic 108 (2001), 19–77.

## 2. Small examples

**Example 1.** For a natural number $`n \lt \beta`$, $`n \le_1 \beta`$ fails.

- If $`n \ge 1`$: $`\exists x\ (n - 1 \lt x)`$ with parameter $`n - 1`$ is true in $`\beta`$ ($`x = n`$) and false in $`n`$.
- If $`n = 0`$: $`\exists x\ (x \le x)`$ is true in $`\beta`$ and false in the empty structure $`0`$.

For the same reason, a successor ordinal $`\gamma + 1`$ is not $`\le_1`$ any larger ordinal.

**Example 2.** $`\omega \lt_1 \omega + 1`$.

By Example 1, no two distinct points below $`\omega + 1`$ are related by $`\le_1`$: pairs of natural numbers are handled by Example 1, and the only other point is $`\omega`$ itself. So in $`(\omega; \le, \le_1)`$ and $`(\omega + 1; \le, \le_1)`$, $`x \le_1 y`$ means the same as $`x = y`$. What remains is to compare the order-only structures $`(\omega; \le)`$ and $`(\omega + 1; \le)`$, and since $`\omega`$ is a limit, the example of [03](03-sigma1-elementary.md) §5 applies.

**Example 3.** If $`\beta \ge \omega + 2`$, then $`\omega \le_1 \beta`$ fails. $`\exists x\ \exists y\ (x \lt y \land x \le_1 y)`$ is true in $`\beta`$ ($`x = \omega`$, $`y = \omega + 1`$ by Example 2, both below $`\beta`$) and false in $`\omega`$ (Example 1).

$`\omega \le_1 \omega`$ holds by the definition. Hence $`\{\beta \mid \omega \le_1 \beta\} = \{\omega, \omega + 1\}`$.

In the order-only language, $`(\omega; \le) \preccurlyeq_{\Sigma_1} (\beta; \le)`$ held for every $`\beta \gt \omega`$. Putting $`\le_1`$ itself into the language makes the relation finer.

## 3. Use in termination proofs

This section uses words that later notes define, and only describes the shape. Columns of an array, parents, ancestors, the bad root and expansion are defined in [05](05-bms.md); the way labels are attached is defined in [06](06-stable-labels.md).

A termination proof for expansion attaches an ordinal label to each column and shows that expansion lowers the label of the last column ([06](06-stable-labels.md)). The property needed is **finite reflection**.

**The shape of finite reflection.** Let $`\alpha \lt_1 \beta`$. Suppose points $`\vec p`$ below $`\alpha`$ and points $`\vec y`$ below $`\beta`$ satisfy a condition $`\psi(\vec p, \vec y)`$ made of finitely many atomic formulas. Then there are points $`\vec y'`$ below $`\alpha`$ with the same condition $`\psi(\vec p, \vec y')`$.

**Reason.** $`\exists \vec y\ \psi(\vec p, \vec y)`$ is a $`\Sigma_1`$ formula true in $`(\beta; \ldots)`$. By $`\Sigma_1`$-elementarity it is true in $`(\alpha; \ldots)`$.

A BMS expansion uses this shape as follows ([05](05-bms.md) §5, [06](06-stable-labels.md)).

- $`\alpha`$ is the label of the bad root column, and $`\beta`$ is the label of the last column.
- $`\vec y`$ are the labels of the columns from the bad root up to the column just before the last one. Each of them is $`\ge \alpha`$ and $`\lt \beta`$.
- $`\vec p`$ are the labels attached to the columns further left.

If $`\psi`$ says "the labels of two columns in the ancestor relation satisfy a given relation", then the new labels $`\vec y'`$ satisfy the same condition. Moreover $`\vec y'`$ lies below $`\alpha`$. Every old label $`\vec y`$ is $`\ge \alpha`$, so the new labels are smaller than the old ones.

## 4. Use in bms-elem-pattern

[bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) proved termination of BMS with $`r`$ rows using $`\mathcal R_r`$.

**The label relations.** The ancestor relation of row $`k`$ is matched with the relation of level $`k + 1`$.

```math
\mathrm{rel}_k(a, b) :\iff a \lt_{k+1} b \qquad (k \lt r)
```

An expansion whose bad root is taken in row $`n`$ uses $`\alpha \lt_{n+1} \beta`$. This is elementarity for $`\Sigma_{n+1}`$ formulas.

**The relation to the top is the problem.** Besides the shape of §3, finite reflection has the following demand (the label interface of [06](06-stable-labels.md)).

```math
\forall i \lt s\ \forall m \lt n\ \bigl(\mathrm{rel}_m(y_i, \beta) \Rightarrow \mathrm{rel}_m(y'_i, \alpha)\bigr)
```

The $`\beta`$ on the left side and the $`\alpha`$ on the right side are tops of structures. A top is not an element of the structure $`(\beta; \ldots)`$. So "$`y_i`$ is in the relation $`\mathrm{rel}_m`$ to the top" is not an atomic formula as it stands.

**How bms-elem-pattern solves it.** It restates the relation to the top by formulas inside the structure.

- It builds a $`\Pi_m`$ formula $`\Phi_m(V)`$ that says from inside the structure "the point $`V`$ is linked to the top at level $`m`$".
- Using $`\Phi_{n-1}`$, it writes a $`\Sigma_{n+1}`$ formula with $`n + 1`$ blocks of quantifiers: a block of existential quantifiers, a block of universal quantifiers, and so on.
- It moves this formula from $`\beta`$ to $`\alpha`$ by $`\alpha \lt_{n+1} \beta`$.
- It extracts the relation between $`y'_i`$ and $`\alpha`$ by lemmas on continuity and cofinality (below the top there are unboundedly many points linked to the top).

So the number of quantifier blocks grows with the number of rows $`r`$. Details are in [proof/bms/README.md](https://github.com/koteitan/bms-elem-pattern/blob/main/proof/bms/README.md) of that repository. The definition of $`\mathcal R_N`$ and examples are in [proof/pss/03-patterns.md](https://github.com/koteitan/bms-elem-pattern/blob/main/proof/pss/03-patterns.md).

## 5. What this repository changes

This repository does not add quantifier blocks. Instead, it puts the relations to the top into the language as symbols.

1. **Every formula is $`\Sigma_1`$.** The strength of a layer is decided by the symbols in the language, not by the quantifier complexity.
2. **Top predicates ([03](03-sigma1-elementary.md) §7) are atomic symbols.** A structure of height $`\gamma`$ has the symbol $`\mathrm{Top}_j(x)`$, interpreted as "$`R(j, x, \gamma)`$". The demand toward the top $`\mathrm{rel}_m(y_i, \beta)`$ becomes the atomic formula $`\mathrm{Top}_m(y_i)`$.
3. **Layer $`k`$ decides which symbols are visible.** The structure of layer $`k`$ has only the top predicates $`\mathrm{Top}_j`$ with $`j \lt k`$. A larger $`k`$ sees more symbols, so the relation is stronger.
4. **The relations $`\mathrm{Rel}_j`$ between points are present for every layer.** $`\mathrm{Rel}_j(x, y) :\iff R(j, x, y)`$ for every $`j`$.
5. **The recursion key ([02](02-well-founded.md) §4) is $`(b, k)`$.** It is the lexicographic order with the top $`b`$ outside and the layer $`k`$ inside ([02](02-well-founded.md) §3).

Then, for an expansion whose bad root is taken in row $`n`$, the demand $`\mathrm{rel}_m(y_i, \beta) \Rightarrow \mathrm{rel}_m(y'_i, \alpha)`$ ($`m \lt n`$) means moving the truth value of the atomic formula $`\mathrm{Top}_m(y_i)`$, visible in layer $`n`$, from $`\beta`$ to $`\alpha`$. One $`\Sigma_1`$ formula is enough. No lemmas on continuity or cofinality are needed.

The resulting relation $`R`$ is not Carlson's $`\mathcal R_N`$ itself, and we do not claim that it coincides with $`\mathcal R_N`$. The definition is given in [07 The relation R](07-relation-r.md).

| | $`\mathcal R_N`$ (bms-elem-pattern) | $`R`$ of this repository |
|---|---|---|
| relation of row $`k`$ | $`\lt_{k+1}`$ of level $`k + 1`$ | $`R(k, \cdot, \cdot)`$ of layer $`k`$ |
| strength of a layer | $`\Sigma_{k+1}`$ quantifiers | visible top predicates $`\mathrm{Top}_j`$ ($`j \lt k`$) |
| formulas | $`\Sigma_1, \ldots, \Sigma_N`$ | $`\Sigma_1`$ only |
| relation to the top | formulas $`\Phi_m`$ and lemmas on continuity and cofinality | atomic symbols $`\mathrm{Top}_j`$ |
| recursion key | the top $`\beta`$ | lexicographic order on $`(b, k)`$ |

## 6. Why BMS needs no root index

[1y-wo-por](https://github.com/koteitan/1y-wo-por) used the same idea for the 1-Y sequence. The label relation required by the 1-Y combinatorial layer had four arguments.

```math
R(k, \eta, a, b) \quad (k \in \mathbb N,\ \eta, a, b \in \mathrm{Ord})
```

$`\eta`$ is the label of the root of the component that the parent–child edge belongs to, an ordinal. Each edge demands a relation that depends on the label of the root. So in 1y-wo-por, the pair $`(k, \eta)`$ of a layer and a root index decided which symbols are visible. $`\mathrm{Rel}_j`$ had 3 arguments, $`\mathrm{Top}_j`$ had 2, and the recursion key was $`(b, k, \eta)`$.

The label interface of BMS ([06](06-stable-labels.md)) demands only relations of the following forms.

- Stable labels: if $`j`$ is an ancestor of column $`i`$ in row $`k`$, then $`\mathrm{rel}_k(f(j), f(i))`$.
- Finite reflection: $`\mathrm{rel}_k(x, y)`$ between points, and $`\mathrm{rel}_m(y, \beta)`$ toward the top.

Each of them is decided by a row number $`k \in \mathbb N`$ and two labels only. No third label, such as the root of a component, appears. So the 3-argument relation $`R(k, a, b)`$ is enough. The visible symbols are decided by the layer $`k`$ alone, and the recursion key is $`(b, k) \in \mathrm{Ord} \times \mathbb N`$.

| | 1y-wo-por | this repository |
|---|---|---|
| relation | $`R(k, \eta, a, b)`$ | $`R(k, a, b)`$ |
| $`\mathrm{Rel}_j`$ | 3 arguments | 2 arguments |
| $`\mathrm{Top}_j`$ | 2 arguments | 1 argument |
| what decides the visible top predicates | $`(k, \eta)`$ | $`k`$ |
| recursion key | $`(b, k, \eta)`$ | $`(b, k)`$ |

## 7. Where this repository uses it

| Place | Use |
|---|---|
| [README](../../README-en.md) "Shape of the proof", "Differences from the other proofs" | the differences from bms-elem-pattern and 1y-wo-por (only $`\Sigma_1`$, top predicates as atomic symbols) |
| [README](../../README-en.md) "The relation R" | the top predicates $`\mathrm{Top}_j`$ and the structure of layer $`k`$ |
| [notes/01-design.md](../../notes/01-design.md) §1, §3.8 (Japanese) | reasons for the design (top predicates in the language, the key $`(b, k)`$) |
| [notes/02-port.md](../../notes/02-port.md) §3 (Japanese) | removing the root index $`\eta`$ from 1y-wo-por |
