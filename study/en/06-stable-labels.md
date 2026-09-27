[← Back](README.md) | [English](06-stable-labels.md) | [Japanese](../06-stable-labels.md)

# Stable labels and height descent

Prerequisites

| Note | Terms used here |
|---|---|
| [01 Ordinals and ω₁](01-ordinals.md) | well-order (§1) |
| [02 Well-founded relations and recursion](02-well-founded.md) | well-founded, infinite descending sequence (§1) |
| [04 Patterns of resemblance](04-patterns-of-resemblance.md) | the form of finite reflection |
| [05 The Bashicu Matrix System](05-bms.md) | array, column, row, entry, parent, ancestor, bad root, expansion, the empty array $`()`$, expansion sequence, one-step expansion $`\triangleleft`$, $`E_r`$, BM4 |

This note explains the combinatorial layer of the BMS termination proof. The core of this layer is Definition 18.1 and Proposition 19.1 of DH's paper ([paper PDF](https://googology.fandom.com/ja/wiki/%E3%83%95%E3%82%A1%E3%82%A4%E3%83%AB%3ABM4%28%E4%BD%9C%E6%88%90%E8%80%85%E6%83%85%E5%A0%B1%E4%BB%98%E3%81%8D%29.pdf)).

This layer takes a set of labels and a family of relations $`(\mathrm{rel}_k)_{k \in \mathbb N}`$ as arguments (§1). It does not use what the labels are. From three conditions on the labels, it proves that the height goes down under expansion (§3–§6). If the height goes down, expansion stops (§8). This repository uses the theorems of this layer as they are. Giving labels that satisfy the three conditions is the job of the semantic layer (§9).

## 1. The label interface

Let $`r \in \mathbb N`$ be the number of rows of the arrays.

**Definition (label interface).** A **label interface** for $`r`$ rows is a triple $`(\mathrm{Lab}, \lt, (\mathrm{rel}_k)_{k \in \mathbb N})`$ such that:

- $`\mathrm{Lab}`$ is a set. Its elements are called **labels**.
- $`\lt`$ is a well-order on $`\mathrm{Lab}`$ ([01](01-ordinals.md) §1). In particular $`\lt`$ is well-founded ([02](02-well-founded.md) §1).
- For each $`k \in \mathbb N`$, $`\mathrm{rel}_k`$ is a binary relation on $`\mathrm{Lab}`$. In §2 we require this relation between the labels of two columns that are in the ancestor relation of row $`k`$.
- Conditions 1–3 below hold.

**Condition 1 (strictness).** For every $`k`$ and $`a, b \in \mathrm{Lab}`$:

```math
\mathrm{rel}_k(a, b) \implies a \lt b
```

**Condition 2 (transitivity).** For every $`k`$ and $`a, b, c \in \mathrm{Lab}`$:

```math
\mathrm{rel}_k(a, b) \ \wedge\ \mathrm{rel}_k(b, c) \implies \mathrm{rel}_k(a, c)
```

**Condition 3 (finite reflection).** Assume all of the following four hypotheses.

- $`n \lt r`$ and $`\mathrm{rel}_n(\alpha, \beta)`$.
- $`X \subseteq \mathrm{Lab}`$ is a finite set, and $`x \lt \alpha`$ for every $`x \in X`$.
- $`s \gt 0`$, and $`y_0 \lt y_1 \lt \cdots \lt y_{s-1}`$ are labels.
- $`\alpha \le y_i \lt \beta`$ for every $`i \lt s`$.

Then there are labels $`y'_0, \ldots, y'_{s-1}`$ satisfying (R1)–(R6) below. In the table, $`i, j \lt s`$, $`k \lt r`$, $`m \lt n`$ and $`x \in X`$ range freely.

| No. | Conclusion |
|---|---|
| (R1) | $`y'_0 \lt y'_1 \lt \cdots \lt y'_{s-1}`$ |
| (R2) | $`y'_i \lt \alpha`$ |
| (R3) | $`x \lt y'_0`$ |
| (R4) | $`\mathrm{rel}_k(x, y_i) \implies \mathrm{rel}_k(x, y'_i)`$ |
| (R5) | $`\mathrm{rel}_k(y_i, y_j) \implies \mathrm{rel}_k(y'_i, y'_j)`$ |
| (R6) | $`\mathrm{rel}_m(y_i, \beta) \implies \mathrm{rel}_m(y'_i, \alpha)`$ |

**How to read it.** Finitely many labels $`y_i`$ in the interval $`[\alpha, \beta)`$ are moved to labels $`y'_i`$ below $`\alpha`$ (R2).

- The order and the relations with the elements of $`X`$ are kept (R3, R4).
- The order and the relations among the $`y_i`$ are kept (R1, R5).
- The relations to the top $`\beta`$ are kept as relations to the new top $`\alpha`$ (R6). This holds only for the rows $`m`$ below row $`n`$.
- (R4) and (R5) hold for all rows $`k \lt r`$.

This is the form of finite reflection in [04](04-patterns-of-resemblance.md). In DH's paper it corresponds to Theorem 17.1.

**Remark.** The relation $`\mathrm{rel}_k`$ is defined also for $`k \ge r`$. But only $`k \lt r`$ is used.

**Example (empty relations).** Let every $`\mathrm{rel}_k`$ be the empty relation. Conditions 1 and 2 hold because the hypothesis $`\mathrm{rel}_k(a, b)`$ is false. Condition 3 also holds because the hypothesis $`\mathrm{rel}_n(\alpha, \beta)`$ is false. So this is a label interface. However, the only arrays with a stable label in the sense of §2 are then the arrays with no ancestor relation at all. A useful label interface is built in [07](07-relation-r.md) and [09](09-obligations.md).

## 2. Stable labels and height

In this note, we write $`i \prec^A_k j`$ when column $`i`$ is an ancestor of column $`j`$ in row $`k`$ of the array $`A`$ (ancestors are in [05](05-bms.md)). $`i \preceq^A_k j`$ means $`i = j`$ or $`i \prec^A_k j`$.

**Definition (stable label, DH's Definition 18.1).** Let $`A`$ be an array with $`r`$ rows and length $`\ell`$. A function $`f : \{0, \ldots, \ell - 1\} \to \mathrm{Lab}`$ is a **stable label** of $`A`$ if the following two hold.

| No. | Condition |
|---|---|
| (S1) | $`i \lt j \lt \ell \implies f(i) \lt f(j)`$ |
| (S2) | if $`k \lt r`$ and $`i \prec^A_k j`$ then $`\mathrm{rel}_k(f(i), f(j))`$ |

$`f(i)`$ is called the label of column $`i`$.

**Definition (height).** When $`A`$ is nonempty, the label $`f(\ell - 1)`$ of the last column is called the **height** of $`f`$ and written $`\mathrm{ht}(f)`$.

**Example.** Let $`A = (0,0)(1,1)(2,2)(3,2)`$. Here $`r = 2`$ and $`\ell = 4`$. The parents and ancestors are as follows (computed by computer).

| Column | 0 | 1 | 2 | 3 |
|---|---|---|---|---|
| Entries | $`(0,0)`$ | $`(1,1)`$ | $`(2,2)`$ | $`(3,2)`$ |
| Parent in row 0 | none | 0 | 1 | 2 |
| Parent in row 1 | none | 0 | 1 | 1 |

- Row 0: the parent of column $`j`$ is the rightmost column left of $`j`$ whose row-0 entry is smaller. Here it is column $`j - 1`$. So $`i \prec^A_0 j`$ whenever $`i \lt j`$.
- Row 1: the parent candidates are the ancestors in row 0. The row-1 entry of column 3 is 2. Among the candidates, column 2 has entry 2, which is not smaller. Column 1 has entry 1, which is smaller. So the parent of column 3 is column 1.
- The ancestor pairs in row 1 are $`(0,1)`$, $`(0,2)`$, $`(0,3)`$, $`(1,2)`$, $`(1,3)`$. $`(2,3)`$ is not one of them.

So $`f`$ is a stable label exactly when the following hold.

```math
f(0) \lt f(1) \lt f(2) \lt f(3)
```

```math
\mathrm{rel}_0(f(i), f(j)) \quad (0 \le i \lt j \le 3)
```

```math
\mathrm{rel}_1(f(0), f(1)),\quad \mathrm{rel}_1(f(0), f(2)),\quad \mathrm{rel}_1(f(0), f(3)),\quad \mathrm{rel}_1(f(1), f(2)),\quad \mathrm{rel}_1(f(1), f(3))
```

$`\mathrm{rel}_1(f(2), f(3))`$ is not required. The height is $`\mathrm{ht}(f) = f(3)`$.

## 3. Proposition 19.1

From now on, fix a label interface satisfying Conditions 1–3.

**Theorem (height descent, DH's Proposition 19.1).** Let $`A`$ be a nonempty array with $`r`$ rows, and $`f`$ a stable label of $`A`$. Let $`N \in \mathbb N`$ and assume $`A[N]`$ is nonempty. Then there is a stable label $`g`$ of $`A[N]`$ with:

```math
\mathrm{ht}(g) \lt \mathrm{ht}(f)
```

Let $`c = \ell - 1`$ be the last column of $`A`$. The proof splits into two cases by whether $`c`$ has a parent (§4, §5–§6).

Both cases use the following property.

**Property 1 (prefix).** An array made of the first few columns of an array $`D`$ is called a **prefix** of $`D`$. In a prefix, the parents and ancestors of the columns are the same as in $`D`$.

**Reason.** The parent of a column is determined only by the entries of that column and of the columns left of it ([05](05-bms.md)). The same holds for ancestors. $`\square`$

## 4. Case 1: the last column has no parent

Assume column $`c`$ has no parent in any row $`k \lt r`$. Then $`A[N]`$ is the array obtained from $`A`$ by deleting the last column ([05](05-bms.md)).

- $`A[N]`$ is a prefix of $`A`$. By Property 1, its parents and ancestors are the same as in $`A`$.
- So the restriction of $`f`$ to the columns $`0, \ldots, c - 1`$ is a stable label of $`A[N]`$. Call it $`g`$.
- $`A[N]`$ is nonempty, so $`c \ge 1`$. By (S1), $`\mathrm{ht}(g) = f(c - 1) \lt f(c) = \mathrm{ht}(f)`$. $`\square`$

**Example.** In $`A = (0,0)(0,0)(0,0)`$, no column has a parent in any row. $`A[3] = (0,0)(0,0)`$ (computed by computer).

## 5. Preparation for Case 2

Assume column $`c`$ has a parent in some row $`k \lt r`$. We restate the notation of expansion in [05](05-bms.md) in the form used in this note.

- $`m_0`$: the largest row in which column $`c`$ has a parent. $`m_0 \lt r`$.
- $`p`$: the parent of column $`c`$ in row $`m_0`$. This is the bad root.
- $`s = c - p`$. $`s \ge 1`$.
- $`G`$: the columns $`0, \ldots, p - 1`$.
- $`B_0`$: the columns $`p, \ldots, c - 1`$. We call this the bad part.

The expansion $`A[N]`$ is the array made of $`G`$ followed by $`N + 1`$ copies of $`B_0`$.

```math
A[N] = G \frown B_0 \frown B_1 \frown \cdots \frown B_N
```

Each $`B_q`$ has $`s`$ columns. The entries of the copies are given by the expansion rule of [05](05-bms.md). This note does not use the rule for the entries directly. It uses only Property 2 below.

We write the number of the $`j`$-th column of $`B_q`$ ($`j \lt s`$) as follows.

```math
\langle q, j \rangle = p + q \cdot s + j
```

For $`q \le N`$, $`A[q] = G \frown B_0 \frown \cdots \frown B_q`$ is a prefix of $`A[N]`$.

**Property 2 (copy lemma, DH's Theorem 6.3 and Corollary 6.12).** Let $`q + 1 \le N`$, $`j \lt s`$ and $`k \lt r`$. If $`i \prec_k \langle q+1, j \rangle`$ in $`A[N]`$, then one of (a)–(d) below holds.

| Case | Place of the ancestor $`i`$ | What holds |
|---|---|---|
| (a) | same block: $`i = \langle q+1, i' \rangle`$, $`i' \lt j`$ | $`p + i' \prec^A_k p + j`$ |
| (b) | $`G`$: $`i \lt p`$ | $`i \prec^A_k p + j`$ |
| (c) | two or more blocks before: $`i = \langle a, i' \rangle`$, $`a \lt q`$ | $`i \prec_k \langle q, j \rangle`$ in $`A[N]`$ |
| (d) | the block just before: $`i = \langle q, i' \rangle`$ | $`k \lt m_0`$, $`p + i' \prec^A_k c`$, $`p \preceq^A_k p + j`$ |

- (a) and (b) bring the ancestor relation back to $`A`$.
- (c) moves the descendant side of the ancestor relation to the same position in the previous block.
- (d) says that an ancestor relation from the block just before occurs only in rows below row $`m_0`$.

This property is in §6 of DH's paper. It is a fact about the entries of arrays only and does not use labels. This note does not prove it.

**Example (copy lemma).** Take the example $`A = (0,0)(1,1)(2,2)(3,2)`$ of §2 and $`N = 2`$. Column 3 has parent column 2 in row 0 and parent column 1 in row 1. So $`m_0 = 1`$, $`p = 1`$, $`s = 2`$. The expansion is as follows (computed by computer).

| Column | 0 | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|---|
| Block | $`G`$ | $`B_0`$ | $`B_0`$ | $`B_1`$ | $`B_1`$ | $`B_2`$ | $`B_2`$ |
| Number | | $`\langle 0,0 \rangle`$ | $`\langle 0,1 \rangle`$ | $`\langle 1,0 \rangle`$ | $`\langle 1,1 \rangle`$ | $`\langle 2,0 \rangle`$ | $`\langle 2,1 \rangle`$ |
| Entries of $`A[2]`$ | $`(0,0)`$ | $`(1,1)`$ | $`(2,2)`$ | $`(3,1)`$ | $`(4,2)`$ | $`(5,1)`$ | $`(6,2)`$ |
| Parent in row 0 | none | 0 | 1 | 2 | 3 | 4 | 5 |
| Parent in row 1 | none | 0 | 1 | 0 | 3 | 0 | 5 |

With $`q = 1`$ and $`j = 1`$, we sort the ancestors of column $`\langle 2, 1 \rangle = 6`$ by Property 2.

| Row $`k`$ | Ancestor $`i`$ | Case | What holds |
|---|---|---|---|
| 0 | 5 | (a) | $`1 \prec^A_0 2`$ |
| 0 | 0 | (b) | $`0 \prec^A_0 2`$ |
| 0 | 1, 2 | (c) | $`1 \prec_0 4`$, $`2 \prec_0 4`$ in $`A[2]`$ |
| 0 | 3, 4 | (d) | $`0 \lt m_0 = 1`$, $`1 \prec^A_0 3`$, $`2 \prec^A_0 3`$, $`1 \prec^A_0 2`$ |
| 1 | 5 | (a) | $`1 \prec^A_1 2`$ |
| 1 | 0 | (b) | $`0 \prec^A_1 2`$ |

Row 1 has no case (d). This is because $`k = 1`$ is not smaller than $`m_0 = 1`$.

## 6. Proof of Case 2: relabelling block by block

Put:

```math
\alpha = f(p), \qquad \beta = f(c), \qquad y_j = f(p + j) \quad (j \lt s)
```

- $`p`$ is the parent of $`c`$ in row $`m_0`$, so $`p \prec^A_{m_0} c`$. Since $`m_0 \lt r`$, (S2) gives $`\mathrm{rel}_{m_0}(\alpha, \beta)`$.
- By (S1), $`\alpha = y_0 \lt y_1 \lt \cdots \lt y_{s-1} \lt \beta`$.

**Invariant.** For $`q = 0, 1, \ldots, N`$ in this order, we build a label $`g_q`$ of $`A[q]`$ satisfying (I1)–(I4) below.

| No. | Condition |
|---|---|
| (I1) | $`g_q`$ is a stable label of $`A[q]`$ |
| (I2) | $`i \lt p \implies g_q(i) = f(i)`$ |
| (I3) | $`j \lt s \implies g_q(\langle q, j \rangle) = y_j`$ |
| (I4) | $`i \lt \langle q, 0 \rangle \implies g_q(i) \lt \alpha`$ |

The last block $`B_q`$ carries the old labels $`y_j`$ of the bad part unchanged (I3). All labels left of it are below $`\alpha`$ (I4).

**The case $`q = 0`$.** $`A[0] = G \frown B_0`$ is the array obtained from $`A`$ by deleting the last column. Let $`g_0`$ be the restriction of $`f`$ to the columns $`0, \ldots, c - 1`$.

- (I1): $`A[0]`$ is a prefix of $`A`$, so this holds by Property 1.
- (I2), (I3): hold because $`g_0 = f`$.
- (I4): if $`i \lt p`$, then $`f(i) \lt f(p) = \alpha`$ by (S1).

**From $`q`$ to $`q + 1`$ ($`q + 1 \le N`$).** We use finite reflection (Condition 3) once. The arguments are:

- $`n = m_0`$, $`\alpha = f(p)`$, $`\beta = f(c)`$. As seen above, $`n \lt r`$ and $`\mathrm{rel}_n(\alpha, \beta)`$.
- $`X = \{ g_q(i) : i \lt \langle q, 0 \rangle \}`$. By (I4), $`x \lt \alpha`$ for every $`x \in X`$.
- $`y_0, \ldots, y_{s-1}`$. As seen above, they are increasing and $`\alpha \le y_j \lt \beta`$.

This gives $`y'_0, \ldots, y'_{s-1}`$. Define the label $`g_{q+1}`$ of $`A[q+1] = G \frown B_0 \frown \cdots \frown B_{q+1}`$ by:

```math
g_{q+1}(i) = g_q(i) \qquad (i \lt \langle q, 0 \rangle)
```

```math
g_{q+1}(\langle q, j \rangle) = y'_j, \qquad g_{q+1}(\langle q+1, j \rangle) = y_j \qquad (j \lt s)
```

That is, the old labels $`y_j`$ of block $`B_q`$ are replaced by the labels $`y'_j`$ below $`\alpha`$. The new block $`B_{q+1}`$ gets the old labels $`y_j`$. The labels left of $`B_q`$ do not change.

(I2) and (I3) hold by definition. (I4) holds left of $`B_q`$ by (I4) for $`g_q`$, and on $`B_q`$ by (R2). We check (I1).

**Checking (S1).** Left of $`B_q`$ we use (S1) for $`g_q`$. The rest is ordered as follows by (R3), (R1), (R2).

```math
x \lt y'_0 \lt \cdots \lt y'_{s-1} \lt \alpha = y_0 \lt \cdots \lt y_{s-1} \qquad (x \in X)
```

**Checking (S2).** Let $`k \lt r`$ and $`i \prec_k j^*`$ in $`A[q+1]`$. $`A[q]`$ and $`A[q+1]`$ are both prefixes of $`A[N]`$, so by Property 1 the ancestor relation is the same in all of them. We split by the place of the descendant column $`j^*`$.

1. When $`j^* \lt \langle q, 0 \rangle`$: both $`i`$ and $`j^*`$ are left of $`B_q`$. The labels are the same as $`g_q`$, so this holds by (S2) for $`g_q`$.
2. When $`j^* = \langle q, j \rangle`$ (inside $`B_q`$): by (S2) for $`g_q`$ and (I3), $`\mathrm{rel}_k(g_q(i), y_j)`$.
   - If $`i \lt \langle q, 0 \rangle`$, then $`g_q(i) \in X`$. By (R4), $`\mathrm{rel}_k(g_q(i), y'_j)`$.
   - If $`i = \langle q, i' \rangle`$, then $`\mathrm{rel}_k(y_{i'}, y_j)`$. By (R5), $`\mathrm{rel}_k(y'_{i'}, y'_j)`$.
3. When $`j^* = \langle q+1, j \rangle`$ (inside $`B_{q+1}`$): the label is $`y_j = f(p + j)`$. We split by the cases of Property 2.
   - (a) $`i = \langle q+1, i' \rangle`$: by $`p + i' \prec^A_k p + j`$ and (S2) for $`f`$, $`\mathrm{rel}_k(y_{i'}, y_j)`$.
   - (b) $`i \lt p`$: by $`i \prec^A_k p + j`$ and (S2) for $`f`$, $`\mathrm{rel}_k(f(i), y_j)`$. By (I2), $`g_{q+1}(i) = f(i)`$.
   - (c) $`i = \langle a, i' \rangle`$, $`a \lt q`$: $`i \prec_k \langle q, j \rangle`$ in $`A[q]`$. By (S2) for $`g_q`$ and (I3), $`\mathrm{rel}_k(g_q(i), y_j)`$. And $`g_{q+1}(i) = g_q(i)`$.
   - (d) $`i = \langle q, i' \rangle`$: the label is $`y'_{i'}`$. By $`p + i' \prec^A_k c`$ and (S2) for $`f`$, $`\mathrm{rel}_k(y_{i'}, \beta)`$. Since $`k \lt m_0 = n`$, (R6) gives $`\mathrm{rel}_k(y'_{i'}, \alpha)`$. If $`j = 0`$, we are done since $`\alpha = y_0`$. If $`j \gt 0`$, then $`p \prec^A_k p + j`$, so (S2) for $`f`$ gives $`\mathrm{rel}_k(\alpha, y_j)`$. By transitivity (Condition 2), $`\mathrm{rel}_k(y'_{i'}, y_j)`$.

**End.** $`g = g_N`$ is a stable label of $`A[N]`$. The last column of $`A[N]`$ is $`\langle N, s - 1 \rangle`$. By (I3) and (S1):

```math
\mathrm{ht}(g) = y_{s-1} = f(c - 1) \lt f(c) = \mathrm{ht}(f)
```

$`\square`$

**Where the conditions are used.**

| Condition | Where it is used |
|---|---|
| well-order | termination in §8 (no infinite descending sequence of heights) |
| strictness (Condition 1) | not used in the proof of Proposition 19.1 |
| transitivity (Condition 2) | case (d) of item 3, when $`j \gt 0`$ |
| (R1), (R2), (R3) | order of the new labels (S1), and (I4) |
| (R4) | ancestors of a column of $`B_q`$ that lie left of $`B_q`$ |
| (R5) | ancestors inside $`B_q`$ |
| (R6) | ancestors from the block just before (case (d) of item 3) |

**Why (R6) is needed only for rows $`m \lt n`$.** (R6) is used only in case (d) of item 3. By Property 2, case (d) occurs only when $`k \lt m_0 = n`$.

## 7. Example

We follow the relabelling for the example $`A = (0,0)(1,1)(2,2)(3,2)`$, $`N = 2`$ of §5. Since $`m_0 = 1`$, $`p = 1`$, $`s = 2`$, we have:

```math
n = 1, \qquad \alpha = f(1), \qquad \beta = f(3), \qquad (y_0, y_1) = (f(1), f(2))
```

- Step $`q = 0`$: use finite reflection with $`X = \{f(0)\}`$ and get $`(y'_0, y'_1)`$.
- Step $`q = 1`$: use finite reflection again with $`X = \{f(0), y'_0, y'_1\}`$, and write the result as $`(z'_0, z'_1)`$.

| Column | 0 | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|---|
| Block | $`G`$ | $`B_0`$ | $`B_0`$ | $`B_1`$ | $`B_1`$ | $`B_2`$ | $`B_2`$ |
| $`g_0`$ ($`A[0]`$) | $`f(0)`$ | $`f(1)`$ | $`f(2)`$ | | | | |
| $`g_1`$ ($`A[1]`$) | $`f(0)`$ | $`y'_0`$ | $`y'_1`$ | $`f(1)`$ | $`f(2)`$ | | |
| $`g_2`$ ($`A[2]`$) | $`f(0)`$ | $`y'_0`$ | $`y'_1`$ | $`z'_0`$ | $`z'_1`$ | $`f(1)`$ | $`f(2)`$ |

The labels are ordered as follows.

```math
f(0) \lt y'_0 \lt y'_1 \lt z'_0 \lt z'_1 \lt f(1) \lt f(2) \lt f(3)
```

The height is $`\mathrm{ht}(g_2) = f(2) \lt f(3) = \mathrm{ht}(f)`$.

At step $`q = 0`$, we check some ancestor relations of $`A[1] = (0,0)(1,1)(2,2)(3,1)(4,2)`$ (the ancestors are the same as in the first five columns of the table in §5).

| Ancestor relation | Place in §6 | Reason |
|---|---|---|
| $`1 \prec 2`$ in row 1 | 2 (inside $`B_0`$) | (R5) applied to $`\mathrm{rel}_1(f(1), f(2))`$ gives $`\mathrm{rel}_1(y'_0, y'_1)`$ |
| $`0 \prec 2`$ in row 0 | 2 (ancestor on the left) | (R4) applied to $`\mathrm{rel}_0(f(0), f(2))`$ gives $`\mathrm{rel}_0(f(0), y'_1)`$ |
| $`2 \prec 3`$ in row 0 | 3 (d), $`j = 0`$ | (R6) ($`m = 0 \lt n = 1`$) applied to $`\mathrm{rel}_0(f(2), \beta)`$ gives $`\mathrm{rel}_0(y'_1, \alpha)`$ |
| $`2 \prec 4`$ in row 0 | 3 (d), $`j = 1`$ | transitivity from $`\mathrm{rel}_0(y'_1, f(1))`$ and $`\mathrm{rel}_0(f(1), f(2))`$ |
| $`0 \prec 3`$ in row 1 | 3 (b) | $`\mathrm{rel}_1(f(0), f(1))`$ from $`0 \prec^A_1 1`$ |

In $`A[1]`$, column 2 is not an ancestor of column 3 in row 1 (the row-1 parent of column 3 is column 0). So $`\mathrm{rel}_1(y'_1, f(1))`$ is not needed. This agrees with the fact that $`\mathrm{rel}_1(f(2), f(3))`$ is not required in $`A`$ (the example of §2).

## 8. Termination and well-foundedness

**Theorem (termination).** Let $`A`$ be an array with $`r`$ rows that has a stable label. Let $`n : \mathbb N \to \mathbb N`$, and put the expansion sequence ([05](05-bms.md) §7) as follows.

```math
A^{(0)} = A, \qquad A^{(t+1)} = A^{(t)}[n(t)]
```

Then $`A^{(T)} = ()`$ for some $`T`$.

**Proof.** Assume no $`A^{(t)}`$ is empty. Let $`f_0`$ be a stable label of $`A^{(0)}`$. By Proposition 19.1, we can choose, for $`t = 0, 1, \ldots`$ in this order, a stable label $`f_{t+1}`$ of $`A^{(t+1)}`$ with $`\mathrm{ht}(f_{t+1}) \lt \mathrm{ht}(f_t)`$.

```math
\mathrm{ht}(f_0) \gt \mathrm{ht}(f_1) \gt \mathrm{ht}(f_2) \gt \cdots
```

The set $`\{ \mathrm{ht}(f_t) : t \in \mathbb N \}`$ is nonempty. Since $`\lt`$ is a well-order, it has a least element $`\mathrm{ht}(f_{t_0})`$. But $`\mathrm{ht}(f_{t_0 + 1})`$ is smaller. This is a contradiction. $`\square`$

**Corollary (well-foundedness).** Assume every array with $`r`$ rows has a stable label. Consider the one-step expansion relation $`\triangleleft`$ on the arrays with $`r`$ rows ([05](05-bms.md) §7).

```math
A \mathrel{\triangleleft} B \iff B \ne () \ \wedge\ \exists N \in \mathbb N\ \ A = B[N]
```

Then $`\triangleleft`$ is well-founded ([02](02-well-founded.md) §1).

**Proof.** Assume $`\triangleleft`$ has an infinite descending sequence $`C_0 \mathrel{\triangleright} C_1 \mathrel{\triangleright} \cdots`$ ($`\triangleright`$ is $`\triangleleft`$ reversed). Then no $`C_t`$ is empty and $`C_{t+1} = C_t[N_t]`$. This is an expansion sequence with no empty term, which contradicts the termination theorem. $`\square`$

**Where the stable labels come from.** The termination theorem needs a stable label of the first array $`A^{(0)}`$. There are two sources.

- The elements of BM4 are the arrays obtained from $`E_r = (0, \ldots, 0)(1, \ldots, 1)`$ by repeated expansion ([05](05-bms.md)). If $`E_r`$ has a stable label, then by Proposition 19.1 every element of BM4 has a stable label. [bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) uses this method.
- In this repository, every array has a stable label ([08](08-closure-chain.md), [09](09-obligations.md)). This is because we build a sequence of labels $`\gamma_0 \lt \gamma_1 \lt \cdots`$ with $`i \lt j \implies \mathrm{rel}_k(\gamma_i, \gamma_j)`$ for every $`k`$, and give column $`i`$ the label $`\gamma_i`$. [08](08-closure-chain.md) and [09](09-obligations.md) write this sequence as $`c_0 \lt c_1 \lt \cdots`$.

The elements of BM4 are arrays with $`r`$ rows, so the expansion relation on BM4 is also well-founded. Expansion does not change the number of rows, so it is also well-founded on BM4 with all row counts put together.

## 9. The work left to the semantic layer

The combinatorial layer does not ask why finite reflection holds. Giving a label interface satisfying Conditions 1–3, and stable labels of arrays, is the job of the **semantic layer**.

| Proof | Labels | Relation $`\mathrm{rel}_k`$ |
|---|---|---|
| DH's paper | admissible ordinals (using the constructible hierarchy $`L`$) | $`L_\alpha \prec^*_{k+2} L_\beta`$ (equation (15.1) of DH's paper) |
| [bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) | ordinals | $`\lt_{k+1}`$ of Carlson's $`\mathcal R_N`$ ($`\Sigma_{k+1}`$-elementarity) |
| this repository | ordinals | $`R(k, \cdot, \cdot)`$ of [07 The relation R](07-relation-r.md) ($`\Sigma_1`$-elementarity only) |

The proofs of Conditions 1–3 in this repository are in [09](09-obligations.md).

## 10. Where this repository uses it

| Place | Use |
|---|---|
| [README](../../README-en.md) "Shape of the proof", "Where the label interface goes" | the two layers and the table of the label interface |
| [README](../../README-en.md) "What is proved" | the termination and well-foundedness of §8 become the final theorems |
| [notes/01-design.md](../../notes/01-design.md) §2, §4 (Japanese) | list of the label interface and its proofs in the semantic layer |
