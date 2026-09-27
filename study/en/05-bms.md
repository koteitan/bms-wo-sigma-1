[← Back](README.md) | [English](05-bms.md) | [Japanese](../05-bms.md)

# The Bashicu Matrix System

Prerequisites

| Note | Terms used here |
|---|---|
| [02 Well-founded relations and recursion](02-well-founded.md) | well-founded |

This note explains the arrays of the Bashicu Matrix System (BMS) and the definition of their expansion. BMS was invented by Bashicu. This repository uses the definitions of the version in DH's paper (BM4). They are Definitions 1.1, 2.1 and 5.1 of the paper.

- Bashicu, "BASIC言語による巨大数のまとめ" (a summary of large numbers in BASIC), Googology Wiki (Japanese). [page](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0%3ABashicuHyudora/BASIC%E8%A8%80%E8%AA%9E%E3%81%AB%E3%82%88%E3%82%8B%E5%B7%A8%E5%A4%A7%E6%95%B0%E3%81%AE%E3%81%BE%E3%81%A8%E3%82%81#%E3%83%90%E3%82%B7%E3%82%AF%E8%A1%8C%E5%88%97%E6%95%B0%28Bashicu_matrix_number%29)
- DH, "Bashicu Matrix System ver. 4 の停止性と展開関係の整礎性" (termination of Bashicu Matrix System ver. 4 and well-foundedness of its expansion relation), Googology Wiki (Japanese, 2026). [paper PDF](https://googology.fandom.com/ja/wiki/%E3%83%95%E3%82%A1%E3%82%A4%E3%83%AB%3ABM4%28%E4%BD%9C%E6%88%90%E8%80%85%E6%83%85%E5%A0%B1%E4%BB%98%E3%81%8D%29.pdf)

The values in the examples were computed by computer, following these definitions (2026-09-28). That the computation follows the definitions was checked with $`(0,0)(1,1)[2] = (0,0)(1,0)(2,0)`$.

## 1. Arrays

**Definition (array).** Let $`r \in \mathbb N`$. An **array** $`A`$ with $`r`$ rows and length $`\ell \in \mathbb N`$ is a sequence of columns $`A_0, \ldots, A_{\ell-1}`$. Each column is an $`r`$-tuple of natural numbers.

- Columns are numbered from 0.
- The $`k`$-th entry of the column $`A_i`$ ($`k \lt r`$) is written $`A_i[k]`$ and called the entry in **row $`k`$**. Rows are also numbered from 0.
- An array is written by listing its columns from left to right, like $`(0,0)(1,1)(2,2)`$. Inside each column, the entry of row 0 is written first.
- The array of length 0 is called the **empty array** and written $`()`$.
- The **last column** of a nonempty array is the column $`c := \ell - 1`$.

**Example.** $`A = (0,0,0)(1,1,1)(2,2,1)(3,1,0)`$ is an array with 3 rows and length 4. $`A_2[1] = 2`$, $`A_3[2] = 0`$, and the last column is $`c = 3`$.

## 2. Parents in row 0

**Definition (parent in row 0).** The **parent** of column $`i`$ in row 0 is the largest $`j`$ with $`j \lt i`$ and $`A_j[0] \lt A_i[0]`$. If there is none, column $`i`$ has no parent in row 0.

A parent in row $`k`$ is also called a **$`k`$-parent**.

**Example.** Row 0 of $`(0,0,0)(1,1,1)(2,2,1)(3,1,0)`$ is $`0, 1, 2, 3`$. The 0-parents of columns 1, 2, 3 are columns 0, 1, 2 respectively. Column 0 has no 0-parent.

## 3. Ancestors and parents in row k+1

**Definition (ancestor).** A column reached from column $`i`$ by following $`k`$-parents one or more times is called a **$`k`$-ancestor** of column $`i`$, written $`j \prec_k i`$. $`j \preceq_k i`$ means $`j = i \lor j \prec_k i`$.

A parent is a column to the left, so $`j \prec_k i`$ implies $`j \lt i`$.

**Definition (candidates and parents in row k+1).** The **candidates** of column $`i`$ in row $`k`$ are

```math
\mathrm{cand}_0(i) := \{j \mid j \lt i\}, \qquad \mathrm{cand}_{k+1}(i) := \{j \mid j \prec_k i\}
```

The $`k`$-parent of column $`i`$ is the largest $`j`$ with $`j \in \mathrm{cand}_k(i)`$ and $`A_j[k] \lt A_i[k]`$. If there is none, column $`i`$ has no parent in row $`k`$. For $`k = 0`$ this is the definition of §2.

$`\prec_{k+1}`$ is decided by the parents in row $`k+1`$, and the parents in row $`k+1`$ are decided by $`\prec_k`$. So everything is decided row by row, starting from row 0.

**Property 1.** If $`j \prec_{k+1} i`$, then $`j \prec_k i`$.

**Proof.** A $`(k+1)`$-parent is a candidate, so it is a $`k`$-ancestor. When $`j \prec_{k+1} i`$, we reach $`j`$ from $`i`$ by following $`(k+1)`$-parents one at a time. Each step goes to a $`k`$-ancestor, so $`j`$ is a $`k`$-ancestor of a $`k`$-ancestor of … of $`i`$. A $`k`$-ancestor of a $`k`$-ancestor is a $`k`$-ancestor, so $`j \prec_k i`$. $`\square`$

**Property 2.** If $`j \prec_k i`$, then $`A_j[k] \lt A_i[k]`$.

**Proof.** The entry of a parent in row $`k`$ is smaller than that of the child. Repeat this once for each $`k`$-parent followed. $`\square`$

**Property 3.** If column $`i`$ has a $`(k+1)`$-parent, it also has a $`k`$-parent.

**Proof.** The $`(k+1)`$-parent is a $`k`$-ancestor of $`i`$. Since a $`k`$-ancestor exists, the first step of following $`k`$-parents exists. $`\square`$

By Property 3, the rows in which column $`i`$ has a parent are of the form $`0, 1, \ldots, m`$. By Property 2, if $`A_i[k] = 0`$, column $`i`$ has no parent in row $`k`$.

**Example.** $`A = (0,0,0)(1,1,1)(2,2,1)(3,1,0)`$. In the table, "$`v \leftarrow j`$" means that the entry is $`v`$ and the parent is column $`j`$.

| row | column 0 | column 1 | column 2 | column 3 |
|---|---|---|---|---|
| 0 | 0 | 1 ← 0 | 2 ← 1 | 3 ← 2 |
| 1 | 0 | 1 ← 0 | 2 ← 1 | 1 ← 0 |
| 2 | 0 | 1 ← 0 | 1 ← 0 | 0 |

The ancestors are as follows. Each cell is the set of $`k`$-ancestors of that column.

| row $`k`$ | column 0 | column 1 | column 2 | column 3 |
|---|---|---|---|---|
| 0 | $`\emptyset`$ | $`\{0\}`$ | $`\{0, 1\}`$ | $`\{0, 1, 2\}`$ |
| 1 | $`\emptyset`$ | $`\{0\}`$ | $`\{0, 1\}`$ | $`\{0\}`$ |
| 2 | $`\emptyset`$ | $`\{0\}`$ | $`\{0\}`$ | $`\emptyset`$ |

- Column 3, row 1: the candidates are the 0-ancestors $`\{0, 1, 2\}`$. Their entries in row 1 are 2 (column 2), 1 (column 1) and 0 (column 0). The largest one smaller than $`A_3[1] = 1`$ is column 0, so the 1-parent is column 0.
- Column 2, row 2: the candidates are the 1-ancestors $`\{0, 1\}`$. $`A_1[2] = 1`$ is not smaller than $`A_2[2] = 1`$. $`A_0[2] = 0`$ is smaller. So the 2-parent is column 0.
- Column 3, row 2: $`A_3[2] = 0`$, so there is no parent.

## 4. The bad root

From here on, $`A`$ is a nonempty array and $`c`$ is its last column.

**Definition (m₀ and the bad root).** Suppose the last column $`c`$ has a parent in some row $`k \lt r`$.

- $`m_0`$ is the largest row number in which column $`c`$ has a parent.
- The $`m_0`$-parent of column $`c`$ is written $`p`$ and called the **bad root**.
- Put $`s := c - p`$. Then $`s \ge 1`$.
- $`G := A_0 \cdots A_{p-1}`$ is called the **good part**.
- $`B_0 := A_p \cdots A_{c-1}`$ is called the **bad part**. Its length is $`s`$.

By Property 3, column $`c`$ has a parent in every row $`0, 1, \ldots, m_0`$ and in no row from $`m_0 + 1`$ up.

**Example.** In $`(0,0,0)(1,1,1)(2,2,1)(3,1,0)`$, the table of §3 shows that column 3 has parents in rows 0 and 1, and not in row 2. So $`m_0 = 1`$, $`p = 0`$, $`s = 3`$. $`G`$ is empty and $`B_0 = (0,0,0)(1,1,1)(2,2,1)`$.

## 5. Expansion

**Definition (difference).** In the situation of §4, the **difference** in row $`k`$ is $`\Delta_k := A_c[k] - A_p[k]`$.

If $`k \le m_0`$, then $`\Delta_k \gt 0`$. Indeed $`p \prec_{m_0} c`$, so $`p \prec_k c`$ by Property 1, and $`A_p[k] \lt A_c[k]`$ by Property 2.

**Definition (expansion A[N]).** $`N \in \mathbb N`$ is called the **copy count**. The array $`A[N]`$ is defined as follows.

- (0) If $`A`$ is empty: $`A[N] := A`$.
- (1) If the last column $`c`$ has no parent in any row $`k \lt r`$: delete the last column. $`A[N] := A_0 \cdots A_{c-1}`$.
- (2) If the last column $`c`$ has a parent: using $`m_0`$, $`p`$, $`s`$, $`G`$ of §4, it is the following array.

```math
A[N] := G\, B_0\, B_1 \cdots B_N
```

The **block** $`B_q`$ ($`0 \le q \le N`$) is an array of length $`s`$. The entry in row $`k`$ of its $`j`$-th column ($`0 \le j \lt s`$) is

```math
(B_q)_j[k] := \begin{cases} A_{p+j}[k] + q \cdot \Delta_k & \text{if } k \lt m_0 \text{ and } p \preceq_k p + j \cr A_{p+j}[k] & \text{otherwise} \end{cases}
```

- The length of $`A[N]`$ is $`p + (N + 1) s`$.
- $`B_0`$ is the bad part itself ($`q = 0`$). $`B_1, \ldots, B_N`$ are its copies.
- The last column $`c`$ is not in $`A[N]`$.
- In block $`B_q`$, the only entries that grow are those in rows $`k \lt m_0`$ of columns $`p + j`$ whose $`k`$-ancestors include the bad root $`p`$ (or $`j = 0`$). They grow by $`q \cdot \Delta_k`$.
- Entries in row $`m_0`$ and above do not grow.

By Property 3, the condition of (1) is the same as "column $`c`$ has no parent in row 0".

## 6. Examples

**Example 1 ($`(0,0)(1,1)[2]`$).**

1. **Parents.** $`c = 1`$. Row 0: the candidates are $`\{0\}`$, and $`0 \lt 1`$, so the 0-parent is column 0. Row 1: the candidates are the 0-ancestors $`\{0\}`$, and $`0 \lt 1`$, so the 1-parent is column 0.
2. **Bad root.** $`m_0 = 1`$, $`p = 0`$, $`s = 1`$. $`G`$ is empty, $`B_0 = (0,0)`$. $`\Delta = (1, 1)`$.
3. **Blocks.** The rows that grow are $`k \lt 1`$, that is, row 0 only. $`B_q = (0 + q, 0)`$.

So $`(0,0)(1,1)[2] = (0,0)(1,0)(2,0)`$. In general $`(0,0)(1,1)[N] = (0,0)(1,0)(2,0) \cdots (N,0)`$.

**Example 2 ($`(0,0)(1,1)(2,2)[2]`$).**

1. **Parents.** $`c = 2`$. The parent in row 0 is column 1. Row 1: the candidates are the 0-ancestors $`\{0, 1\}`$, and $`A_1[1] = 1 \lt 2`$, so the 1-parent is column 1.
2. **Bad root.** $`m_0 = 1`$, $`p = 1`$, $`s = 1`$. $`G = (0,0)`$, $`B_0 = (1,1)`$. $`\Delta = (1, 1)`$.
3. **Blocks.** Only row 0 grows. $`B_q = (1 + q, 1)`$.

So $`(0,0)(1,1)(2,2)[2] = (0,0)(1,1)(2,1)(3,1)`$.

**Example 3 ($`(0,0)(1,1)(2,1)[2]`$).** An example where the bad root differs from the parent in row 0.

1. **Parents.** $`c = 2`$. The parent in row 0 is column 1. Row 1: the candidates are $`\{0, 1\}`$. $`A_1[1] = 1`$ is not smaller than $`A_2[1] = 1`$. $`A_0[1] = 0`$ is smaller. So the 1-parent is column 0.
2. **Bad root.** $`m_0 = 1`$, $`p = 0`$, $`s = 2`$. $`G`$ is empty, $`B_0 = (0,0)(1,1)`$. $`\Delta = (2, 1)`$.
3. **Blocks.** Only row 0 grows. Since $`0 \preceq_0 0`$ and $`0 \prec_0 1`$, both columns grow. $`B_1 = (2,0)(3,1)`$, $`B_2 = (4,0)(5,1)`$.

So $`(0,0)(1,1)(2,1)[2] = (0,0)(1,1)(2,0)(3,1)(4,0)(5,1)`$.

**Example 4 ($`(0,0,0)(1,1,1)[2]`$).** An example with 3 rows.

1. **Parents.** $`c = 1`$. In each of rows 0, 1, 2, the parent of column 1 is column 0.
2. **Bad root.** $`m_0 = 2`$, $`p = 0`$, $`s = 1`$. $`\Delta = (1, 1, 1)`$.
3. **Blocks.** Rows 0 and 1 grow. $`B_q = (q, q, 0)`$.

So $`(0,0,0)(1,1,1)[2] = (0,0,0)(1,1,0)(2,2,0)`$.

**Example 5 ($`(0,0)(1,0)(2,0)[2]`$).** An example with $`m_0 = 0`$, where no entry grows.

1. **Parents.** $`c = 2`$. The parent in row 0 is column 1. $`A_2[1] = 0`$, so there is no parent in row 1.
2. **Bad root.** $`m_0 = 0`$, $`p = 1`$, $`s = 1`$.
3. **Blocks.** There is no row $`k \lt 0`$, so $`B_q = (1,0)`$.

So $`(0,0)(1,0)(2,0)[2] = (0,0)(1,0)(1,0)(1,0)`$.

**Example 6 (deleting the last column).** The last column of $`(0,0)(1,1)(0,0)`$ has entry 0 in row 0. It has no parent in row 0. So it has no parent in any row (Property 3). Hence $`(0,0)(1,1)(0,0)[N] = (0,0)(1,1)`$ for every $`N`$. Likewise $`(0,0)[N] = ()`$.

**Example 7 ($`(0,0,0)(1,1,1)(2,2,1)(3,1,0)[2]`$).** The array of the examples in §3 and §4.

1. **Bad root.** By the example of §4, $`m_0 = 1`$, $`p = 0`$, $`s = 3`$. $`\Delta = (3, 1, 0)`$.
2. **Blocks.** Only row 0 grows. Each of columns 0, 1, 2 satisfies $`0 \preceq_0 j`$, so all three columns grow.

| block | columns |
|---|---|
| $`B_0`$ | $`(0,0,0)(1,1,1)(2,2,1)`$ |
| $`B_1`$ | $`(3,0,0)(4,1,1)(5,2,1)`$ |
| $`B_2`$ | $`(6,0,0)(7,1,1)(8,2,1)`$ |

So $`A[2] = (0,0,0)(1,1,1)(2,2,1)(3,0,0)(4,1,1)(5,2,1)(6,0,0)(7,1,1)(8,2,1)`$.

**Example 8 ($`(0,0,0)(1,0,0)(1,1,1)[2]`$).** An example where, in the same row, some columns grow and others do not.

1. **Parents.** $`c = 2`$.

   | row | column 0 | column 1 | column 2 |
   |---|---|---|---|
   | 0 | 0 | 1 ← 0 | 1 ← 0 |
   | 1 | 0 | 0 | 1 ← 0 |
   | 2 | 0 | 0 | 1 ← 0 |

   Column 2, row 0: $`A_1[0] = 1`$ is not smaller than $`A_2[0] = 1`$, so the parent is column 0. Column 1 has entry 0 in row 1, so it has no parent there. Hence column 0 is not a 1-ancestor of column 1.
2. **Bad root.** $`m_0 = 2`$, $`p = 0`$, $`s = 2`$. $`\Delta = (1, 1, 1)`$.
3. **Blocks.** Rows 0 and 1 may grow.
   - Column $`j = 0`$: $`0 \preceq_k 0`$, so rows 0 and 1 grow.
   - Column $`j = 1`$: $`0 \prec_0 1`$, so row 0 grows. $`0 \prec_1 1`$ fails, so row 1 does not grow.

   $`B_1 = (1,1,0)(2,0,0)`$, $`B_2 = (2,2,0)(3,0,0)`$.

So $`(0,0,0)(1,0,0)(1,1,1)[2] = (0,0,0)(1,0,0)(1,1,0)(2,0,0)(2,2,0)(3,0,0)`$.

---

A table of some expansions.

| array $`A`$ | $`N`$ | $`A[N]`$ | $`m_0`$ | $`p`$ | $`s`$ |
|---|---|---|---|---|---|
| $`(0,0)`$ | 2 | $`()`$ | none | none | none |
| $`(0,0)(1,0)`$ | 2 | $`(0,0)(0,0)(0,0)`$ | 0 | 0 | 1 |
| $`(0,0)(1,1)`$ | 0 | $`(0,0)`$ | 1 | 0 | 1 |
| $`(0,0)(1,1)`$ | 1 | $`(0,0)(1,0)`$ | 1 | 0 | 1 |
| $`(0,0)(1,1)`$ | 2 | $`(0,0)(1,0)(2,0)`$ | 1 | 0 | 1 |
| $`(0,0)(1,0)(2,0)`$ | 2 | $`(0,0)(1,0)(1,0)(1,0)`$ | 0 | 1 | 1 |
| $`(0,0)(1,1)(2,0)`$ | 2 | $`(0,0)(1,1)(1,1)(1,1)`$ | 0 | 1 | 1 |
| $`(0,0)(1,1)(1,1)`$ | 2 | $`(0,0)(1,1)(1,0)(2,1)(2,0)(3,1)`$ | 1 | 0 | 2 |
| $`(0,0)(1,1)(2,1)`$ | 2 | $`(0,0)(1,1)(2,0)(3,1)(4,0)(5,1)`$ | 1 | 0 | 2 |
| $`(0,0)(1,1)(2,2)`$ | 2 | $`(0,0)(1,1)(2,1)(3,1)`$ | 1 | 1 | 1 |
| $`(0,0,0)(1,1,1)`$ | 2 | $`(0,0,0)(1,1,0)(2,2,0)`$ | 2 | 0 | 1 |
| $`(0,0,0)(1,1,1)(2,1,1)`$ | 2 | $`(0,0,0)(1,1,1)(2,1,0)(3,2,1)(4,2,0)(5,3,1)`$ | 2 | 0 | 2 |
| $`(0,0,0)(1,1,1)(2,2,2)`$ | 2 | $`(0,0,0)(1,1,1)(2,2,1)(3,3,1)`$ | 2 | 1 | 1 |
| $`(0,0,0)(1,0,0)(1,1,1)`$ | 2 | $`(0,0,0)(1,0,0)(1,1,0)(2,0,0)(2,2,0)(3,0,0)`$ | 2 | 0 | 2 |

## 7. E_r and BM4

**Definition (initial array).** The array $`E_r := (0, \ldots, 0)(1, \ldots, 1)`$ with $`r`$ rows is called the **initial array**. Its length is 2.

**Definition (BM4).** The set of arrays with $`r`$ rows obtained from $`E_r`$ by finitely many expansions is called **BM4 with $`r`$ rows**. The copy count may be chosen freely at each step. The union of BM4 with $`r`$ rows over all $`r`$ is called **BM4**. An element of BM4 carries its row count $`r`$ with it.

**Example.** By Example 4, $`E_3[2] = (0,0,0)(1,1,0)(2,2,0)`$, which is an element of BM4 with 3 rows. Expanding further gives the following (computed by computer).

```math
(0,0,0)(1,1,0)(2,2,0)[2] = (0,0,0)(1,1,0)(2,1,0)(3,1,0)
```

All entries in row 2 are 0, so there is no parent in row 2. This expansion is Example 2 with an entry 0 in row 2 added to each column.

For some arrays in the examples of §6 we have not checked whether they are obtained from $`E_r`$. Theorems 1 and 2 of §8 hold for every array, whether or not it is obtained from $`E_r`$.

**Definition (expansion sequence).** For an array $`A`$ with $`r`$ rows and a function $`n : \mathbb N \to \mathbb N`$, the **expansion sequence** is

```math
A^{(0)} := A, \qquad A^{(t+1)} := A^{(t)}[n(t)]
```

$`A^{(t)}`$ is the $`t`$-th array. Its index is written as a superscript to distinguish it from a column $`A_i`$. $`n(t)`$ is the copy count of the $`t`$-th expansion.

**Definition (one-step expansion).** For arrays $`A`$, $`B`$ with $`r`$ rows, the following relation is called **one-step expansion**.

```math
A \mathrel{\triangleleft} B \iff B \ne () \land \exists N \in \mathbb N\ \ A = B[N]
```

The condition $`B \ne ()`$ is there because $`()[N] = ()`$. Without it, $`() \mathrel{\triangleleft} ()`$ would hold, and the relation would not be well-founded.

## 8. The final theorems

The final theorems of this repository ([README](../../README-en.md) "The four final theorems") are as follows. $`r \in \mathbb N`$ is arbitrary.

1. Theorem 1 (termination): for every array $`A`$ with $`r`$ rows and every $`n : \mathbb N \to \mathbb N`$, there is $`T`$ with $`A^{(T)} = ()`$.
2. Theorem 2: on the set of all arrays with $`r`$ rows, one-step expansion $`\triangleleft`$ is well-founded.
3. Theorem 3: on BM4 with $`r`$ rows, $`\triangleleft`$ is well-founded.
4. Theorem 4: on BM4, one-step expansion is well-founded. Expansion does not change the row count, so this relation only holds between arrays with the same row count.

Theorem 2 follows from Theorem 1: an infinite descending sequence $`C_0 \mathrel{\triangleright} C_1 \mathrel{\triangleright} \cdots`$ of $`\triangleleft`$ is an expansion sequence none of whose terms is empty ($`\triangleright`$ is $`\triangleleft`$ in the reverse direction). Theorem 3 is Theorem 2 restricted to a subset. Theorem 4 follows from Theorem 3 for each row count. The proof of Theorem 1 is the topic of [06](06-stable-labels.md) and later notes.

## 9. Where this repository uses it

| Place | Use |
|---|---|
| [README](../../README-en.md) "Notation", "The four final theorems" | arrays, $`A[N]`$, expansion sequences, $`E_r`$, BM4, the four theorems |
| [README](../../README-en.md) "Shape of the proof" | the combinatorial layer (arrays, parents, ancestors, expansion) |
| [notes/01-design.md](../../notes/01-design.md) §1, §2.4 (Japanese) | the shape of the combinatorial layer, and where expansion uses the label interface |
| [notes/02-port.md](../../notes/02-port.md) §1 (Japanese) | where the definitions of arrays and expansion come from |
