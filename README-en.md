[English](README-en.md) | [Japanese](README.md)

# bms-wo-sigma-1: well-foundedness of BMS by Σ₁-elementarity alone

This repository proves in Lean 4, for every number of rows, that the expansion of the Bashicu Matrix System (BM4) always terminates.

The label relation is defined directly on ordinals. The only model-theoretic notion used in its definition is $`\Sigma_1`$-elementary substructure. No constructible universe $`L`$, no admissible ordinal and no elementarity of level $`\Sigma_2`$ or higher is used. The method is the same as what [1y-wo-por](https://github.com/koteitan/1y-wo-por) did for the 1-Y sequence.

- Lean 4.33.1, Mathlib v4.33.1.
- No `sorry` and no new axiom. The only axioms are `propext`, `Classical.choice` and `Quot.sound`.

## What is proved

### Notation

- An array with $`r`$ rows is a finite sequence $`A = (A_0, \ldots, A_{\ell-1})`$ of elements of $`\mathbb N^r`$ (`BM4.Arr r`). Each $`A_i`$ is called a column of $`A`$. $`A_i[k]`$ is the entry of column $`A_i`$ in row $`k`$ ($`k \lt r`$). The case $`\ell = 0`$ is the empty array $`()`$. An array need not be standard.
- $`A[N]`$ is the expansion of the array $`A`$ by the natural number $`N`$ (`BM4.expand A N`, Definition 5.1 of DH's paper).
- The definitions of parents and ancestors are in [study/en/05-bms.md](study/en/05-bms.md).
- If the last column has no parent in any row, $`A[N]`$ is $`A`$ without its last column.
- Otherwise, $`m_0`$ is the largest row number in which the last column has a parent. $`p`$ is the position of the parent of the last column in row $`m_0`$ (the bad root). $`G`$ is the columns left of position $`p`$, and $`B_0`$ is the columns from position $`p`$ up to the one before the last column. Then $`A[N] = G \frown B_0 \frown B_1 \frown \cdots \frown B_N`$. $`B_q`$ is a copy of $`B_0`$, except that in each row $`k \lt m_0`$ the increment $`q \cdot (A_{\ell-1}[k] - A_p[k])`$ is added to column $`p`$ itself and to the columns that have column $`p`$ as a row-$`k`$ ancestor.
- An expansion sequence is the sequence given by $`A^{(0)} = A`$, $`A^{(t+1)} = A^{(t)}[n(t)]`$ (`BM4.seq A n`). Each $`n(t)`$ may be chosen freely.
- $`E_r = ((0,\ldots,0),(1,\ldots,1))`$ (`BM4.E r`). BM4 with $`r`$ rows is the set $`\mathrm{BM4}_r`$ of arrays reached from $`E_r`$ by finitely many expansions (`BM4.Elt r`).

### The four final theorems

The final theorems are in [Por/WellOrdering.lean](Por/WellOrdering.lean), namespace `Por`.

1. `terminates`: for every number of rows $`r`$, every array $`A`$ with $`r`$ rows and every $`n : \mathbb N \to \mathbb N`$, the expansion sequence reaches the empty array.

```math
A^{(0)} = A,\quad A^{(t+1)} = A^{(t)}[n(t)] \quad\implies\quad \exists T,\ A^{(T)} = ()
```

2. `step_wf`: on all arrays with $`r`$ rows, the relation of one expansion step is well-founded. The relation is the following (`Por.Step r`).

```math
A \prec B \iff B \ne () \ \land\ \exists N,\ A = B[N]
```

That is, there is no infinite sequence $`C_0, C_1, C_2, \ldots`$ with $`C_t \ne ()`$ and $`C_{t+1} = C_t[N_t]`$.

3. `R_wf`: on $`\mathrm{BM4}_r`$, the relation of one expansion step is well-founded (`BM4.R r`).
4. `R'_wf`: on BM4 over all row counts, the relation of one expansion step is well-founded (`BM4.R'`). An element of BM4 carries its row count.

```math
\mathrm{BM4} = \{\, (r, A) \mid r \in \mathbb N,\ A \in \mathrm{BM4}_r \,\}
```

The first theorem is the main one. The second follows from the first in a few lines. The third and the fourth are restrictions of the second.

Every array has an initial label (`Por.stable_all`, below), so the first and the second theorems also hold for arrays that are not standard.

## Shape of the proof

The proof has two layers.

- The combinatorial layer (`Bm4/`). This layer assumes only the label interface `BM4.LabelSystem r`. From it, it shows that an expansion lowers the label of the last column (`BM4.descent`, Proposition 19.1 of DH's paper). It is `lean/Bm4/` of [bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern), used unchanged. Its origin is the formalization [dh-bms-wf-formal](https://github.com/koteitan/dh-bms-wf-formal).
- The semantic layer (`Por/`). It provides labels satisfying the interface. The labels are ordinals and the relation is $`R`$ of the next section (`Por.labelSystem r`).

The label interface consists of a well-ordered type of labels $`\mathrm{Lab}`$, a relation $`\mathrm{rel}_k`$ for each layer $`k \in \mathbb N`$, and three properties. The three properties are $`\mathrm{rel}_k(a,b) \Rightarrow a \lt b`$, transitivity, and finite reflection (below).

A stable label of an array $`A`$ is a map $`f`$ from column positions to labels satisfying the following two conditions (`BM4.Stable`, Definition 18.1 of DH's paper). $`i \prec^A_k j`$ reads "column $`i`$ is a row-$`k`$ ancestor of column $`j`$" (`BM4.anc`).

```math
i \lt j \lt \ell \implies f(i) \lt f(j), \qquad k \lt r,\ i \prec^A_k j \implies \mathrm{rel}_k(f(i), f(j))
```

The height is the label of the last column, $`\mathrm{ht}(A,f) = f(\ell-1)`$ (`BM4.ht`). `BM4.descent` says the following. Let $`f`$ be a stable label of $`A`$, with $`A \ne ()`$ and $`A[N] \ne ()`$. Then $`A[N]`$ has a stable label $`g`$ with the following property.

```math
\mathrm{ht}(A[N],g) \lt \mathrm{ht}(A,f)
```

Termination follows. Every array has a stable label. If an expansion sequence never reached the empty array, repeating `BM4.descent` would give an infinite sequence of ordinals whose heights strictly decrease. Ordinals are well-founded, so this cannot happen.

### Differences from the other proofs

- DH's proof uses admissible ordinals as labels and $`L_\alpha \prec^*_{k+2} L_\beta`$ as the relation (equation (15.1) of DH's paper: elementarity for formulas with at most $`k+2`$ alternations). It uses KP set theory.
- [bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) replaced the labels by Carlson's structure $`R_N`$. There the relation $`\alpha \le_{j+1} \beta`$ of layer $`j`$ is $`\Sigma_{j+1}`$-elementarity, which uses formulas with several quantifier blocks.
- In this repository every layer is $`\Sigma_1`$. The only quantifiers are one block of existential quantifiers. The strength gained at higher layers comes from putting the relations toward the top, $`\mathrm{Top}_j`$, into the language as atomic symbols.
- [1y-wo-por](https://github.com/koteitan/1y-wo-por) used the same method for 1-Y. The 1-Y interface needs a root index $`\eta`$. So there the relation is $`R(k,\eta,a,b)`$, $`\mathrm{Rel}_j`$ has 3 arguments, $`\mathrm{Top}_j`$ has 2 arguments, and the recursion key is (top, layer, index). The BMS interface needs no $`\eta`$. So here the relation is $`R(k,a,b)`$, $`\mathrm{Rel}_j`$ has 2 arguments, $`\mathrm{Top}_j`$ has 1 argument, and the recursion key is (top, layer).

## The relation R

$`R(k,a,b)`$ reads "at layer $`k`$, $`a`$ is stable toward $`b`$". It is defined by one formula.

```math
R(k,a,b) \iff a \lt b \ \land\ \mathfrak A^{a}_{k} \preccurlyeq_{\Sigma_1} \mathfrak A^{b}_{k}
```

$`\mathfrak A^{\gamma}_{k}`$ is the structure of height $`\gamma`$ at layer $`k`$. Its domain is $`\{x \mid x \lt \gamma\}`$.

```math
\mathfrak A^{\gamma}_{k} = \bigl(\gamma;\ \lt,\ (\mathrm{Rel}_j)_{j \in \mathbb N},\ (\mathrm{Top}_j)_{j \lt k}\bigr)
```

- Inner relations: $`\mathrm{Rel}_j(x,y) :\iff R(j,x,y)`$, for every layer $`j`$.
- Top predicates: $`\mathrm{Top}_j(x) :\iff R(j,x,\gamma)`$, only for layers $`j \lt k`$.
- $`\preccurlyeq_{\Sigma_1}`$ is $`\Sigma_1`$-elementary substructure: every $`\Sigma_1`$ formula of layer $`k`$ with parameters below $`a`$ has the same truth value in both structures (`Por.Elem`, `Por.ElemL`).
- A $`\Sigma_1`$ formula is given by a tuple $`(m,n,D,\mathit{bb},\mathit{np})`$. $`\mathit{np}`$ is the number of parameters, $`\mathit{bb}`$ the number of existentially quantified variables, $`n \le \mathit{np}+\mathit{bb}`$ the number of variables read, $`m`$ a bound on the layers of the symbols read, and $`D`$ a set of atomic diagrams. The formula reads "there are $`\mathit{bb}`$ values below the height such that the atomic diagram of the parameters and these values is in $`D`$" (`Por.Sat`). In Lean $`\mathit{np}`$ is written `r`. It is not the row count $`r`$.

The right-hand side reads $`R`$ itself. So $`R`$ is defined by well-founded recursion on the key $`(b,k)`$ in lexicographic order (`Por.stepF`, `Por.RF`). Every $`R`$ read on the right has a smaller key.

- In $`\mathrm{Rel}_j(x,y)`$ we have $`y \lt b`$.
- In the top predicates of $`\mathfrak A^{a}_k`$ the top is $`a \lt b`$.
- In the top predicates of $`\mathfrak A^{b}_k`$ the layer is $`j \lt k`$.

In Lean this is `Por.R` with its defining equation `Por.R_iff` ([Por/Relation.lean](Por/Relation.lean)).

### Where the label interface goes

| Interface | Content | Lean name |
|---|---|---|
| label type | ordinals; $`\lt`$ is a well-order | `Ordinal` of Mathlib |
| `rel_lt` | $`R(k,a,b)`$ implies $`a \lt b`$ | `Por.R_lt` |
| `rel_trans` | $`R(k,a,b)`$ and $`R(k,b,c)`$ imply $`R(k,a,c)`$ | `Por.R_trans` |
| `reflect` | finite reflection | `Por.reflect` |
| initial label | every array has a stable label | `Por.stable_all` |

`Por.labelSystem r : BM4.LabelSystem r` packs the first four rows ([Por/Model.lean](Por/Model.lean)). The last row is not part of the interface. The termination proof uses it as the label of the first array $`A^{(0)}`$ of an expansion sequence.

Transitivity is proved by composing two elementarity steps. $`\mathfrak A^{a}_k \preccurlyeq_{\Sigma_1} \mathfrak A^{b}_k`$ and $`\mathfrak A^{b}_k \preccurlyeq_{\Sigma_1} \mathfrak A^{c}_k`$ share the same middle structure $`\mathfrak A^{b}_k`$.

Finite reflection is the following statement. Let $`n \lt r`$ and $`R(n,\alpha,\beta)`$. Let $`X`$ be a finite set below $`\alpha`$. Let $`s \gt 0`$ and $`\alpha \le y_0 \lt \cdots \lt y_{s-1} \lt \beta`$. Then there is $`y'`$ with $`X \lt y'_0 \lt \cdots \lt y'_{s-1} \lt \alpha`$ such that the following hold for $`x \in X`$, $`i, j \lt s`$, $`k \lt r`$ and $`m \lt n`$.

```math
R(k,x,y_i) \Rightarrow R(k,x,y'_i), \qquad R(k,y_i,y_j) \Rightarrow R(k,y'_i,y'_j), \qquad R(m,y_i,\beta) \Rightarrow R(m,y'_i,\alpha)
```

The proof writes the whole atomic diagram of $`(X, y)`$ as one $`\Sigma_1`$ formula. The diagram reads the order, $`\mathrm{Rel}_k`$ for layers $`k \lt r`$, and $`\mathrm{Top}_m`$ for layers $`m \lt n`$. The parameters are $`X`$ and the existentially quantified variables are $`y`$. This formula is true in $`\mathfrak A^{\beta}_n`$. By $`R(n,\alpha,\beta)`$ it is also true in $`\mathfrak A^{\alpha}_n`$. Its witnesses are $`y'`$. $`\mathrm{Top}_m(y'_i)`$ in $`\mathfrak A^{\alpha}_n`$ is $`R(m,y'_i,\alpha)`$.

The initial label comes from a chain $`c_0 \lt c_1 \lt \cdots`$ of closure points below $`\omega_1`$ (`Por.cC`).

- $`\gamma`$ is good if $`(\gamma; \lt, R, \mathrm{Top}^{\omega_1}) \preccurlyeq_{\Sigma_1} (\omega_1; \lt, R, \mathrm{Top}^{\omega_1})`$ in the full language with the top predicates of $`\omega_1`$ (`Por.Good`).
- $`\lambda(\gamma)`$ is the closure of $`\gamma`$ under witnesses. If $`\gamma \lt \omega_1`$, then $`\gamma \lt \lambda(\gamma) \lt \omega_1`$ and $`\lambda(\gamma)`$ is good (`Por.lam`, `Por.lam_good`).
- $`c_0 = \lambda(0)`$ and $`c_{t+1} = \lambda(c_t)`$.
- At a good $`\alpha \lt \omega_1`$, $`R(j,x,\alpha) \iff R(j,x,\omega_1)`$ for $`x \lt \alpha`$ (`Por.top_abs`, by induction on the layer $`j`$).
- Hence $`i \lt j`$ implies $`R(k,c_i, c_j)`$ at every layer $`k`$ (`Por.chain_R`).
- So the map $`i \mapsto c_i`$ is a stable label of every array, whatever its ancestor relation is (`Por.stable_all`).

The proof uses the axiom of choice and the regularity of $`\omega_1`$. The labels are ordinals below $`\omega_1`$. No ordinal bound and no notation system is obtained.

The full design and proof are in [notes/01-design.md](notes/01-design.md) (in Japanese).

## Mathematical background

[study/](study/en/README.md) has background notes for reading this repository (in English and Japanese). There are nine: ordinals and $`\omega_1`$, well-founded relations and well-founded recursion, structures and $`\Sigma_1`$-elementary substructures, Carlson's patterns of resemblance, the Bashicu Matrix System, stable labels and the descent of the height, the relation $`R`$, closure below $`\omega_1`$ and the chain, and the proofs of the interface and the final theorems. The notes contain no Lean.

## Files

| Path | Content |
|---|---|
| [Por/](Por/) | The semantic layer. 9 files, about 790 lines. Uses Mathlib |
| [Bm4/](Bm4/) | The combinatorial layer. 14 modules, about 3,000 lines. Copied from bms-elem-pattern |
| [notes/](notes/) | Design notes (in Japanese) |
| [study/](study/en/README.md) | Notes on the mathematical background (in English and Japanese) |
| [Audit.lean](Audit.lean) | The axiom audit. Not part of any `lean_lib` |
| [LICENSE](LICENSE), [NOTICE](NOTICE) | CC BY-SA 4.0 and the record of origins |

The files of `Por/`, in import order:

| File | Content |
|---|---|
| [Tuple.lean](Por/Tuple.lean) | the ordinal type `Ord`, concatenation `cat` |
| [Omega1.lean](Por/Omega1.lean) | $`\omega_1`$ (`Om`), enumeration of countable ordinals `enumBelow` |
| [Formula.lean](Por/Formula.lean) | atomic diagrams `Diag`, truth of $`\Sigma_1`$ formulas `Sat`, layer-restricted elementarity `ElemL` |
| [Relation.lean](Por/Relation.lean) | the recursion `stepF`, `RF`, the relation `R`, `R_iff`, `R_lt`, `R_trans` |
| [Reflection.lean](Por/Reflection.lean) | finite reflection `reflect` |
| [Closure.lean](Por/Closure.lean) | good points `Good`, closure points `lam`, `lam_good` |
| [Chain.lean](Por/Chain.lean) | absoluteness of the top predicates `top_abs`, the chain `cC`, `chain_R` |
| [Model.lean](Por/Model.lean) | the label interface `labelSystem`, the label of every array `stable_all` |
| [WellOrdering.lean](Por/WellOrdering.lean) | the four final theorems |

The files of `Bm4/`, in import order. The numbers of definitions, lemmas and propositions are those of DH's paper.

| File | Content |
|---|---|
| [Defs.lean](Bm4/Defs.lean) | arrays `Arr`, parents `parent`, ancestors `anc`, expansion `expand`, $`E_r`$, BM4 `Elt`, the expansion relations `R`, `R'` (Definitions 1.1, 2.1, 5.1) |
| [Basic.lean](Bm4/Basic.lean) | basic properties of parents and ancestors (Lemma 2.2), prefix invariance (Lemma 3.1), convexity of parent candidates (Lemma 4.1) |
| [Copy.lean](Bm4/Copy.lean) | setup for the copy lemma (Theorem 6.3): the bad-root data `BadRoot`, positions and entries of $`G \frown B_0 \frown B_1 \frown \cdots`$ |
| [CopyPaper/Interval.lean](Bm4/CopyPaper/Interval.lean) | interval-internal parents (Definition 6.1, Lemma 6.2), the six claims (C1)–(C6) as predicates |
| [CopyPaper/L1.lean](Bm4/CopyPaper/L1.lean) | Lemma 6.4: claim (C1) |
| [CopyPaper/L3.lean](Bm4/CopyPaper/L3.lean) | Lemma 6.5: claim (C3) for rows $`k \lt m_0`$ |
| [CopyPaper/L4.lean](Bm4/CopyPaper/L4.lean) | Lemmas 6.9, 6.10: the boundary claim (C4) |
| [CopyPaper/L5.lean](Bm4/CopyPaper/L5.lean) | Lemma 6.6: claim (C5), parents do not jump over copies |
| [CopyPaper/L6.lean](Bm4/CopyPaper/L6.lean) | Lemma 6.8: claim (C6) |
| [CopyPaper/L2.lean](Bm4/CopyPaper/L2.lean) | Lemma 6.7: claim (C2) |
| [CopyPaper/Assemble.lean](Bm4/CopyPaper/Assemble.lean) | the assembly of Proposition 6.11, Theorem 6.3, Corollary 6.12 |
| [CopyPaper/Char.lean](Bm4/CopyPaper/Char.lean) | existence of parents in the expanded array (in the form Proposition 7.1 uses) |
| [Expand.lean](Bm4/Expand.lean) | connects `expand` (Definition 5.1) with the bad-root data |
| [Label.lean](Bm4/Label.lean) | the label interface `LabelSystem`, stable labels `Stable` (Definition 18.1), height `ht`, descent `descent` (Proposition 19.1) |

The files of `notes/`:

- [01-design.md](notes/01-design.md): design of the semantic layer: the list of interface properties, the definition of $`R`$, the proof of each property, and the Lean names.
- [02-port.md](notes/02-port.md): record of how `Bm4/` was brought over, and of how `Por/` was made from `Por/` of 1y-wo-por.

## Building

Lean 4.33.1 and Mathlib v4.33.1 (`lean-toolchain`, `lakefile.toml`).

The author checked the proof with the checking tool leanman, from the repository root:

```sh
leanman build -C . Bm4 Por
leanman check -C . Audit.lean
```

The same can be done with lake alone:

```sh
lake exe cache get
lake build Bm4 Por
lake env lean Audit.lean
```

- The default target is `Por`. `Por` imports every module of `Bm4`. So a bare `lake build` already builds every module the final theorems need.
- `Audit.lean` is checked after `Bm4` and `Por` are built.

## Axiom audit

[Audit.lean](Audit.lean) runs `#print axioms` on the main theorems. They are:

- final theorems: `Por.terminates`, `Por.step_wf`, `Por.R_wf`, `Por.R'_wf`;
- the model: `Por.labelSystem`, `Por.reflect`, `Por.R_trans`, `Por.stable_all`, `Por.chain_R`, `Por.R_iff`;
- the descent of the combinatorial layer: `BM4.descent`.

Every line prints output of the following form.

```text
'Por.terminates' depends on axioms: [propext, Classical.choice, Quot.sound]
```

- Each uses only the three standard axioms of Lean. There is no `sorryAx`.
- The sources contain no `sorry` and no `axiom` declaration.

## References

- DH, "Bashicu Matrix System ver. 4 の停止性と展開関係の整礎性" (termination of BM4 and well-foundedness of its expansion relation), Googology Wiki (Japanese) (2026). [paper PDF](https://googology.fandom.com/ja/wiki/%E3%83%95%E3%82%A1%E3%82%A4%E3%83%AB%3ABM4%28%E4%BD%9C%E6%88%90%E8%80%85%E6%83%85%E5%A0%B1%E4%BB%98%E3%81%8D%29.pdf), [announcement blog post](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0%3ADeltaEta22223/BM4%E3%81%AE%E5%81%9C%E6%AD%A2%E6%80%A7%E8%A8%BC%E6%98%8E)
- R. Hunter, "Well-Orderedness of the Bashicu Matrix System", arXiv:2307.04606 (2023). [arXiv](https://arxiv.org/abs/2307.04606)
- T. J. Carlson, "Elementary Patterns of Resemblance", Annals of Pure and Applied Logic 108 (2001), 19–77.
- koteitan, [dh-bms-wf-formal](https://github.com/koteitan/dh-bms-wf-formal). A Lean 4 formalization of DH's proof. The origin of `Bm4/`.
- koteitan, [bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern). Termination of BMS by patterns of resemblance ($`\Sigma_n`$-elementarity). `Bm4/` is copied from here.
- koteitan, [1y-wo-por](https://github.com/koteitan/1y-wo-por). Well-foundedness of 1-Y by $`\Sigma_1`$-elementarity alone. The origin of `Por/`.
- Phyrion, [1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean). A Lean formalization of the well-foundedness of 1-Y.
- The mathlib Community, [Mathlib](https://github.com/leanprover-community/mathlib4).

## License

This repository is licensed under CC BY-SA 4.0 ([LICENSE](LICENSE)). [NOTICE](NOTICE) records the origins and the changes.

- `Bm4/`: copied from `lean/Bm4/` of [bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) (CC BY-SA 4.0). Its origin is [dh-bms-wf-formal](https://github.com/koteitan/dh-bms-wf-formal). It is ported from Lean 4.30.0 to 4.33.1. The only change of a proof is `col_pos` in `Bm4/Copy.lean`. Each file says so in its header.
- `Por/`: made from `Por/` of [1y-wo-por](https://github.com/koteitan/1y-wo-por), whose helpers come from `lean/Pattern/` of bms-elem-pattern. The root index of 1-Y is removed, and the model is stated against the label interface `BM4.LabelSystem` of `Bm4/`. Each file names its sources in its header.
- All code is by the same author (koteitan). No code from a project without a license is copied or adapted.
