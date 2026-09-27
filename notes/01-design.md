[← README](../README.md) | [PLAN](../PLAN.md) | [移植の記録 →](02-port.md)

# 設計：Σ₁ 初等性だけによる BMS の整礎性

意味の層の設計のノートである。組合せの層がラベルに求める約束を正確に並べ（§2）、それを満たす関係を順序数だけで定義し（§3）、各約束を証明する（§4）。§5 に注意、§6 に Lean のファイルを書く。`Bm4/` と `Por/` をどこから持ってきたかは [02-port.md](02-port.md) に分けた。

## 0. 要約

- 目標：バシク行列システム（BM4）の展開がいつか必ず止まることを、すべての行数 $`r`$ について示す。構成的宇宙 $`L`$ も、許容順序数も、KP 集合論も、$`Σ_2`$ 以上の初等性も使わない。
- 方法：組合せの層（`Bm4/`）は変えずに使う。これは DH の論文の BM4 の証明の組合せの部分を形式化したものである（[dh-bms-wf-formal](https://github.com/koteitan/dh-bms-wf-formal) から [bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) の `lean/Bm4/` を経て来た）。意味の層（`Por/`）で、ラベルの約束 `BM4.LabelSystem r` を満たすラベルを、順序数の上に直接定義した関係 $`R`$ で与える。
- 関係：$`R(k,a,b)`$ は「層 $`k`$ の言語で、高さ $`a`$ の構造が高さ $`b`$ の構造の $`Σ_1`$ 初等部分構造である」ことである。言語は、すべての層の $`R`$（高さより下の点どうし）と、高さへの $`R`$ を表す上端述語（層 $`j \lt k`$ だけ）を持つ。$`R`$ は（上端、層）の辞書式順序による整礎再帰で定義する。
- 状態（2026-09-28）：定義と全部の約束の証明と最終定理 4 つを Lean で書いた。Lean 4.33.1 と Mathlib v4.33.1 で緑である。`sorry` は無い。公理は `propext`、`Classical.choice`、`Quot.sound` だけである（`Audit.lean`）。
- [1y-wo-por](https://github.com/koteitan/1y-wo-por) の意味の層から、根の添字 $`η`$ を除いたものである。BMS の約束には $`η`$ が要らないからである。代わりに推移律が要るが、これは定義からすぐに出る（§4.4）。

## 1. 全体の形

証明は二層に分かれる。

- 組合せの層（`Bm4/`）。$`r`$ 行の配列、列の親と先祖、展開 $`A[N]`$ を定義する。配列の各列に、ラベルの型の元を付ける。展開したあとの配列にも、最後の列のラベルがもっと小さい付け方があることを示す（`BM4.descent`、DH の論文の命題 19.1）。この層がラベルについて使うのは、`BM4.LabelSystem r` の場だけである。
- 意味の層（`Por/`）。`BM4.LabelSystem r` を満たすラベルを与える（`Por.labelSystem r`）。さらに、どの配列にも最初のラベルがあることを示す（`Por.stable_all`）。

ラベルを何にするかは、証明によって違う。

| 証明 | ラベル | 層 $`k`$ の関係 |
|---|---|---|
| DH の論文 | 許容順序数 | $`L_α \prec^*_{k+2} L_β`$（式 (15.1)）。KP 集合論を使う |
| [bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) | Carlson の構造 $`\mathcal R_N`$ の順序数 | $`α \le_{k+1} β`$。$`Σ_{k+1}`$ 初等性で、量化子のブロックが複数ある |
| このリポジトリ | $`ω_1`$ より下の順序数 | $`R(k,α,β)`$。どの層も $`Σ_1`$ 初等性で、上端述語を原子記号として持つ |

bms-elem-pattern の有限反映は、層 $`n \ge 1`$ で $`Σ_{n+1}`$ の文と、共終な連続性の補題を使う。このリポジトリでは、上端への関係が原子記号なので、それらは要らない（§3.8）。

## 2. 約束の一覧

### 2.1 ラベルの約束

組合せの層の約束は `Bm4/Label.lean` の次の構造である。

```lean
structure LabelSystem (r : ℕ) where
  Lab : Type u
  [linOrd : LinearOrder Lab]
  [wf : WellFoundedLT Lab]
  rel : ℕ → Lab → Lab → Prop
  rel_lt : ∀ {k a b}, rel k a b → a < b
  rel_trans : ∀ {k a b c}, rel k a b → rel k b c → rel k a c
  reflect : ∀ (n : ℕ) (α β : Lab), n < r → rel n α β →
    ∀ (X : Finset Lab), (∀ x ∈ X, x < α) →
    ∀ (s : ℕ) (y : ℕ → Lab), 0 < s → (∀ i j, i < j → j < s → y i < y j) →
      (∀ i, i < s → α ≤ y i) → (∀ i, i < s → y i < β) →
    ∃ y' : ℕ → Lab,
      (∀ i j, i < j → j < s → y' i < y' j) ∧
      (∀ i, i < s → y' i < α) ∧
      (∀ x ∈ X, x < y' 0) ∧
      (∀ x ∈ X, ∀ i, i < s → ∀ k, k < r → rel k x (y i) → rel k x (y' i)) ∧
      (∀ i j, i < s → j < s → ∀ k, k < r → rel k (y i) (y j) → rel k (y' i) (y' j)) ∧
      (∀ i, i < s → ∀ m, m < n → rel m (y i) β → rel m (y' i) α)
```

読み方。

- `Lab` はラベルの型で、整列している（線形順序で、$`\lt`$ が整礎）。
- `rel k a b` は「層 $`k`$ で、ラベル $`a`$ は $`b`$ へ安定している」と読む。以下 $`\mathrm{rel}_k(a,b)`$ と書く。
- `reflect` は有限反映（DH の論文の定理 17.1）である。$`n \lt r`$、$`\mathrm{rel}_n(α,β)`$、$`X`$ は $`α`$ より下の有限集合、$`s \gt 0`$、$`α \le y_0 \lt \cdots \lt y_{s-1} \lt β`$ とする。このとき $`y'_0 \lt \cdots \lt y'_{s-1} \lt α`$ で、次の (a)〜(d) を満たすものがある。

```math
\begin{aligned}
&\text{(a)}\quad \forall x \in X,\ x \lt y'_0 \cr
&\text{(b)}\quad \forall x \in X\ \forall i \lt s\ \forall k \lt r,\ \mathrm{rel}_k(x,y_i) \Rightarrow \mathrm{rel}_k(x,y'_i) \cr
&\text{(c)}\quad \forall i, j \lt s\ \forall k \lt r,\ \mathrm{rel}_k(y_i,y_j) \Rightarrow \mathrm{rel}_k(y'_i,y'_j) \cr
&\text{(d)}\quad \forall i \lt s\ \forall m \lt n,\ \mathrm{rel}_m(y_i,β) \Rightarrow \mathrm{rel}_m(y'_i,α)
\end{aligned}
```

(b)(c) は層 $`k \lt r`$ のすべてについて言う。$`k`$ は $`n`$ より大きくてもよい。(d) は層 $`m \lt n`$ だけについて言う。

### 2.2 安定なラベルと高さの降下

配列 $`A`$ は長さ $`\ell`$ と列 $`A_0, …, A_{\ell-1}`$ を持つ。$`i \prec^A_k j`$ は「列 $`i`$ は列 $`j`$ の行 $`k`$ の先祖である」ことである（`BM4.anc A k i j`）。

$`A`$ の安定なラベルとは、写像 $`f : ℕ → \mathrm{Lab}`$ で次を満たすものである（`BM4.Stable`、DH の論文の定義 18.1）。

```math
i \lt j \lt \ell \implies f(i) \lt f(j), \qquad k \lt r,\ j \lt \ell,\ i \prec^A_k j \implies \mathrm{rel}_k(f(i), f(j))
```

高さは $`\mathrm{ht}(A,f) := f(\ell-1)`$ である（`BM4.ht`）。組合せの層の中心の定理は次である。

```lean
theorem descent {A : Arr r} {f : ℕ → S.Lab} (hf : Stable S A f) (h0 : 0 < A.len) (N : ℕ)
    (h0' : 0 < (expand A N).len) :
    ∃ g, Stable S (expand A N) g ∧ ht S (expand A N) g < ht S A f
```

### 2.3 約束の表

| 記号 | 約束の場 | 内容 | 本モデルの Lean 名 |
|---|---|---|---|
| L0 | `Lab`、`linOrd`、`wf` | ラベルの型と整列順序 | `Ord := Ordinal.{0}`。順序は Mathlib のもの |
| L1 | `rel` | 層ごとの関係 | `R` |
| L2 | `rel_lt` | $`R(k,a,b)`$ なら $`a \lt b`$ | `R_lt` |
| L3 | `rel_trans` | $`R(k,a,b)`$ かつ $`R(k,b,c)`$ なら $`R(k,a,c)`$ | `R_trans` |
| L4 | `reflect` | 有限反映 | `reflect` |
| L5 | （約束の外） | どの配列にも安定なラベルがある | `stable_all` |

L0〜L4 をまとめたものが `Por.labelSystem r : BM4.LabelSystem.{1} r` である（`Por/Model.lean`）。宇宙が 1 なのは、`Ordinal.{0}` が `Type 1` の元だからである。

L5 は約束には入っていない。最終定理の証明が、展開の列の最初の配列のラベルとして使う（§4.9）。

### 2.4 組合せの層での使われ方

- L4：`BM4.descent` の場合 2（最後の列に親がある）で、コピーを 1 つ作るたびに 1 回呼ぶ（`BM4.BadRoot.inv_succ`）。引数は次のとおりである。
  - $`n := m_0`$（最後の列が親を持つ行の番号の最大）。$`m_0 \lt r`$ である。
  - $`α := f(p)`$（悪い根のラベル）、$`β := f(c)`$（最後の列のラベル）。$`p`$ は $`c`$ の行 $`m_0`$ の親なので、安定性から $`\mathrm{rel}_{m_0}(α,β)`$ である。
  - $`X`$ は、すでにラベルを付けた列（$`B_q`$ の先頭より左）のラベルの集合である。
  - $`y_i := f(p+i)`$（$`i \lt s`$）は悪い部分 $`B_0`$ のラベルである。
  - 得た $`y'`$ を、コピー $`B_q`$ の新しいラベルにする。新しいコピー $`B_{q+1}`$ には、元のラベル $`y`$ を付ける。
- L3：場合 2 で、先祖が隣のコピー $`B_q`$ にある場合に 1 回使う（DH の論文の注意 19.2 の場合 (f)）。$`\mathrm{rel}_k(y'_{i}, α)`$ と $`\mathrm{rel}_k(α, y_j)`$ をつなぐ。
- L2：`BM4.descent` の中では使わない。約束の場なので、与える必要はある。
- L0：最終定理が、高さの集合の最小元を取るところで使う（§4.9）。

### 2.5 要らないもの

- dh-bms-wf-formal の約束にあった `rel_mono`（層についての単調性）と `init`（すべての層で結ばれた 2 つのラベルがあること）は、bms-elem-pattern で約束から除かれた。命題 19.1 はどちらも使わない。同時に、行の数 $`r`$ が約束の引数になった。
- 1-Y の約束にあった定義域 $`D`$、根の添字 $`η`$、添字の弱化は無い。
- ラベルの上界、ラベルが可算であること、配列が標準形であることは要らない。

## 3. 定義

### 3.1 記号

- $`\mathrm{Ord}`$ は順序数全体（Lean では `Ordinal.{0}`、別名 `Ord`）。$`ω_1`$ は最初の非可算順序数（Lean では `Om`）。
- 鍵 $`(b,k) ∈ \mathrm{Ord} × ℕ`$ の辞書式順序：$`(b',k') \lhd (b,k) :⟺ b' \lt b ∨ (b' = b ∧ k' \lt k)`$。上端が外側である。2 つの整列順序の辞書式積なので、$`\lhd`$ は整礎である。

### 3.2 言語と Σ₁ 論理式

記号は次の 3 種類である。

- 2 変数の $`\lt`$。
- 各 $`j ∈ ℕ`$ について、2 変数の $`\mathrm{Rel}_j`$。
- 各 $`j ∈ ℕ`$ について、1 変数の $`\mathrm{Top}_j`$。

$`Σ_1`$ 論理式は $`∃ \vec y\ ψ(\vec p, \vec y)`$ の形で、$`ψ`$ は量化子を含まない。1 つの論理式は有限個の記号しか使わない。

Lean では、論理式を 5 つ組 `(m, n, D, bb, r)` で表す。このノートでは、パラメータの数を $`\mathit{np}`$ と書く（Lean では `r`）。行の数 $`r`$ と区別するためである。

- $`m`$ は記号の上限で、$`\mathrm{Rel}_j`$ と $`\mathrm{Top}_j`$ は $`j \lt m`$ だけを使う。
- $`\mathit{np}`$ はパラメータの数、$`\mathit{bb}`$ は存在量化する変数の数、$`n \le \mathit{np} + \mathit{bb}`$ は行列が読む変数の数である。
- $`D`$ は行列で、`Diag m n` の部分集合である。`Diag m n` は $`n`$ 点の完全な原子図式（$`\lt`$、$`\mathrm{Rel}_j`$、$`\mathrm{Top}_j`$ のビット）の型で、有限である。量化子の無い論理式は、それを満たす完全な原子図式の集合で表せる。
- 変数の値の列は、パラメータ $`p_0, …, p_{\mathit{np}-1}`$ のあとに証人 $`y_0, …, y_{\mathit{bb}-1}`$ を並べたもの（`cat np p y`）である。

$`\lt`$ のビットは線形順序を決めるので、等号も決まる。等号の記号は要らない。

見える上端述語は、層の番号だけで決まる。層 $`k`$ の論理式では、$`\mathrm{Top}_j`$ は $`j \lt k`$ のときだけ見える（`below k j :⟺ j < k`）。見えないビットは偽と読む（`diagM`）。見えるかどうかは層の番号だけで決まり、点の位置にも値にもよらない。この性質は §4.7 で使う。

### 3.3 層 k の構造

$`R`$ が、必要なところで定義済みだとする。高さ $`γ`$、層 $`k`$ の構造を次で定める。領域は $`\{x : x \lt γ\}`$ である。

```math
\mathfrak A^{γ}_{k} = \bigl(γ;\ \lt,\ (\mathrm{Rel}_j)_{j∈ℕ},\ (\mathrm{Top}_j)_{j \lt k}\bigr)
```

```math
\begin{aligned}
\mathrm{Rel}_j(x,y) &:⟺ R(j,x,y) && (j ∈ ℕ),\cr
\mathrm{Top}_j(x) &:⟺ R(j,x,γ) && (j \lt k).
\end{aligned}
```

- $`\mathrm{Rel}_j`$ は内部の関係である。すべての層 $`j`$ を持つ。点はどれも高さより下にある。
- $`\mathrm{Top}_j`$ は上端述語である。層 $`j \lt k`$ だけを持つ。
- 層 $`k`$ の論理式とは、この言語の $`Σ_1`$ 論理式である。

### 3.4 関係 R

```math
R(k,a,b) \;:⟺\; a \lt b \ ∧\ \mathfrak A^{a}_{k} ≼_{Σ_1} \mathfrak A^{b}_{k}
```

ここで $`\mathfrak A^{a}_{k} ≼_{Σ_1} \mathfrak A^{b}_{k}`$ は、層 $`k`$ のすべての $`Σ_1`$ 論理式 $`φ`$ と、すべてのパラメータ $`\vec p \lt a`$ について、次が成り立つことである。

```math
\mathfrak A^{a}_{k} ⊨ φ(\vec p) \iff \mathfrak A^{b}_{k} ⊨ φ(\vec p)
```

- 2 つの構造の上端述語は別の関係である。$`\mathfrak A^{a}`$ では $`a`$ への $`R`$、$`\mathfrak A^{b}`$ では $`b`$ への $`R`$ である。
- 量化子の無い $`φ`$ を取ると、$`a`$ より下の点では、見える原子の真偽が一致する。特に、$`x \lt a`$、$`j \lt k`$ について $`R(j,x,a) ⟺ R(j,x,b)`$ である。したがって $`\mathfrak A^{a}_{k}`$ は $`\mathfrak A^{b}_{k}`$ の部分構造で、しかも $`Σ_1`$ 初等である。
- 読み方は「層 $`k`$ で、$`a`$ は $`b`$ へ安定している」である。

再帰。$`R`$ は鍵 $`(b,k)`$ についての $`\lhd`$ による整礎再帰で、すべての $`a`$ について一度に定義する。$`(b,k)`$ の定義が読む $`R`$ は次の 3 種類だけで、どれも鍵が小さい。

1. $`\mathrm{Rel}_j(x,y)`$：点はすべて高さ（$`a`$ か $`b`$）より下なので $`y \lt b`$。鍵は $`(y,j) \lhd (b,k)`$。
2. $`\mathfrak A^{a}`$ の上端述語 $`R(j,x,a)`$：鍵は $`(a,j)`$ で、$`a \lt b`$。
3. $`\mathfrak A^{b}`$ の上端述語 $`R(j,x,b)`$：鍵は $`(b,j)`$ で、$`j \lt k`$。

$`R`$ は $`\mathrm{Ord}`$ 全体で定義される。ラベルとして使うのは $`ω_1`$ より下の順序数である。$`ω_1`$ は L5 の補助の上端にだけ現れる。

### 3.5 ラベルのデータ（L0、L1）

$`\mathrm{Lab} := \mathrm{Ord}`$、順序は $`\lt`$、$`\mathrm{rel}_k := R(k,\cdot,\cdot)`$ とする。行の数 $`r`$ は、$`R`$ の定義には現れない。$`r`$ は有限反映の (b)(c) の層の範囲 $`k \lt r`$ にだけ現れる。

### 3.6 L5 のための補助

- 周りの構造 $`\mathfrak B := (ω_1;\ \lt,\ (\mathrm{Rel}_j)_{j∈ℕ},\ (\mathrm{Top}^{ω_1}_j)_{j∈ℕ})`$。ここで $`\mathrm{Top}^{ω_1}_j(x) :⟺ R(j,x,ω_1)`$ で、すべての層の上端述語を持つ。
- $`\mathrm{Good}(α) :⟺ \mathfrak B{\restriction}α ≼_{Σ_1} \mathfrak B`$（すべての記号を使う言語で）。$`\mathfrak B{\restriction}α`$ は $`\mathfrak B`$ を $`α`$ に制限したもので、上端述語は $`ω_1`$ へのもののままである。README では「$`α`$ はよい」と言う。
- $`0 \lt γ \lt ω_1`$ に対し、全射 $`e_γ : ℕ → γ`$ を 1 つ選ぶ（`enumBelow`）。
- $`h(φ, \vec p)`$（`witHeight`）：$`\mathfrak B ⊨ φ(\vec p)`$ なら、選んだ証人 $`\vec y`$ について $`\sup_i (y_i + 1)`$。そうでなければ 0。
- $`\mathrm{next}(γ) := \max\bigl(γ, \sup_{(φ,l)} h(φ, e_γ ∘ l)\bigr) + 1`$（`next`）。$`φ`$ は $`Σ_1`$ 論理式全体を、$`l`$ は自然数の有限列全体を動く。
- $`λ(γ) := \sup_{t ∈ ℕ} \mathrm{next}^t(γ)`$（`lam`）。
- 鎖：$`c_0 := λ(0)`$、$`c_{t+1} := λ(c_t)`$（`cC`）。

$`\mathrm{Good}`$ な点の集合が閉じていることは示していないし、使わない。そのため club とは呼ばない。

### 3.7 Lean の名前との対応

| 数学 | Lean 名（名前空間 `Por`） |
|---|---|
| 完全な原子図式の型 | `Diag m n` |
| 内部の関係と上端述語の型 | `RelF := ℕ → Ord → Ord → Prop`、`TopF := ℕ → Ord → Prop` |
| 点の列の原子図式（見えないビットは偽） | `diagM rel top allow m n v` |
| 高さ $`M`$ で $`Σ_1`$ 論理式が真 | `Sat rel top allow M m n D bb r p` |
| 見えるビット | `below k`（層 $`k`$）、`full`（全部） |
| $`Σ_1`$ 初等性 | `ElemL rel topA topB k a b`、真の関係では `Elem k a b` |
| 見えないビットを偽にする | `maskD` |
| 鍵と順序 | `Idx := Ord × ℕ`、`ilt`、`ilt_wf` |
| 再帰 | `stepF`、`RF := ilt_wf.fix stepF`、`R k a b := RF (b, k) a` |
| 真の内部関係と上端述語 | `relR`、`topR γ` |
| ラベルの体系 | `labelSystem r` |
| 補助 | `Good`、`Form`、`witHeight`、`next`、`tower`、`lam`、`cC` |

中心の定義は次のとおりである（`Por/Formula.lean` と `Por/Relation.lean` から）。

```lean
def below (k : ℕ) : ℕ → Prop := fun j => j < k

def ElemL (rel : RelF) (topA topB : TopF) (k : ℕ) (a b : Ord) : Prop :=
  ∀ (m n : ℕ) (D : Set (Diag m n)) (bb r : ℕ) (p : ℕ → Ord),
    n ≤ r + bb → (∀ i < r, p i < a) →
    (Sat rel topA (below k) a m n D bb r p ↔ Sat rel topB (below k) b m n D bb r p)

noncomputable def stepF (t : Idx) (IH : ∀ t' : Idx, ilt t' t → Ord → Prop) : Ord → Prop :=
  fun a => a < t.1 ∧
    ElemL (fun j x y => ∃ h : y < t.1, IH (y, j) (Prod.Lex.left _ _ h) x)
      (fun j x => ∃ h : a < t.1, IH (a, j) (Prod.Lex.left _ _ h) x)
      (fun j x => ∃ h : j < t.2, IH (t.1, j) (Prod.Lex.right _ h) x)
      t.2 a t.1

noncomputable def RF : Idx → Ord → Prop := ilt_wf.fix stepF

noncomputable def R (k : ℕ) (a b : Ord) : Prop := RF (b, k) a

theorem R_iff {k : ℕ} {a b : Ord} : R k a b ↔ a < b ∧ Elem k a b
```

### 3.8 形を決めた理由

次の特徴は、どれも証明のどこかで使う。

1. どの層の言語も、すべての層の $`\mathrm{Rel}_j`$ を持つ。そのため上端を再帰の一番外に置く。
   - 理由：有限反映の (b)(c) は、層 $`k \lt r`$ のすべてについて $`\mathrm{rel}_k`$ を運ぶ。使える初等性は $`R(n,α,β)`$ だけで、$`k`$ は $`n`$ より大きくてもよい。したがって $`R(k,\cdot,\cdot)`$ が層 $`n`$ の言語で書けなければならない。原子記号にすれば書ける。
   - 合法である理由：$`\mathrm{Rel}_j`$ は高さより下の点どうしの関係なので、その上端は小さい（§3.4 の 1）。
2. 上端述語 $`\mathrm{Top}_j`$ を原子記号として持つ。層は $`j \lt k`$ のものだけである。
   - 理由：有限反映の (d) は $`\mathrm{rel}_m(y'_i, α)`$ を求める。これは上端 $`α`$ への関係で、$`α`$ は構造 $`\mathfrak A^{α}`$ の元ではない。$`R`$ の定義を展開して書くと $`Σ_1`$ にならない。bms-elem-pattern はこれを $`Σ_{n+1}`$ の文と連続性の補題で扱った。原子記号にすれば、原子図式の一部として運べる。
   - 層を $`j \lt k`$ に限る理由：$`\mathfrak A^{b}_{k}`$ の上端述語は、同じ上端 $`b`$ の $`R`$ を読む。層が小さくないと再帰が循環する（§3.4 の 3）。
   - $`j \lt k`$ は、(d) の範囲 $`m \lt n`$ とちょうど一致する。
3. 見えるかどうかは層の番号だけで決まる。
   - 理由：層 $`k`$ の論理式は、見えないビットを偽にするだけで、すべての記号を使う言語の論理式に訳せる（`maskD`）。L5 の証明はこの翻訳を使う（§4.7）。
   - 1-Y では同じ層の上端述語を「名前付き」にする工夫が要った。根の添字 $`η`$ があったからである。BMS では $`η`$ が無いので、その工夫は要らない。
4. $`Σ_1`$ だけを使う。$`Σ_n`$（$`n ≥ 2`$）も、bms-elem-pattern の $`Φ_m`$ や連続性・共終性の補題も要らない。上端との関係が原子記号だからである。
5. 1 つの論理式が使う記号は有限個（上限 $`m`$）にする。そうしないと論理式の全体が可算にならず、$`\mathrm{next}(γ) \lt ω_1`$ が言えない。

## 4. 証明

### 4.1 R はうまく定義され、定義の式を満たす

Lean：`ilt_wf`、`RF_eq`、`elem_stage`、`R_iff`。

**主張.** 右辺の構造を真の $`R`$ で解釈して、次が成り立つ。

```math
R(k,a,b) \iff a \lt b \ ∧\ \mathfrak A^{a}_{k} ≼_{Σ_1} \mathfrak A^{b}_{k}
```

**証明.**

1. $`\lhd`$ は整礎である（`WellFounded.prod_lex`）。`RF := ilt_wf.fix stepF` とすると、`WellFounded.fix_eq` から `RF t = stepF t RF` が成り立つ（`RF_eq`）。
2. `stepF` は、呼ぶ鍵が小さいことの証明を引数に持つ「途中の関係」を使う。高さ $`b`$、層 $`k`$ では次の 3 つである。
   - $`\mathrm{Rel}^{\mathrm{st}}_j(x,y) :⟺ y \lt b ∧ R(j,x,y)`$
   - $`\mathrm{Top}^{\mathrm{st},a}_j(x) :⟺ a \lt b ∧ R(j,x,a)`$
   - $`\mathrm{Top}^{\mathrm{st},b}_j(x) :⟺ j \lt k ∧ R(j,x,b)`$
3. $`a \lt b`$ とする。層 $`k`$ の論理式が読むビットでは、付けた条件はいつも真である（`elem_stage`）。
   - $`\mathrm{Rel}`$ のビット：点は高さ $`≤ b`$ より下にあるので $`y \lt b`$（`cat_bound`）。
   - 高さ $`a`$ の上端述語：$`a \lt b`$。
   - 高さ $`b`$ の見える上端述語：`below k` から $`j \lt k`$。
4. 見えないビットは、どちらの解釈でも偽である。よって原子図式は等しく（`diagM_congr`）、論理式の真偽も等しい（`sat_congr`）。
5. $`a ≥ b`$ なら両辺とも偽である。$`\square`$

### 4.2 L0、L1

- L0：`Ord := Ordinal.{0}`。線形順序と整礎性は Mathlib のインスタンスである。
- L1：`rel := R`。

### 4.3 L2（R_lt）

$`R(k,a,b)`$ なら、`R_iff` の第 1 項から $`a \lt b`$ である。

### 4.4 L3（R_trans）

**主張.** $`R(k,a,b)`$ かつ $`R(k,b,c)`$ なら $`R(k,a,c)`$。

**証明.**

1. `R_iff` から $`a \lt b \lt c`$ なので $`a \lt c`$。
2. 層 $`k`$ の論理式 $`φ`$ とパラメータ $`\vec p \lt a`$ を取る。$`\vec p \lt a \lt b`$ なので、2 つの初等性がどちらも使える。

```math
\mathfrak A^{a}_{k} ⊨ φ(\vec p) \iff \mathfrak A^{b}_{k} ⊨ φ(\vec p) \iff \mathfrak A^{c}_{k} ⊨ φ(\vec p)
```

3. 真ん中の構造は、どちらの初等性でも同じ $`\mathfrak A^{b}_{k}`$ である。層が同じで、上端述語はどちらも $`b`$ への $`R`$ だからである。$`\square`$

1-Y では推移律は約束に無く、Lean でも示していなかった。BMS の約束には推移律がある（§2.4）。

### 4.5 L4：有限反映

Lean：`reflect`、`listTuple`、`listTuple_lt`、`mem_listTuple`、`lt_iff_of_diagM_eq`、`rel_iff_of_diagM_eq`、`top_iff_of_diagM_eq`。

**仮定.** $`n \lt r`$、$`R(n,α,β)`$。$`X`$ は有限集合で、$`X \lt α`$。$`s \gt 0`$、$`y_0 \lt \cdots \lt y_{s-1}`$、$`α \le y_i \lt β`$。

**示すこと.** §2.1 の $`y'`$（順序、$`y'_i \lt α`$、(a)〜(d)）。

**証明.**

1. `R_iff` から $`\mathfrak A^{α}_{n} ≼_{Σ_1} \mathfrak A^{β}_{n}`$ が出る。
2. $`X`$ の元を並べて、パラメータの列 $`x_0, …, x_{|X|-1}`$ を作る（`listTuple X`）。どれも $`\lt α`$ である。
3. 点の列 $`v := (x_0, …, x_{|X|-1}, y_0, …, y_{s-1})`$ を考える。$`δ`$ を、$`\mathfrak A^{β}_{n}`$ での $`v`$ の完全な原子図式とする。記号の上限は $`r`$ である。つまり $`δ`$ は次のビットを持つ。
   - 全部の組の $`\lt`$。
   - 層 $`k \lt r`$ の $`\mathrm{Rel}_k`$、つまり $`R(k,\cdot,\cdot)`$ の真偽。
   - 層 $`m \lt n`$ の $`\mathrm{Top}_m`$、つまり $`R(m,\cdot, β)`$ の真偽。層 $`n ≤ m \lt r`$ の $`\mathrm{Top}_m`$ は見えないので偽である。
4. 次の論理式を作る。行列は 1 点集合 $`\{δ\}`$ で、パラメータは $`x`$、証人は $`s`$ 個である。

```math
Φ :≡ ∃ z_0 \dots ∃ z_{s-1}\ \bigl[\ \mathrm{diag}(x_0, …, x_{|X|-1}, z_0, …, z_{s-1}) = δ\ \bigr]
```

5. $`\mathfrak A^{β}_{n} ⊨ Φ`$ である。$`z := y`$ と取ればよい。$`y_i \lt β`$ である。
6. $`Σ_1`$ 初等性から $`\mathfrak A^{α}_{n} ⊨ Φ`$ である。その証人を $`y'_i \lt α`$ とする。$`\mathfrak A^{α}_{n}`$ での $`(x, y')`$ の原子図式は $`δ`$ に等しい。
7. 2 つの図式が等しいので、各ビットを読むと次が出る。どれも同値で出るが、使うのは片方の向きである。
   - 順序：$`y_i \lt y_j ⟺ y'_i \lt y'_j`$。よって $`y'`$ は狭義増加である。
   - (a)：$`x \lt α ≤ y_0`$ なので $`x \lt y_0`$ のビットは真である。よって $`x \lt y'_0`$。
   - (b)：$`k \lt r`$ なので $`R(k,x,y_i)`$ のビットは図式にある。よって $`R(k,x,y_i) ⟺ R(k,x,y'_i)`$。
   - (c)：同じく $`R(k,y_i,y_j) ⟺ R(k,y'_i,y'_j)`$。
   - (d)：$`m \lt n`$ なので $`\mathrm{Top}_m`$ は見える。$`\mathfrak A^{β}_{n}`$ では $`\mathrm{Top}_m(y_i)`$ は $`R(m,y_i,β)`$、$`\mathfrak A^{α}_{n}`$ では $`\mathrm{Top}_m(y'_i)`$ は $`R(m,y'_i,α)`$ である。よって $`R(m,y_i,β) ⟺ R(m,y'_i,α)`$。$`\square`$

使わなかったもの：$`α`$ や $`β`$ が極限であること、閉包点であること。

1-Y の有限反映（`finiteReflection`）は、図式の辺と上端への要求を並べた行列（`reflMat`）を使った。ここでは原子図式の全体を 1 点集合にする。行列の中身を読む補題が要らず、証明が短くなる。

### 4.6 L5 の準備：閉包点

Lean：`witHeight_lt`、`next_lt`、`lam_lt`、`lt_lam`、`exists_tower`、`wit_below`、`lam_good`。

**主張.** $`γ \lt ω_1`$ なら、$`γ \lt λ(γ) \lt ω_1`$ かつ $`\mathrm{Good}(λ(γ))`$ である。

**証明.**

1. $`\mathrm{next}(γ) \lt ω_1`$ である。
   - 添字の集合（$`Σ_1`$ 論理式と自然数の有限列の組）は可算である。各行列は有限集合 `Diag m n` の部分集合だからである。
   - 各 $`h(φ, \vec p)`$ は、$`ω_1`$ より下の順序数の後者の、有限個の上限なので $`\lt ω_1`$ である（`om_succ_lt`）。
   - $`ω_1`$ より下の順序数の可算個の上限は $`\lt ω_1`$ である（`Ordinal.iSup_lt_omega_one`。$`ω_1`$ の正則性）。
2. 同じ理由で $`λ(γ) \lt ω_1`$ である。また $`γ \lt \mathrm{next}(γ) ≤ λ(γ)`$。
3. $`\mathrm{Good}(λ(γ))`$ の $`⇒`$：$`λ(γ)`$ より下の証人は $`ω_1`$ より下の証人でもある。$`\mathfrak B{\restriction}λ(γ)`$ は $`\mathfrak B`$ の制限なので、行列は同じに評価される。
4. $`\mathrm{Good}(λ(γ))`$ の $`⇐`$：パラメータ $`\vec p \lt λ(γ)`$ は有限個なので、ある $`t`$ で全部 $`\lt \mathrm{next}^t(γ)`$ になる（`exists_tower`）。$`\mathrm{next}^t(γ)`$ は可算なので、$`\vec p = e_{\mathrm{next}^t(γ)} ∘ l`$ となる $`l`$ がある（`exists_params`）。$`(φ, l)`$ について選んだ証人は $`\lt \mathrm{next}^{t+1}(γ) ≤ λ(γ)`$ である（`wit_below`）。$`\square`$

この節は 1-Y と同じである。論理式の型だけが違う。

### 4.7 L5 の中心：上端述語の絶対性

Lean：`sat_abs`、`top_abs`。

**主張.** $`\mathrm{Good}(α)`$ かつ $`α \lt ω_1`$ なら、すべての層 $`j`$ と $`x \lt α`$ について次が成り立つ。

```math
R(j,x,α) \iff R(j,x,ω_1)
```

**証明.** $`j`$ についての強い帰納法をする。

1. `R_iff` で両辺を開く。$`x \lt α`$ も $`x \lt ω_1`$ も真である。残るのは、層 $`j`$ の論理式 $`ψ`$（パラメータ $`\lt x`$）について、$`\mathfrak A^{α}_{j} ⊨ ψ ⟺ \mathfrak A^{ω_1}_{j} ⊨ ψ`$ を示すことである（`sat_abs`）。
2. $`ψ`$ が読む上端述語のビット $`\mathrm{Top}_i(v)`$（$`v \lt α`$）は $`i \lt j`$ を満たす。帰納法の仮定から $`R(i,v,α) ⟺ R(i,v,ω_1)`$ である。
3. よって $`\mathfrak A^{α}_{j} ⊨ ψ ⟺ \mathfrak B{\restriction}α ⊨ ψ^{*}`$ である。ここで $`ψ^{*}`$ は、$`ψ`$ の見えないビットを偽にした、すべての記号を使う言語の論理式である（`sat_mask`）。
4. $`\mathrm{Good}(α)`$ から $`\mathfrak B{\restriction}α ⊨ ψ^{*} ⟺ \mathfrak B ⊨ ψ^{*}`$ である。パラメータは $`\lt x \lt α`$ である。
5. 見えるビットの読み方は同じなので、$`\mathfrak B ⊨ ψ^{*} ⟺ \mathfrak A^{ω_1}_{j} ⊨ ψ`$ である。$`\square`$

§3.8 の 3（見えるかどうかは層だけで決まる）はここで使う。$`ψ^{*}`$ が作れるのはそのためである。1-Y では帰納法は（層、添字）の辞書式順序についてだった。ここでは層だけである。

### 4.8 L5：鎖とすべての配列のラベル

Lean：`cC_lt`、`cC_strictMono`、`cC_good`、`chain_R`、`stable_all`。

**主張（`chain_R`）.** $`i \lt j`$ なら、すべての層 $`k`$ について $`R(k,c_i, c_j)`$ である。

**証明.** §4.6 から $`c_t \lt ω_1`$、$`c_t \lt c_{t+1}`$、$`\mathrm{Good}(c_t)`$ である。$`c_i \lt c_j`$ である。層 $`k`$ の論理式 $`ψ`$ とパラメータ $`\lt c_i`$ について、次の同値が成り立つ。

```math
\mathfrak A^{c_i}_{k} ⊨ ψ \iff \mathfrak B{\restriction}c_i ⊨ ψ^{*} \iff \mathfrak B ⊨ ψ^{*} \iff \mathfrak B{\restriction}c_j ⊨ ψ^{*} \iff \mathfrak A^{c_j}_{k} ⊨ ψ
```

1 番目と 4 番目は §4.7（$`c_i`$ と $`c_j`$ で使う）、2 番目と 3 番目は $`\mathrm{Good}`$ である。$`\square`$

**L5（`stable_all`）.** どの行数 $`r`$、どの $`r`$ 行の配列 $`A`$ についても、$`f := c`$ は $`A`$ の安定なラベルである。

- $`f`$ は狭義増加である。
- $`i \prec^A_k j`$ なら $`i \lt j`$ である（`BM4.anc_lt`）。`chain_R` から $`R(k,c_i, c_j)`$。

$`A`$ の形は使わない。先祖の関係が何であっても、鎖の 2 点はすべての層で結ばれているからである。よって 1 つの $`f`$ が、すべての配列を同時にラベル付けする。標準形の条件は要らない。$`\square`$

### 4.9 最終定理

Lean：`Por/WellOrdering.lean` の `terminates`、`step_wf`、`R_wf`、`R'_wf`。

**`terminates`.** $`r`$ 行の配列 $`A`$ と $`n : ℕ → ℕ`$ について、$`A^{(0)} = A`$、$`A^{(t+1)} = A^{(t)}[n(t)]`$ とする（`BM4.seq A n`）。ある $`T`$ で $`A^{(T)} = ()`$ である。

1. どの $`t`$ でも $`A^{(t)} \ne ()`$ だとする。
2. ラベル $`g_t`$ を順に作る。$`g_0(i) := c_i`$ は §4.8 から $`A^{(0)}`$ の安定なラベルである。$`g_t`$ が $`A^{(t)}`$ の安定なラベルなら、`BM4.descent` から $`A^{(t+1)}`$ の安定なラベル $`g_{t+1}`$ で、$`\mathrm{ht}(A^{(t+1)}, g_{t+1}) \lt \mathrm{ht}(A^{(t)}, g_t)`$ となるものがある（`chain`、`chain_lt`）。
3. 高さの集合 $`\{\mathrm{ht}(A^{(t)}, g_t) : t ∈ ℕ\}`$ は空でない順序数の集合なので、最小元 $`\mathrm{ht}(A^{(t_0)}, g_{t_0})`$ を持つ（L0）。
4. $`\mathrm{ht}(A^{(t_0+1)}, g_{t_0+1})`$ はそれより小さい。矛盾する。$`\square`$

**`step_wf`.** 関係 $`A \prec B :⟺ B \ne () ∧ ∃N,\ A = B[N]`$（`Step r`）は整礎である。無限の降下列 $`C_0 \succ C_1 \succ \cdots`$ があるとする。$`C_{t+1} = C_t[N_t]`$ となる $`N_t`$ を選ぶと、$`C_t`$ は `BM4.seq C_0 N t` に等しい。`terminates` から、ある $`T`$ で $`C_T = ()`$ である。これは $`C_T \ne ()`$ に反する。$`\square`$

**`R_wf`.** `BM4.R r` は、`BM4.Elt r`（$`E_r`$ から届く配列）の上の同じ関係である。`step_wf` の逆像なので整礎である。$`\square`$

**`R'_wf`.** `BM4.R'` は、行の数を持つ元 $`(r, A)`$ の上の関係である。関係があるなら行の数は等しい。$`r`$ ごとに `R_wf` の帰納法で、各元が到達可能（`Acc`）であることを示す。$`\square`$

検査（2026-09-28）。`leanman build Bm4 Por` は終了コード 0 である。`Audit.lean` の `#print axioms` は、最終定理 4 つ、`labelSystem`、`reflect`、`R_trans`、`stable_all`、`chain_R`、`R_iff`、`BM4.descent` のどれについても `[propext, Classical.choice, Quot.sound]` を出す。

### 4.10 使わない性質（Lean で未検査）

組合せの層はこれらを使わない。参考として書く。

- 層についての単調性：$`R(k+1,a,b) ⇒ R(k,a,b)`$。層 $`k`$ の論理式は、見えないビット $`\mathrm{Top}_k`$ を偽にすれば層 $`k+1`$ の論理式になるからである。これは元の約束の `rel_mono` に当たる。
- 局所性：上端が $`≤ δ`$ の $`R`$ は、上端が $`δ + 1`$ より下の再帰だけで決まる。

## 5. 注意

1. **強さ.** 証明は $`ω_1`$ の正則性（可算選択）と選択公理を使う。ラベルは $`ω_1`$ より下の閉包点で、順序数の上界や表記系は得られない。DH の証明、bms-elem-pattern、1y-wo-por も同じである。
2. **名前.** $`R`$ は Carlson の $`\mathcal R_N`$ そのものではない。上端述語を持つ $`Σ_1`$ 初等性を、上端を外側にした再帰で定義したものである。標準的な patterns of resemblance の構造と同じだとは主張しない。
3. **名前の衝突.** `BM4.R r` は BM4 の上の 1 段の展開の関係で、`Por.R` はラベルの関係である。別のものである。
4. **仕様への信頼.** BM4 の展開が `BM4.expand` で正しく書かれていることは、DH の論文の定義 5.1 の形式化（dh-bms-wf-formal）に依る。ほかの版のバシク行列との一致は扱わない。
5. **付随の主張.** §4.10 の性質は Lean で検査していない。組合せの層は使わない。
6. **ツールチェーン.** Lean 4.33.1 と Mathlib v4.33.1 に固定する。`Bm4/` は Lean 4.30.0 から上げた（[02-port.md](02-port.md)）。

## 6. Lean のファイル

### 6.1 Por/

名前空間はどのファイルも `Por` である。`Por.lean` は下の 9 ファイルを import する。

| # | ファイル | 中身 | 行数 |
|---|---|---|---:|
| 1 | `Por/Tuple.lean` | `Ord`、`cat`、`cat_left`、`cat_right`、`cat_lt`、`cat_congr_left`、`cat_bound` | 54 |
| 2 | `Por/Omega1.lean` | `Om`、`om_pos`、`om_succ_lt`、`countable_Iio`、`enumBelow`、`enumBelow_surj`、`params`、`exists_params` | 63 |
| 3 | `Por/Formula.lean` | `Diag`、`RelF`、`TopF`、`diagM`、`Sat`、`full`、`below`、`ElemL`、`diagM_congr`、`sat_congr`、`maskD`、`diagM_mask`、`sat_mask`、`lt_iff_of_diagM_eq`、`rel_iff_of_diagM_eq`、`top_iff_of_diagM_eq` | 129 |
| 4 | `Por/Relation.lean` | `Idx`、`ilt`、`ilt_wf`、`stepF`、`RF`、`R`、`RF_eq`、`relR`、`topR`、`Elem`、`elem_stage`、`R_iff`、`R_lt`、`R_trans` | 105 |
| 5 | `Por/Reflection.lean` | `listTuple`、`listTuple_lt`、`mem_listTuple`、`reflect` | 95 |
| 6 | `Por/Closure.lean` | `Good`、`Form`、`witHeight`、`witHeight_lt`、`next`、`lt_next`、`next_lt`、`wit_below`、`tower`、`lam`、`tower_lt`、`tower_mono`、`tower_le_lam`、`lam_lt`、`lt_lam`、`exists_tower`、`lam_good` | 137 |
| 7 | `Por/Chain.lean` | `sat_abs`、`top_abs`、`cC`、`cC_lt`、`cC_strictMono`、`cC_good`、`chain_R` | 84 |
| 8 | `Por/Model.lean` | `labelSystem`、`stable_all` | 34 |
| 9 | `Por/WellOrdering.lean` | `chain`、`chain_lt`（private）、`terminates`、`Step`、`step_wf`、`R_wf`、`R'_wf` | 90 |

import の順：`Tuple` → `Omega1`、`Formula` → `Relation` → `Reflection`、`Closure`（と `Omega1`）→ `Chain` → `Model`（と `Bm4.Label`）→ `WellOrdering`。

どのファイルにも、何を示すかを書いたモジュールの説明（英語）と、出どころを書いた見出し（英語）がある。

### 6.2 Bm4/

`Bm4/` は 14 ファイル、3,000 行である。一覧と出どころは [02-port.md](02-port.md) にある。意味の層が使うのは `Bm4/Label.lean` の `LabelSystem`、`Stable`、`ht`、`descent` と、`Bm4/Defs.lean` の `Arr`、`anc`、`expand`、`seq`、`Elt`、`R`、`R'`、`Bm4/Basic.lean` の `anc_lt` である。

### 6.3 検査の方法

- 検査は leanman で行う。リポジトリの根で `leanman build Bm4 Por`、1 ファイルなら `leanman check -C . <ファイル>`。`lake build` でもよい。
- 公理の監査は `leanman check -C . Audit.lean` で行う。`Audit.lean` はどの `lean_lib` にも入っていない。
- 判定は終了コードで行う（0 が緑）。`#print axioms` の出力は `[propext, Classical.choice, Quot.sound]` になるはずである。ほかの公理（特に `sorryAx`）が出たら止まる。
