[← 設計](01-design.md) | [README](../README.md) | [PLAN](../PLAN.md)

# 移植の記録

`Bm4/` と `Por/` をどこから持ってきて、何を変えたかの記録である。

## 0. 要約

- `Bm4/`（組合せの層、14 ファイル、3,000 行）：[bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) の `lean/Bm4/` をコピーした。元は [dh-bms-wf-formal](https://github.com/koteitan/dh-bms-wf-formal)（DH の論文の BM4 の証明の形式化）である。Lean 4.30.0 から 4.33.1 に上げた。証明の変更は `Bm4/Copy.lean` の `col_pos` の 1 か所だけである（§2）。
- `Por/`（意味の層、9 ファイル、791 行）：[1y-wo-por](https://github.com/koteitan/1y-wo-por) の `Por/` から作った。根の添字 $`η`$ を除き、1-Y の約束の代わりに BMS の約束 `BM4.LabelSystem r` を満たすようにした（§3）。
- 1y-wo-por の組合せの層（`ZeroY/`、`OneY/`、`Por/BMS/`）は持ってこない。BMS の組合せの層は `Bm4/` で足りる。

## 1. Bm4/ の出どころ

### 1.1 経路

1. dh-bms-wf-formal：DH の論文（巨大数研究 Wiki、2026）の BM4 の停止性の証明を Lean 4 で形式化したもの。組合せの部分（配列、親、先祖、展開、コピーの補題、命題 19.1）と、集合論の部分（許容順序数のラベル）がある。
2. bms-elem-pattern の `lean/Bm4/`：dh-bms-wf-formal の組合せの部分をコピーしたもの。ラベルの約束 `LabelSystem` から `rel_mono` と `init` を除き、行の数 $`r`$ を約束の引数にした。
3. このリポジトリの `Bm4/`：bms-elem-pattern のリビジョン [`201f695`](https://github.com/koteitan/bms-elem-pattern/tree/201f695c48021c2e2e4776292ed228859d8ef317) の `lean/Bm4/` をコピーした。`lean/Bm4/` を最後に変えたコミットは `d7ac182` である。

### 1.2 ファイル

| ファイル | 行数 | 中身 |
|---|---:|---|
| `Bm4/Defs.lean` | 126 | 配列 `Arr r`、親 `parent`、先祖 `anc`、候補 `cand`、展開 `expand`（定義 5.1）、`E r`、`Reachable`、`seq`、`Elt`、`R`、`R'` |
| `Bm4/Basic.lean` | 422 | 親と先祖の基本の補題（`anc_lt`、`anc_trans`、`anc_congr_iff` など） |
| `Bm4/Copy.lean` | 358 | 悪い根のデータ `BadRoot`、位置 `pos q j`、展開した配列 `tA` の成分（`col_lt`、`col_pos` など） |
| `Bm4/CopyPaper/Interval.lean` | 233 | コピーの補題の準備。区間の中の親（定義 6.1、補題 6.2）と、(C1)〜(C6) を述語として書いたもの |
| `Bm4/CopyPaper/L1.lean` 〜 `L6.lean` | 1,206 | コピーの補題（定理 6.3）の 6 つの主張 (C1)〜(C6) |
| `Bm4/CopyPaper/Assemble.lean` | 135 | 命題 6.11 の組み立てと系 6.12 |
| `Bm4/CopyPaper/Char.lean` | 69 | 展開した配列で親があること。(C1)〜(C3) から出す 2 つの補題 |
| `Bm4/Expand.lean` | 77 | `expand` と悪い根のデータをつなぐ補題（`expand_eq`、`expand_last` など） |
| `Bm4/Label.lean` | 374 | ラベルの約束 `LabelSystem`、安定なラベル `Stable`（定義 18.1）、高さ `ht`、降下 `descent`（命題 19.1） |
| 合計 | 3,000 | |

`L1.lean`〜`L6.lean` の行数は 189、278、178、176、241、144 である。bms-elem-pattern での合計は 2,923 行である。差の 77 行は、各ファイルの先頭に足した出どころの見出し（5 行 × 14）と、§2 の変更（7 行）である。

根のファイル `Bm4.lean` は `import Bm4.Label` の 1 行である。`Bm4.Label` から、ほかの 13 ファイルがすべて import される。

## 2. Lean 4.30.0 から 4.33.1 へ

bms-elem-pattern は Lean 4.30.0 と Mathlib v4.30.0 を使う。このリポジトリは Lean 4.33.1 と Mathlib v4.33.1 を使う。1y-wo-por と同じ版である。

`diff -r` で比べた違いは、次の 3 種類だけである。

1. 14 ファイルすべての先頭に、出どころの見出しを足した。見出しは、コピー元のパス、ライセンス（CC BY-SA 4.0）、dh-bms-wf-formal から来たこと、変更点を書く。
2. `Bm4/Copy.lean` のファイルの説明から、閉じた形の別証明（`Bm4/CopyClosed.lean`）への言及を消した。そのファイルは bms-elem-pattern の `lean/Bm4/` にも無く、このリポジトリにも無い。
3. `Bm4/Copy.lean` の定理 `col_pos` の証明を変えた。

### 2.1 col_pos の変更

`col_pos` は、展開した配列の位置 $`p + q s + j`$ の成分を述べる。

```lean
theorem col_pos {q j : ℕ} (hj : j < b.s) (k : ℕ) :
    b.tA.col (b.pos q j) k =
      if b.Asc k j then A.col (b.p + j) k + q * b.Δ k else A.col (b.p + j) k
```

右辺の `if` の条件は `b.Asc k j` である。左辺を `tildeCol` で開くと、`if k < b.m ∧ ancEq A k b.p (b.p + j)` が出る。`Asc` の定義は `k < b.m ∧ ancEq A k b.p (b.p + j)` なので、2 つの条件は定義を開くと同じ命題である。しかし `Decidable` のインスタンスが違う。

- 右辺の `if b.Asc k j` は、`Asc` が定義なので、`open Classical` による `Classical.propDecidable` を使う。
- 左辺の `if k < b.m ∧ …` は、`∧` のインスタンス（`instDecidableAnd`）を使う。

元の証明は次の 1 行だった。

```lean
  simp only [tA, tildeCol, hnot, if_false, h1, hdiv, hmod, Asc, Δ]
```

Lean 4.30.0 ではこれで閉じた。Lean 4.33.1 では閉じない。2 つの `if` は、インスタンスが違うので同じ項にならない。

新しい証明は、条件で場合を分け、2 つの `if` を別々に書き換える。

```lean
  by_cases hc : b.Asc k j
  · rw [if_pos hc]
    have hc' : k < b.m ∧ ancEq A k b.p (b.p + j) := hc
    simp only [tA, tildeCol, hnot, if_false, h1, hdiv, hmod, Δ]
    rw [if_pos hc']
  · rw [if_neg hc]
    have hc' : ¬ (k < b.m ∧ ancEq A k b.p (b.p + j)) := hc
    simp only [tA, tildeCol, hnot, if_false, h1, hdiv, hmod]
    rw [if_neg hc']
```

`if_pos` と `if_neg` は、どのインスタンスの `if` にも使える。そのため、インスタンスの違いが問題にならない。定理の主張は変えていない。

ほかの 13 ファイルは、見出しのほかは一字も変えずに 4.33.1 で通った。

## 3. Por/ の出どころ

### 3.1 経路

- 1y-wo-por の `Por/`：1-Y の意味の層。リビジョン [`d555ade`](https://github.com/koteitan/1y-wo-por/tree/d555ade85feeb21d8f042911b4db5c1dc4c06e43) を使った（`Por/` を最後に変えたコミットは `4b617fc`）。その補助の一部は、bms-elem-pattern の `lean/Pattern/` から来ている。
- このリポジトリの `Por/`：1y-wo-por の `Por/` から、根の添字 $`η`$ を除いた。1-Y の約束（`OneY.RootIndexed.*`）の代わりに、BMS の約束 `BM4.LabelSystem r` を満たすようにした。

どのファイルの先頭にも、出どころと変更点を書いた見出しがある。

### 3.2 ファイルごとの変更

行数は「1y-wo-por → このリポジトリ」である。

| ファイル | 行数 | 変更 |
|---|---|---|
| `Tuple.lean` | 49 → 54 | `cat_right`（`cat k p q (k + i) = q i`）を足した。`Reflection.lean` で証人の位置を読むのに使う。本体のほかの部分は同じ |
| `Omega1.lean` | 63 → 63 | 見出しだけ |
| `Formula.lean` | 104 → 129 | 原子図式の形を変えた（§3.3）。見えるビット `allowL k S` を `below k` に替えた。`ElemL` から添字 $`η`$ と名前の位置の集合 $`S`$ を除いた。図式が等しいときにビットを読む補題 3 つを足した |
| `Relation.lean` | 120 → 105 | 鍵を（上端、層）にした（§3.4）。`R_index_le`、`R_weaken` を消した。`R_trans` を足した |
| `Reflection.lean` | 127 → 95 | 中身を全部替えた（§3.5） |
| `Closure.lean` | 137 → 137 | 見出しだけ。本体の文字列は同じである。論理式の型 `Form` は `Diag` を通して変わる |
| `Chain.lean` | 103 → 84 | 絶対性の帰納法を層だけにした。`chain_R` から $`η`$ を除いた。`initial_all` を消した（§3.6） |
| `Model.lean` | 35 → 34 | `model_obligations` を消した。`labelSystem` と `stable_all` を足した（§3.7） |
| `WellOrdering.lean` | 59 → 90 | 中身を全部替えた（§3.8） |

1y-wo-por の `Por/BMS.lean` と `Por/BMS/`（1-Y の組合せの層が使う BMS の層、6 ファイル、3,302 行）は持ってこない。`Audit.lean` は新しく書いた。1y-wo-por では `#print axioms` の行が `Model.lean` と `WellOrdering.lean` の末尾にあった。ここでは `Audit.lean` にまとめた。

### 3.3 Formula.lean

| 1y-wo-por | このリポジトリ |
|---|---|
| `Diag m n` の $`\mathrm{Rel}`$ のビット：`Fin m → Fin n → Fin n → Fin n → Bool`（3 変数） | `Fin m → Fin n → Fin n → Bool`（2 変数） |
| `Diag m n` の $`\mathrm{Top}`$ のビット：`Fin m → Fin n → Fin n → Bool`（2 変数） | `Fin m → Fin n → Bool`（1 変数） |
| `RelF := ℕ → Ord → Ord → Ord → Prop` | `RelF := ℕ → Ord → Ord → Prop` |
| `TopF := ℕ → Ord → Ord → Prop` | `TopF := ℕ → Ord → Prop` |
| 見えるビット `allow : ℕ → ℕ → Prop`（層と位置） | `allow : ℕ → Prop`（層だけ） |
| `full := fun _ _ => True` | `full := fun _ => True` |
| `allowL k S j a := j < k ∨ (j = k ∧ a ∈ S)` | `below k j := j < k` |
| `ElemL rel topA topB k η a b`。名前の位置 $`S`$ を量化し、`∀ s ∈ S, s < r ∧ p s < η` を仮定する | `ElemL rel topA topB k a b`。$`S`$ も $`η`$ も無い |

`diagM`、`Sat`、`diagM_congr`、`sat_congr`、`maskD`、`diagM_mask`、`sat_mask` は、変数の数を合わせただけで、組み立ては同じである。

足した補題は次の 3 つである。2 つの点の列の原子図式が等しいとき、それぞれのビットの真偽が一致することを言う。`Reflection.lean` の `reflect` が使う。

- `lt_iff_of_diagM_eq`：$`\lt`$ のビット。
- `rel_iff_of_diagM_eq`：$`\mathrm{Rel}_j`$ のビット（$`j \lt m`$）。
- `top_iff_of_diagM_eq`：見える $`\mathrm{Top}_j`$ のビット（$`j \lt m`$、`allow j`）。

### 3.4 Relation.lean

| 1y-wo-por | このリポジトリ |
|---|---|
| `Idx := Ord × ℕ × Ord`（上端、層、添字） | `Idx := Ord × ℕ`（上端、層） |
| `ilt` は 3 つ組の辞書式順序 | `ilt` は組の辞書式順序 |
| `stepF` の条件：`t.2.2 ≤ a ∧ a < t.1 ∧ ElemL …` | `a < t.1 ∧ ElemL …` |
| 高さ $`b`$ の見える上端述語の条件：`Prod.Lex (· < ·) (· < ·) (j, ξ) (k, η)` | `j < k` |
| `R k η a b := RF (b, k, η) a` | `R k a b := RF (b, k) a` |
| `R_iff : R k η a b ↔ η ≤ a ∧ a < b ∧ Elem k η a b` | `R_iff : R k a b ↔ a < b ∧ Elem k a b` |
| `R_lt`、`R_index_le`、`R_weaken` | `R_lt`、`R_trans` |

`elem_stage` の最後の場合（高さ $`b`$ の見える上端述語）は、1y-wo-por では `allowL` を場合分けして辞書式順序の証明を作った。ここでは `below k j` がそのまま `j < k` なので、1 行で済む。

`R_trans` は新しい。2 つの初等性を、同じ真ん中の構造 $`\mathfrak A^{b}_{k}`$ でつなぐ（[01-design.md](01-design.md) §4.4）。

### 3.5 Reflection.lean

1y-wo-por の中身は、1-Y の約束 `FiniteReflection` の証明だった。これを全部消した。

- 消したもの：`getLt`、`getRel`、`getTop` とその `_diagM` 補題、`sigBound`、`atom_layer_lt`、`need_layer_lt`、`reflMat`、`reflMat_iff`、`finiteReflection`。`OneY.RootIndexed.Representation` の import。
- 足したもの：`listTuple`、`listTuple_lt`、`mem_listTuple`（bms-elem-pattern の `lean/Pattern/Reflect.lean` から。Lean 4.33.1 に合わせ、`Ordinal.{0}` を `Ord` と書いた）、`reflect`（新しく書いた）。

`reflect` は BMS の約束の `reflect` の場を示す。証明の形は次のとおりである（[01-design.md](01-design.md) §4.5）。

- パラメータは $`X`$ の元の列（`listTuple X`）、証人は $`y_0, …, y_{s-1}`$ である。
- 行列は、高さ $`β`$ での完全な原子図式 1 つからなる 1 点集合である。記号の上限は行の数 $`r`$、見えるビットは `below n` である。
- $`R(n,α,β)`$ で高さ $`α`$ に移し、証人 $`y'`$ を得る。図式が等しいので、§3.3 の 3 つの補題で各ビットを読む。

1y-wo-por の `reflMat` は、図式の辺と上端への要求を 1 つずつ並べた行列だった。ここでは原子図式の全体を 1 点集合にするので、行列を読む補題（`reflMat_iff`）が要らない。

### 3.6 Chain.lean

| 1y-wo-por | このリポジトリ |
|---|---|
| `sat_abs` の帰納法の仮定：`∀ q : ℕ × Ord, Prod.Lex … q (j, ζ) → q.2 < α → ∀ x < α, (R q.1 q.2 x α ↔ R q.1 q.2 x Om)` | `∀ i < j, ∀ x < α, (R i x α ↔ R i x Om)` |
| `top_abs`：$`ℕ × \mathrm{Ord}`$ の辞書式順序についての整礎帰納法 | `Nat.strong_induction_on` による層 $`j`$ についての帰納法 |
| `chain_R (hij : i < j) (k : ℕ) (hη : η ≤ cC i) : R k η (cC i) (cC j)` | `chain_R (hij : i < j) (k : ℕ) : R k (cC i) (cC j)` |
| `initial_all`：すべての 1-Y の図式に表現がある | 消した。代わりに `Model.lean` の `stable_all` |

`sat_abs` の中で、見える上端述語のビットを帰納法の仮定に渡すところは、1y-wo-por では `allowL` を場合分けした。ここでは `below j i` がそのまま `i < j` なので、そのまま渡せる。`cC`、`cC_lt`、`cC_strictMono`、`cC_good` は同じである。`OneY.RootIndexed.Representation` の import を消した。

### 3.7 Model.lean

- 消したもの：`model_obligations`（1-Y の入口の定理の 6 つの仮定のまとめ）。`OneY.RootIndexed` の `open`。
- 足したもの：
  - `labelSystem r : BM4.LabelSystem.{1} r`。`Lab := Ord`、`rel := R`、`rel_lt := R_lt`、`rel_trans := R_trans`、`reflect` は `Por.reflect r`。
  - `stable_all (A : BM4.Arr r) : BM4.Stable (labelSystem r) A cC`。単調性は `cC_strictMono`、先祖の条件は `BM4.anc_lt` と `chain_R` から出る。
- import に `Bm4.Label` を足した。

### 3.8 WellOrdering.lean

1y-wo-por の中身は、1-Y の最終定理 4 つ（`expansion_wellFounded`、`generated_strictWellOrder`、`descendants_strictWellOrder`、`expansion_chain_reaches_empty`）だった。どれも 1-Y の組合せの層の定理にモデルを渡すだけだった。これを全部消した。

新しい中身は、bms-elem-pattern の `lean/Pattern/Main.lean` の `chain`、`chain_lt`、`terminates`、`StdR_wf` の形に従う。

| bms-elem-pattern | このリポジトリ |
|---|---|
| `chain`、`chain_lt`：最初の配列の安定なラベル $`f_0`$ を引数に取り、`descent` でラベルを順に作る | 同じ。最初のラベルは `cC` に決めてある（`stable_all`） |
| `terminates (hA : Std r A) (n : ℕ → ℕ)`：標準の配列の展開の列は空に着く。標準であることから $`f_0`$ を作る | `terminates (A : BM4.Arr r) (n : ℕ → ℕ)`：任意の配列。$`f_0`$ は `cC` |
| `StdR_wf`：標準の配列の上の 1 段の展開の関係が整礎 | `step_wf`：すべての $`r`$ 行の配列の上で整礎（関係は `Step r`） |
| （無し） | `R_wf`：`BM4.R r`（$`E_r`$ から届く配列の上）が整礎。`step_wf` の逆像 |
| （無し） | `R'_wf`：`BM4.R'`（すべての行数をまとめた BM4 の上）が整礎 |

`#print axioms` の行は `Audit.lean` に移した。

## 4. 持ってこなかったもの

- bms-elem-pattern の `lean/Pattern/`：Carlson の構造 $`\mathcal R_N`$ の上のラベル。$`Σ_n`$ の段（`Basic.lean` の `lev`、`lab` の類）、3 行までの有限反映（`Reflect.lean` の `reflect_one`、`reflect_two`、`labelSystem`）、すべての行の有限反映（`General.lean` の $`Φ_m`$、共終な連続性、`labelSystemGen`）、`Chain.lean` の `lab_lam`、`lamChain`。このリポジトリでは $`Σ_1`$ だけを使うので、どれも要らない。1y-wo-por を通して来たのは、`cat` の類、`Om` の類、`enumBelow`、`params`、閉包の組み立て、再帰の組み立て、`listTuple` の類だけである。
- dh-bms-wf-formal の集合論の部分（許容順序数と $`L`$ の上のラベル）。
- 1y-wo-por の `ZeroY/`、`OneY/`、`Por/BMS/`。

## 5. 規模

| 部分 | ファイル | 行数 |
|---|---:|---:|
| `Bm4/`（組合せの層） | 14 | 3,000 |
| `Por/`（意味の層） | 9 | 791 |
| `Audit.lean` | 1 | 28 |

## 6. 検査

- `leanman build Bm4 Por` は終了コード 0 である（2026-09-28）。`sorry` は無い。
- `Audit.lean` の `#print axioms` は、どの行も `[propext, Classical.choice, Quot.sound]` を出す。対象は、最終定理 4 つ、`labelSystem`、`reflect`、`R_trans`、`stable_all`、`chain_R`、`R_iff`、`BM4.descent` である。
