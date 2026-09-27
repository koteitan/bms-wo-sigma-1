[English](README-en.md) | [Japanese](README.md)

# bms-wo-sigma-1：Σ₁ 初等性だけによる BMS の整礎性

バシク行列システム（BM4）の展開がいつか必ず止まることを、すべての行数について Lean 4 で証明したリポジトリである。

ラベルの関係は、順序数の上に直接定義する。その定義に使うモデル理論の概念は $`\Sigma_1`$ 初等部分構造だけである。構成的宇宙 $`L`$ も、許容順序数も、$`\Sigma_2`$ 以上の初等性も使わない。方法は [1y-wo-por](https://github.com/koteitan/1y-wo-por) が 1-Y 数列でしたことと同じである。

- Lean 4.33.1、Mathlib v4.33.1。
- `sorry` は無い。新しい公理も無い。公理は `propext`、`Classical.choice`、`Quot.sound` だけである。

## 何を証明したか

### 記号

- $`r`$ 行の配列とは、$`\mathbb N^r`$ の元の有限列 $`A = (A_0, \ldots, A_{\ell-1})`$ である（`BM4.Arr r`）。$`A_i`$ を $`A`$ の列と呼ぶ。$`A_i[k]`$ は列 $`A_i`$ の行 $`k`$ の成分である（$`k \lt r`$）。$`\ell = 0`$ のときが空の配列 $`()`$ である。配列は標準形である必要は無い。
- $`A[N]`$ は、配列 $`A`$ を自然数 $`N`$ で展開したものである（`BM4.expand A N`、DH の論文の定義 5.1）。
- 親と先祖の定義は [study/05-bms.md](study/05-bms.md) にある。
- 最後の列がどの行にも親を持たないとき、$`A[N]`$ は $`A`$ から最後の列を除いたものである。
- そうでないとき、$`m_0`$ は最後の列が親を持つ行の番号の最大である。$`p`$ は、行 $`m_0`$ での最後の列の親（悪い根）の位置である。$`G`$ は位置 $`p`$ より左の列、$`B_0`$ は位置 $`p`$ から最後の列の 1 つ前までの列である。このとき $`A[N] = G \frown B_0 \frown B_1 \frown \cdots \frown B_N`$ である。$`B_q`$ は $`B_0`$ の写しである。ただし行 $`k \lt m_0`$ では、列 $`p`$ 自身と、列 $`p`$ を行 $`k`$ の先祖に持つ列に、増分 $`q \cdot (A_{\ell-1}[k] - A_p[k])`$ を足す。
- 展開の列とは、$`A^{(0)} = A`$、$`A^{(t+1)} = A^{(t)}[n(t)]`$ で決まる列である（`BM4.seq A n`）。各段の $`n(t)`$ は自由に選べる。
- $`E_r = ((0,\ldots,0),(1,\ldots,1))`$ である（`BM4.E r`）。$`r`$ 行の BM4 とは、$`E_r`$ から有限回の展開で届く配列の集合 $`\mathrm{BM4}_r`$ である（`BM4.Elt r`）。

### 最終定理 4 つ

最終定理は [Por/WellOrdering.lean](Por/WellOrdering.lean) にある。名前空間は `Por` である。

1. `terminates`：どの行数 $`r`$、どの $`r`$ 行の配列 $`A`$、どの $`n : \mathbb N \to \mathbb N`$ についても、展開の列はいつか空の配列に着く。

```math
A^{(0)} = A,\quad A^{(t+1)} = A^{(t)}[n(t)] \quad\implies\quad \exists T,\ A^{(T)} = ()
```

2. `step_wf`：$`r`$ 行のすべての配列の上で、1 段の展開の関係は整礎である。関係は次のとおりである（`Por.Step r`）。

```math
A \prec B \iff B \ne () \ \land\ \exists N,\ A = B[N]
```

つまり、$`C_t \ne ()`$ かつ $`C_{t+1} = C_t[N_t]`$ である無限列 $`C_0, C_1, C_2, \ldots`$ は無い。

3. `R_wf`：$`\mathrm{BM4}_r`$ の上で、1 段の展開の関係は整礎である（`BM4.R r`）。
4. `R'_wf`：すべての行数をまとめた BM4 の上で、1 段の展開の関係は整礎である（`BM4.R'`）。BM4 の元は行数を持つ。

```math
\mathrm{BM4} = \{\, (r, A) \mid r \in \mathbb N,\ A \in \mathrm{BM4}_r \,\}
```

1 番目が中心である。2 番目は 1 番目から数行で出る。3、4 番目は 2 番目を制限したものである。

どの配列も初めのラベルを持つので（後述の `Por.stable_all`）、1、2 番目は標準形でない配列にも成り立つ。

## 証明の形

証明は二層に分かれる。

- 組合せの層（`Bm4/`）。この層は、ラベルについての約束 `BM4.LabelSystem r` だけを仮定する。その上で、展開すると最後の列のラベルが下がることを示す（`BM4.descent`、DH の論文の命題 19.1）。[bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) の `lean/Bm4/` をそのまま使う。元は [dh-bms-wf-formal](https://github.com/koteitan/dh-bms-wf-formal) の形式化である。
- 意味の層（`Por/`）。約束を満たすラベルを与える。ラベルは順序数、関係は次の節の $`R`$ である（`Por.labelSystem r`）。

ラベルの約束は、整列したラベルの型 $`\mathrm{Lab}`$ と、層 $`k \in \mathbb N`$ ごとの関係 $`\mathrm{rel}_k`$ と、3 つの性質からなる。3 つの性質は、$`\mathrm{rel}_k(a,b) \Rightarrow a \lt b`$、推移律、有限反映（後述）である。

配列 $`A`$ の安定なラベルとは、列の位置からラベルへの写像 $`f`$ で、次の 2 つを満たすものである（`BM4.Stable`、DH の論文の定義 18.1）。$`i \prec^A_k j`$ は「列 $`i`$ は列 $`j`$ の行 $`k`$ の先祖である」と読む（`BM4.anc`）。

```math
i \lt j \lt \ell \implies f(i) \lt f(j), \qquad k \lt r,\ i \prec^A_k j \implies \mathrm{rel}_k(f(i), f(j))
```

高さは最後の列のラベル $`\mathrm{ht}(A,f) = f(\ell-1)`$ である（`BM4.ht`）。`BM4.descent` は次を言う。$`f`$ が $`A`$ の安定なラベルで、$`A \ne ()`$、$`A[N] \ne ()`$ とする。このとき $`A[N]`$ の安定なラベル $`g`$ で、次を満たすものがある。

```math
\mathrm{ht}(A[N],g) \lt \mathrm{ht}(A,f)
```

停止性は次のように出る。どの配列にも安定なラベルがある。展開の列が空に着かないとすると、`BM4.descent` を繰り返して、高さが真に下がり続ける順序数の無限列ができる。順序数は整礎なので、これは起こらない。

### 他の証明との違い

- DH の証明は、許容順序数をラベルにし、$`L_\alpha \prec^*_{k+2} L_\beta`$（DH の論文の式 (15.1)。交代数 $`k+2`$ までの論理式での初等性）を関係にする。KP 集合論を使う。
- [bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) は、ラベルを Carlson の構造 $`R_N`$ に替えた。そこでは層 $`j`$ の関係 $`\alpha \le_{j+1} \beta`$ は $`\Sigma_{j+1}`$ 初等性であり、量化子のブロックが複数ある論理式を使う。
- このリポジトリでは、どの層も $`\Sigma_1`$ である。量化子は存在量化のブロック 1 つだけである。層を上げたときの強さは、上端への関係 $`\mathrm{Top}_j`$ を原子記号として言語に入れることで得る。
- [1y-wo-por](https://github.com/koteitan/1y-wo-por) も同じ方法を 1-Y で使った。1-Y の約束には根の添字 $`\eta`$ が要る。そこで関係は $`R(k,\eta,a,b)`$、$`\mathrm{Rel}_j`$ は 3 変数、$`\mathrm{Top}_j`$ は 2 変数、再帰の鍵は（上端、層、添字）である。BMS の約束には $`\eta`$ が要らない。そこで関係は $`R(k,a,b)`$、$`\mathrm{Rel}_j`$ は 2 変数、$`\mathrm{Top}_j`$ は 1 変数、再帰の鍵は（上端、層）である。

## 関係 R

$`R(k,a,b)`$ は「層 $`k`$ で、$`a`$ は $`b`$ へ安定している」と読む。定義は次の 1 つの式である。

```math
R(k,a,b) \iff a \lt b \ \land\ \mathfrak A^{a}_{k} \preccurlyeq_{\Sigma_1} \mathfrak A^{b}_{k}
```

$`\mathfrak A^{\gamma}_{k}`$ は高さ $`\gamma`$、層 $`k`$ の構造である。領域は $`\{x \mid x \lt \gamma\}`$ である。

```math
\mathfrak A^{\gamma}_{k} = \bigl(\gamma;\ \lt,\ (\mathrm{Rel}_j)_{j \in \mathbb N},\ (\mathrm{Top}_j)_{j \lt k}\bigr)
```

- 内部の関係：$`\mathrm{Rel}_j(x,y) :\iff R(j,x,y)`$。すべての層 $`j`$ を持つ。
- 上端述語：$`\mathrm{Top}_j(x) :\iff R(j,x,\gamma)`$。層 $`j \lt k`$ だけを持つ。
- $`\preccurlyeq_{\Sigma_1}`$ は $`\Sigma_1`$ 初等部分構造である。$`a`$ より下のパラメータを持つ層 $`k`$ の $`\Sigma_1`$ 論理式の真偽が、2 つの構造で一致する（`Por.Elem`、`Por.ElemL`）。
- $`\Sigma_1`$ 論理式は組 $`(m,n,D,\mathit{bb},\mathit{np})`$ で表す。$`\mathit{np}`$ はパラメータの数、$`\mathit{bb}`$ は存在量化する変数の数、$`n \le \mathit{np}+\mathit{bb}`$ は読む変数の数、$`m`$ は読む記号の層の上限、$`D`$ は原子図式の集合である。論理式は「高さより下に $`\mathit{bb}`$ 個の値があって、パラメータとその値の原子図式が $`D`$ に入る」と読む（`Por.Sat`）。Lean では $`\mathit{np}`$ を `r` と書く。行の数 $`r`$ とは別のものである。

右辺は $`R`$ 自身を読む。そこで $`R`$ を、鍵 $`(b,k)`$ の辞書式順序による整礎再帰で定義する（`Por.stepF`、`Por.RF`）。右辺が読む $`R`$ は、どれも鍵が小さい。

- $`\mathrm{Rel}_j(x,y)`$ では $`y \lt b`$ である。
- $`\mathfrak A^{a}_k`$ の上端述語では、上端が $`a \lt b`$ である。
- $`\mathfrak A^{b}_k`$ の上端述語では、層が $`j \lt k`$ である。

Lean では `Por.R` と、その定義の式 `Por.R_iff` である（[Por/Relation.lean](Por/Relation.lean)）。

### ラベルの約束の行き先

| 約束 | 内容 | Lean 名 |
|---|---|---|
| ラベルの型 | 順序数。$`\lt`$ は整列順序 | Mathlib の `Ordinal` |
| `rel_lt` | $`R(k,a,b)`$ なら $`a \lt b`$ | `Por.R_lt` |
| `rel_trans` | $`R(k,a,b)`$ かつ $`R(k,b,c)`$ なら $`R(k,a,c)`$ | `Por.R_trans` |
| `reflect` | 有限反映 | `Por.reflect` |
| 初めのラベル | どの配列にも安定なラベルがある | `Por.stable_all` |

最初の 4 行をまとめたものが `Por.labelSystem r : BM4.LabelSystem r` である（[Por/Model.lean](Por/Model.lean)）。最後の行は約束には入っていない。停止性の証明が、展開の列の最初の配列 $`A^{(0)}`$ のラベルとして使う。

推移律は、2 つの初等性をつないで示す。$`\mathfrak A^{a}_k \preccurlyeq_{\Sigma_1} \mathfrak A^{b}_k`$ と $`\mathfrak A^{b}_k \preccurlyeq_{\Sigma_1} \mathfrak A^{c}_k`$ は、同じ構造 $`\mathfrak A^{b}_k`$ をはさむ。

有限反映は次の命題である。$`n \lt r`$ で $`R(n,\alpha,\beta)`$ とする。$`X`$ は $`\alpha`$ より下の有限集合とする。$`s \gt 0`$ で $`\alpha \le y_0 \lt \cdots \lt y_{s-1} \lt \beta`$ とする。このとき $`X \lt y'_0 \lt \cdots \lt y'_{s-1} \lt \alpha`$ となる $`y'`$ があり、$`x \in X`$、$`i, j \lt s`$、$`k \lt r`$、$`m \lt n`$ について次が成り立つ。

```math
R(k,x,y_i) \Rightarrow R(k,x,y'_i), \qquad R(k,y_i,y_j) \Rightarrow R(k,y'_i,y'_j), \qquad R(m,y_i,\beta) \Rightarrow R(m,y'_i,\alpha)
```

証明では、$`(X, y)`$ の原子図式の全体を 1 つの $`\Sigma_1`$ 論理式に書く。図式は、順序、層 $`k \lt r`$ の $`\mathrm{Rel}_k`$、層 $`m \lt n`$ の $`\mathrm{Top}_m`$ を読む。パラメータは $`X`$、存在量化する変数は $`y`$ である。この論理式は $`\mathfrak A^{\beta}_n`$ で真である。$`R(n,\alpha,\beta)`$ により $`\mathfrak A^{\alpha}_n`$ でも真である。その存在の値が $`y'`$ である。$`\mathfrak A^{\alpha}_n`$ での $`\mathrm{Top}_m(y'_i)`$ は $`R(m,y'_i,\alpha)`$ である。

初めのラベルは、$`\omega_1`$ より下の閉包点の鎖 $`c_0 \lt c_1 \lt \cdots`$ で作る（`Por.cC`）。

- $`\gamma`$ がよいとは、$`\omega_1`$ の上端述語を使った全言語で、$`(\gamma; \lt, R, \mathrm{Top}^{\omega_1}) \preccurlyeq_{\Sigma_1} (\omega_1; \lt, R, \mathrm{Top}^{\omega_1})`$ であることである（`Por.Good`）。
- $`\lambda(\gamma)`$ は、$`\gamma`$ を存在の値について閉じた点である。$`\gamma \lt \omega_1`$ なら $`\gamma \lt \lambda(\gamma) \lt \omega_1`$ で、$`\lambda(\gamma)`$ はよい（`Por.lam`、`Por.lam_good`）。
- $`c_0 = \lambda(0)`$、$`c_{t+1} = \lambda(c_t)`$ である。
- よい $`\alpha \lt \omega_1`$ では、$`x \lt \alpha`$ について $`R(j,x,\alpha) \iff R(j,x,\omega_1)`$ である（`Por.top_abs`、層 $`j`$ についての帰納法）。
- そのため $`i \lt j`$ なら、すべての層 $`k`$ で $`R(k,c_i, c_j)`$ である（`Por.chain_R`）。
- よって写像 $`i \mapsto c_i`$ は、先祖の関係によらず、どの配列の安定なラベルにもなる（`Por.stable_all`）。

証明は選択公理と $`\omega_1`$ の正則性を使う。ラベルは $`\omega_1`$ より下の順序数である。順序数の上界や表記系は得られない。

詳しい設計と証明は [notes/01-design.md](notes/01-design.md) にある（日本語）。

## 数学の解説

[study/](study/README.md) に、このリポジトリを読むための背景ノートがある（日本語と英語）。順序数と $`\omega_1`$、整礎関係と整礎再帰、構造と $`\Sigma_1`$ 初等部分構造、Carlson の patterns of resemblance、バシク行列システム、安定なラベルと高さの降下、関係 $`R`$、$`\omega_1`$ より下の閉包と鎖、約束の証明と最終定理の 9 本である。ノートには Lean は出てこない。

## ファイル

| 場所 | 中身 |
|---|---|
| [Por/](Por/) | 意味の層。9 ファイル、約 790 行。Mathlib を使う |
| [Bm4/](Bm4/) | 組合せの層。14 モジュール、約 3,000 行。bms-elem-pattern から写した |
| [notes/](notes/) | 設計のノート（日本語） |
| [study/](study/README.md) | 数学の解説のノート（日本語と英語） |
| [Audit.lean](Audit.lean) | 公理の監査。どの `lean_lib` にも入っていない |
| [LICENSE](LICENSE)、[NOTICE](NOTICE) | CC BY-SA 4.0 と出どころの記録 |

`Por/` の中身。上から import の順である。

| ファイル | 中身 |
|---|---|
| [Tuple.lean](Por/Tuple.lean) | 順序数の型 `Ord`、列をつなぐ `cat` |
| [Omega1.lean](Por/Omega1.lean) | $`\omega_1`$（`Om`）、可算順序数の数え上げ `enumBelow` |
| [Formula.lean](Por/Formula.lean) | 原子図式 `Diag`、$`\Sigma_1`$ 論理式の真偽 `Sat`、層つきの初等性 `ElemL` |
| [Relation.lean](Por/Relation.lean) | 再帰 `stepF`、`RF`、関係 `R`、`R_iff`、`R_lt`、`R_trans` |
| [Reflection.lean](Por/Reflection.lean) | 有限反映 `reflect` |
| [Closure.lean](Por/Closure.lean) | よい点 `Good`、閉包点 `lam`、`lam_good` |
| [Chain.lean](Por/Chain.lean) | 上端述語の絶対性 `top_abs`、鎖 `cC`、`chain_R` |
| [Model.lean](Por/Model.lean) | ラベルの約束 `labelSystem`、すべての配列のラベル `stable_all` |
| [WellOrdering.lean](Por/WellOrdering.lean) | 最終定理 4 つ |

`Bm4/` の中身。上から import の順である。定義、補題、命題の番号は DH の論文のものである。

| ファイル | 中身 |
|---|---|
| [Defs.lean](Bm4/Defs.lean) | 配列 `Arr`、親 `parent`、先祖 `anc`、展開 `expand`、$`E_r`$、BM4 `Elt`、展開の関係 `R`、`R'`（定義 1.1、2.1、5.1） |
| [Basic.lean](Bm4/Basic.lean) | 親と先祖の基本性質（補題 2.2）、接頭辞での不変性（補題 3.1）、親の候補の凸性（補題 4.1） |
| [Copy.lean](Bm4/Copy.lean) | コピー補題（定理 6.3）の準備。悪い根のデータ `BadRoot`、$`G \frown B_0 \frown B_1 \frown \cdots`$ の位置と成分 |
| [CopyPaper/Interval.lean](Bm4/CopyPaper/Interval.lean) | 区間の中の親（定義 6.1、補題 6.2）、6 つの主張 (C1)–(C6) の述語 |
| [CopyPaper/L1.lean](Bm4/CopyPaper/L1.lean) | 補題 6.4：主張 (C1) |
| [CopyPaper/L3.lean](Bm4/CopyPaper/L3.lean) | 補題 6.5：行 $`k \lt m_0`$ の主張 (C3) |
| [CopyPaper/L4.lean](Bm4/CopyPaper/L4.lean) | 補題 6.9、6.10：境界の主張 (C4) |
| [CopyPaper/L5.lean](Bm4/CopyPaper/L5.lean) | 補題 6.6：主張 (C5)。親はコピーを飛び越えない |
| [CopyPaper/L6.lean](Bm4/CopyPaper/L6.lean) | 補題 6.8：主張 (C6) |
| [CopyPaper/L2.lean](Bm4/CopyPaper/L2.lean) | 補題 6.7：主張 (C2) |
| [CopyPaper/Assemble.lean](Bm4/CopyPaper/Assemble.lean) | 命題 6.11 の組み立て、定理 6.3、系 6.12 |
| [CopyPaper/Char.lean](Bm4/CopyPaper/Char.lean) | 展開した配列での親の存在（命題 7.1 が使う形） |
| [Expand.lean](Bm4/Expand.lean) | 展開 `expand`（定義 5.1）と悪い根のデータをつなぐ |
| [Label.lean](Bm4/Label.lean) | ラベルの約束 `LabelSystem`、安定なラベル `Stable`（定義 18.1）、高さ `ht`、降下 `descent`（命題 19.1） |

`notes/` の中身。

- [01-design.md](notes/01-design.md)：意味の層の設計。約束の一覧、$`R`$ の定義、各約束の証明、Lean の名前との対応。
- [02-port.md](notes/02-port.md)：`Bm4/` を持ってきた記録と、`Por/` を 1y-wo-por の `Por/` から作った記録。

## ビルド

Lean 4.33.1 と Mathlib v4.33.1 を使う（`lean-toolchain`、`lakefile.toml`）。

作者の環境では、検査ツール leanman で検査した。リポジトリの根で次のコマンドを使う。

```sh
leanman build -C . Bm4 Por
leanman check -C . Audit.lean
```

lake だけでも同じことができる。

```sh
lake exe cache get
lake build Bm4 Por
lake env lean Audit.lean
```

- 既定のターゲットは `Por` である。`Por` は `Bm4` のすべてのモジュールを import する。そのため `lake build` だけでも、最終定理に要るモジュールはすべてビルドされる。
- `Audit.lean` は `Bm4` と `Por` をビルドしたあとに検査する。

## 公理の監査

[Audit.lean](Audit.lean) は主な定理の `#print axioms` を並べたファイルである。対象は次のとおりである。

- 最終定理：`Por.terminates`、`Por.step_wf`、`Por.R_wf`、`Por.R'_wf`。
- モデル：`Por.labelSystem`、`Por.reflect`、`Por.R_trans`、`Por.stable_all`、`Por.chain_R`、`Por.R_iff`。
- 組合せの層の降下：`BM4.descent`。

どの行も次の形を出力する。

```text
'Por.terminates' depends on axioms: [propext, Classical.choice, Quot.sound]
```

- どれも Lean の標準の 3 つの公理だけである。`sorryAx` は無い。
- ソースに `sorry` も `axiom` 宣言も無い。

## 参考文献

- DH, 「Bashicu Matrix System ver. 4 の停止性と展開関係の整礎性」, 巨大数研究 Wiki (2026). [論文 PDF](https://googology.fandom.com/ja/wiki/%E3%83%95%E3%82%A1%E3%82%A4%E3%83%AB%3ABM4%28%E4%BD%9C%E6%88%90%E8%80%85%E6%83%85%E5%A0%B1%E4%BB%98%E3%81%8D%29.pdf), [発表のブログ記事](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0%3ADeltaEta22223/BM4%E3%81%AE%E5%81%9C%E6%AD%A2%E6%80%A7%E8%A8%BC%E6%98%8E)
- R. Hunter, "Well-Orderedness of the Bashicu Matrix System", arXiv:2307.04606 (2023). [arXiv](https://arxiv.org/abs/2307.04606)
- T. J. Carlson, "Elementary Patterns of Resemblance", Annals of Pure and Applied Logic 108 (2001), 19–77.
- koteitan, [dh-bms-wf-formal](https://github.com/koteitan/dh-bms-wf-formal). DH の証明の Lean 4 による形式化。`Bm4/` の元。
- koteitan, [bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern). patterns of resemblance（$`\Sigma_n`$ 初等性）による BMS の停止性。`Bm4/` はここから写した。
- koteitan, [1y-wo-por](https://github.com/koteitan/1y-wo-por). $`\Sigma_1`$ 初等性だけによる 1-Y の整礎性。`Por/` の元。
- Phyrion, [1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean). 1-Y の整礎性の Lean の形式化。
- The mathlib Community, [Mathlib](https://github.com/leanprover-community/mathlib4).

## ライセンス

このリポジトリは CC BY-SA 4.0 である（[LICENSE](LICENSE)）。出どころと変更点は [NOTICE](NOTICE) に書いてある。

- `Bm4/`：[bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) の `lean/Bm4/`（CC BY-SA 4.0）を写したものである。元は [dh-bms-wf-formal](https://github.com/koteitan/dh-bms-wf-formal) である。Lean 4.30.0 から 4.33.1 に移した。証明を変えたのは `Bm4/Copy.lean` の `col_pos` だけである。各ファイルの先頭にそのことを書いてある。
- `Por/`：[1y-wo-por](https://github.com/koteitan/1y-wo-por) の `Por/` から作った。その補助は bms-elem-pattern の `lean/Pattern/` から来ている。1-Y の根の添字を外し、`Bm4/` のラベルの約束 `BM4.LabelSystem` に合わせた。各ファイルの先頭に元を書いてある。
- どのコードも同じ著作者（koteitan）による。ライセンスの無いプロジェクトのコードは、写しても翻案してもいない。
