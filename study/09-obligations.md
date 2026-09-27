[← Back](README.md) | [English](en/09-obligations.md) | [Japanese](09-obligations.md)

# 約束の証明と最終定理

前提

| ノート | ここで使う言葉 |
|---|---|
| [01 順序数と ω₁](01-ordinals.md) | 順序数の $`\lt`$ が整列順序であること、無限降下列が無いこと（§1）、$`\omega_1`$ |
| [02 整礎関係と整礎再帰](02-well-founded.md) | 整礎、整礎帰納法（§1、§2） |
| [03 構造と Σ₁ 初等部分構造](03-sigma1-elementary.md) | 原子図式、ビット（§3）、$`\Sigma_1`$ 論理式の 5 つ組と行列（§7）、見えるビットと、見えないビットを偽にする補題 2（§8） |
| [05 バシク行列システム](05-bms.md) | $`r`$ 行の配列、列、親、先祖、展開 $`A[N]`$、空の配列 $`()`$、展開列、1 段の展開 $`\triangleleft`$、$`E_r`$、BM4 |
| [06 安定なラベルと高さの降下](06-stable-labels.md) | ラベルの約束、$`\mathrm{rel}_k`$、有限反映、安定なラベル、高さ $`\mathrm{ht}`$、DH の命題 19.1（高さの降下） |
| [07 関係 R](07-relation-r.md) | $`R(k, a, b)`$、層、層 $`k`$ の構造 $`\mathfrak A^{\gamma}_{k}`$、層 $`k`$ の論理式、$`\mathrm{Rel}_j`$、$`\mathrm{Top}_j`$、$`\mathrm{Elem}`$、定義の式、狭義性と推移律の定理（§7） |
| [08 ω₁ より下の閉包と鎖](08-closure-chain.md) | $`\mathfrak B`$、$`\mathfrak B{\restriction}\gamma`$、Good、閉包点、鎖 $`c_t`$ と性質 9〜11 |

このノートは、関係 $`R`$ がラベルの約束をどう満たすかを説明する。そのあと、すべての配列に安定なラベルを付け、最終定理を導く。中心は有限反映（§3）と、鎖によるラベル（§4〜§6）である。

## 1. 約束の一覧

行数 $`r \in \mathbb N`$ を固定する。ラベルは順序数、ラベルの順序は順序数の $`\lt`$ とする。関係は $`\mathrm{rel}_k(a, b) :\iff R(k, a, b)`$ とする。

| 約束（[06](06-stable-labels.md)） | 内容 | 節 |
|---|---|---|
| 整列 | ラベルの $`\lt`$ は整列順序 | §2 |
| 狭義性 | $`R(k, a, b) \implies a \lt b`$ | §2 |
| 推移律 | $`R(k, a, b) \land R(k, b, c) \implies R(k, a, c)`$ | §2 |
| 有限反映 | $`n \lt r`$ と $`R(n, \alpha, \beta)`$ から、$`[\alpha, \beta)`$ の有限個の点を $`\alpha`$ より下に移す | §3 |

最終定理には、約束のほかに、最初の配列の安定なラベルが要る。これは §4〜§6 で作る。

## 2. 整列、狭義性、推移律

- 整列：順序数の $`\lt`$ は整列順序である（[01](01-ordinals.md) §1）。
- 狭義性：[07](07-relation-r.md) §7 の定理（狭義性）。定義の式の右辺の 1 番目の条件である。
- 推移律：[07](07-relation-r.md) §7 の定理（推移律）。2 つの $`\Sigma_1`$ 初等性を、真ん中の同じ構造 $`\mathfrak A^{b}_{k}`$ でつなぐ。

## 3. 有限反映

**示すこと.** 次を仮定する。

- $`n \lt r`$ と $`R(n, \alpha, \beta)`$。
- $`X`$ は順序数の有限集合で、$`X`$ の元はどれも $`\lt \alpha`$。
- $`s \gt 0`$ と $`\alpha \le y_0 \lt y_1 \lt \cdots \lt y_{s-1} \lt \beta`$。

このとき、$`y'_0 \lt y'_1 \lt \cdots \lt y'_{s-1} \lt \alpha`$ で、次の 4 つを満たすものを作る。ここで $`x \in X`$、$`i, j \lt s`$、$`k \lt r`$、$`m \lt n`$ とする。

- (a) $`x \lt y'_0`$。
- (b) $`R(k, x, y_i) \implies R(k, x, y'_i)`$。
- (c) $`R(k, y_i, y_j) \implies R(k, y'_i, y'_j)`$。
- (d) $`R(m, y_i, \beta) \implies R(m, y'_i, \alpha)`$。

**証明.**

1. $`X`$ の元を $`x_0, \ldots, x_{|X|-1}`$ と並べる。$`|X|`$ は $`X`$ の元の数である。並べる順は問わない。
2. 変数の列を $`z = (x_0, \ldots, x_{|X|-1}, y_0, \ldots, y_{s-1})`$ とする。長さは $`|X| + s`$ である。
3. 高さ $`\beta`$ の層 $`n`$ の構造 $`\mathfrak A^{\beta}_{n}`$ で、$`z`$ の原子図式を $`d`$ とする。記号の上限は $`r`$ とする。$`d`$ は次のビットからなる。$`i, j \lt |X| + s`$ とする。
   - 順序のビット $`[z_i \lt z_j]`$。
   - $`\mathrm{Rel}_k`$ のビット $`[R(k, z_i, z_j)]`$（$`k \lt r`$）。
   - $`\mathrm{Top}_m`$ のビット $`[R(m, z_i, \beta)]`$（$`m \lt n`$）。$`m \lt n \lt r`$ なので、記号の上限 $`r`$ に収まる。$`n \le m \lt r`$ の $`\mathrm{Top}_m`$ のビットは、層 $`n`$ では見えないので偽である。
4. 次の $`\Sigma_1`$ 論理式 $`\Phi`$ を作る。パラメータは $`x_0, \ldots, x_{|X|-1}`$ で、証人は $`y_0, \ldots, y_{s-1}`$ である。

```math
\Phi(x_0, \ldots, x_{|X|-1}) :\equiv \exists y_0 \cdots \exists y_{s-1}\ \ \mathrm{diag}(x_0, \ldots, x_{|X|-1}, y_0, \ldots, y_{s-1}) \in \{d\}
```

5. $`\Phi`$ は層 $`n`$ の論理式である。[03](03-sigma1-elementary.md) §7 の 5 つ組では、記号の上限が $`r`$、変数の数が $`|X| + s`$、行列が $`\{d\}`$、証人の数が $`s`$、パラメータの数が $`|X|`$ である。行列は 1 つの原子図式だけを持つ。つまり $`\Phi`$ は「原子図式の全部が $`d`$ と同じになる証人がある」という論理式である。
6. 高さ $`\beta`$ で $`\Phi`$ は真である。証人は $`y_0, \ldots, y_{s-1}`$ そのもので、どれも $`\lt \beta`$ である。そのときの原子図式は、3 の定義から $`d`$ である。
7. 定義の式（[07](07-relation-r.md)）から $`\mathrm{Elem}(n, \alpha, \beta)`$ である。パラメータ $`x_0, \ldots, x_{|X|-1}`$ はどれも $`\lt \alpha`$ である。よって高さ $`\alpha`$ でも $`\Phi`$ は真である。その証人を $`y'_0, \ldots, y'_{s-1}`$ とする。どれも $`\lt \alpha`$ である。高さ $`\alpha`$ の構造 $`\mathfrak A^{\alpha}_{n}`$ での $`(x_0, \ldots, x_{|X|-1}, y'_0, \ldots, y'_{s-1})`$ の原子図式は $`d`$ である。
8. 2 つの原子図式が同じなので、$`y`$ についての各ビットが $`y'`$ に移る。
   - 順序のビット：$`i \lt j`$ なら $`y_i \lt y_j`$ なので、$`y'_i \lt y'_j`$。$`x \lt \alpha \le y_0`$ なので、$`x \lt y'_0`$。後者が (a) である。
   - $`\mathrm{Rel}_k`$ のビット：$`\mathrm{Rel}_k`$ はどの高さでも $`R(k, \cdot, \cdot)`$ である。よって $`R(k, x, y_i) \iff R(k, x, y'_i)`$ と $`R(k, y_i, y_j) \iff R(k, y'_i, y'_j)`$。これが (b) と (c) である。
   - $`\mathrm{Top}_m`$ のビット：高さ $`\beta`$ では、$`\mathrm{Top}_m(y_i)`$ は $`R(m, y_i, \beta)`$ である。高さ $`\alpha`$ では、$`\mathrm{Top}_m(y'_i)`$ は $`R(m, y'_i, \alpha)`$ である。よって $`R(m, y_i, \beta) \iff R(m, y'_i, \alpha)`$。これが (d) である。$`\square`$

**注意.**

- 証明から出るのは (b)〜(d) の同値である。約束が求めるのは $`\implies`$ の向きだけである。
- $`\Phi`$ は偽のビットも含む。したがって、成り立たない関係も $`y'`$ に移る。
- (d) は、$`\beta`$ への関係を $`\alpha`$ への関係に移す。上端述語 $`\mathrm{Top}_m`$ が言語の記号なので、これを 1 つの $`\Sigma_1`$ 論理式で言える（[04](04-patterns-of-resemblance.md) §5）。
- 使わなかったもの：$`\alpha`$ や $`\beta`$ が極限順序数であること、閉包点であること。

**例（手で書いた形だけの例）.** $`r = 2`$、$`n = 1`$、$`X = \{x_0\}`$（$`|X| = 1`$）、$`s = 2`$ とする。$`z = (x_0, y_0, y_1)`$ である。高さ $`\beta`$ で真のビットが、次の 6 つだけだと仮定する。この 6 つは、推移律に反しないように選んだ。

```math
x_0 \lt y_0,\quad x_0 \lt y_1,\quad y_0 \lt y_1,\quad R(0, x_0, y_0),\quad R(1, x_0, y_0),\quad R(0, y_1, \beta)
```

このとき $`\Phi`$ は次の形である。

```math
\exists y_0\ \exists y_1\ \bigl[\ x_0 \lt y_0 \land x_0 \lt y_1 \land y_0 \lt y_1 \land \mathrm{Rel}_0(x_0, y_0) \land \mathrm{Rel}_1(x_0, y_0) \land \mathrm{Top}_0(y_1) \land \Psi\ \bigr]
```

$`\Psi`$ は、ほかのビット（たとえば $`\mathrm{Rel}_0(y_0, y_1)`$、$`\mathrm{Top}_0(y_0)`$、$`y_1 \lt y_0`$）の否定をすべて並べたものである。反映すると、$`x_0 \lt y'_0 \lt y'_1 \lt \alpha`$ で、次を満たす $`y'_0, y'_1`$ が取れる。

```math
R(0, x_0, y'_0),\quad R(1, x_0, y'_0),\quad R(0, y'_1, \alpha),\quad \neg R(0, y'_0, y'_1),\quad \neg R(0, y'_0, \alpha)
```

## 4. 上端述語の絶対性

**定理（上端述語の絶対性）.** $`\mathrm{Good}(\delta)`$ かつ $`\delta \lt \omega_1`$ とする。すべての $`j \in \mathbb N`$ と $`x \lt \delta`$ について、次が成り立つ。

```math
R(j, x, \delta) \iff R(j, x, \omega_1)
```

**証明.** $`j`$ について、自然数の $`\lt`$ で整礎帰納法をする（[02](02-well-founded.md) §2）。

1. 定義の式（[07](07-relation-r.md)）で両辺を開く。$`x \lt \delta`$ も $`x \lt \omega_1`$ も真である。残りは、層 $`j`$ の論理式 $`\psi`$（パラメータ $`\lt x`$）について、高さ $`\delta`$ と高さ $`\omega_1`$ での真偽が一致することである。
2. 高さ $`\delta`$ で $`\psi`$ が読む上端述語のビットは $`\mathrm{Top}_i(u)`$（$`i \lt j`$、$`u \lt \delta`$）である。その意味は $`R(i, u, \delta)`$ である。帰納法の仮定から、これは $`R(i, u, \omega_1)`$ と同値である。
3. よって $`\mathfrak A^{\delta}_{j}`$ は、見えるビットで $`\mathfrak B{\restriction}\delta`$ と一致する。[03](03-sigma1-elementary.md) §8 の補題 2 で、$`\psi`$ を、見えないビットを偽にした全記号の論理式 $`\psi^*`$ に訳す。
4. $`\mathrm{Good}(\delta)`$ から、$`\mathfrak B{\restriction}\delta \models \psi^* \iff \mathfrak B \models \psi^*`$。
5. $`\mathfrak A^{\omega_1}_{j}`$ は、$`\mathfrak B`$ の $`i \ge j`$ の上端述語を見えなくしたものである。もう一度補題 2 で戻すと、$`\mathfrak A^{\omega_1}_{j}`$ での真偽になる。$`\square`$

まとめると、パラメータ $`\vec p \lt x`$ について次の同値をつないでいる。

```math
\mathfrak A^{\delta}_{j} \models \psi(\vec p) \iff \mathfrak B{\restriction}\delta \models \psi^*(\vec p) \iff \mathfrak B \models \psi^*(\vec p) \iff \mathfrak A^{\omega_1}_{j} \models \psi(\vec p)
```

2 で「見えるかどうかは層の番号だけで決まる」（[03](03-sigma1-elementary.md) §8）を使う。そのため、帰納法は層 $`j`$ だけについて行えばよい。

## 5. 鎖の 2 点は R の関係にある

**定理（鎖の 2 点は R の関係にある）.** 自然数 $`i \lt j`$ と、任意の層 $`k \in \mathbb N`$ について $`R(k, c_i, c_j)`$。

**証明.** [08](08-closure-chain.md) §7 の性質 10 から $`c_i \lt c_j`$ である。層 $`k`$ の論理式 $`\psi`$ と、パラメータ $`\vec p \lt c_i`$ について、次の同値をつなぐ。

```math
\mathfrak A^{c_i}_{k} \models \psi \iff \mathfrak B{\restriction}c_i \models \psi^* \iff \mathfrak B \models \psi^* \iff \mathfrak B{\restriction}c_j \models \psi^* \iff \mathfrak A^{c_j}_{k} \models \psi
```

1 番目と 4 番目は、§4 の定理（$`c_i`$ と $`c_j`$ で使う）と [03](03-sigma1-elementary.md) §8 の補題 2 である。§4 の定理の仮定は [08](08-closure-chain.md) §7 の性質 9、11 である。2 番目と 3 番目は $`\mathrm{Good}(c_i)`$ と $`\mathrm{Good}(c_j)`$ である（$`\vec p \lt c_i \lt c_j`$）。よって $`\mathrm{Elem}(k, c_i, c_j)`$ で、定義の式から $`R(k, c_i, c_j)`$。$`\square`$

## 6. すべての配列の安定なラベル

**定理（すべての配列の安定なラベル）.** $`r \in \mathbb N`$ とし、$`A`$ を任意の $`r`$ 行の配列とする。$`f(t) := c_t`$（$`t \in \mathbb N`$）は、$`A`$ の安定なラベルである。

**証明.** 安定なラベルの 2 つの条件（[06](06-stable-labels.md)）を確かめる。

- $`f`$ は狭義増加である（[08](08-closure-chain.md) §7 の性質 10）。
- $`k \lt r`$ で、列 $`i`$ が列 $`j`$ の $`k`$-先祖とする。先祖は左にあるので $`i \lt j`$ である。§5 の定理から $`R(k, c_i, c_j)`$。$`\square`$

$`f`$ は $`A`$ にも $`r`$ にも依らない。$`f`$ は配列の成分を見ない。どの 2 列 $`i \lt j`$ も、すべての層で $`R`$ の関係にある。これは安定なラベルが求めるよりも多い。したがって、$`E_r`$ から展開で得られる配列だけでなく、すべての配列にラベルが付く。

**例（計算機で計算した）.** $`r = 2`$、$`A = (0,0)(2,1)(1,1)`$ とする。親と先祖を小さい Python のプログラムで計算した。

| 行 | 列 1 の親 | 列 2 の親 | 先祖の組 |
|---|---|---|---|
| 0 | 列 0 | 列 0 | (0, 1)、(0, 2) |
| 1 | 列 0 | 列 0 | (0, 1)、(0, 2) |

組 $`(i, j)`$ は「列 $`i`$ は列 $`j`$ の先祖」を表す。安定なラベルが求めるのは、$`c_0 \lt c_1 \lt c_2`$ と次の 4 つである。

```math
R(0, c_0, c_1),\quad R(0, c_0, c_2),\quad R(1, c_0, c_1),\quad R(1, c_0, c_2)
```

どれも §5 の定理から出る。§5 の定理からは $`R(0, c_1, c_2)`$ と $`R(1, c_1, c_2)`$ も出るが、この配列では求められていない。

## 7. 最終定理

$`r`$ 行の配列 $`A`$ と、関数 $`n : \mathbb N \to \mathbb N`$ について、展開列（[05](05-bms.md) §7）を次で定める。

```math
A^{(0)} = A, \qquad A^{(t+1)} = A^{(t)}[n(t)]
```

$`()`$ は空の配列（長さ 0 の配列）を表す（[05](05-bms.md) §1）。

**定理 1（停止性）.** すべての $`r \in \mathbb N`$、すべての $`r`$ 行の配列 $`A`$、すべての $`n : \mathbb N \to \mathbb N`$ について、次が成り立つ。

```math
\exists T \in \mathbb N\ \ A^{(T)} = ()
```

**証明.** どの $`A^{(t)}`$ も空でないとする。$`t`$ についての再帰で、$`A^{(t)}`$ の安定なラベル $`g_t`$ を選ぶ。

- $`g_0(i) := c_i`$（§6）。
- $`g_t`$ が $`A^{(t)}`$ の安定なラベルなら、DH の命題 19.1（[06](06-stable-labels.md)）から、$`A^{(t+1)}`$ の安定なラベル $`g_{t+1}`$ で $`\mathrm{ht}(g_{t+1}) \lt \mathrm{ht}(g_t)`$ となるものがある。その 1 つを選択公理で選ぶ。命題 19.1 は、$`A^{(t)}`$ と $`A^{(t+1)}`$ が空でないことと、§2、§3 のラベルの約束を使う。

すると次の順序数の無限降下列ができる。

```math
\mathrm{ht}(g_0) \gt \mathrm{ht}(g_1) \gt \mathrm{ht}(g_2) \gt \cdots
```

これは [01](01-ordinals.md) §1 に反する。$`\square`$

**定理 2（すべての配列での整礎性）.** $`r`$ 行の配列全体の上の関係 $`\triangleleft_r`$ を次で定める。これは [05](05-bms.md) §7 の 1 段の展開 $`\triangleleft`$ に、行数を添字として付けたものである。

```math
A \triangleleft_r B :\iff B \ne () \land \exists N \in \mathbb N\ \ A = B[N]
```

$`\triangleleft_r`$ は整礎である。

**証明.** $`\triangleleft_r`$ の無限降下列 $`C_0 \triangleright_r C_1 \triangleright_r \cdots`$ があるとする。$`C_{t+1} = C_t[N_t]`$ で、どの $`C_t`$ も空でない。これは定理 1（$`A = C_0`$、$`n(t) = N_t`$）に反する。$`\square`$

**定理 3（BM4 の $`r`$ 行の部分での整礎性）.** $`E_r = (0, \ldots, 0)(1, \ldots, 1)`$ から有限回の展開で得られる配列の集合を $`\mathrm{BM4}_r`$ とする。$`\triangleleft_r`$ を $`\mathrm{BM4}_r`$ に制限した関係は整礎である。

**証明.** 整礎な関係を部分集合に制限しても、整礎である。定理 2 から出る。$`\square`$

**定理 4（BM4 全体での整礎性）.** BM4 を、行数 $`r`$ と $`A \in \mathrm{BM4}_r`$ の組 $`(r, A)`$ の全体とする。関係を次で定める。

```math
(r', A) \triangleleft (r, B) :\iff r' = r \land A \triangleleft_r B
```

$`\triangleleft`$ は BM4 の上で整礎である。

**証明.** 展開は行数を変えない。よって $`\triangleleft`$ の無限降下列は、ある 1 つの $`\mathrm{BM4}_r`$ の中にある。これは定理 3 に反する。$`\square`$

**強さ.** 証明は選択公理と $`\omega_1`$ の正則性を使う。ラベルは $`\omega_1`$ より下の閉包点で、具体的な値は分からない。順序数の上界や表記系は得られない。構成的宇宙 $`L`$ も許容順序数も使わない。モデル論の概念は $`\Sigma_1`$ 初等性だけを使う。

## 8. このリポジトリでの使われ方

| 場所 | 使い方 |
|---|---|
| [README](../README.md)「ラベルの約束の行き先」 | 約束の表と、有限反映・すべての配列のラベルの要約 |
| [README](../README.md)「何を証明したか」 | 最終定理 4 つ（§7） |
| [notes/01-design.md](../notes/01-design.md) §4.5、§4.7、§4.8、§4.9 | 各約束の証明、上端述語の絶対性、鎖、最終定理 |
