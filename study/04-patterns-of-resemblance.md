[← Back](README.md) | [English](en/04-patterns-of-resemblance.md) | [Japanese](04-patterns-of-resemblance.md)

# Patterns of resemblance

前提

| ノート | ここで使う言葉 |
|---|---|
| [01 順序数と ω₁](01-ordinals.md) | 順序数、極限順序数、$`\mathrm{Ord}`$ |
| [02 整礎関係と整礎再帰](02-well-founded.md) | 整礎再帰、鍵、辞書式順序 |
| [03 構造と Σ₁ 初等部分構造](03-sigma1-elementary.md) | 構造 $`(\gamma; \ldots)`$、点、$`\Sigma_1`$ 論理式、$`\preccurlyeq_{\Sigma_1}`$、上端、上端述語（§7） |

このノートは、Carlson の patterns of resemblance の考え方を説明する。次に、[bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) が BMS でそれをどう使ったかを述べる。最後に、このリポジトリがそれをどう変えたかと、BMS では根の添字が要らない理由を述べる。

## 1. 自分自身を言語に持つ関係

**定義（Carlson の ≤₁）.** 順序数の上の関係 $`\le_1`$ を次の式で定める。

```math
\alpha \le_1 \beta \iff \alpha \le \beta \ \land\ (\alpha; \le, \le_1) \preccurlyeq_{\Sigma_1} (\beta; \le, \le_1)
```

$`\alpha \lt_1 \beta`$ は $`\alpha \lt \beta \land \alpha \le_1 \beta`$ のことである。

**読み方.** 「$`\alpha`$ より下の順序数の形は、$`\beta`$ より下まで広げても、$`\Sigma_1`$ 論理式では見分けられない」。ここで形とは、大小関係と、関係 $`\le_1`$ 自身である。

右辺は左辺の $`\le_1`$ を使う。循環に見えるが、$`\beta`$ についての整礎再帰で定義できる。

- 構造 $`(\beta; \le, \le_1)`$ の領域は $`\{x \mid x \lt \beta\}`$ である。そこで読む $`\le_1`$ は、$`x, y \lt \beta`$ の $`x \le_1 y`$ だけである。
- $`x \le_1 y`$ の真偽は、鍵 $`y \lt \beta`$ の段階で決まっている。
- 構造 $`(\alpha; \ldots)`$ も同じで、$`\alpha \le \beta`$ である。

Carlson はこれを $`\le_1, \ldots, \le_N`$（$`\Sigma_1, \ldots, \Sigma_N`$ の初等性）に広げた構造を調べた。

```math
\mathcal R_N = (\mathrm{Ord}; \le, \le_1, \ldots, \le_N)
```

- $`N \ge 1`$ は自然数である。
- $`\alpha \le_i \beta`$ は、$`\le_1`$ の定義の $`\preccurlyeq_{\Sigma_1}`$ を、$`\Sigma_i`$ 論理式での初等性に替えたものである。$`\Sigma_i`$ 論理式は、存在量化子のかたまりから始めて、存在量化子と全称量化子のかたまりを交互に $`i`$ 個並べ、その後ろに量化子の無い論理式を置いたものである。
- 関係 $`\le_1, \ldots, \le_N`$ のそれぞれを $`\mathcal R_N`$ の **段** と呼ぶ。

文献：T. J. Carlson, Elementary patterns of resemblance, Annals of Pure and Applied Logic 108 (2001), 19–77。

## 2. 小さい例

**例 1.** 自然数 $`n \lt \beta`$ について、$`n \le_1 \beta`$ ではない。

- $`n \ge 1`$ のとき：パラメータ $`n - 1`$ の $`\exists x\ (n - 1 \lt x)`$ は、$`\beta`$ で真（$`x = n`$）、$`n`$ で偽である。
- $`n = 0`$ のとき：$`\exists x\ (x \le x)`$ は、$`\beta`$ で真、空の構造 $`0`$ で偽である。

同じ理由で、後者順序数 $`\gamma + 1`$ も、それより大きい順序数と $`\le_1`$ の関係にない。

**例 2.** $`\omega \lt_1 \omega + 1`$ である。

例 1 から、$`\omega + 1`$ より下の異なる 2 点は $`\le_1`$ の関係にない。自然数どうしは例 1 で、残りは $`\omega`$ 自身だけだからである。したがって $`(\omega; \le, \le_1)`$ と $`(\omega + 1; \le, \le_1)`$ では、$`x \le_1 y`$ は $`x = y`$ と同じである。すると比べるのは順序だけの構造 $`(\omega; \le)`$ と $`(\omega + 1; \le)`$ で、$`\omega`$ は極限なので [03](03-sigma1-elementary.md) §5 の例から成り立つ。

**例 3.** $`\beta \ge \omega + 2`$ なら、$`\omega \le_1 \beta`$ ではない。$`\exists x\ \exists y\ (x \lt y \land x \le_1 y)`$ は、$`\beta`$ で真（例 2 の $`x = \omega`$、$`y = \omega + 1`$ はどちらも $`\beta`$ より下にある）、$`\omega`$ で偽（例 1）だからである。

$`\omega \le_1 \omega`$ は定義から成り立つ。以上から $`\{\beta \mid \omega \le_1 \beta\} = \{\omega, \omega + 1\}`$ である。

順序だけの言語では、$`\omega`$ より大きいどの $`\beta`$ でも $`(\omega; \le) \preccurlyeq_{\Sigma_1} (\beta; \le)`$ だった。$`\le_1`$ 自身を言語に入れたので、関係が細かくなった。

## 3. 停止性の証明での使い方

この節は、あとのノートで定義する言葉を先に使って、形だけを述べる。配列の列、親、先祖、悪い根、展開は [05](05-bms.md) で、ラベルの付け方は [06](06-stable-labels.md) で定義する。

展開の停止性の証明では、列ごとに順序数のラベルを付け、展開で最後の列のラベルが下がることを示す（[06](06-stable-labels.md)）。そこで要る性質は **有限反映** である。

**有限反映の形.** $`\alpha \lt_1 \beta`$ とする。$`\alpha`$ より下の点 $`\vec p`$ と、$`\beta`$ より下の点 $`\vec y`$ が、有限個の原子式の条件 $`\psi(\vec p, \vec y)`$ を満たすとする。すると、$`\alpha`$ より下の点 $`\vec y'`$ で、同じ条件 $`\psi(\vec p, \vec y')`$ を満たすものがある。

**理由.** $`\exists \vec y\ \psi(\vec p, \vec y)`$ は $`\Sigma_1`$ 論理式で、$`(\beta; \ldots)`$ で真である。$`\Sigma_1`$ 初等性から $`(\alpha; \ldots)`$ でも真である。

BMS の展開では、この形を次のように使う（[05](05-bms.md) §5、[06](06-stable-labels.md)）。

- $`\alpha`$ は悪い根の列のラベル、$`\beta`$ は最後の列のラベルである。
- $`\vec y`$ は、悪い根から最後の列の 1 つ前までの列のラベルである。どれも $`\alpha`$ 以上、$`\beta`$ 未満である。
- $`\vec p`$ は、それより左の列に付けたラベルである。

$`\psi`$ に「先祖の関係にある 2 列のラベルが、決まった関係を満たす」と書いておけば、新しいラベル $`\vec y'`$ も同じ条件を満たす。しかも $`\vec y'`$ は $`\alpha`$ より下にある。古いラベル $`\vec y`$ はどれも $`\alpha`$ 以上なので、新しいラベルは古いラベルより小さい。

## 4. bms-elem-pattern での使い方

[bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) は、$`r`$ 行の BMS の停止性を $`\mathcal R_r`$ で示した。

**ラベルの関係.** 行 $`k`$ の先祖の関係に、段 $`k + 1`$ の関係を対応させる。

```math
\mathrm{rel}_k(a, b) :\iff a \lt_{k+1} b \qquad (k \lt r)
```

行 $`n`$ で悪い根を使う展開では、$`\alpha \lt_{n+1} \beta`$ を使う。これは $`\Sigma_{n+1}`$ 論理式での初等性である。

**上端との関係が問題になる.** 有限反映には、§3 の形のほかに次の要求がある（[06](06-stable-labels.md) のラベルの約束）。

```math
\forall i \lt s\ \forall m \lt n\ \bigl(\mathrm{rel}_m(y_i, \beta) \Rightarrow \mathrm{rel}_m(y'_i, \alpha)\bigr)
```

右辺の $`\alpha`$ と左辺の $`\beta`$ は、構造の上端である。上端は構造 $`(\beta; \ldots)`$ の元ではない。そのため「$`y_i`$ が上端と関係 $`\mathrm{rel}_m`$ にある」は、そのままでは原子式にならない。

**bms-elem-pattern の解き方.** 上端との関係を、構造の中の論理式で言い換える。

- 「点 $`V`$ が上端と段 $`m`$ で結ばれている」を、構造の中から言う $`\Pi_m`$ 論理式 $`\Phi_m(V)`$ を作る。
- $`\Phi_{n-1}`$ を使って、存在量化子のかたまり、全称量化子のかたまり、…と量化子のかたまりを $`n + 1`$ 個並べた $`\Sigma_{n+1}`$ 論理式を書く。
- この論理式を $`\alpha \lt_{n+1} \beta`$ で $`\beta`$ から $`\alpha`$ へ移す。
- 連続性と共終性の補題（上端の下に、上端と結ばれた点が非有界にあること）で、$`y'_i`$ と $`\alpha`$ の関係を取り出す。

したがって、行の数 $`r`$ が増えると、量化子のかたまりの数も増える。詳しくは同リポジトリの [proof/bms/README.md](https://github.com/koteitan/bms-elem-pattern/blob/main/proof/bms/README.md) にある。$`\mathcal R_N`$ の定義と例は [proof/pss/03-patterns.md](https://github.com/koteitan/bms-elem-pattern/blob/main/proof/pss/03-patterns.md) にある。

## 5. このリポジトリの変更点

このリポジトリは、量化子のかたまりを増やさない。代わりに、上端との関係を記号として言語に入れる。

1. **論理式はすべて $`\Sigma_1`$ にする.** 層の強さは、量化子の複雑さではなく、言語にある記号で決める。
2. **上端述語（[03](03-sigma1-elementary.md) §7）を原子記号にする.** 高さ $`\gamma`$ の構造は、記号 $`\mathrm{Top}_j(x)`$ を「$`R(j, x, \gamma)`$」と解釈して持つ。上端への要求 $`\mathrm{rel}_m(y_i, \beta)`$ は、原子式 $`\mathrm{Top}_m(y_i)`$ になる。
3. **層 $`k`$ で見える記号を決める.** 層 $`k`$ の構造は、$`j \lt k`$ の上端述語 $`\mathrm{Top}_j`$ だけを持つ。$`k`$ が大きいほど、見える記号が増え、関係は強くなる。
4. **点どうしの関係 $`\mathrm{Rel}_j`$ はすべての層で持つ.** $`\mathrm{Rel}_j(x, y) :\iff R(j, x, y)`$ をすべての $`j`$ について持つ。
5. **再帰の鍵（[02](02-well-founded.md) §4）を $`(b, k)`$ にする.** 上端 $`b`$ を外側、層 $`k`$ を内側に置いた辞書式順序である（[02](02-well-founded.md) §3）。

すると、行 $`n`$ で悪い根を使う展開の要求 $`\mathrm{rel}_m(y_i, \beta) \Rightarrow \mathrm{rel}_m(y'_i, \alpha)`$（$`m \lt n`$）は、層 $`n`$ で見える原子式 $`\mathrm{Top}_m(y_i)`$ の真偽を $`\beta`$ から $`\alpha`$ へ移すことになる。$`\Sigma_1`$ 論理式 1 つで足りる。連続性や共終性の補題は要らない。

こうしてできた関係 $`R`$ は、Carlson の $`\mathcal R_N`$ そのものではない。$`\mathcal R_N`$ と同じだとは主張しない。定義は [07 関係 R](07-relation-r.md) で述べる。

| | $`\mathcal R_N`$（bms-elem-pattern） | このリポジトリの $`R`$ |
|---|---|---|
| 行 $`k`$ の関係 | 段 $`k + 1`$ の $`\lt_{k+1}`$ | 層 $`k`$ の $`R(k, \cdot, \cdot)`$ |
| 層の強さ | $`\Sigma_{k+1}`$ の量化子 | 見える上端述語 $`\mathrm{Top}_j`$（$`j \lt k`$） |
| 論理式 | $`\Sigma_1, \ldots, \Sigma_N`$ | $`\Sigma_1`$ だけ |
| 上端との関係 | 論理式 $`\Phi_m`$ と、連続性・共終性の補題 | 原子記号 $`\mathrm{Top}_j`$ |
| 再帰の鍵 | 上端 $`\beta`$ | $`(b, k)`$ の辞書式順序 |

## 6. BMS では根の添字が要らない理由

同じ考え方を 1-Y 数列に使ったのが [1y-wo-por](https://github.com/koteitan/1y-wo-por) である。1-Y の組合せの層が要求するラベルの関係は、4 つの引数を持っていた。

```math
R(k, \eta, a, b) \quad (k \in \mathbb N,\ \eta, a, b \in \mathrm{Ord})
```

$`\eta`$ は、親子の辺が属する成分の根のラベルで、順序数である。辺ごとに、根のラベルに応じた関係を要求するからである。そのため 1y-wo-por では、層と根の添字の組 $`(k, \eta)`$ で見える記号を決めた。$`\mathrm{Rel}_j`$ は 3 引数、$`\mathrm{Top}_j`$ は 2 引数で、再帰の鍵は $`(b, k, \eta)`$ だった。

BMS のラベルの約束（[06](06-stable-labels.md)）が要求するのは、次の形の関係だけである。

- 安定なラベル：$`j`$ が列 $`i`$ の行 $`k`$ での先祖なら、$`\mathrm{rel}_k(f(j), f(i))`$。
- 有限反映：点どうしの $`\mathrm{rel}_k(x, y)`$ と、上端への $`\mathrm{rel}_m(y, \beta)`$。

どれも、行の番号 $`k \in \mathbb N`$ と 2 つのラベルだけで決まる。成分の根のような、3 つ目のラベルは現れない。したがって関係は $`R(k, a, b)`$ の 3 引数で足りる。見える記号は層 $`k`$ だけで決まり、再帰の鍵は $`(b, k) \in \mathrm{Ord} \times \mathbb N`$ になる。

| | 1y-wo-por | このリポジトリ |
|---|---|---|
| 関係 | $`R(k, \eta, a, b)`$ | $`R(k, a, b)`$ |
| $`\mathrm{Rel}_j`$ | 3 引数 | 2 引数 |
| $`\mathrm{Top}_j`$ | 2 引数 | 1 引数 |
| 見える上端述語を決めるもの | $`(k, \eta)`$ | $`k`$ |
| 再帰の鍵 | $`(b, k, \eta)`$ | $`(b, k)`$ |

## 7. このリポジトリでの使われ方

| 場所 | 使い方 |
|---|---|
| [README](../README.md)「証明の形」「他の証明との違い」 | bms-elem-pattern、1y-wo-por との違い（$`\Sigma_1`$ だけ、上端述語を原子記号にする） |
| [README](../README.md)「関係 R」 | 上端述語 $`\mathrm{Top}_j`$ と、層 $`k`$ の構造 |
| [notes/01-design.md](../notes/01-design.md) §1、§3.8 | 設計の理由（上端述語を言語に入れること、鍵 $`(b, k)`$） |
| [notes/02-port.md](../notes/02-port.md) §3 | 1y-wo-por から根の添字 $`\eta`$ を除いたこと |
