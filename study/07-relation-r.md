[← Back](README.md) | [English](en/07-relation-r.md) | [Japanese](07-relation-r.md)

# 関係 R

前提

| ノート | ここで使う言葉 |
|---|---|
| [01 順序数と ω₁](01-ordinals.md) | 順序数、$`\mathrm{Ord}`$ |
| [02 整礎関係と整礎再帰](02-well-founded.md) | 辞書式順序、整礎再帰、ガードつきの再帰 |
| [03 構造と Σ₁ 初等部分構造](03-sigma1-elementary.md) | 高さ、点、証人、$`\Sigma_1`$ 論理式の 5 つ組と行列、上端、上端述語（§7）、見えるビットと 2 つの構造の比べ方（§8） |
| [04 Patterns of resemblance](04-patterns-of-resemblance.md) | 上端述語を原子記号にする考え方 |
| [06 安定なラベルと高さの降下](06-stable-labels.md) | ラベルの約束、関係 $`\mathrm{rel}_k`$、そのうち狭義性と推移律 |

このノートは、このリポジトリのラベルの関係 $`R`$ の定義と、定義から直接出る性質を説明する。

## 1. 記号

- $`\mathrm{Ord}`$：順序数全体。
- $`R(k, a, b)`$：層 $`k \in \mathbb N`$、下の点 $`a \in \mathrm{Ord}`$、上の点 $`b \in \mathrm{Ord}`$。**層** $`k`$ は、[06](06-stable-labels.md) のラベルの関係 $`\mathrm{rel}_k`$ の添字 $`k`$ にあたる。$`R`$ は §4 で定義する。§2、§3 では、$`R`$ を記号の解釈に使う。§5 で述べるとおり、この使い方は循環しない。
- $`\mathrm{Ord} \times \mathbb N`$ の辞書式順序：$`(b', j) \lhd (b, k) \iff b' \lt b \lor (b' = b \land j \lt k)`$。§5 の再帰で使う。

## 2. 言語

記号は 3 種類である。

| 記号 | 引数の数 | 意味（高さ $`\gamma`$ の構造で） |
|---|---|---|
| $`\lt`$ | 2 | 順序数の大小 |
| $`\mathrm{Rel}_j`$（$`j \in \mathbb N`$） | 2 | $`\mathrm{Rel}_j(x, y) :\iff R(j, x, y)`$ |
| $`\mathrm{Top}_j`$（$`j \in \mathbb N`$） | 1 | $`\mathrm{Top}_j(x) :\iff R(j, x, \gamma)`$ |

$`\mathrm{Rel}_j`$ は点どうしの関係、$`\mathrm{Top}_j`$ は点から上端 $`\gamma`$ への関係（上端述語）である（[03](03-sigma1-elementary.md) §7）。$`\gamma`$ 自身は領域に無い。

表の解釈を、§5 の段の解釈と区別して **真の解釈** と呼ぶ。上端述語の真の解釈は、高さ $`\gamma`$ ごとに違う。

## 3. 層 k の構造

**定義（層 k の構造）.** 順序数 $`\gamma`$ を高さとし、層 $`k`$ の構造を次で定める。領域は $`\{x \mid x \lt \gamma\}`$ である。

```math
\mathfrak A^{\gamma}_{k} = \bigl(\gamma;\ \lt,\ (\mathrm{Rel}_j)_{j \in \mathbb N},\ (\mathrm{Top}_j)_{j \lt k}\bigr)
```

- $`\mathrm{Rel}_j`$ はすべての層 $`j`$ で持つ。
- $`\mathrm{Top}_j`$ は $`j \lt k`$ だけで持つ。$`j \ge k`$ の上端述語は無い。

**層 $`k`$ の論理式** とは、この構造の言語の $`\Sigma_1`$ 論理式である。

**見えるビット.** 層 $`k`$ の論理式で見えるビット（[03](03-sigma1-elementary.md) §8）は、$`\lt`$ のビット、すべての $`\mathrm{Rel}_j`$ のビット、$`j \lt k`$ の $`\mathrm{Top}_j`$ のビットである。$`j \ge k`$ の $`\mathrm{Top}_j`$ のビットは見えない。見えないビットは偽と読む。見えるかどうかは層の番号 $`j`$ だけで決まり、点の値に依らない。

**例.** 層 2 で、次の論理式を考える。

```math
\exists y\ \bigl(p_0 \lt y \land \mathrm{Rel}_3(p_0, y) \land \mathrm{Top}_1(y)\bigr)
```

- $`\mathrm{Rel}_3(p_0, y)`$ は書ける。$`\mathrm{Rel}_j`$ はすべての $`j`$ で書ける。
- $`\mathrm{Top}_1(y)`$ は書ける（$`1 \lt 2`$）。
- $`\mathrm{Top}_2(y)`$ や $`\mathrm{Top}_3(p_0)`$ は、この層では書けない（読んでも偽になる）。

## 4. 定義

**定義（R）.**

```math
R(k, a, b) \iff a \lt b \ \land\ \mathfrak A^{a}_{k} \preccurlyeq_{\Sigma_1} \mathfrak A^{b}_{k}
```

ここで $`\mathfrak A^{a}_{k} \preccurlyeq_{\Sigma_1} \mathfrak A^{b}_{k}`$ は、層 $`k`$ のすべての $`\Sigma_1`$ 論理式 $`\varphi`$ と、すべてのパラメータ $`\vec p \lt a`$ について、次が成り立つことである。

```math
\mathfrak A^{a}_{k} \models \varphi(\vec p) \iff \mathfrak A^{b}_{k} \models \varphi(\vec p)
```

この比較（真の解釈で比べる）を $`\mathrm{Elem}(k, a, b)`$ と書く。2 つの構造で、上端述語は別のもの（$`a`$ への $`R`$ と $`b`$ への $`R`$）である（[03](03-sigma1-elementary.md) §8 の違い 1）。

## 5. 再帰

右辺は $`R`$ 自身を読む。鍵 $`(b, k)`$ の辞書式順序 $`\lhd`$（§1、[02](02-well-founded.md) §3）で整礎再帰をする。すべての $`a`$ について一度に定義する。

**右辺が読む R.** 3 種類だけで、どれも鍵が小さい。表の $`\mathfrak A^{a}`$、$`\mathfrak A^{b}`$ は $`\mathfrak A^{a}_{k}`$、$`\mathfrak A^{b}_{k}`$ の略である。

| 読むもの | 鍵 | 小さい理由 |
|---|---|---|
| $`\mathrm{Rel}_j(x, y)`$ | $`(y, j)`$ | 点は高さ（$`a`$ か $`b`$）より下なので $`y \lt b`$ |
| $`\mathfrak A^{a}`$ の上端述語 $`\mathrm{Top}_j(x)`$ | $`(a, j)`$ | $`a \lt b`$ |
| $`\mathfrak A^{b}`$ の見える上端述語 $`\mathrm{Top}_j(x)`$ | $`(b, j)`$ | $`j \lt k`$ |

**ガードつきの再帰.** 鍵 $`t = (b, k)`$ での値は、$`R(k, \cdot, b)`$ を満たす $`a`$ の集合である。これを、鍵 $`t`$ での再帰の 1 ステップで使う次の解釈で定める。この解釈を **段の解釈** と呼ぶ。記号の右肩の $`\mathrm{st}`$ は、段の解釈であることを表す印である。3 つの解釈には、鍵が小さいという条件をガードとして付ける（[02](02-well-founded.md) §5）。

| 段の解釈 | 式 |
|---|---|
| $`\mathrm{Rel}^{\mathrm{st}}_j(x, y)`$ | $`y \lt b \land R(j, x, y)`$ |
| $`\mathrm{Top}^{\mathrm{st},a}_j(x)`$ | $`a \lt b \land R(j, x, a)`$ |
| $`\mathrm{Top}^{\mathrm{st},b}_j(x)`$ | $`j \lt k \land R(j, x, b)`$ |

段の解釈で比べた $`\Sigma_1`$ 初等性を $`\mathrm{Elem}^{\mathrm{st}}(k, a, b)`$ と書く。段の解釈は小さい鍵での $`R`$ だけを読むので、[02](02-well-founded.md) §4 の整礎再帰で $`R`$ が決まる。定義の等式は、次のガードつきの等式である。

```math
R(k, a, b) \iff a \lt b \land \mathrm{Elem}^{\mathrm{st}}(k, a, b)
```

## 6. ガードを外す

**補題（ガードを外す）.** $`a \lt b`$ なら、$`\mathrm{Elem}^{\mathrm{st}}(k, a, b) \iff \mathrm{Elem}(k, a, b)`$ である。つまり、段の解釈での $`\Sigma_1`$ 初等性と、真の解釈での $`\Sigma_1`$ 初等性は同値である。

**証明.** 層 $`k`$ の論理式が読むビットでは、ガードがいつも真であることを示す。

1. $`\mathrm{Rel}`$ のビット：点は、パラメータ（$`\lt a`$）か証人（$`\lt`$ 高さ $`\le b`$）である。よって $`y \lt b`$。
2. 高さ $`a`$ の上端述語：ガードは $`a \lt b`$ で、仮定そのものである。
3. 高さ $`b`$ の見える上端述語：見えるのは $`j \lt k`$ の $`\mathrm{Top}_j`$ だけである（§3）。ガードは $`j \lt k`$ で、これはいつも真である。

見えないビットは、どちらの解釈でも偽である。よって [03](03-sigma1-elementary.md) §8 の補題 1 から、原子図式が等しく、真偽も等しい。$`\square`$

**定理（定義の式）.**

```math
R(k, a, b) \iff a \lt b \land \mathrm{Elem}(k, a, b)
```

**証明.** §5 のガードつきの等式に、$`a \lt b`$ の下で補題（ガードを外す）を使う。$`\square`$

## 7. 定義から直接出る性質

**定理（狭義性）.** $`R(k, a, b)`$ なら $`a \lt b`$。定義の式の右辺の 1 番目の条件である。これが [06](06-stable-labels.md) のラベルの約束の狭義性（$`\mathrm{rel}_k(a, b) \implies a \lt b`$）である。

**定理（推移律）.** $`R(k, a, b)`$ かつ $`R(k, b, c)`$ なら $`R(k, a, c)`$。これが [06](06-stable-labels.md) のラベルの約束の推移律である。

**証明.** 定義の式から $`a \lt b`$、$`b \lt c`$ なので $`a \lt c`$。層 $`k`$ の論理式 $`\varphi`$ と、パラメータ $`\vec p \lt a`$ を取る。$`\vec p \lt a \lt b`$ なので、2 つの仮定がどちらも使える。

```math
\mathfrak A^{a}_{k} \models \varphi(\vec p) \iff \mathfrak A^{b}_{k} \models \varphi(\vec p) \iff \mathfrak A^{c}_{k} \models \varphi(\vec p)
```

1 つ目の $`\iff`$ は $`R(k, a, b)`$、2 つ目の $`\iff`$ は $`R(k, b, c)`$ から出る。よって $`\mathrm{Elem}(k, a, c)`$ である。定義の式から $`R(k, a, c)`$。$`\square`$

この証明では、2 つの仮定の真ん中の構造が同じ $`\mathfrak A^{b}_{k}`$ である。どちらの仮定も層 $`k`$ で、上端述語は「$`b`$ への $`R`$」と解釈する。そのため 2 つの同値をそのままつなげられる。

**性質（見える上端述語の一致）.** $`R(k, a, b)`$ で、$`x \lt a`$、$`j \lt k`$ とする。このとき次が成り立つ。

```math
R(j, x, a) \iff R(j, x, b)
```

**理由.** 量化子の無い論理式 $`\mathrm{Top}_j(p_0)`$ を、パラメータ $`x`$ で使う。$`j \lt k`$ なので層 $`k`$ の論理式である。高さ $`a`$ では左辺、高さ $`b`$ では右辺を意味する。証明はこの性質を使わない。使うのは、似た形の [09](09-obligations.md) の定理（上端述語の絶対性）である。これは Good な点と $`\omega_1`$ の間での上端述語の一致である。

**性質（下の点は極限順序数）.** $`R(k, a, b)`$ なら、$`a`$ は 0 でない極限順序数である。

**理由.** [03](03-sigma1-elementary.md) §5 の例と同じである。

- $`a = 0`$ のとき：$`\exists y\ \neg(y \lt y)`$（$`m = 0`$、$`n = 1`$、$`\mathit{bb} = 1`$、$`\mathit{np} = 0`$、行列は「$`[v_0 \lt v_0] = 0`$」である完全な原子図式の集合）は、高さ $`b`$ で真、高さ 0 で偽である。
- $`a = \gamma + 1`$ のとき：パラメータ $`\gamma \lt a`$ の $`\exists y\ (\gamma \lt y)`$ は、高さ $`b`$ で真（$`y = \gamma + 1 \lt b`$）、高さ $`a`$ で偽である。

どちらも $`\mathrm{Elem}`$ に反する。組合せの層はこの性質を使わない。

## 8. 使わない性質

次の 2 つの性質は、この証明では使わない。

- 層についての単調性：$`j \le k`$ かつ $`R(k, a, b)`$ なら $`R(j, a, b)`$。層 $`j`$ の論理式は層 $`k`$ の論理式でもあり、2 つの層は見える記号を同じに解釈するので、成り立つ。
- 局所性：上端が $`\le \delta`$ の $`R`$ は、鍵が $`(\delta + 1, 0)`$ より小さい再帰だけで決まる。成り立つと考えられるが、ここでは証明しない。

## 9. このリポジトリでの使われ方

| 場所 | 使い方 |
|---|---|
| [README](../README.md)「関係 R」 | 定義の式と、再帰の 3 つの読み方 |
| [README](../README.md)「ラベルの約束の行き先」 | 狭義性と推移律は §7 の 2 つの定理から出る |
| [notes/01-design.md](../notes/01-design.md) §3.3、§3.4、§4.1、§4.3、§4.4 | 関係 R の定義、再帰、定義の式、狭義性、推移律 |
