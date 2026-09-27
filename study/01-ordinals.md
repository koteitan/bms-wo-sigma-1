[← Back](README.md) | [English](en/01-ordinals.md) | [Japanese](01-ordinals.md)

# 順序数と ω₁

前提: なし

このノートは、順序数と $`\omega_1`$ を説明する。あとのノートでは、展開の停止性の証明で、配列の列に順序数を付けて使う（[06 安定なラベルと高さの降下](06-stable-labels.md)）。使う事実は §5 の正則性と §6 の数え上げである。

## 1. 整列順序と順序数

**定義（整列順序）.** 集合 $`X`$ の上の全順序 $`\lt`$ が **整列順序** であるとは、$`X`$ の空でない部分集合がどれも最小元を持つことをいう。

**定義（無限降下列）.** $`x_0 \gt x_1 \gt x_2 \gt \cdots`$ となる列 $`(x_n)_{n \in \mathbb N}`$ を **無限降下列** と呼ぶ。

全順序が整列順序であることと、無限降下列が無いことは同値である。「無限降下列が無いなら整列順序」の向きには、選択公理の弱い形（従属選択）を使う。

| 順序 | 整列か | 理由 |
|---|---|---|
| $`(\mathbb N, \lt)`$ | はい | 空でない部分集合は最小元を持つ |
| $`(\mathbb Z, \lt)`$ | いいえ | $`0 \gt -1 \gt -2 \gt \cdots`$ |
| $`(\mathbb Q_{\ge 0}, \lt)`$ | いいえ | $`1 \gt 1/2 \gt 1/4 \gt \cdots`$ |

**定義（順序数）.** **順序数** は整列順序の型である。順序数 $`\alpha`$ は、それより小さい順序数の集合 $`\{\beta \mid \beta \lt \alpha\}`$ と同一視する。

小さい順に並べると次のようになる。

```math
0,\ 1,\ 2,\ \ldots,\ \omega,\ \omega+1,\ \omega+2,\ \ldots,\ \omega \cdot 2,\ \ldots,\ \omega^2,\ \ldots
```

- $`\omega`$ は自然数全体の型である。$`\omega = \{0, 1, 2, \ldots\}`$。
- 順序数の全体は $`\lt`$ で整列する。空でない順序数の集まりには、どれも最小元がある。
- 順序数の全体を $`\mathrm{Ord}`$ と書く。

## 2. 後者と極限

**定義（後者）.** $`\alpha + 1`$ は $`\alpha`$ の次の順序数である。$`\alpha + 1`$ の形の順序数を **後者順序数** と呼ぶ。

**定義（極限順序数）.** 0 でも後者順序数でもない順序数を **極限順序数** と呼ぶ。

| 順序数 | 種類 |
|---|---|
| $`0`$ | どちらでもない |
| $`5`$、$`\omega+1`$、$`\omega \cdot 2 + 3`$ | 後者 |
| $`\omega`$、$`\omega \cdot 2`$、$`\omega^2`$ | 極限 |

**性質.** $`\alpha`$ が極限順序数で $`\beta \lt \alpha`$ なら、$`\beta + 1 \lt \alpha`$ である。したがって $`\beta`$ より上に、$`\alpha`$ より下の元が無限個ある。

この性質は [03 構造と Σ₁ 初等部分構造](03-sigma1-elementary.md) の例で使う。

## 3. 上限

**定義（上限）.** 順序数の集合 $`S`$ の **上限** $`\sup S`$ は、$`S`$ のすべての元以上である最小の順序数である。

- $`S`$ が最大元を持てば、$`\sup S`$ はその最大元である。空でない有限集合ならいつもそうである。空集合の上限は $`0`$ である。
- $`S`$ が最大元を持たなければ、$`\sup S`$ は $`S`$ に入らない。

| $`S`$ | $`\sup S`$ |
|---|---|
| $`\{2, 5, 3\}`$ | $`5`$ |
| $`\{0, 1, 2, \ldots\}`$ | $`\omega`$ |
| $`\{\omega, \omega+1, \omega+2, \ldots\}`$ | $`\omega \cdot 2`$ |

「すべての元より真に大きい」数が欲しいときは、$`\sup_{i} (y_i + 1)`$ を使う。$`y_i \lt y_i + 1 \le \sup_i (y_i + 1)`$ だからである。[08 ω₁ より下の閉包と鎖](08-closure-chain.md) で定義する「証人の高さ」はこの形である。

## 4. 可算と ω₁

**定義（可算）.** 集合 $`X`$ が **可算** であるとは、$`X`$ が空であるか、全射 $`\mathbb N \to X`$ があることをいう。

**定義（可算順序数）.** 順序数 $`\alpha`$ が **可算** であるとは、$`\{\beta \mid \beta \lt \alpha\}`$ が可算であることをいう。

$`0, 1, \omega, \omega+1, \omega \cdot 2, \omega^2, \omega^\omega, \varepsilon_0`$ はどれも可算である。

**定義（ω₁）.** $`\omega_1`$ は最初の非可算順序数である。つまり、$`\omega_1`$ より小さい順序数はちょうど可算順序数である。

```math
\alpha \lt \omega_1 \iff \alpha \text{ は可算}
```

次の 3 つを使う。

- $`0 \lt \omega_1`$。
- $`\alpha \lt \omega_1 \implies \alpha + 1 \lt \omega_1`$。
- $`\gamma \lt \omega_1 \implies \{\beta \mid \beta \lt \gamma\}`$ は可算。

2 つめの理由：$`\{\beta \mid \beta \lt \alpha + 1\} = \{\beta \mid \beta \lt \alpha\} \cup \{\alpha\}`$ で、可算集合に 1 点を足しても可算である。言いかえると、$`\omega_1`$ は極限順序数である。

## 5. ω₁ の正則性

**定理（ω₁ の正則性）.** 各 $`n \in \mathbb N`$ について $`\alpha_n \lt \omega_1`$ なら、次が成り立つ。

```math
\sup_{n \in \mathbb N} \alpha_n \lt \omega_1
```

添字の集合は $`\mathbb N`$ でなくても、可算ならよい。

**証明.** $`\sigma := \sup_n \alpha_n`$ と置く。$`\beta \lt \sigma`$ なら、ある $`n`$ で $`\beta \lt \alpha_n`$ である。よって

```math
\{\beta \mid \beta \lt \sigma\} = \bigcup_{n} \{\beta \mid \beta \lt \alpha_n\}
```

である。右辺は可算集合の可算個の和である。$`\alpha_n = 0`$ の項は和に何も足さないので除く。残りの各 $`n`$ で全射 $`e_n : \mathbb N \to \alpha_n`$ を 1 つずつ選ぶと、$`(n, t) \mapsto e_n(t)`$ は $`\mathbb N \times \mathbb N`$ から和の上への全射になる。$`\mathbb N \times \mathbb N`$ は可算なので、和も可算である。よって $`\sigma`$ は可算で、$`\sigma \lt \omega_1`$ である。$`\square`$

- 全射 $`e_n`$ を可算個同時に選ぶところで、選択公理（可算選択）を使う。
- 添字が非可算なら成り立たない。例えば $`\sup_{\alpha \lt \omega_1} \alpha = \omega_1`$ である。

## 6. 可算順序数の数え上げ

$`0 \lt \gamma \lt \omega_1`$ なら、$`\{\beta \mid \beta \lt \gamma\}`$ は空でなく可算なので、全射 $`e_\gamma : \mathbb N \to \gamma`$ がある。選択公理でそれを 1 つ選び、$`e_\gamma`$ と書く。$`\gamma = 0`$ のときは全射が無いので、$`e_0`$ を値がいつも $`0`$ の関数 $`\mathbb N \to \mathrm{Ord}`$ とする。

**定理（数え上げ）.** $`\gamma \lt \omega_1`$ かつ $`a \lt \gamma`$ なら、ある $`t \in \mathbb N`$ で $`e_\gamma(t) = a`$ である。

これを使うと、$`\gamma`$ より下の有限個の順序数を、自然数の有限列で表せる。この順序数は、あとで論理式のパラメータ（[03](03-sigma1-elementary.md) §2 で定義する）として使うので、ここでもパラメータと呼ぶ。

**定義（パラメータの符号）.** 自然数の列 $`l = (l_0, l_1, \ldots)`$ に対し、$`\mathrm{params}_\gamma(l)(i) := e_\gamma(l_i)`$ とする（列の外は $`l_i := 0`$ と読む）。

**定理（符号の存在）.** $`\gamma \lt \omega_1`$、$`k \in \mathbb N`$ で、$`p_0, \ldots, p_{k-1} \lt \gamma`$ なら、ある自然数の列 $`l`$ で、すべての $`i \lt k`$ について $`\mathrm{params}_\gamma(l)(i) = p_i`$ である。

**例.** $`\gamma = \omega + 1`$ とし、$`e_\gamma(0) = \omega`$、$`e_\gamma(t+1) = t`$ という数え上げが選ばれたとする。パラメータ $`(3, \omega, 0)`$ は $`l = (4, 0, 1)`$ で表される。

**なぜ要るか.** [08 ω₁ より下の閉包と鎖](08-closure-chain.md) では、$`\gamma`$ より下のパラメータを持つすべての論理式（[03](03-sigma1-elementary.md) §2 で定義する）について上限を取る。パラメータを順序数の組のまま走らせる代わりに、自然数の列 $`l`$ を走らせる。すると添字の集合は「論理式と自然数の有限列の組」の全体になる。この集合は $`\gamma`$ に依らず、可算である（[08](08-closure-chain.md)）。よって §5 の定理をそのまま使える。

## 7. このリポジトリでの使われ方

| 場所 | 使い方 |
|---|---|
| [README](../README.md)「関係 R」 | 列に付ける値（ラベル）は順序数で、順序は $`\lt`$ |
| [README](../README.md)「ラベルの約束の行き先」 | 順序数の順序 $`\lt`$ が整列順序であること（§1） |
| [notes/01-design.md](../notes/01-design.md) §3.6、§4.6 | $`\omega_1`$、数え上げ $`e_\gamma`$、閉包点（[08](08-closure-chain.md)）が $`\omega_1`$ より下にあること（§5 の正則性） |
