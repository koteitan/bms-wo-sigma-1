[← Back](README.md) | [English](en/08-closure-chain.md) | [Japanese](08-closure-chain.md)

# ω₁ より下の閉包と鎖

前提

| ノート | ここで使う言葉 |
|---|---|
| [01 順序数と ω₁](01-ordinals.md) | $`\omega_1`$、正則性、数え上げ $`e_\gamma`$、パラメータの符号 $`\mathrm{params}_\gamma`$ |
| [03 構造と Σ₁ 初等部分構造](03-sigma1-elementary.md) | 証人、Tarski–Vaught 判定法、$`\Sigma_1`$ 論理式の 5 つ組と行列、完全な原子図式（§7）、見えるビット（§8） |
| [07 関係 R](07-relation-r.md) | $`R`$、層、記号 $`\mathrm{Rel}_j`$、$`\mathrm{Top}_j`$ とその真の解釈 |

このノートは、$`\omega_1`$ より下に「$`\Sigma_1`$ の証人で閉じた点」を作る方法を説明する。これは Löwenheim–Skolem の定理と同じ考え方で、証人を足して上限を取る。できた点を並べた鎖が、[09](09-obligations.md) でラベルになる。

## 1. 周りの構造と Good

**定義（周りの構造）.** すべての記号を持つ高さ $`\omega_1`$ の構造を $`\mathfrak B`$ とする。

```math
\mathfrak B = \bigl(\omega_1;\ \lt,\ (\mathrm{Rel}_j)_{j \in \mathbb N},\ (\mathrm{Top}^{\omega_1}_j)_{j \in \mathbb N}\bigr), \qquad \mathrm{Top}^{\omega_1}_j(x) :\iff R(j, x, \omega_1)
```

上端述語はすべての層で持つ。すべてのビットが見える（[03](03-sigma1-elementary.md) §8）。

**定義（Good）.** 順序数 $`\gamma \le \omega_1`$ について、$`\mathfrak B{\restriction}\gamma`$ を、$`\mathfrak B`$ の領域を $`\{x \mid x \lt \gamma\}`$ に制限したものとする。上端述語は $`\omega_1`$ へのもののままである。

```math
\mathrm{Good}(\gamma) :\iff \mathfrak B{\restriction}\gamma \preccurlyeq_{\Sigma_1} \mathfrak B
```

つまり、$`\vec p \lt \gamma`$ のすべての $`\Sigma_1`$ 論理式 $`\varphi`$ で、$`\mathfrak B{\restriction}\gamma \models \varphi(\vec p) \iff \mathfrak B \models \varphi(\vec p)`$ である。

$`\mathfrak B{\restriction}\gamma`$ は $`\mathfrak B`$ の本当の部分構造である（解釈が同じで、領域だけが違う）。だから [03](03-sigma1-elementary.md) §6 の Tarski–Vaught 判定法がそのまま使える。

## 2. 論理式は可算個

**定義（論理式の集合）.** [03](03-sigma1-elementary.md) §7 の 5 つ組 $`(m, n, D, \mathit{bb}, \mathit{np})`$ 全体の集合を $`\mathcal F`$ とする。$`D`$ は、$`m, n`$ で決まる完全な原子図式の集合の部分集合である。

**可算である理由.** $`m, n`$ を決めると、完全な原子図式は有限個しかない（[03](03-sigma1-elementary.md) §3、§7）。その部分集合 $`D`$ も有限個しかない。$`m, n, \mathit{bb}, \mathit{np}`$ は自然数である。よって $`\mathcal F`$ は可算である。自然数の有限列の集合 $`\mathbb N^{\lt\omega}`$ も可算なので、$`\mathcal F \times \mathbb N^{\lt\omega}`$ も可算である。

1 つの論理式が使う記号を有限個（上限 $`m`$）にしたのはこのためである。無限個の記号を使える論理式を許すと、論理式の全体が可算にならない。

## 3. 証人の高さ

**定義（証人の高さ）.** 論理式 $`\varphi = (m, n, D, \mathit{bb}, \mathit{np}) \in \mathcal F`$ と、$`\omega_1`$ より下のパラメータの列 $`\vec p`$ について（$`\varphi`$ は最初の $`\mathit{np}`$ 個 $`p_0, \ldots, p_{\mathit{np}-1}`$ を読む）：

- $`\mathfrak B \models \varphi(\vec p)`$ なら、証人 $`y_0, \ldots, y_{\mathit{bb}-1} \lt \omega_1`$ を選択公理で 1 組選び、$`h(\varphi, \vec p) := \sup_{i \lt \mathit{bb}} (y_i + 1)`$ とする。
- そうでなければ $`h(\varphi, \vec p) := 0`$ とする。

**定理（証人の高さは ω₁ より下）.** $`h(\varphi, \vec p) \lt \omega_1`$。

**証明.** 有限個の $`y_i + 1`$ の最大値で、どれも $`\omega_1`$ より下である（[01](01-ordinals.md) §4）。$`\square`$

選んだ証人はどれも $`h(\varphi, \vec p)`$ より下にある。

## 4. 閉包の 1 ステップ

**定義（閉包の 1 ステップ）.**

```math
\mathrm{next}(\gamma) := \max\Bigl(\gamma,\ \sup_{(\varphi, l)} h\bigl(\varphi, \mathrm{params}_\gamma(l)\bigr)\Bigr) + 1
```

上限は $`(\varphi, l) \in \mathcal F \times \mathbb N^{\lt\omega}`$ の全体を動く。$`\mathrm{params}_\gamma(l)`$ は [01](01-ordinals.md) §6 の、自然数の列で表したパラメータである。

| 性質 | 内容 | 理由 |
|---|---|---|
| 性質 1 | $`\gamma \lt \mathrm{next}(\gamma)`$ | $`+1`$ |
| 性質 2 | $`\gamma \lt \omega_1 \implies \mathrm{next}(\gamma) \lt \omega_1`$ | 可算個の上限（[01](01-ordinals.md) §5） |
| 性質 3 | $`\gamma \lt \omega_1`$、$`\vec p \lt \gamma`$、$`\mathfrak B \models \varphi(\vec p)`$ なら、証人を $`\mathrm{next}(\gamma)`$ より下に取れる | 下の証明 |

**性質 3 の証明.** [01](01-ordinals.md) §6 の定理（符号の存在）から、$`\vec p = \mathrm{params}_\gamma(l)`$ となる列 $`l`$ がある。$`(\varphi, l)`$ について選んだ証人は、$`h(\varphi, \mathrm{params}_\gamma(l))`$ より下にある。これは上限の項の 1 つなので、$`\mathrm{next}(\gamma)`$ より下である。$`\square`$

## 5. λ

**定義（λ）.**

```math
\mathrm{next}^0(\gamma) := \gamma, \quad \mathrm{next}^{t+1}(\gamma) := \mathrm{next}\bigl(\mathrm{next}^t(\gamma)\bigr), \qquad \lambda(\gamma) := \sup_{t \in \mathbb N} \mathrm{next}^t(\gamma)
```

$`t \in \mathbb N`$ である。$`\lambda(\gamma)`$ の形の順序数を **閉包点** と呼ぶ。

| 性質 | 内容 |
|---|---|
| 性質 4 | $`\gamma \lt \omega_1 \implies \mathrm{next}^t(\gamma) \lt \omega_1`$ |
| 性質 5 | $`t \le t' \implies \mathrm{next}^t(\gamma) \le \mathrm{next}^{t'}(\gamma)`$ |
| 性質 6 | $`\gamma \lt \omega_1 \implies \lambda(\gamma) \lt \omega_1`$（可算個の上限） |
| 性質 7 | $`\gamma \lt \lambda(\gamma)`$ |
| 性質 8 | $`k \in \mathbb N`$、$`p_0, \ldots, p_{k-1} \lt \lambda(\gamma)`$ なら、ある $`t`$ で全部 $`\lt \mathrm{next}^t(\gamma)`$ |

性質 8 は $`k`$ についての帰納法で示す。各 $`p_i`$ は上限より小さいので、ある $`t_i`$ で $`p_i \lt \mathrm{next}^{t_i}(\gamma)`$ である。$`t := \max_i t_i`$ を取る。

## 6. λ(γ) は Good

**定理（λ(γ) は Good）.** $`\gamma \lt \omega_1`$ なら $`\mathrm{Good}(\lambda(\gamma))`$。

**証明.** Tarski–Vaught 判定法（[03](03-sigma1-elementary.md) §6）の形で示す。$`\vec p \lt \lambda(\gamma)`$ とする。

- $`\Rightarrow`$：$`\lambda(\gamma)`$ より下の証人は、$`\omega_1`$ より下の証人でもある（性質 6）。行列の評価は同じである。
- $`\Leftarrow`$：性質 8 から、ある $`t`$ で $`\vec p \lt \mathrm{next}^t(\gamma)`$ である。性質 3 を $`\mathrm{next}^t(\gamma)`$ で使うと、証人は $`\mathrm{next}^{t+1}(\gamma) \le \lambda(\gamma)`$ より下に取れる。$`\square`$

**例（形だけ）.** $`\gamma = 0`$ とする。$`\lambda(0)`$ は、「$`\mathfrak B`$ で真の $`\Sigma_1`$ の主張で、パラメータが $`\lambda(0)`$ より下のもの」の証人をすべて含む。$`\lambda(0)`$ の具体的な値は分からない。証明は値を使わず、$`\lambda(0) \lt \omega_1`$ と $`\mathrm{Good}(\lambda(0))`$ だけを使う。

**Good な点の集合について.** Good な点の集合が $`\omega_1`$ の中で閉じていることは示していないし、使わない。そのため club（閉非有界集合）とは呼ばない。

## 7. 鎖

**定義（鎖）.**

```math
c_0 := \lambda(0), \qquad c_{t+1} := \lambda(c_t)
```

| 性質 | 内容 |
|---|---|
| 性質 9 | $`c_t \lt \omega_1`$ |
| 性質 10 | $`c_0 \lt c_1 \lt c_2 \lt \cdots`$ |
| 性質 11 | $`\mathrm{Good}(c_t)`$ |

どれも §5、§6 から $`t`$ についての帰納法で出る。

この鎖の 2 点は、すべての層で $`R`$ の関係にある。つまり $`i \lt j`$ なら、すべての $`k`$ で $`R(k, c_i, c_j)`$ である。その証明には、Good な点 $`\alpha \lt \omega_1`$ で上端述語が $`\omega_1`$ の上端述語と一致すること（$`x \lt \alpha`$ なら $`R(j, x, \alpha) \iff R(j, x, \omega_1)`$）が要る。この一致は層 $`j`$ についての帰納法で示す。どちらも [09](09-obligations.md) で説明する。

## 8. このリポジトリでの使われ方

| 場所 | 使い方 |
|---|---|
| [README](../README.md)「ラベルの約束の行き先」 | すべての配列のラベルは、$`\omega_1`$ より下の閉包点の鎖で作る |
| [notes/01-design.md](../notes/01-design.md) §3.6、§4.6 | 周りの構造、Good、next、λ、鎖、λ(γ) が Good であることの証明 |
