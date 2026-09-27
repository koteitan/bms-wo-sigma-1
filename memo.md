# MEMO — bms-wo-sigma-1

## 方針

BMS の停止性の証明は二層に分かれる。

- 組合せの層（`Bm4/`）。抽象的なラベルの約束 `BM4.LabelSystem r` だけを仮定して、
  展開で末尾のラベルが下がること（`BM4.descent`、DH の命題 19.1）を示す。
  koteitan/bms-elem-pattern の `lean/Bm4/` をそのまま使う。
- 意味の層（`Por/`）。約束を満たすラベルを与える。

bms-elem-pattern は、意味の層に Carlson の R_N（Σ_{j+1} 初等性、量化子のブロックが複数ある論理式）を使った。
このリポジトリは、1y-wo-por と同じく Σ₁ 初等性だけを使う。上端への関係を原子記号 Top_j として
言語に入れ、層 k の構造 𝔄^γ_k = (γ; <, (Rel_j)_j, (Top_j)_{j<k}) の Σ₁ 初等性で R_k を定義する。
BMS の約束には根の添字が要らないので、1y-wo-por の R(k, η, a, b) から η を外した R(k, a, b) になる。

## 守ること

- 検証は `leanman build -C <このリポジトリ> Bm4 Por`、`leanman check -C <このリポジトリ> Audit.lean`。
- 緑を確認してから commit し、すぐ push する。
- ライセンスの無いコード（YesMetaZFC など）は複製も翻案もしない。
