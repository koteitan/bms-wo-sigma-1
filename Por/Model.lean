import Por.Reflection
import Por.Chain
import Bm4.Label

/-!
# The model is a label system

This file packs the relation `R` into the label interface `BM4.LabelSystem r` of the
BMS layer: labels are the ordinals, `rel = R`.

  * `R` is strict (`R_lt`) and transitive (`R_trans`);
  * finite reflection holds (`reflect`).

It also proves that every array carries a stable label (`stable_all`): the chain
`cC` labels every column, since any two of its members are related at every layer.
-/

open Classical Cardinal Ordinal

namespace Por

/-- The label system of `r` rows. -/
noncomputable def labelSystem (r : ℕ) : BM4.LabelSystem.{1} r where
  Lab := Ord
  rel := R
  rel_lt := R_lt
  rel_trans := R_trans
  reflect := fun n α β hn h X hX s y hs hy hyα hyβ => reflect r n α β hn h X hX s y hs hy hyα hyβ

/-- Every array carries a stable label: the chain `cC`. -/
theorem stable_all {r : ℕ} (A : BM4.Arr r) : BM4.Stable (labelSystem r) A cC :=
  ⟨fun _ _ hij _ => cC_strictMono hij, fun k _ _ _ _ h => chain_R (BM4.anc_lt h) k⟩

end Por
