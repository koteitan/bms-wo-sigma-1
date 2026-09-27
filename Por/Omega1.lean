/-
Adapted from koteitan, bms-elem-pattern, `lean/Pattern/Chain.lean`
(https://github.com/koteitan/bms-elem-pattern, CC BY-SA 4.0), through `Por/Omega1.lean` of
koteitan, 1y-wo-por (https://github.com/koteitan/1y-wo-por). Changes: ported to Lean 4.33.1.
-/
import Por.Tuple

/-!
# ω₁ and enumerations of countable ordinals

This file defines `Om := ω₁`. It proves that `ω₁` is positive and closed under
successor, and that the ordinals below a countable `γ` are countable. It then
enumerates them (`enumBelow`), so that every finite list of parameters below `γ`
is coded by a list of natural numbers (`exists_params`).
-/

open Classical Cardinal Ordinal

namespace Por

noncomputable abbrev Om : Ord := ω₁

theorem om_pos : (0 : Ord) < Om := Ordinal.omega_pos 1

theorem om_succ_lt {a : Ord} (h : a < Om) : Order.succ a < Om := by
  have hl : Order.IsSuccLimit (ω₁ : Ord) := by
    rw [← Cardinal.ord_aleph]
    exact Cardinal.isSuccLimit_ord (by simp)
  exact hl.succ_lt h

theorem countable_Iio {γ : Ord} (h : γ < Om) : (Set.Iio γ).Countable := by
  rw [← Cardinal.le_aleph0_iff_set_countable, Cardinal.mk_Iio_ordinal, Cardinal.lift_le_aleph0]
  rw [Om, ← Cardinal.ord_aleph, Cardinal.lt_ord, Cardinal.lt_aleph_one_iff] at h
  exact h

/-- An enumeration of the ordinals below `γ` (onto when `0 < γ < ω₁`). -/
noncomputable def enumBelow (γ : Ord) : ℕ → Ord :=
  if h : (Set.Iio γ).Countable ∧ (Set.Iio γ).Nonempty then
    Classical.choose (h.1.exists_eq_range h.2)
  else fun _ => 0

theorem enumBelow_surj {γ : Ord} (hγ : γ < Om) {a : Ord} (ha : a < γ) :
    ∃ t, enumBelow γ t = a := by
  have h : (Set.Iio γ).Countable ∧ (Set.Iio γ).Nonempty := ⟨countable_Iio hγ, ⟨a, ha⟩⟩
  have hs := Classical.choose_spec (h.1.exists_eq_range h.2)
  have hmem : a ∈ Set.Iio γ := ha
  rw [hs] at hmem
  obtain ⟨t, ht⟩ := hmem
  exact ⟨t, by simp only [enumBelow, dif_pos h]; exact ht⟩

/-- Parameters below `γ`, coded by a list of indices. -/
noncomputable def params (γ : Ord) (l : List ℕ) : ℕ → Ord :=
  fun i => enumBelow γ (l.getD i 0)

theorem exists_params {γ : Ord} (hγ : γ < Om) {k : ℕ} {p : ℕ → Ord}
    (hp : ∀ i < k, p i < γ) : ∃ l : List ℕ, ∀ i < k, params γ l i = p i := by
  choose t ht using fun i (hi : i < k) => enumBelow_surj hγ (hp i hi)
  refine ⟨(List.range k).map fun i => if h : i < k then t i h else 0, fun i hi => ?_⟩
  unfold params
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp [hi, ht]

end Por
