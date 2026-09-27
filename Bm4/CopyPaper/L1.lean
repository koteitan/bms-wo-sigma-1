/-
Copied from koteitan, bms-elem-pattern, `lean/Bm4/CopyPaper/L1.lean`
(https://github.com/koteitan/bms-elem-pattern, CC BY-SA 4.0), which takes it from koteitan,
dh-bms-wf-formal (https://github.com/koteitan/dh-bms-wf-formal). Changes: ported to Lean 4.33.1 (no other change).
-/
/-
  Lemma 6.4 of the paper (local proof I): the first claim of Theorem 6.3 for row `k`,
  assuming the same claim for all rows `h < k` and nothing else.

  The argument is the paper's own (§6.3): inside one copy `Bq`, the direct `k`-parent
  relation is index-wise the same as the direct `k`-parent relation of the bad part of `A`,
  because every position strictly between two positions of `Bq` is again a position of `Bq`
  and the entries of `Bq` are the entries of the bad part shifted by `q * Δ k` exactly on the
  ascending columns.  Ancestry is then iterated parenthood on both sides.

  This file uses only the setup of `Bm4/Copy.lean` (the structure, positions, entries,
  ascension) together with Lemma 2.2 and Lemma 4.1; it does not use the closed forms.
-/
import Bm4.CopyPaper.Interval

open Classical

namespace BM4

variable {r : ℕ} {A : Arr r}

namespace BadRoot

variable (b : BadRoot A)

private theorem addLtRight {x y d : ℕ} : x + d < y + d ↔ x < y := by omega

private theorem addLeRight {x y d : ℕ} : x + d ≤ y + d ↔ x ≤ y := by omega

/-! ### Entries inside one copy

Ascending columns only get larger, and the shift `q * Δ k` is the same for all of them. -/

/-- Ascension only adds: the `k`-entry of column `t` of `Bq` is at least the `k`-entry of
column `t` of the bad part. -/
theorem le_col_pos {q t k : ℕ} (ht : t < b.s) :
    A.col (b.p + t) k ≤ b.tA.col (b.pos q t) k := by
  rw [b.col_pos ht]
  split
  · exact Nat.le_add_right _ _
  · exact le_rfl

/-- `P ≼ₖ D_i` and `D_i ≺ₖ D_j` give `P ≼ₖ D_j`. -/
theorem asc_of_asc_of_anc {k i j : ℕ} (hi : b.Asc k i) (h : anc A k (b.p + i) (b.p + j)) :
    b.Asc k j :=
  ⟨hi.1, ancEq_trans hi.2 (Or.inr h)⟩

/-- Along a genuine `k`-ancestor edge of the bad part, the two columns of `Bq` are shifted by
the same amount, so the comparison of their `k`-entries is unchanged. -/
theorem col_lt_iff_of_anc {q i j k : ℕ} (hi : i < b.s) (hj : j < b.s)
    (h : anc A k (b.p + i) (b.p + j)) :
    b.tA.col (b.pos q i) k < b.tA.col (b.pos q j) k ↔ A.col (b.p + i) k < A.col (b.p + j) k := by
  by_cases hasc : b.Asc k j
  · have hasci : b.Asc k i := b.asc_of_cand hasc (cand_of_anc h)
    rw [b.col_pos_asc hi hasci, b.col_pos_asc hj hasc]
    exact addLtRight
  · have hasci : ¬ b.Asc k i := fun hc => hasc (b.asc_of_asc_of_anc hc h)
    rw [b.col_pos_not_asc hi hasci, b.col_pos_not_asc hj hasc]

/-- One half of the same comparison for a mere structural candidate: an invalid candidate of
the bad part stays invalid inside `Bq`. -/
theorem col_le_of_le_of_cand {q i j k : ℕ} (hi : i < b.s) (hj : j < b.s)
    (hc : cand A k (b.p + i) (b.p + j)) (hle : A.col (b.p + j) k ≤ A.col (b.p + i) k) :
    b.tA.col (b.pos q j) k ≤ b.tA.col (b.pos q i) k := by
  by_cases hasc : b.Asc k j
  · have hasci : b.Asc k i := b.asc_of_cand hasc hc
    rw [b.col_pos_asc hj hasc, b.col_pos_asc hi hasci]
    exact addLeRight.mpr hle
  · rw [b.col_pos_not_asc hj hasc]
    exact hle.trans (b.le_col_pos hi)

/-! ### The index-wise correspondence -/

/-- Structural candidates inside a copy: for row `0` both sides say `i < j`, and for row
`k + 1` both sides are `k`-ancestry, which is the previous claim. -/
theorem cand_copy_iff (k : ℕ) (ih : ∀ h, h < k → b.Claim1 h) {q i j : ℕ}
    (hq : q ≤ b.N) (hi : i < b.s) (hj : j < b.s) :
    cand b.tA k (b.pos q i) (b.pos q j) ↔ cand A k (b.p + i) (b.p + j) := by
  cases k with
  | zero =>
    simp only [cand_zero, b.pos_lt_pos_same_iff]
    omega
  | succ k =>
    have hc : b.Claim1 k := ih k (Nat.lt_succ_self k)
    exact hc q hq i j hi hj

/-- Direct parents inside one copy correspond index-wise to direct parents inside the bad
part of `A`. -/
theorem parent_copy_iff (k : ℕ) (ih : ∀ h, h < k → b.Claim1 h) {q i j : ℕ}
    (hq : q ≤ b.N) (hi : i < b.s) (hj : j < b.s) :
    parent b.tA k (b.pos q i) (b.pos q j) ↔ parent A k (b.p + i) (b.p + j) := by
  constructor
  · -- (⇒)
    intro hp
    have hij : i < j := b.pos_lt_pos_same_iff.mp (parent_lt hp)
    have hcand : cand A k (b.p + i) (b.p + j) :=
      (b.cand_copy_iff k ih hq hi hj).mp (parent_cand hp)
    have h3 := parent_val_lt hp
    have hval : A.col (b.p + i) k < A.col (b.p + j) k := by
      by_cases hasc : b.Asc k j
      · have hasci : b.Asc k i := b.asc_of_cand hasc hcand
        rw [b.col_pos_asc hi hasci, b.col_pos_asc hj hasc] at h3
        exact addLtRight.mp h3
      · rw [b.col_pos_not_asc hj hasc] at h3
        exact lt_of_le_of_lt (b.le_col_pos hi) h3
    refine ⟨by omega, hcand, hval, ?_, parent_row_lt hp,
      by have := b.lt_c_of_lt_s hj; omega⟩
    intro y hy1 hy2 hcy
    by_contra hcon
    -- an internal valid candidate would produce a direct parent inside the copy
    have hcon' : A.col y k < A.col (b.p + j) k := not_le.mp hcon
    obtain ⟨z, hz, hzge⟩ :=
      exists_parent_of_intECand (A := A) (lo := y) (hi := b.p + j + 1) (k := k) (j := y)
        (i := b.p + j)
        ⟨le_rfl, Nat.lt_succ_of_lt (cand_lt hcy), hcy, hcon', parent_row_lt hp,
          by have := b.lt_c_of_lt_s hj; omega⟩
    have hz1 : z < b.p + j := parent_lt hz
    have hz2 : b.p + i < z := lt_of_lt_of_le hy1 hzge
    obtain ⟨i2, rfl⟩ : ∃ i2, z = b.p + i2 := ⟨z - b.p, by omega⟩
    have hi2s : i2 < b.s := by omega
    have hcz : cand b.tA k (b.pos q i2) (b.pos q j) :=
      (b.cand_copy_iff k ih hq hi2s hj).mpr (parent_cand hz)
    have hlt : b.tA.col (b.pos q i2) k < b.tA.col (b.pos q j) k :=
      (b.col_lt_iff_of_anc hi2s hj (anc_of_parent hz)).mpr (parent_val_lt hz)
    have hmax := parent_max hp (b.pos_lt_pos_same (i := i) (j := i2) (by omega))
      (b.pos_lt_pos_same (i := i2) (j := j) (by omega)) hcz
    omega
  · -- (⇐)
    intro hp
    have hij : i < j := by have := parent_lt hp; omega
    have hcand : cand b.tA k (b.pos q i) (b.pos q j) :=
      (b.cand_copy_iff k ih hq hi hj).mpr (parent_cand hp)
    have hval : b.tA.col (b.pos q i) k < b.tA.col (b.pos q j) k :=
      (b.col_lt_iff_of_anc hi hj (anc_of_parent hp)).mpr (parent_val_lt hp)
    refine ⟨b.pos_lt_pos_same hij, hcand, hval, ?_, parent_row_lt hp,
      b.pos_lt_tA_len hq hj⟩
    intro y hy1 hy2 hcy
    obtain ⟨i2, rfl, hlt1, hlt2⟩ := b.between_same_copy hj hy1 hy2
    have hi2s : i2 < b.s := hlt2.trans hj
    have hcA : cand A k (b.p + i2) (b.p + j) := (b.cand_copy_iff k ih hq hi2s hj).mp hcy
    exact b.col_le_of_le_of_cand hi2s hj hcA
      (parent_max hp (j' := b.p + i2) (by omega) (by omega) hcA)

/-! ### Iterating parents -/

/-- Ancestry inside one copy is iterated internal parenthood, hence corresponds index-wise to
ancestry inside the bad part. -/
theorem anc_copy_iff (k : ℕ) (ih : ∀ h, h < k → b.Claim1 h) (q : ℕ) (hq : q ≤ b.N) :
    ∀ j, j < b.s → ∀ i, i < b.s →
      (anc b.tA k (b.pos q i) (b.pos q j) ↔ anc A k (b.p + i) (b.p + j)) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j IH =>
  intro hj i hi
  constructor
  · intro h
    obtain ⟨u, hu, hup⟩ := anc_last_step h
    rcases hu with rfl | hu
    · exact anc_of_parent ((b.parent_copy_iff k ih hq hi hj).mp hup)
    · obtain ⟨i2, rfl, hlt1, hlt2⟩ := b.between_same_copy hj (anc_lt hu) (parent_lt hup)
      have hi2s : i2 < b.s := hlt2.trans hj
      have h1 : anc A k (b.p + i) (b.p + i2) := (IH i2 hlt2 hi2s i hi).mp hu
      exact anc_of_anc_of_parent h1 ((b.parent_copy_iff k ih hq hi2s hj).mp hup)
  · intro h
    obtain ⟨u, hu, hup⟩ := anc_last_step h
    rcases hu with rfl | hu
    · exact anc_of_parent ((b.parent_copy_iff k ih hq hi hj).mpr hup)
    · have hlt1 : b.p + i < u := anc_lt hu
      have hlt2 : u < b.p + j := parent_lt hup
      obtain ⟨i2, rfl⟩ : ∃ i2, u = b.p + i2 := ⟨u - b.p, by omega⟩
      have hij2 : i2 < j := by omega
      have hi2s : i2 < b.s := hij2.trans hj
      have h1 : anc b.tA k (b.pos q i) (b.pos q i2) := (IH i2 hij2 hi2s i hi).mpr hu
      exact anc_of_anc_of_parent h1 ((b.parent_copy_iff k ih hq hi2s hj).mpr hup)

/-- **Lemma 6.4** (local proof I): the first claim of Theorem 6.3 for row `k` follows from the
same claim for all rows `h < k`, using none of the other five claims. -/
theorem lemma_6_4 (k : ℕ) (ih : ∀ h, h < k → b.Claim1 h) : b.Claim1 k := by
  intro q hq i j hi hj
  exact b.anc_copy_iff k ih q hq j hj i hi

end BadRoot

end BM4
