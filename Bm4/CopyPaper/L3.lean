/-
Copied from koteitan, bms-elem-pattern, `lean/Bm4/CopyPaper/L3.lean`
(https://github.com/koteitan/bms-elem-pattern, CC BY-SA 4.0), which takes it from koteitan,
dh-bms-wf-formal (https://github.com/koteitan/dh-bms-wf-formal). Changes: ported to Lean 4.33.1 (no other change).
-/
/-
  Lemma 6.5 of the paper (local proof II): the third claim of Theorem 6.3 for a row `k < m₀`,
  assuming only `(C1)_k` and, when `k = k'+1`, the claim `(C3)_{k'}` of the previous row.

  The argument is the paper's own (§6.4).  Fix `q ≥ 1` and compare the two intervals

      I_q = B_{q-1} ⌢ (P⁽�q⁾)      and      I_0 = B₀ ⌢ (C),

  i.e. in position language the positions `≥ pos (q-1) 0` with target `pos q 0`, and the
  positions `≥ p` with target `c = A.len - 1`.

  1. Candidates correspond: for `i < s`, `pos (q-1) i` is a structural `k`-candidate of
     `pos q 0` iff `p + i` is one of `c`.  For `k = 0` both sides hold outright; for
     `k = k'+1` both sides are `≺_{k'}`, which is `(C3)_{k'}`.
  2. Validity corresponds: a structural `k`-candidate `D_i` of `C` ascends in row `k`
     (Lemma 4.1, via `asc_of_cand_c`), so its entry in `B_{q-1}` is `D_i(k) + (q-1)Δ_k`,
     while `P⁽�q⁾(k) = P(k) + qΔ_k = C(k) + (q-1)Δ_k`.  The two `<` comparisons agree.
  3. Direct parents therefore correspond (both are "the largest valid candidate in the
     interval", and the positions strictly inside the two intervals correspond by
     `between_prev_copy`), and ancestors follow by taking the last step of the chain and
     transporting the remaining, copy-internal part with `(C1)_k`.

  This file uses only the setup of `Bm4/Copy.lean` (structure, positions, entries, ascension)
  together with Lemma 2.2 and Lemma 4.1; it uses none of the closed forms.
-/
import Bm4.CopyPaper.Interval

open Classical

namespace BM4

variable {r : ℕ} {A : Arr r}

namespace BadRoot

variable (b : BadRoot A)

private theorem addLtR {x y d : ℕ} : x + d < y + d ↔ x < y := by omega

private theorem addLeR {x y d : ℕ} : x + d ≤ y + d ↔ x ≤ y := by omega

/-! ### Entries in the two intervals

Both intervals differ by the same shift `(q-1) * Δ k`, on the columns that matter. -/

/-- A structural `k`-candidate of `C` ascends (`k < m₀`), so its entry in copy `q` is the
entry in the bad part shifted by `q * Δ k`. -/
theorem col_asc_eq {k q i : ℕ} (hk : k < b.m) (hi : i < b.s)
    (hc : cand A k (b.p + i) (A.len - 1)) :
    b.tA.col (b.pos q i) k = A.col (b.p + i) k + q * b.Δ k :=
  b.col_pos_asc hi (b.asc_of_cand_c hk hc)

/-- The leading column of copy `q` (`q ≥ 1`, `k < m₀`) carries the entry of `C` shifted by
`(q-1) * Δ k`. -/
theorem col_lead_eq {k q : ℕ} (hk : k < b.m) (hq : 0 < q) :
    b.tA.col (b.pos q 0) k = A.col (A.len - 1) k + (q - 1) * b.Δ k := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  rw [b.col_pos_asc b.s_pos (b.asc_zero hk)]
  have h1 := b.val_p_add_Δ hk.le
  simp only [Nat.add_zero, Nat.add_sub_cancel]
  have h2 : A.col b.p k + (q' + 1) * b.Δ k = (A.col b.p k + b.Δ k) + q' * b.Δ k := by ring
  rw [h2, h1]

/-! ### Step 1: candidates correspond -/

/-- Structural candidates in the two intervals correspond.  For row `0` both sides hold; for
row `k'+1` both sides are `k'`-ancestry, i.e. exactly `(C3)_{k'}`. -/
theorem cand_bridge {k q i : ℕ} (h3 : ∀ k', k = k' + 1 → b.Claim3 k') (hqN : q ≤ b.N)
    (hq : 0 < q) (hi : i < b.s) :
    cand b.tA k (b.pos (q - 1) i) (b.pos q 0) ↔ cand A k (b.p + i) (A.len - 1) := by
  cases k with
  | zero =>
    simp only [cand_zero]
    exact ⟨fun _ => b.lt_c_of_lt_s hi, fun _ => b.pos_lt_pos_of_lt (by omega) hi⟩
  | succ k' => exact h3 k' rfl q hqN i hq hi

/-- **(6.5)** in the paper's own notation.  The two consecutive intervals of this local proof
are `I_q = B_{q-1} ⌢ P⁽ᑫ⁾ = [pos (q-1) 0, pos q 0 + 1)` and `I₀ = B₀ ⌢ (C) = [p, len)`, and
step 1 says that their internal **structural** candidates (Definition 6.1's `Candᴵₖ`, validity
not required) correspond index-wise:
`D_i⁽ᑫ⁻¹⁾ ∈ Cand_k^{I_q}(P⁽ᑫ⁾) ⟺ D_i⁽⁰⁾ ∈ Cand_k^{I₀}(C)`. -/
theorem intCand_bridge {k q i : ℕ} (h3 : ∀ k', k = k' + 1 → b.Claim3 k') (hqN : q ≤ b.N)
    (hq : 0 < q) (hi : i < b.s) :
    IntCand b.tA (b.pos (q - 1) 0) (b.pos q 0 + 1) k (b.pos (q - 1) i) (b.pos q 0) ↔
      IntCand A b.p A.len k (b.p + i) (A.len - 1) := by
  have hmemT : b.pos (q - 1) 0 ≤ b.pos (q - 1) i := by simp only [BadRoot.pos]; omega
  have hc := b.cand_bridge h3 hqN hq hi
  constructor
  · exact fun h => ⟨Nat.le_add_right _ _, by have := b.lt_c_of_lt_s hi; omega, hc.mp h.2.2⟩
  · exact fun h =>
      ⟨hmemT, by have := cand_lt (hc.mpr h.2.2); omega, hc.mpr h.2.2⟩

/-! ### Step 2 and 3: direct parents correspond -/

/-- The bridge for direct parents: `D_i⁽�q⁻¹⁾` is the `k`-parent of `P⁽�q⁾` iff `D_i` is the
`k`-parent of `C`.  Both say "the largest valid structural candidate in the interval", and
the interiors of the two intervals correspond index-wise. -/
theorem parent_bridge {k q i : ℕ} (hk : k < b.m) (h3 : ∀ k', k = k' + 1 → b.Claim3 k')
    (hqN : q ≤ b.N) (hq : 0 < q) (hi : i < b.s) :
    parent b.tA k (b.pos (q - 1) i) (b.pos q 0) ↔ parent A k (b.p + i) (A.len - 1) := by
  constructor
  · -- (⇒)
    intro hp
    have hkr : k < r := hk.trans (parent_row_lt b.hpar)
    have hcl : A.len - 1 < A.len := parent_target_lt b.hpar
    have hcA : cand A k (b.p + i) (A.len - 1) := (b.cand_bridge h3 hqN hq hi).mp (parent_cand hp)
    have hval := parent_val_lt hp
    rw [b.col_asc_eq hk hi hcA, b.col_lead_eq hk hq] at hval
    refine ⟨b.lt_c_of_lt_s hi, hcA, addLtR.mp hval, ?_, hkr, hcl⟩
    intro y hy1 hy2 hcy
    obtain ⟨i', rfl⟩ : ∃ i', y = b.p + i' := ⟨y - b.p, by omega⟩
    have hi's : i' < b.s := b.lt_s_of_lt_c hy2
    have hii' : i < i' := by omega
    have hcy' : cand b.tA k (b.pos (q - 1) i') (b.pos q 0) :=
      (b.cand_bridge h3 hqN hq hi's).mpr hcy
    have hkey := parent_max hp (b.pos_lt_pos_same hii')
      (b.pos_lt_pos_of_lt (by omega) hi's) hcy'
    rw [b.col_asc_eq hk hi's hcy, b.col_lead_eq hk hq] at hkey
    exact addLeR.mp hkey
  · -- (⇐)
    intro hp
    have hcA : cand A k (b.p + i) (A.len - 1) := parent_cand hp
    have hkr : k < r := hk.trans (parent_row_lt b.hpar)
    refine ⟨b.pos_lt_pos_of_lt (by omega) hi, (b.cand_bridge h3 hqN hq hi).mpr hcA, ?_, ?_,
      hkr, b.pos_lt_tA_len hqN b.s_pos⟩
    · rw [b.col_asc_eq hk hi hcA, b.col_lead_eq hk hq]
      exact addLtR.mpr (parent_val_lt hp)
    · intro y hy1 hy2 hcy
      obtain ⟨i', rfl, hii', hi's⟩ := b.between_prev_copy hq hy1 hy2
      have hcA' : cand A k (b.p + i') (A.len - 1) := (b.cand_bridge h3 hqN hq hi's).mp hcy
      have hkey : A.col (A.len - 1) k ≤ A.col (b.p + i') k :=
        parent_max hp (by omega) (b.lt_c_of_lt_s hi's) hcA'
      rw [b.col_asc_eq hk hi's hcA', b.col_lead_eq hk hq]
      exact addLeR.mpr hkey

/-! ### Iterating parents -/

/-- The bridge for ancestors.  Take the last step of the chain: it is a direct parent of the
target inside the interval, handled by `parent_bridge`; what remains lies inside one copy
(resp. inside the bad part) and is transported by `(C1)_k`. -/
theorem anc_bridge {k q i : ℕ} (hk : k < b.m) (h1 : b.Claim1 k)
    (h3 : ∀ k', k = k' + 1 → b.Claim3 k') (hqN : q ≤ b.N) (hq : 0 < q) (hi : i < b.s) :
    anc b.tA k (b.pos (q - 1) i) (b.pos q 0) ↔ anc A k (b.p + i) (A.len - 1) := by
  constructor
  · intro h
    obtain ⟨u, hu, hup⟩ := anc_last_step h
    rcases hu with rfl | hu
    · exact anc_of_parent ((b.parent_bridge hk h3 hqN hq hi).mp hup)
    · obtain ⟨i', rfl, hii', hi's⟩ := b.between_prev_copy hq (anc_lt hu) (parent_lt hup)
      have hA : anc A k (b.p + i) (b.p + i') := (h1 (q - 1) (by omega) i i' hi hi's).mp hu
      exact anc_of_anc_of_parent hA ((b.parent_bridge hk h3 hqN hq hi's).mp hup)
  · intro h
    obtain ⟨u, hu, hup⟩ := anc_last_step h
    rcases hu with rfl | hu
    · exact anc_of_parent ((b.parent_bridge hk h3 hqN hq hi).mpr hup)
    · have hlt1 : b.p + i < u := anc_lt hu
      have hlt2 : u < A.len - 1 := parent_lt hup
      obtain ⟨i', rfl⟩ : ∃ i', u = b.p + i' := ⟨u - b.p, by omega⟩
      have hi's : i' < b.s := b.lt_s_of_lt_c hlt2
      have hT : anc b.tA k (b.pos (q - 1) i) (b.pos (q - 1) i') :=
        (h1 (q - 1) (by omega) i i' hi hi's).mpr hu
      exact anc_of_anc_of_parent hT ((b.parent_bridge hk h3 hqN hq hi's).mpr hup)

/-- **Lemma 6.5** (local proof II): for `k < m₀`, `(C3)_k` follows from `(C1)_k` and, when
`k > 0`, `(C3)_{k-1}`. -/
theorem lemma_6_5 {k : ℕ} (hk : k < b.m) (h1 : b.Claim1 k)
    (h3 : ∀ k', k = k' + 1 → b.Claim3 k') : b.Claim3 k := by
  intro q hqN i hq hi
  exact b.anc_bridge hk h1 h3 hqN hq hi

end BadRoot

end BM4
