/-
Copied from koteitan, bms-elem-pattern, `lean/Bm4/CopyPaper/L2.lean`
(https://github.com/koteitan/bms-elem-pattern, CC BY-SA 4.0), which takes it from koteitan,
dh-bms-wf-formal (https://github.com/koteitan/dh-bms-wf-formal). Changes: ported to Lean 4.33.1 (no other change).
-/
/-
  Lemma 6.7 of the paper (local proof II): the second claim `Claim2 k` of Theorem 6.3 for row `k`,
  assuming `Claim2 h` for all rows `h < k`, `Claim1 k`, `Claim5 k` and, according to the row,
  `Claim3 k` (for `k < m₀`) or `Claim4` (for `k ≥ m₀`).

  The argument is the paper's own (§6.6).  Fix `E ∈ G`, `q` and `j < s`, and compare
  `E ≺ₖ D_j⁽ᑫ⁾` in the expanded array with `E ≺ₖ D_j` in `A`.

  * `q = 0`.  Then `D_j⁽⁰⁾ = D_j` lies in the common prefix `[0, c)`, so Lemma 3.1
    (`anc_tA_prefix`) already identifies the two relations.

  * `q > 0` and `D_j` ascends in row `k` (`Asc k j`, which forces `k < m₀`).  The bridge
    `Claim3 k` applied to the leading columns gives `P ≺ₖ P⁽¹⁾ ≺ₖ ⋯ ≺ₖ P⁽ᑫ⁾`, and `Claim1 k`
    transports the copy-internal tail `P ≼ₖ D_j` to `P⁽ᑫ⁾ ≼ₖ D_j⁽ᑫ⁾`; hence `P ≺ₖ D_j⁽ᑫ⁾`.
    Both sides of `Claim2 k` therefore split at `P` by Lemma 2.2 (4), and the piece
    `E ≺ₖ P` is common to the two arrays by Lemma 3.1.

  * `q > 0` and `D_j` does not ascend.  Let `R = D_{i₀}` with `i₀` least such that
    `i₀ < s` and `D_{i₀} ≼ₖ D_j` in `A`.  Then `R` does not ascend either, so (6.15)
    `Ã(R⁽ᑫ⁾, k) = A(R, k)`.  Minimality of `i₀` shows that no `k`-parent of `R` (in `A`) and
    no `k`-parent of `R⁽ᑫ⁾` (in `Ã`, using `Claim5 k` for `i₀ > 0` and `Claim4` for `i₀ = 0`)
    lies at or after `p`; by Lemma 6.2 there is then no internal valid candidate on either
    side.  The candidate sets of `R` and `R⁽ᑫ⁾` seen from `G` agree — for `k = 0` trivially,
    for `k = h+1` by `Claim2 h` — hence so do the direct parents, and the ancestor chains from
    `E` continue inside the common prefix `G`, where Lemma 3.1 applies.  Finally `Claim1 k`
    collapses `D_j⁽ᑫ⁾` to `R⁽ᑫ⁾` and `D_j` to `R` on the two sides.

  This file uses only the setup of `Bm4/Copy.lean` (structure, positions, entries, ascension),
  the interval lemmas of `Bm4/CopyPaper/Interval.lean` and the bridge `lead_bridge` of
  `Bm4/CopyPaper/L6.lean`; it uses none of the closed forms.
-/
import Bm4.CopyPaper.L6

open Classical

namespace BM4

variable {r : ℕ} {A : Arr r}

/-! ### Two convenience forms of transitivity -/

private theorem anc_ancEq {B : Arr r} {k x y z : ℕ} (h₁ : anc B k x y) (h₂ : ancEq B k y z) :
    anc B k x z := by
  rcases h₂ with rfl | h₂
  · exact h₁
  · exact anc_trans h₁ h₂

/-- Lemma 6.2 in the form used below: if every direct `k`-parent of `t` is left of `lo`, then
`t` has no internal valid `k`-candidate at all. -/
theorem no_intECand_of_parent_lt {B : Arr r} {k lo hi t : ℕ}
    (h : ∀ y, parent B k y t → y < lo) : ∀ z, ¬ IntECand B lo hi k z t := by
  intro z hz
  obtain ⟨y, hy, hyge⟩ := exists_parent_of_intECand hz
  exact absurd (h y hy) (not_lt.mpr hyge)

namespace BadRoot

variable (b : BadRoot A)

/-! ### The chain of leading columns (`k < m₀`)

`Claim3 k` gives one step `P⁽ᑫ⁾ ≺ₖ P⁽ᑫ⁺¹⁾` (`lead_bridge`); iterating it from `P⁽⁰⁾ = P`
reaches every later leading column. -/

/-- For `k < m₀` and `q > 0`, the bad root is a `k`-ancestor of the leading column of `Bq`. -/
theorem lead_chain_from_p {k : ℕ} (hk : k < b.m) (h3 : b.Claim3 k) :
    ∀ q, q ≤ b.N → 0 < q → anc b.tA k b.p (b.pos q 0) := by
  intro q
  induction q with
  | zero => intro _ h; omega
  | succ q' ih =>
    intro hqN _
    have hstep : anc b.tA k (b.pos q' 0) (b.pos (q' + 1) 0) := b.lead_bridge hk h3 hqN
    rcases Nat.eq_zero_or_pos q' with rfl | hq'
    · rw [b.pos_zero_zero] at hstep; exact hstep
    · exact anc_trans (ih (by omega) hq') hstep

/-! ### Case 1: the target column ascends -/

/-- Case 1 of Lemma 6.7.  `Asc k j` forces `k < m₀`; the bridge plus the copy-internal tail
make `P` a `k`-ancestor of `D_j⁽ᑫ⁾`, and `P ≼ₖ D_j` in `A`.  Both sides then factor through
`P`, and the piece below `p` lives in the common prefix. -/
theorem claim2_asc {k q j E : ℕ} (h1 : b.Claim1 k) (h3 : k < b.m → b.Claim3 k)
    (hqN : q ≤ b.N) (hq : 0 < q) (hj : j < b.s) (hE : E < b.p) (hasc : b.Asc k j) :
    anc b.tA k E (b.pos q j) ↔ anc A k E (b.p + j) := by
  have hk : k < b.m := hasc.1
  have hlead : anc b.tA k b.p (b.pos q 0) := b.lead_chain_from_p hk (h3 hk) q hqN hq
  have htail : ancEq b.tA k (b.pos q 0) (b.pos q j) := by
    rcases hasc.2 with heq | hanc
    · have hj0 : j = 0 := by omega
      subst hj0; exact ancEq_refl _ _ _
    · exact Or.inr ((h1 q hqN 0 j b.s_pos hj).mpr (by simpa using hanc))
  have hbp : anc b.tA k b.p (b.pos q j) := anc_ancEq hlead htail
  constructor
  · intro h
    have hEp : anc b.tA k E b.p := anc_of_anc_of_anc_of_lt h hbp hE
    exact anc_ancEq ((b.anc_tA_prefix b.p_lt_c k E).mp hEp) hasc.2
  · intro h
    have hEpA : anc A k E b.p := by
      rcases hasc.2 with heq | hanc
      · have hj0 : j = 0 := by omega
        subst hj0; simpa using h
      · exact anc_of_anc_of_anc_of_lt h hanc hE
    exact anc_trans ((b.anc_tA_prefix b.p_lt_c k E).mpr hEpA) hbp

/-! ### Case 2, the local data at the minimal column `R`

`R = D_{i₀}` is a column of the bad part with `Ã(R⁽ᑫ⁾,k) = A(R,k)` whose `k`-parents lie in
`G` on both sides.  Under these hypotheses the two arrays cannot be distinguished from `G`. -/

/-- Step 6: the structural `k`-candidates of `R⁽ᑫ⁾` and of `R` seen from `G` agree.
For `k = 0` both sides just say `E < ·`; for `k = h+1` this is `Claim2 h`. -/
theorem cand_agree {k q i E : ℕ} (h2low : ∀ h, h < k → b.Claim2 h) (hqN : q ≤ b.N)
    (hi : i < b.s) (hE : E < b.p) : cand b.tA k E (b.pos q i) ↔ cand A k E (b.p + i) := by
  cases k with
  | zero =>
    simp only [cand_zero]
    have := b.p_le_pos q i
    omega
  | succ h =>
    have h2 : b.Claim2 h := h2low h (Nat.lt_succ_self h)
    exact h2 q hqN i E hi hE

/-- Step 7: with no internal valid candidate on either side, the direct `k`-parents of `R⁽ᑫ⁾`
and of `R` inside `G` are the same.  The `<`-component is free, the candidate component is
step 6, the value component is (6.15) together with `col_lt`, and maximality is settled below
`p` by step 6 and at or above `p` by the absence of internal candidates. -/
theorem parent_agree {k q i y : ℕ} (h2low : ∀ h, h < k → b.Claim2 h) (hqN : q ≤ b.N)
    (hi : i < b.s) (hnasc : ¬ b.Asc k i)
    (hnoT : ∀ z, ¬ IntECand b.tA b.p (b.pos q i + 1) k z (b.pos q i))
    (hnoA : ∀ z, ¬ IntECand A b.p (b.p + i + 1) k z (b.p + i))
    (hy : y < b.p) :
    parent b.tA k y (b.pos q i) ↔ parent A k y (b.p + i) := by
  have hcolT : b.tA.col (b.pos q i) k = A.col (b.p + i) k := b.col_pos_not_asc hi hnasc
  have hcoly : b.tA.col y k = A.col y k := b.col_lt hy
  have hple : b.p ≤ b.pos q i := b.p_le_pos q i
  have hlenA : b.p + i < A.len := by have := b.lt_c_of_lt_s hi; omega
  have hlenT : b.pos q i < b.tA.len := b.pos_lt_tA_len hqN hi
  constructor
  · rintro ⟨-, hc, hv, hmax, hkr, -⟩
    refine ⟨by omega, (b.cand_agree h2low hqN hi hy).mp hc,
      by rw [← hcolT, ← hcoly]; exact hv, ?_, hkr, hlenA⟩
    intro z hz1 hz2 hz3
    rcases lt_or_ge z b.p with hzp | hzp
    · have hcz : cand b.tA k z (b.pos q i) := (b.cand_agree h2low hqN hi hzp).mpr hz3
      have hmx := hmax z hz1 (by omega) hcz
      rw [hcolT, b.col_lt hzp] at hmx
      exact hmx
    · exact not_lt.mp (fun hcc => hnoA z ⟨hzp, Nat.lt_succ_of_lt (cand_lt hz3), hz3, hcc, hkr, hlenA⟩)
  · rintro ⟨-, hc, hv, hmax, hkr, -⟩
    refine ⟨by omega, (b.cand_agree h2low hqN hi hy).mpr hc,
      by rw [hcolT, hcoly]; exact hv, ?_, hkr, hlenT⟩
    intro z hz1 hz2 hz3
    rcases lt_or_ge z b.p with hzp | hzp
    · have hcz : cand A k z (b.p + i) := (b.cand_agree h2low hqN hi hzp).mp hz3
      have hmx := hmax z hz1 (by omega) hcz
      rw [hcolT, b.col_lt hzp]
      exact hmx
    · exact not_lt.mp (fun hcc => hnoT z ⟨hzp, Nat.lt_succ_of_lt (cand_lt hz3), hz3, hcc, hkr, hlenT⟩)

/-- Step 9: ancestry from `G` into `R⁽ᑫ⁾` and into `R` agree.  Split off the last step of the
chain (`anc_last_step`): its direct parent lies in `G` and moves across by step 7, while the
remaining chain lives in the common prefix and moves across by Lemma 3.1.  (The paper's side
condition `E < p` is not needed here: the last step already forces the whole chain into `G`.) -/
theorem anc_transfer_root {k q i : ℕ} (h2low : ∀ h, h < k → b.Claim2 h) (hqN : q ≤ b.N)
    (hi : i < b.s) (hnasc : ¬ b.Asc k i)
    (hminT : ∀ y, parent b.tA k y (b.pos q i) → y < b.p)
    (hminA : ∀ y, parent A k y (b.p + i) → y < b.p) (E : ℕ) :
    anc b.tA k E (b.pos q i) ↔ anc A k E (b.p + i) := by
  have hnoT : ∀ z, ¬ IntECand b.tA b.p (b.pos q i + 1) k z (b.pos q i) :=
    no_intECand_of_parent_lt hminT
  have hnoA : ∀ z, ¬ IntECand A b.p (b.p + i + 1) k z (b.p + i) :=
    no_intECand_of_parent_lt hminA
  constructor
  · intro h
    obtain ⟨u, hu, hup⟩ := anc_last_step h
    have hul : u < b.p := hminT u hup
    have hpA : parent A k u (b.p + i) :=
      (b.parent_agree h2low hqN hi hnasc hnoT hnoA hul).mp hup
    rcases hu with rfl | hu
    · exact anc_of_parent hpA
    · exact anc_of_anc_of_parent ((b.anc_tA_prefix (hul.trans b.p_lt_c) k E).mp hu) hpA
  · intro h
    obtain ⟨u, hu, hup⟩ := anc_last_step h
    have hul : u < b.p := hminA u hup
    have hpT : parent b.tA k u (b.pos q i) :=
      (b.parent_agree h2low hqN hi hnasc hnoT hnoA hul).mpr hup
    rcases hu with rfl | hu
    · exact anc_of_parent hpT
    · exact anc_of_anc_of_parent ((b.anc_tA_prefix (hul.trans b.p_lt_c) k E).mpr hu) hpT

/-! ### Case 2: the target column does not ascend -/

/-- Case 2 of Lemma 6.7.  `R = D_{i₀}` is the leftmost column of the bad part with
`D_{i₀} ≼ₖ D_j` in `A`; minimality puts every `k`-parent of `R` and of `R⁽ᑫ⁾` into `G`, and
`Claim1 k` collapses `D_j` to `R` on both sides. -/
theorem claim2_not_asc {k q j E : ℕ} (h2low : ∀ h, h < k → b.Claim2 h) (h1 : b.Claim1 k)
    (h5 : b.Claim5 k) (h4 : b.m ≤ k → b.Claim4) (hqN : q ≤ b.N) (hq : 0 < q)
    (hj : j < b.s) (hE : E < b.p) (hnasc : ¬ b.Asc k j) :
    anc b.tA k E (b.pos q j) ↔ anc A k E (b.p + j) := by
  have hex : ∃ i, i < b.s ∧ ancEq A k (b.p + i) (b.p + j) := ⟨j, hj, ancEq_refl _ _ _⟩
  obtain ⟨i₀, ⟨hi₀s, hi₀eq⟩, hmin⟩ :
      ∃ i₀, (i₀ < b.s ∧ ancEq A k (b.p + i₀) (b.p + j)) ∧
        ∀ i, i < i₀ → ¬ (i < b.s ∧ ancEq A k (b.p + i) (b.p + j)) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
  have hi₀j : i₀ ≤ j := by have := ancEq_le hi₀eq; omega
  -- 1. `R` does not ascend either
  have hnasc0 : ¬ b.Asc k i₀ := fun hasc => hnasc ⟨hasc.1, ancEq_trans hasc.2 hi₀eq⟩
  -- 3. minimality on the `A` side
  have hminA : ∀ y, parent A k y (b.p + i₀) → y < b.p := by
    intro y hp
    by_contra hy
    have hy' : b.p ≤ y := not_lt.mp hy
    obtain ⟨i, rfl⟩ : ∃ i, y = b.p + i := ⟨y - b.p, by omega⟩
    have hii : i < i₀ := by have := parent_lt hp; omega
    exact hmin i hii ⟨by omega, ancEq_trans (Or.inr (anc_of_parent hp)) hi₀eq⟩
  -- 4. minimality on the `Ã` side
  have hminT : ∀ y, parent b.tA k y (b.pos q i₀) → y < b.p := by
    intro y hp
    rcases Nat.eq_zero_or_pos i₀ with hz | hpos
    · -- the leading column: low rows are excluded by step 1, high rows by `Claim4`
      have hkm : b.m ≤ k := by
        by_contra hcon
        exact hnasc0 (by rw [hz]; exact b.asc_zero (not_le.mp hcon))
      rw [hz] at hp
      exact h4 hkm k hkm q y hq (anc_of_parent hp)
    · rcases h5 q i₀ y hi₀s hpos hp with hg | ⟨i, rfl⟩
      · exact hg
      · exfalso
        have hii : i < i₀ := b.pos_lt_pos_same_iff.mp (parent_lt hp)
        have hiA : anc A k (b.p + i) (b.p + i₀) :=
          (h1 q hqN i i₀ (by omega) hi₀s).mp (anc_of_parent hp)
        exact hmin i hii ⟨by omega, ancEq_trans (Or.inr hiA) hi₀eq⟩
  -- 8. collapse `D_j` to `R` on both sides
  have hTeq : ancEq b.tA k (b.pos q i₀) (b.pos q j) := by
    rcases eq_or_lt_of_le hi₀j with heq | hlt
    · rw [heq]; exact ancEq_refl _ _ _
    · exact Or.inr ((h1 q hqN i₀ j hi₀s hj).mpr (anc_of_ancEq_of_ne hi₀eq (by omega)))
  have hcollT : anc b.tA k E (b.pos q j) ↔ anc b.tA k E (b.pos q i₀) := by
    constructor
    · intro h
      rcases hTeq with heq | hanc
      · rwa [← heq] at h
      · exact anc_of_anc_of_anc_of_lt h hanc (by have := b.p_le_pos q i₀; omega)
    · intro h; exact anc_ancEq h hTeq
  have hcollA : anc A k E (b.p + j) ↔ anc A k E (b.p + i₀) := by
    constructor
    · intro h
      rcases hi₀eq with heq | hanc
      · rwa [← heq] at h
      · exact anc_of_anc_of_anc_of_lt h hanc (by omega)
    · intro h; exact anc_ancEq h hi₀eq
  -- 9. transfer at `R`
  rw [hcollT, hcollA]
  exact b.anc_transfer_root h2low hqN hi₀s hnasc0 hminT hminA E

/-! ### Lemma 6.7 -/

/-- **Lemma 6.7** (local proof II): the second claim of Theorem 6.3 for row `k`. -/
theorem lemma_6_7 {k : ℕ} (h2low : ∀ h, h < k → b.Claim2 h) (h1 : b.Claim1 k) (h5 : b.Claim5 k)
    (h34 : (k < b.m → b.Claim3 k) ∧ (b.m ≤ k → b.Claim4)) : b.Claim2 k := by
  intro q hqN j E hj hE
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · -- the first copy is part of the common prefix (Lemma 3.1)
    rw [b.pos_zero]
    exact b.anc_tA_prefix (b.lt_c_of_lt_s hj) k E
  by_cases hasc : b.Asc k j
  · exact b.claim2_asc h1 h34.1 hqN hq hj hE hasc
  · exact b.claim2_not_asc h2low h1 h5 h34.2 hqN hq hj hE hasc

end BadRoot

end BM4
