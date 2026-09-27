/-
Copied from koteitan, bms-elem-pattern, `lean/Bm4/CopyPaper/L5.lean`
(https://github.com/koteitan/bms-elem-pattern, CC BY-SA 4.0), which takes it from koteitan,
dh-bms-wf-formal (https://github.com/koteitan/dh-bms-wf-formal). Changes: ported to Lean 4.33.1 (no other change).
-/
/-
  Lemma 6.6 of the paper (local proof III): the fifth claim `(C5)_k` of Theorem 6.3,
  "no jumping over copies", for row `k`.

  The argument is the paper's own (§6.5).  Fix `j > 0` and suppose, for contradiction, that
  the direct `k`-parent `Q` of `D_j^(q) = pos q j` lies in an earlier copy `B_a`, `a < q`.

  1. Step 1.  For every `h < k` we have `P^(q) = pos q 0 ≺_h pos q j`.  Otherwise follow the
     `h`-parent chain leftwards from `pos q j`; the first column of the chain that leaves the
     interval `[pos q 0, pos q j]` is a non-leading column of `B_q`, so `(C5)_h` puts its
     direct parent in `G`, while the chain from `Q` can only reach columns `≥ Q ≥ p`.
  2. Step 2.  `pos q 0` is not a `k`-ancestor of `pos q j`: on one `k`-parent chain the direct
     parent would then be `≥ pos q 0`, contradicting `Q ∈ B_a`.  With `(C1)_k` this gives
     `¬ (P ≺ᴬ_k D_j)`, hence `¬ Asc k j`, hence the target entry is unchanged.
  3. Step 3.  `A.col (p + j) k ≤ A.col p k`.  Otherwise `P` is a valid `k`-candidate of `D_j`
     inside `B₀` (structural by step 1 and `(C1)_{k-1}`), so `exists_parent_of_intECand` puts
     the direct `A`-parent of `D_j` inside `B₀`, and `(C1)_k` transports it back into `B_q`.
  4. Step 4.  Lemma 4.1 (`convex`) applied to `Q ≺_k pos q j` with the intermediate column
     `pos q 0` gives `Q ≺_k pos q 0`.  For `k ≥ m₀` this contradicts `(C4)`; for `k < m₀`,
     `(C3)_k` builds the chain `pos 0 0 ≺_k pos 1 0 ≺_k ⋯ ≺_k pos q 0`, and comparing it with
     `Q` through `anc_of_anc_of_anc_of_lt` yields `pos 0 0 ≺_k pos q j`, whose `anc_val_lt`
     contradicts step 3.

  This file uses only the setup of `Bm4/Copy.lean` (structure, positions, entries, ascension)
  together with Lemma 2.2 and Lemma 4.1; it uses none of the closed forms.
-/
import Bm4.CopyPaper.Interval

open Classical

namespace BM4

variable {r : ℕ} {A : Arr r}

namespace BadRoot

variable (b : BadRoot A)

/-! ### Non-strict comparison of positions inside one copy -/

theorem pos_le_pos_same_iff {q i j : ℕ} : b.pos q i ≤ b.pos q j ↔ i ≤ j := by
  unfold pos; omega

theorem pos_le_pos_same {q i j : ℕ} (h : i ≤ j) : b.pos q i ≤ b.pos q j :=
  b.pos_le_pos_same_iff.mpr h

/-! ### Step 0: no `k`-ancestor of the target sits at or after the leading column

If the direct `k`-parent of `pos q j` is in an earlier copy, then every `k`-ancestor of
`pos q j` is strictly left of `pos q 0`: on a single `k`-parent chain, the last step is the
direct parent, and `anc_last_step` puts every ancestor at or before it. -/

theorem no_anc_ge_of_parent_earlier {k q j a i z : ℕ} (ha : a < q) (hi : i < b.s)
    (hp : parent b.tA k (b.pos a i) (b.pos q j))
    (hz : anc b.tA k z (b.pos q j)) (hzge : b.pos q 0 ≤ z) : False := by
  obtain ⟨u, hu, hup⟩ := anc_last_step hz
  have heq : u = b.pos a i := parent_unique hup hp
  have hle : z ≤ u := ancEq_le hu
  have hlt : b.pos a i < b.pos q 0 := b.pos_lt_pos_of_lt ha hi
  omega

/-! ### Step 1: the leading column of `B_q` is an `h`-ancestor for every `h < k`

Follow the `h`-parent chain leftwards from `pos q j`.  `anc_exit_point` produces the first
column `u` of the chain at or after `pos q 0` together with its direct parent `y'`, which is
strictly left of `pos q 0`.  If `u = pos q 0` we are done; otherwise `u` is a non-leading
column of `B_q`, so `(C5)_h` says `y' ∈ G` or `y' ∈ B_q` — the first contradicts `p ≤ y ≤ y'`,
the second contradicts `y' < pos q 0`. -/

theorem lead_anc_of_earlier {h q j y : ℕ} (h5 : b.Claim5 h) (hj : j < b.s) (hj0 : 0 < j)
    (hyp : b.p ≤ y) (hylt : y < b.pos q 0) (hanc : anc b.tA h y (b.pos q j)) :
    anc b.tA h (b.pos q 0) (b.pos q j) := by
  obtain ⟨u, y', hu, huv, hy'u, hy', hyy'⟩ :=
    anc_exit_point hanc hylt (b.pos_le_pos_same (Nat.zero_le j))
  have hple : b.p ≤ u := (b.p_le_pos q 0).trans hu
  obtain ⟨j', hjj, rfl⟩ : ∃ j', j' ≤ j ∧ u = b.pos q j' := by
    obtain ⟨a', i', hi', rfl⟩ := b.exists_pos hple
    have hle2 : b.pos a' i' ≤ b.pos q j := ancEq_le huv
    have haq : a' = q := by
      rcases lt_trichotomy a' q with hlt | heq | hgt
      · exact absurd (b.pos_lt_pos_of_lt (j := 0) hlt hi') (by omega)
      · exact heq
      · exact absurd (b.pos_lt_pos_of_lt (j := i') hgt hj) (by omega)
    rw [haq] at hle2
    exact ⟨i', b.pos_le_pos_same_iff.mp hle2, by rw [haq]⟩
  rcases Nat.eq_zero_or_pos j' with rfl | hj'0
  · -- the chain already reaches the leading column
    refine anc_of_ancEq_of_ne huv ?_
    intro hcc
    obtain ⟨-, h0⟩ := b.pos_inj b.s_pos hj hcc
    omega
  · -- `(C5)_h` applied to the non-leading column `u`
    exfalso
    have hQy : b.p ≤ y' := hyp.trans (ancEq_le hyy')
    have hj's : j' < b.s := lt_of_le_of_lt hjj hj
    rcases h5 q j' y' hj's hj'0 hy'u with hlt2 | ⟨i'', hi''⟩
    · omega
    · rw [hi''] at hy'
      have hneg : i'' < 0 := b.pos_lt_pos_same_iff.mp hy'
      omega

/-! ### Structural candidacy supplied by step 1 -/

/-- `P` is a structural `k`-candidate of `D_j`: for `k = 0` because `j > 0`, for `k = k'+1`
because of step 1 in row `k'` together with `(C1)_{k'}`. -/
theorem cand_p_of_lead {k q j : ℕ} (hq : q ≤ b.N) (hj : j < b.s) (hj0 : 0 < j)
    (hlow : ∀ h, h < k → b.Claim1 h)
    (hlead : ∀ h, h < k → anc b.tA h (b.pos q 0) (b.pos q j)) :
    cand A k b.p (b.p + j) := by
  cases k with
  | zero => exact cand_zero.mpr (by omega)
  | succ k' =>
    have hs := hlead k' (Nat.lt_succ_self k')
    have hc := (hlow k' (Nat.lt_succ_self k')) q hq 0 j b.s_pos hj
    have hA : anc A k' (b.p + 0) (b.p + j) := hc.mp hs
    exact cand_succ.mpr (by simpa using hA)

/-- The leading column of `B_q` is a structural `k`-candidate of `pos q j` in the expanded
array: for `k = 0` by position, for `k = k'+1` by step 1 in row `k'`. -/
theorem cand_lead_of_lead {k q j : ℕ} (hj0 : 0 < j)
    (hlead : ∀ h, h < k → anc b.tA h (b.pos q 0) (b.pos q j)) :
    cand b.tA k (b.pos q 0) (b.pos q j) := by
  cases k with
  | zero => exact cand_zero.mpr (b.pos_lt_pos_same hj0)
  | succ k' => exact cand_succ.mpr (hlead k' (Nat.lt_succ_self k'))

/-! ### The chain of leading columns (`k < m₀`) -/

/-- `(C3)_k` iterated: for `k < m₀`, `P^(a) ≺_k P^(q)` whenever `a < q`. -/
theorem chain_lead {k : ℕ} (hkm : k < b.m) (h3 : b.Claim3 k) :
    ∀ a q, q ≤ b.N → a < q → anc b.tA k (b.pos a 0) (b.pos q 0) := by
  intro a q
  induction q with
  | zero => intro _ h; omega
  | succ q' ih =>
    intro hqN _
    have hpc : anc A k (b.p + 0) (A.len - 1) := by simpa using b.anc_p_c hkm.le
    have hq1 : q' + 1 - 1 = q' := by omega
    have hstep : anc b.tA k (b.pos q' 0) (b.pos (q' + 1) 0) := by
      have hh := (h3 (q' + 1) hqN 0 (Nat.succ_pos q') b.s_pos).mpr hpc
      rwa [hq1] at hh
    rcases Nat.lt_or_ge a q' with hlt | hge
    · exact anc_trans (ih (by omega) hlt) hstep
    · have haq : a = q' := by omega
      rw [haq]
      exact hstep

/-! ### Lemma 6.6 -/

/-- **Lemma 6.6** (local proof III). -/
theorem lemma_6_6 {k : ℕ}
    (hlow : ∀ h, h < k → b.Claim1 h ∧ b.Claim5 h)
    (h1 : b.Claim1 k)
    (h34 : (k < b.m → b.Claim3 k) ∧ (b.m ≤ k → b.Claim4)) :
    b.Claim5 k := by
  intro q j y hj hj0 hp
  by_contra hcon
  -- the target is a column of `Ã`, so the paper's range `q ≤ N` is automatic
  have hqN : q ≤ b.N := b.le_N_of_pos_lt_tA_len (parent_target_lt hp)
  have hkr : k < r := parent_row_lt hp
  -- the parent `Q` is neither in `G` nor in `B_q`, so it lies in an earlier copy `B_a`
  have hyp : b.p ≤ y := not_lt.mp (fun hh => hcon (Or.inl hh))
  have hnotpos : ∀ i', y ≠ b.pos q i' := fun i' hh => hcon (Or.inr ⟨i', hh⟩)
  rcases b.lt_pos_cases hj (parent_lt hp) with hlt | ⟨a, i, hi, rfl, hcase⟩
  · omega
  have ha : a < q := by
    rcases hcase with hh | ⟨haq, _⟩
    · exact hh
    · exact absurd (by rw [haq]) (hnotpos i)
  have hQlt : b.pos a i < b.pos q 0 := b.pos_lt_pos_of_lt ha hi
  -- Step 0
  have hno : ∀ z, anc b.tA k z (b.pos q j) → b.pos q 0 ≤ z → False :=
    fun z hz hzge => b.no_anc_ge_of_parent_earlier ha hi hp hz hzge
  -- Step 1
  have hlead : ∀ h, h < k → anc b.tA h (b.pos q 0) (b.pos q j) := by
    intro h hh
    exact b.lead_anc_of_earlier (hlow h hh).2 hj hj0 (b.p_le_pos a i) hQlt
      (anc_mono hh.le (anc_of_parent hp))
  -- Step 2
  have hnotA : ¬ anc A k b.p (b.p + j) := by
    intro hc
    exact hno (b.pos q 0) ((h1 q hqN 0 j b.s_pos hj).mpr (by simpa using hc)) le_rfl
  have hnasc : ¬ b.Asc k j := fun hasc => hnotA (anc_of_ancEq_of_ne hasc.2 (by omega))
  have htgt : b.tA.col (b.pos q j) k = A.col (b.p + j) k := b.col_pos_not_asc hj hnasc
  -- Step 3
  have hcandP : cand A k b.p (b.p + j) :=
    b.cand_p_of_lead hqN hj hj0 (fun h hh => (hlow h hh).1) hlead
  have hstep3 : A.col (b.p + j) k ≤ A.col b.p k := by
    by_contra hcc
    have hc : A.col b.p k < A.col (b.p + j) k := not_le.mp hcc
    obtain ⟨y', hy'p, hy'ge⟩ :=
      exists_parent_of_intECand (A := A) (lo := b.p) (hi := b.p + j + 1) (k := k) (j := b.p)
        (i := b.p + j)
        ⟨le_rfl, Nat.lt_succ_of_lt (cand_lt hcandP), hcandP, hc, hkr,
          by have := b.lt_c_of_lt_s hj; have := b.p_lt_c; omega⟩
    have hy'lt : y' < b.p + j := parent_lt hy'p
    obtain ⟨i', rfl⟩ : ∃ i', y' = b.p + i' := ⟨y' - b.p, by omega⟩
    have hi's : i' < b.s := by omega
    refine hno (b.pos q i') ((h1 q hqN i' j hi's hj).mpr (anc_of_parent hy'p)) ?_
    exact b.pos_le_pos_same (Nat.zero_le i')
  -- Step 4: convexity (Lemma 4.1)
  have hancQ : anc b.tA k (b.pos a i) (b.pos q 0) := by
    have hcv : ancEq b.tA k (b.pos a i) (b.pos q 0) :=
      convex (anc_of_parent hp) hQlt.le (b.pos_le_pos_same (Nat.zero_le j))
        (Or.inr (b.cand_lead_of_lead hj0 hlead))
    exact anc_of_ancEq_of_ne hcv (by omega)
  rcases Nat.lt_or_ge k b.m with hkm | hkm
  · -- `k < m₀`: the chain of leading columns
    have hchain := b.chain_lead hkm (h34.1 hkm)
    have hA : anc b.tA k (b.pos a 0) (b.pos q 0) := hchain a q hqN ha
    have hEq1 : ancEq b.tA k (b.pos a 0) (b.pos a i) := by
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · exact Or.inl rfl
      · exact Or.inr (anc_of_anc_of_anc_of_lt hA hancQ (b.pos_lt_pos_same hi0))
    have hEq0 : ancEq b.tA k (b.pos 0 0) (b.pos a 0) := by
      rcases Nat.eq_zero_or_pos a with rfl | ha0
      · exact Or.inl rfl
      · exact Or.inr (hchain 0 a (by omega) ha0)
    have hfin : anc b.tA k (b.pos 0 0) (b.pos q j) := by
      refine anc_of_ancEq_of_ne
        (ancEq_trans (ancEq_trans hEq0 hEq1) (Or.inr (anc_of_parent hp))) ?_
      have h0 : b.pos 0 0 = b.p := b.pos_zero_zero
      have h2 : b.p ≤ b.pos a i := b.p_le_pos a i
      have h3 : b.pos q 0 ≤ b.pos q j := b.pos_le_pos_same (Nat.zero_le j)
      omega
    have hval := anc_val_lt hfin
    rw [b.pos_zero_zero, htgt, b.col_prefix b.p_lt_c] at hval
    omega
  · -- `k ≥ m₀`: `(C4)`
    have hQ := h34.2 hkm k hkm q (b.pos a i) (by omega) hancQ
    have := b.p_le_pos a i
    omega

end BadRoot

end BM4
