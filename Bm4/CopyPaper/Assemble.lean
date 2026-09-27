/-
Copied from koteitan, bms-elem-pattern, `lean/Bm4/CopyPaper/Assemble.lean`
(https://github.com/koteitan/bms-elem-pattern, CC BY-SA 4.0), which takes it from koteitan,
dh-bms-wf-formal (https://github.com/koteitan/dh-bms-wf-formal). Changes: ported to Lean 4.33.1 (no other change).
-/
/-
  Proposition 6.11 (the acyclic assembly), Theorem 6.3 and Corollary 6.12 of the paper.

  The local lemmas 6.4–6.10 are combined in the three stages the paper prescribes (§6.9):

  * **Stage 1** (`stage1`), rows `k < m₀` in increasing order, each row in the order
    `(C1)ₖ → (C3)ₖ → (C5)ₖ → (C2)ₖ → (C6)ₖ`.  `(C4)` is not available yet and is not used:
    for `k < m₀` the boundary hypothesis of Lemmas 6.6–6.8 is discharged by `(C3)ₖ`.
  * **Stage 2** (`claim4`), the boundary claim `(C4)`: Lemma 6.9 when `m₀ = 0`, and Lemma 6.10
    from `(C3)_{m₀-1}` and `(C6)_{m₀-1}` — both supplied by stage 1 — when `m₀ > 0`.
  * **Stage 3** (`stage3`), all rows in increasing order, in the order
    `(C1)ₖ → (C5)ₖ → (C2)ₖ → (C6)ₖ`, using stage 1 below `m₀` and `(C4)` at and above it.

  The paper's lexicographic ranking `(0,k,·) < (1,0,0) < (2,k,·)` is exactly this stage order,
  so the two strong inductions below are the formal content of Proposition 6.11.

  This file uses none of the closed forms of `Bm4/Copy.lean`.
-/
import Bm4.CopyPaper.L1
import Bm4.CopyPaper.L2
import Bm4.CopyPaper.L3
import Bm4.CopyPaper.L4
import Bm4.CopyPaper.L5
import Bm4.CopyPaper.L6

open Classical

namespace BM4

variable {r : ℕ} {A : Arr r}

namespace BadRoot

variable (b : BadRoot A)

/-! ### Stage 1: the rows below `m₀`, independently of `(C4)` -/

/-- Stage 1 of Proposition 6.11 (6.22): for `k < m₀` the five claims of row `k` hold, proved in
the order `(C1)ₖ → (C3)ₖ → (C5)ₖ → (C2)ₖ → (C6)ₖ`.  No appeal to `(C4)` occurs. -/
theorem stage1 : ∀ k, k < b.m →
    b.Claim1 k ∧ b.Claim3 k ∧ b.Claim5 k ∧ b.Claim2 k ∧ b.Claim6 k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hIH : ∀ h, h < k → b.Claim1 h ∧ b.Claim3 h ∧ b.Claim5 h ∧ b.Claim2 h ∧ b.Claim6 h :=
      fun h hh => ih h hh (by omega)
    have c1 : b.Claim1 k := b.lemma_6_4 k fun h hh => (hIH h hh).1
    have c3 : b.Claim3 k := b.lemma_6_5 hk c1 fun k' hk' => (hIH k' (by omega)).2.1
    have h34 : (k < b.m → b.Claim3 k) ∧ (b.m ≤ k → b.Claim4) :=
      ⟨fun _ => c3, fun hc => absurd hc (by omega)⟩
    have c5 : b.Claim5 k := b.lemma_6_6 (fun h hh => ⟨(hIH h hh).1, (hIH h hh).2.2.1⟩) c1 h34
    have c2 : b.Claim2 k := b.lemma_6_7 (fun h hh => (hIH h hh).2.2.2.1) c1 c5 h34
    exact ⟨c1, c3, c5, c2, b.lemma_6_8 c1 c5 h34⟩

/-! ### Stage 2: the boundary claim `(C4)` -/

/-- Stage 2 of Proposition 6.11: `(C4)` itself, from Lemma 6.9 (`m₀ = 0`) or Lemma 6.10
(`m₀ > 0`, using `(C3)_{m₀-1}` and `(C6)_{m₀-1}` from stage 1). -/
theorem claim4 : b.Claim4 := by
  rcases Nat.eq_zero_or_pos b.m with hm | hm
  · exact b.lemma_6_9 hm
  · have h := b.stage1 (b.m - 1) (by omega)
    exact b.lemma_6_10 hm h.2.1 h.2.2.2.2

/-! ### Stage 3: all rows -/

/-- Stage 3 of Proposition 6.11 (6.21)/(6.23): `(C1)ₖ`, `(C5)ₖ`, `(C2)ₖ`, `(C6)ₖ` for every row.
Below `m₀` this is stage 1; at and above `m₀` the boundary hypothesis is `(C4)`. -/
theorem stage3 : ∀ k, b.Claim1 k ∧ b.Claim5 k ∧ b.Claim2 k ∧ b.Claim6 k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases lt_or_ge k b.m with hk | hk
    · have h := b.stage1 k hk
      exact ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
    · have c1 : b.Claim1 k := b.lemma_6_4 k fun h hh => (ih h hh).1
      have h34 : (k < b.m → b.Claim3 k) ∧ (b.m ≤ k → b.Claim4) :=
        ⟨fun hc => absurd hc (by omega), fun _ => b.claim4⟩
      have c5 : b.Claim5 k := b.lemma_6_6 (fun h hh => ⟨(ih h hh).1, (ih h hh).2.1⟩) c1 h34
      have c2 : b.Claim2 k := b.lemma_6_7 (fun h hh => (ih h hh).2.2.1) c1 c5 h34
      exact ⟨c1, c5, c2, b.lemma_6_8 c1 c5 h34⟩

/-! ### Theorem 6.3 -/

/-- **Theorem 6.3** (the copy lemma), in the paper's own formulation: the six claims
`(C1)`–`(C6)`, obtained from the local lemmas 6.4–6.10 by Proposition 6.11. -/
theorem theorem_6_3 :
    (∀ k, b.Claim1 k) ∧ (∀ k, b.Claim2 k) ∧ (∀ k, k < b.m → b.Claim3 k) ∧ b.Claim4 ∧
      (∀ k, b.Claim5 k) ∧ (∀ k, b.Claim6 k) :=
  ⟨fun k => (b.stage3 k).1, fun k => (b.stage3 k).2.2.1,
   fun k hk => (b.stage1 k hk).2.1, b.claim4,
   fun k => (b.stage3 k).2.1, fun k => (b.stage3 k).2.2.2⟩

/-! ### Corollary 6.12 -/

/-- **Corollary 6.12** (6.24): a `k`-ancestor relation across two adjacent copies forces
`k < m₀`, and splits into `D_i ≺ᴬₖ C` and `P ≼ᴬₖ D_j` on the original array. -/
theorem corollary_6_12 {k q i j : ℕ} (hi : i < b.s) (hj : j < b.s)
    (h : anc b.tA k (b.pos q i) (b.pos (q + 1) j)) :
    k < b.m ∧ anc A k (b.p + i) (A.len - 1) ∧ ancEq A k b.p (b.p + j) := by
  have hst := b.stage3 k
  -- `D_j⁽ᑫ⁺¹⁾` is a column of `Ã`, so the paper's range condition `q + 1 ≤ N` holds
  have hqN : q + 1 ≤ b.N := by
    obtain ⟨u, -, hu⟩ := anc_last_step h
    exact b.le_N_of_pos_lt_tA_len (parent_target_lt hu)
  -- the passing property (6.16) of Lemma 6.8, with `a = q`, `b = q+1`
  have hpass := b.passing hst.1 hst.2.1 (Nat.lt_succ_self q) hi hj h
  have hkm : k < b.m := by
    by_contra hc
    have hlt := b.claim4 k (not_lt.mp hc) (q + 1) (b.pos q i) (Nat.succ_pos q) hpass.1
    have := b.p_le_pos q i
    omega
  refine ⟨hkm, ?_, ?_⟩
  · -- `(C3)ₖ` transports the first half
    have hb := (b.stage1 k hkm).2.1 (q + 1) hqN i (Nat.succ_pos q) hi
    simp only [Nat.add_sub_cancel] at hb
    exact hb.mp hpass.1
  · -- `(C1)ₖ` transports the copy-internal tail
    rcases hpass.2 with heq | hanc
    · have hj0 : j = 0 := ((b.pos_inj b.s_pos hj heq).2).symm
      subst hj0
      exact Or.inl (by omega)
    · exact Or.inr (by
        have := (hst.1 (q + 1) hqN 0 j b.s_pos hj).mp hanc
        simpa using this)

end BadRoot

end BM4
