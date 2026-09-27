/-
Copied from koteitan, bms-elem-pattern, `lean/Bm4/CopyPaper/L6.lean`
(https://github.com/koteitan/bms-elem-pattern, CC BY-SA 4.0), which takes it from koteitan,
dh-bms-wf-formal (https://github.com/koteitan/dh-bms-wf-formal). Changes: ported to Lean 4.33.1 (no other change).
-/
/-
  Lemma 6.8 of the paper (local proof V): the sixth claim of Theorem 6.3 for row `k`,
  assuming `(C1)_k`, `(C5)_k` and, according to the row, `(C3)_k` (for `k < m₀`) or `(C4)`
  (for `k ≥ m₀`).

  The argument is the paper's own (§6.7).

  1. *Passing property* (6.16).  If a column of an earlier copy `B_a` (`a < c'`) is a
     `k`-ancestor of `D_j⁽ᶜ'⁾`, the chain from `D_j⁽ᶜ'⁾` must pass through the leading column
     `P⁽ᶜ'⁾`.  Indeed, follow the `k`-parent chain down from `D_j⁽ᶜ'⁾`.  As long as the index
     `j` is non-zero, `(C5)_k` says the direct `k`-parent is either in `G` or again in `B_{c'}`;
     the first alternative is impossible, because the chain has to reach a column of `B_a`,
     which lies at or right of `p`.  So the chain stays inside `B_{c'}` and its index strictly
     decreases at every step, hence it meets index `0`.

  2. *High rows* `k ≥ m₀`.  Both sides of `(C6)_k` are false: an ancestor from an earlier copy
     would, by the passing property, be a `k`-ancestor of a leading column of a copy `q ≥ 1`,
     and `(C4)` forces every such ancestor into `G`.

  3. *Low rows* `k < m₀`.  `(C3)_k` applied to the leading column (index `0`, which is a
     `k`-ancestor of `C` in `A` because `p` is the `m₀`-parent of `C`) gives the bridge
     `P⁽ᶜ'⁾ ≺ₖ P⁽ᶜ'⁺¹⁾`.  Forward: `D_i⁽ᵃ⁾ ≺ₖ P⁽ᶜ'⁾ ≺ₖ P⁽ᶜ'⁺¹⁾ ≼ₖ D_j⁽ᶜ'⁺¹⁾`, the last step
     being the copy-internal tail transported by `(C1)_k`.  Backward: `D_i⁽ᵃ⁾` and `P⁽ᶜ'⁾` are
     two `k`-ancestors of `P⁽ᶜ'⁺¹⁾` with `D_i⁽ᵃ⁾ < P⁽ᶜ'⁾`, so Lemma 2.2 (4) makes the first an
     ancestor of the second; then transport the tail back with `(C1)_k`.

  This file uses only the setup of `Bm4/Copy.lean` (structure, positions, entries, ascension)
  together with Lemma 2.2; it uses none of the closed forms.
-/
import Bm4.CopyPaper.Interval

open Classical

namespace BM4

variable {r : ℕ} {A : Arr r}

namespace BadRoot

variable (b : BadRoot A)

/-! ### A convenience form of transitivity -/

private theorem anc_of_anc_of_ancEq {B : Arr r} {k x y z : ℕ} (h₁ : anc B k x y)
    (h₂ : ancEq B k y z) : anc B k x z := by
  rcases h₂ with rfl | h₂
  · exact h₁
  · exact anc_trans h₁ h₂

/-! ### The passing property (6.16)

Following the `k`-parent chain down from `D_j⁽ᶜ'⁾`: by `(C5)_k` each step either leaves for `G`
— impossible, since the chain must reach `D_i⁽ᵃ⁾ ≥ p` — or stays in `B_{c'}` with a strictly
smaller index, so index `0` is reached. -/

private theorem passing_aux {k : ℕ} (h5 : b.Claim5 k) {a c' i : ℕ} (hac : a < c')
    (hi : i < b.s) :
    ∀ j, j < b.s → anc b.tA k (b.pos a i) (b.pos c' j) →
      anc b.tA k (b.pos a i) (b.pos c' 0) ∧ ancEq b.tA k (b.pos c' 0) (b.pos c' j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j IH =>
  intro hj h
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · exact ⟨h, ancEq_refl _ _ _⟩
  obtain ⟨u, hu, hup⟩ := anc_last_step h
  rcases h5 c' j u hj hj0 hup with hG | ⟨i', rfl⟩
  · -- the chain would have left the copy before reaching `D_i⁽ᵃ⁾`
    have h1 : b.p ≤ b.pos a i := b.p_le_pos a i
    have h2 : b.pos a i ≤ u := ancEq_le hu
    omega
  · have hlt : i' < j := b.pos_lt_pos_same_iff.mp (parent_lt hup)
    have hne : b.pos a i ≠ b.pos c' i' := ne_of_lt (b.pos_lt_pos_of_lt hac hi)
    obtain ⟨hA, hT⟩ := IH i' hlt (hlt.trans hj) (anc_of_ancEq_of_ne hu hne)
    exact ⟨hA, ancEq_trans hT (Or.inr (anc_of_parent hup))⟩

set_option linter.unusedVariables false in
/-- The "passing" property (6.16): an ancestor in an earlier copy passes through the head of the
target's copy. -/
theorem passing {k : ℕ} (h1 : b.Claim1 k) (h5 : b.Claim5 k) {a c' i j : ℕ}
    (hac : a < c') (hi : i < b.s) (hj : j < b.s)
    (h : anc b.tA k (b.pos a i) (b.pos c' j)) :
    anc b.tA k (b.pos a i) (b.pos c' 0) ∧ ancEq b.tA k (b.pos c' 0) (b.pos c' j) :=
  b.passing_aux h5 hac hi j hj h

/-! ### Transporting a copy-internal tail between copies, and the bridge -/

/-- `(C1)_k` moves a copy-internal (non-strict) ancestor relation from one copy to any other. -/
theorem ancEq_transport {k q q' i j : ℕ} (h1 : b.Claim1 k) (hq : q ≤ b.N) (hq' : q' ≤ b.N)
    (hi : i < b.s) (hj : j < b.s)
    (h : ancEq b.tA k (b.pos q i) (b.pos q j)) : ancEq b.tA k (b.pos q' i) (b.pos q' j) := by
  rcases h with heq | h
  · obtain ⟨-, rfl⟩ := b.pos_inj hi hj heq
    exact ancEq_refl _ _ _
  · exact Or.inr ((h1 q' hq' i j hi hj).mpr ((h1 q hq i j hi hj).mp h))

/-- The bridge between consecutive leading columns, for `k < m₀`: `(C3)_k` applied to index `0`,
whose counterpart `P ≺ₖ C` holds in `A` because `p` is the `m₀`-parent of `C`. -/
theorem lead_bridge {k : ℕ} (hk : k < b.m) (h3 : b.Claim3 k) {c' : ℕ} (hc' : c' + 1 ≤ b.N) :
    anc b.tA k (b.pos c' 0) (b.pos (c' + 1) 0) := by
  have hpc : anc A k (b.p + 0) (A.len - 1) := by
    simpa using b.anc_p_c hk.le
  have h := (h3 (c' + 1) hc' 0 (by omega) b.s_pos).mpr hpc
  simpa using h

/-! ### Lemma 6.8 -/

/-- **Lemma 6.8** (local proof V). -/
theorem lemma_6_8 {k : ℕ} (h1 : b.Claim1 k) (h5 : b.Claim5 k)
    (h34 : (k < b.m → b.Claim3 k) ∧ (b.m ≤ k → b.Claim4)) : b.Claim6 k := by
  intro a c' hac hc' i j hi hj
  rcases lt_or_ge k b.m with hk | hk
  · -- low rows: both sides hold, linked by the bridge `P⁽ᶜ'⁾ ≺ₖ P⁽ᶜ'⁺¹⁾`
    have hbr : anc b.tA k (b.pos c' 0) (b.pos (c' + 1) 0) := b.lead_bridge hk (h34.1 hk) hc'
    constructor
    · intro h
      obtain ⟨hA, hT⟩ := b.passing h1 h5 hac hi hj h
      exact anc_of_anc_of_ancEq (anc_trans hA hbr)
        (b.ancEq_transport (q := c') (q' := c' + 1) h1 (by omega) hc' b.s_pos hj hT)
    · intro h
      obtain ⟨hA, hT⟩ := b.passing h1 h5 (show a < c' + 1 by omega) hi hj h
      have hA' : anc b.tA k (b.pos a i) (b.pos c' 0) :=
        anc_of_anc_of_anc_of_lt hA hbr (b.pos_lt_pos_of_lt hac hi)
      exact anc_of_anc_of_ancEq hA'
        (b.ancEq_transport (q := c' + 1) (q' := c') h1 hc' (by omega) b.s_pos hj hT)
  · -- high rows: `(C4)` makes both sides false
    have h4 : b.Claim4 := h34.2 hk
    have hp : b.p ≤ b.pos a i := b.p_le_pos a i
    refine iff_of_false (fun h => ?_) (fun h => ?_)
    · obtain ⟨hA, -⟩ := b.passing h1 h5 hac hi hj h
      have := h4 k hk c' (b.pos a i) (by omega) hA
      omega
    · obtain ⟨hA, -⟩ := b.passing h1 h5 (show a < c' + 1 by omega) hi hj h
      have := h4 k hk (c' + 1) (b.pos a i) (by omega) hA
      omega

end BadRoot

end BM4
