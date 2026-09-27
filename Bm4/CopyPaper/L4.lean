/-
Copied from koteitan, bms-elem-pattern, `lean/Bm4/CopyPaper/L4.lean`
(https://github.com/koteitan/bms-elem-pattern, CC BY-SA 4.0), which takes it from koteitan,
dh-bms-wf-formal (https://github.com/koteitan/dh-bms-wf-formal). Changes: ported to Lean 4.33.1 (no other change).
-/
/-
  Lemmas 6.9 and 6.10 of the paper (local proof of the boundary claim `(C4)`).

  `(C4)` says: for `q ≥ 1` and every row `k ≥ m₀`, every `k`-ancestor of the leading column
  `P⁽ᑫ⁾ = pos q 0` of copy `Bq` lies in `G`, i.e. is `< p`.

  The paper's argument (§6.8) is the same in both lemmas, and only the way the entry
  inequality for earlier copies is obtained differs.

  * Since `k ≥ m₀`, `anc_mono` reduces everything to the row `k = m₀`.
  * Row `m₀` is not an ascending row (`not_asc_of_ge`), so copying leaves it untouched
    (`col_pos_not_asc`): the `m₀`-entry of `D_i⁽ᵃ⁾` is `D_i(m₀)` for every copy `a`, and the
    `m₀`-entry of `P⁽ᑫ⁾` is `P(m₀)`.
  * Hence a position `y` of the interval `[p, P⁽ᑫ⁾)` is a *valid* `m₀`-candidate of `P⁽ᑫ⁾`
    only if `D_i(m₀) < P(m₀)` for the index `i` with `y = D_i⁽ᵃ⁾`.  For `i = 0` this is
    `P(m₀) < P(m₀)`, and for `i > 0` the maximality of `P` (`parent_max` applied to
    `b.hpar`, packaged as `val_c_le_of_cand_m`) gives `C(m₀) ≤ D_i(m₀)`, whereas
    `P(m₀) < C(m₀)`; so no such `y` exists.
  * With no internal valid candidate, Lemma 6.2 (2) (`parent_lt_of_no_intECand`) puts the
    direct `m₀`-parent of `P⁽ᑫ⁾` in `G`, and an ancestor is `≤` the last member of its chain,
    so it lies in `G` too.

  The step "`D_i` is a structural `m₀`-candidate of `C`" is free when `m₀ = 0`
  (every earlier column is a structural `0`-candidate) — this is Lemma 6.9.  When `m₀ > 0` it
  has to be imported from the copy: the hypothesis is `D_i⁽ᵃ⁾ ≺_{m₀-1} P⁽ᑫ⁾`, which `(C6)_{m₀-1}`
  moves down to `D_i⁽ᵃ⁾ ≺_{m₀-1} P⁽ᵃ⁺¹⁾` and `(C3)_{m₀-1}` transports to
  `D_i ≺ᴬ_{m₀-1} C`, i.e. `cand A m₀ (p+i) c` — this is Lemma 6.10.

  This file uses only the setup of `Bm4/Copy.lean` (structure, positions, entries, ascension)
  together with Lemma 2.2 and the interval lemmas of `Bm4/CopyPaper/Interval.lean`; it uses
  none of the closed forms.
-/
import Bm4.CopyPaper.Interval

open Classical

namespace BM4

variable {r : ℕ} {A : Arr r}

namespace BadRoot

variable (b : BadRoot A)

/-! ### Row `m₀` is unchanged by copying -/

/-- Row `m₀` never ascends, so every copy carries the `m₀`-entries of the bad part. -/
theorem col_pos_m (q j : ℕ) (hj : j < b.s) :
    b.tA.col (b.pos q j) b.m = A.col (b.p + j) b.m :=
  b.col_pos_not_asc hj (b.not_asc_of_ge le_rfl)

/-- The leading column of every copy carries the `m₀`-entry of `P`. -/
theorem col_lead_m (q : ℕ) : b.tA.col (b.pos q 0) b.m = A.col b.p b.m := by
  rw [b.col_pos_m q 0 b.s_pos, Nat.add_zero]

/-! ### The shared step (Lemma 6.2 (2) plus one step of the chain) -/

/-- If no position of the interval `[p, P⁽ᑫ⁾)` is a valid `k`-candidate of `P⁽ᑫ⁾`, then every
`k`-ancestor of `P⁽ᑫ⁾` lies in `G`.  The direct parent is `< p` by Lemma 6.2 (2), and an
ancestor is at most the last member of its chain. -/
theorem anc_lt_p_of_no_intECand {k q : ℕ}
    (h : ∀ y, ¬ IntECand b.tA b.p (b.pos q 0 + 1) k y (b.pos q 0)) {y : ℕ}
    (hanc : anc b.tA k y (b.pos q 0)) : y < b.p := by
  obtain ⟨u, hu, hup⟩ := anc_last_step hanc
  exact lt_of_le_of_lt (ancEq_le hu) (parent_lt_of_no_intECand (Nat.lt_succ_self _) h hup)

/-- Turning the entry inequality `P(m₀) ≤ D_i(m₀)` into the absence of internal valid
`m₀`-candidates of `P⁽ᑫ⁾`.  The inequality is only required for those columns that actually
occur as structural `m₀`-candidates, which is what the two lemmas below can supply. -/
theorem no_intECand_of_entry {q : ℕ}
    (hentry : ∀ a i, a < q → i < b.s → cand b.tA b.m (b.pos a i) (b.pos q 0) →
      A.col b.p b.m ≤ A.col (b.p + i) b.m) :
    ∀ y, ¬ IntECand b.tA b.p (b.pos q 0 + 1) b.m y (b.pos q 0) := by
  rintro y ⟨hy, -, hc, hv, -, -⟩
  have hylt : y < b.pos q 0 := cand_lt hc
  rcases b.lt_pos_cases b.s_pos hylt with h | ⟨a, i, hi, rfl, hcase⟩
  · exact absurd hy (not_le.mpr h)
  · have haq : a < q := by
      rcases hcase with h | ⟨_, h⟩
      · exact h
      · exact absurd h (Nat.not_lt_zero i)
    rw [b.col_pos_m a i hi, b.col_lead_m q] at hv
    exact absurd (hentry a i haq hi hc) (not_le.mpr hv)

/-! ### Lemma 6.9: the case `m₀ = 0` -/

/-- **Lemma 6.9**: for `m₀ = 0`, `(C4)` holds with no other claim.

Every column `D_i` with `i > 0` is a structural `0`-candidate of `C` (structural
`0`-candidacy is just "to the left"), so the maximality of `P` gives
`C(0) ≤ D_i(0)`, while `P(0) < C(0)`.  Row `0 = m₀` is unchanged by copying, so no earlier
copy — and, `P⁽ᑫ⁾` being the head of its own copy, no column of the copy itself — contains a
valid `0`-candidate of `P⁽ᑫ⁾`; hence the whole `0`-ancestor set of `P⁽ᑫ⁾` lies in `G`. -/
theorem lemma_6_9 (hm : b.m = 0) : b.Claim4 := by
  intro k hk q y _ hanc
  have hanc' : anc b.tA b.m y (b.pos q 0) := anc_mono hk hanc
  refine b.anc_lt_p_of_no_intECand (b.no_intECand_of_entry ?_) hanc'
  intro a i _ hi _
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simp
  · -- `D_i` is a structural `m₀`-candidate of `C` because `m₀ = 0`.
    have hcA : cand A b.m (b.p + i) (A.len - 1) := by
      rw [hm]; exact b.lt_c_of_lt_s hi
    have h1 := b.val_c_le_of_cand_m hi0 (b.lt_c_of_lt_s hi) hcA
    have h2 := b.val_p_lt_c
    omega

/-! ### Lemma 6.10: the case `m₀ > 0` -/

/-- `(C6)ₖ` used backwards: ancestry from copy `a` into the head of *any* later copy already
happens into the head of copy `a+1`.  (Nothing to do when the target is copy `a+1` itself.) -/
theorem anc_lead_of_anc_lead {k a i : ℕ} (h6 : b.Claim6 k) (hi : i < b.s) :
    ∀ q, q ≤ b.N → a < q → anc b.tA k (b.pos a i) (b.pos q 0) →
      anc b.tA k (b.pos a i) (b.pos (a + 1) 0) := by
  intro q
  induction q with
  | zero => intro _ h; exact absurd h (Nat.not_lt_zero a)
  | succ q ih =>
    intro hqN haq hanc
    rcases Nat.lt_or_ge a q with hlt | hge
    · exact ih (by omega) hlt ((h6 a q hlt hqN i 0 hi b.s_pos).mpr hanc)
    · have haq' : a = q := by omega
      subst haq'
      exact hanc

/-- **Lemma 6.10**: for `m₀ > 0`, `(C4)` follows from `(C3)_{m₀-1}` and `(C6)_{m₀-1}`.

A structural `m₀`-candidate of `P⁽ᑫ⁾` inside an earlier copy `Ba` (`a < q`) is a
`(m₀-1)`-ancestor `D_i⁽ᵃ⁾ ≺_{m₀-1} P⁽ᑫ⁾`.  `(C6)_{m₀-1}` walks the target down to `P⁽ᵃ⁺¹⁾`
and `(C3)_{m₀-1}` transports the result to `D_i ≺ᴬ_{m₀-1} C`, i.e. `D_i` is a structural
`m₀`-candidate of `C`.  From there the argument of Lemma 6.9 applies verbatim. -/
theorem lemma_6_10 (hm : 0 < b.m) (h3 : b.Claim3 (b.m - 1)) (h6 : b.Claim6 (b.m - 1)) :
    b.Claim4 := by
  obtain ⟨m', hm'⟩ : ∃ m', b.m = m' + 1 := ⟨b.m - 1, by omega⟩
  have hpred : b.m - 1 = m' := by omega
  rw [hpred] at h3 h6
  intro k hk q y _ hanc
  have hanc' : anc b.tA b.m y (b.pos q 0) := anc_mono hk hanc
  -- `P⁽ᑫ⁾` is a column of `Ã`, so `q` is within the paper's copy range `0,…,N`.
  have hqN : q ≤ b.N := by
    obtain ⟨u, -, hup⟩ := anc_last_step hanc'
    have hlt := parent_target_lt hup
    rw [b.tA_len] at hlt
    simp only [BadRoot.pos, Nat.add_zero] at hlt
    have hs := b.s_pos
    have hq : q < b.N + 1 := by
      by_contra hcon
      have : (b.N + 1) * b.s ≤ q * b.s := Nat.mul_le_mul_right _ (by omega)
      omega
    omega
  refine b.anc_lt_p_of_no_intECand (b.no_intECand_of_entry ?_) hanc'
  intro a i haq hi hc
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simp
  · -- `hc` is `(m₀-1)`-ancestry from the earlier copy.
    have hcanc : anc b.tA m' (b.pos a i) (b.pos q 0) := by rw [hm'] at hc; exact hc
    -- `(C6)_{m₀-1}`: move the target down to the head of copy `a+1`.
    have hstep : anc b.tA m' (b.pos a i) (b.pos (a + 1) 0) :=
      b.anc_lead_of_anc_lead h6 hi q hqN haq hcanc
    -- `(C3)_{m₀-1}`: transport to the `A`-side.
    have hbridge := h3 (a + 1) (by omega) i (Nat.succ_pos a) hi
    simp only [Nat.add_sub_cancel] at hbridge
    have hA : anc A m' (b.p + i) (A.len - 1) := hbridge.mp hstep
    have hcA : cand A b.m (b.p + i) (A.len - 1) := by rw [hm']; exact hA
    have h1 := b.val_c_le_of_cand_m hi0 (b.lt_c_of_lt_s hi) hcA
    have h2 := b.val_p_lt_c
    omega

end BadRoot

end BM4
