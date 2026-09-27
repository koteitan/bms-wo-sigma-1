/-
Copied from koteitan, bms-elem-pattern, `lean/Bm4/CopyPaper/Char.lean`
(https://github.com/koteitan/bms-elem-pattern, CC BY-SA 4.0), which takes it from koteitan,
dh-bms-wf-formal (https://github.com/koteitan/dh-bms-wf-formal). Changes: ported to Lean 4.33.1 (no other change).
-/
/-
  Existence of parents in the expanded array, derived from the paper's own six claims
  (Theorem 6.3, assembled in `Bm4/CopyPaper/Assemble.lean`).

  Proposition 7.1 needs only one consequence of the copy lemma: a column of `G ⌢ B₀ ⌢ B₁ ⌢ ⋯`
  whose entry is positive has a `k`-parent.  The two lemmas below supply it in the two shapes
  the induction of §7 produces:

  * `hasParent_tA_of_hasParent_A` — column `j` of any copy, from a `k`-parent of `D_j` in `A`,
    by (C1) when that parent lies in the bad part and by (C2) when it lies in `G`;
  * `hasParent_tA_lead` — the leading column `P⁽ᑫ⁾` of a copy `q ≥ 1` in a row `k < m₀`, by (C3)
    from the `k`-parent of `C` inside `B₀`.

  Nothing here characterises the ancestor relation of the expanded array: the paper's statement
  of the copy lemma is the six claims themselves, and the induction of §7 uses only these two
  existence facts.
-/
import Bm4.CopyPaper.Assemble

open Classical

namespace BM4

variable {r : ℕ} {A : Arr r}

namespace BadRoot

variable (b : BadRoot A)

/-- (C1) and (C2): if `D_j` has a `k`-parent in `A`, then column `j` of every copy has a
`k`-parent in the expanded array.

A parent `y` of `D_j` in `A` is either in the bad part — then (C1) turns `y ≺ᴬₖ D_j` into
`y⁽ᑫ⁾ ≺ₖ D_j⁽ᑫ⁾` — or in `G`, where (C2) does the same.  Either way `D_j⁽ᑫ⁾` has a `k`-ancestor,
and the last step of that chain is a `k`-parent. -/
theorem hasParent_tA_of_hasParent_A (k : ℕ) {q j : ℕ} (hqN : q ≤ b.N) (hj : j < b.s)
    (h : HasParent A k (b.p + j)) : HasParent b.tA k (b.pos q j) := by
  obtain ⟨y, hy⟩ := h
  have hst := b.stage3 k
  have hanc : ∃ z, anc b.tA k z (b.pos q j) := by
    rcases lt_or_ge y b.p with hlt | hge
    · exact ⟨y, (hst.2.2.1 q hqN j y hj hlt).mpr (anc_of_parent hy)⟩
    · have hyj : y < b.p + j := parent_lt hy
      refine ⟨b.pos q (y - b.p), (hst.1 q hqN (y - b.p) j (by omega) hj).mpr ?_⟩
      rw [Nat.add_sub_cancel' hge]
      exact anc_of_parent hy
  obtain ⟨z, hz⟩ := hanc
  obtain ⟨u, -, hu⟩ := anc_last_step hz
  exact ⟨u, hu⟩

/-- (C3): for `k < m₀` the leading column `P⁽ᑫ⁾` of every copy `q ≥ 1` has a `k`-parent.

`exists_parent_c` puts the `k`-parent `D_i` of `C` inside `B₀`, and (C3) turns `D_i ≺ᴬₖ C` into
`D_i⁽ᑫ⁻¹⁾ ≺ₖ P⁽ᑫ⁾`. -/
theorem hasParent_tA_lead {k q : ℕ} (hk : k < b.m) (hqN : q ≤ b.N) (hq : 0 < q) :
    HasParent b.tA k (b.pos q 0) := by
  obtain ⟨i, hi, hp⟩ := b.exists_parent_c hk.le
  have hc3 : b.Claim3 k := (b.stage1 k hk).2.1
  obtain ⟨u, -, hu⟩ := anc_last_step ((hc3 q hqN i hq hi).mpr (anc_of_parent hp))
  exact ⟨u, hu⟩

end BadRoot

end BM4
