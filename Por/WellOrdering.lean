/-
`chain`, `chain_lt`, `terminates` and `step_wf` follow `chain`, `chain_lt`, `terminates` and
`StdR_wf` of koteitan, bms-elem-pattern, `lean/Pattern/Main.lean`
(https://github.com/koteitan/bms-elem-pattern, CC BY-SA 4.0). Changes: every array is labelled
by the chain `cC`, so the statements hold for all arrays, not only for standard ones.
-/
import Por.Model

/-!
# The final BMS theorems

This file plugs the label system of `Por.Model` into the height descent
`BM4.descent` of the BMS layer. It proves:

  * every expansion sequence of an array with `r` rows reaches the empty array,
    whatever copy counts are chosen (`terminates`);
  * one-step expansion on the arrays with `r` rows is well-founded (`step_wf`);
  * one-step expansion on BM4 with `r` rows is well-founded (`R_wf`);
  * one-step expansion on BM4, the union over all row counts, is well-founded (`R'_wf`).

The labels are countable ordinals. The only model-theoretic notion used is Σ₁-elementarity.
-/

open Classical Cardinal Ordinal

namespace Por

/-- The labels chosen along an expansion sequence with no empty term. -/
private noncomputable def chain {r : ℕ} {A : BM4.Arr r} {n : ℕ → ℕ}
    (hpos : ∀ t, 0 < (BM4.seq A n t).len) :
    ∀ t, {g : ℕ → Ord // BM4.Stable (labelSystem r) (BM4.seq A n t) g} :=
  Nat.rec ⟨cC, stable_all A⟩ fun t g =>
    ⟨_, (BM4.descent (labelSystem r) g.2 (hpos t) (n t) (hpos (t + 1))).choose_spec.1⟩

private theorem chain_lt {r : ℕ} {A : BM4.Arr r} {n : ℕ → ℕ}
    (hpos : ∀ t, 0 < (BM4.seq A n t).len) (t : ℕ) :
    BM4.ht (labelSystem r) (BM4.seq A n (t + 1)) (chain hpos (t + 1)).1
      < BM4.ht (labelSystem r) (BM4.seq A n t) (chain hpos t).1 :=
  (BM4.descent (labelSystem r) (chain hpos t).2 (hpos t) (n t) (hpos (t + 1))).choose_spec.2

/-- **Termination**: for every `r`, every expansion sequence starting from any array with
`r` rows reaches the empty array. -/
theorem terminates {r : ℕ} (A : BM4.Arr r) (n : ℕ → ℕ) : ∃ T, (BM4.seq A n T).len = 0 := by
  by_contra hcon
  simp only [not_exists] at hcon
  have hpos : ∀ t, 0 < (BM4.seq A n t).len := fun t => Nat.pos_of_ne_zero (hcon t)
  obtain ⟨β, ⟨t₀, rfl⟩, hmin⟩ :=
    (wellFounded_lt (α := Ord)).has_min
      (Set.range fun t => BM4.ht (labelSystem r) (BM4.seq A n t) (chain hpos t).1)
      ⟨_, Set.mem_range_self 0⟩
  exact hmin _ (Set.mem_range_self (t₀ + 1)) (chain_lt hpos t₀)

/-- One-step expansion on all arrays with `r` rows: `A ≺ B` iff `B` is nonempty and
`A = B[N]` for some `N`. -/
def Step (r : ℕ) (A B : BM4.Arr r) : Prop := 0 < B.len ∧ ∃ N, A = BM4.expand B N

/-- **Well-foundedness** of one-step expansion on all arrays with `r` rows. -/
theorem step_wf (r : ℕ) : WellFounded (Step r) := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  refine ⟨fun B => ?_⟩
  obtain ⟨B, hB⟩ := B
  have hstep : ∀ t, ∃ N, B (t + 1) = BM4.expand (B t) N := fun t => (hB t).2
  choose n hn using hstep
  have hBseq : ∀ t, B t = BM4.seq (B 0) n t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih => rw [hn t, ih]; rfl
  obtain ⟨T, hT⟩ := terminates (B 0) n
  have hlen : 0 < (B T).len := (hB T).1
  rw [hBseq T, hT] at hlen
  exact absurd hlen (lt_irrefl 0)

/-- **Well-foundedness** of one-step expansion on BM4 with `r` rows (the arrays reachable
from `((0,…,0),(1,…,1))`). -/
theorem R_wf (r : ℕ) : WellFounded (BM4.R r) :=
  InvImage.wf (fun A : BM4.Elt r => A.1) (step_wf r)

/-- **Well-foundedness** of one-step expansion on BM4, the union over all row counts. -/
theorem R'_wf : WellFounded BM4.R' := by
  have key : ∀ r (B : BM4.Elt r), Acc BM4.R' ⟨r, B⟩ := by
    intro r B
    refine (R_wf r).induction B (C := fun B => Acc BM4.R' ⟨r, B⟩) fun B ih => ⟨_, ?_⟩
    rintro ⟨r', A⟩ ⟨h, hR⟩
    dsimp only at h
    subst h
    exact ih A hR
  exact ⟨fun ⟨r, B⟩ => key r B⟩

end Por
