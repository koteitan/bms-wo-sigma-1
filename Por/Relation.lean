/-
Adapted from koteitan, 1y-wo-por, `Por/Relation.lean` (https://github.com/koteitan/1y-wo-por),
whose shape (`stepF`, `RF`, `RF_eq`, `elem_stage`, `R_iff`) follows `stage`, `RFix`,
`RFix_eq`, `stage_agree`, `elem_congr`, `rel_iff` of koteitan, bms-elem-pattern,
`lean/Pattern/Basic.lean` (https://github.com/koteitan/bms-elem-pattern, CC BY-SA 4.0).
Changes: there is no root index; the recursion key is the pair (top, layer); `R_trans` is new.
-/
import Por.Formula

/-!
# The relation `R`

This file defines the label relation of the model:

  R k a b  :⟺  a < b ∧ 𝔄^a_k ≼_{Σ₁} 𝔄^b_k.

The structure `𝔄^γ_k` has domain `{x | x < γ}`, the order, all relations
`Rel_j(x,y) :⟺ R j x y`, and the top predicates `Top_j(x) :⟺ R j x γ` for `j < k`.
`R` is defined by well-founded recursion on `(top, layer)` in lexicographic order.

It proves the defining equation `R_iff`, strictness `R_lt` and transitivity `R_trans`.
-/

open Classical Cardinal Ordinal

namespace Por

/-- `(top, layer)`. -/
abbrev Idx := Ord × ℕ

abbrev ilt : Idx → Idx → Prop := Prod.Lex (· < ·) (· < ·)

theorem ilt_wf : WellFounded ilt :=
  WellFounded.prod_lex wellFounded_lt wellFounded_lt

/-- One recursion step at `t = (b, k)`: the set of `a` with `R k a b`, computed from the
values at lexicographically smaller pairs. -/
noncomputable def stepF (t : Idx) (IH : ∀ t' : Idx, ilt t' t → Ord → Prop) : Ord → Prop :=
  fun a => a < t.1 ∧
    ElemL (fun j x y => ∃ h : y < t.1, IH (y, j) (Prod.Lex.left _ _ h) x)
      (fun j x => ∃ h : a < t.1, IH (a, j) (Prod.Lex.left _ _ h) x)
      (fun j x => ∃ h : j < t.2, IH (t.1, j) (Prod.Lex.right _ h) x)
      t.2 a t.1

noncomputable def RF : Idx → Ord → Prop := ilt_wf.fix stepF

/-- `R k a b`: in layer `k`, the label `a` is stable into `b`. -/
noncomputable def R (k : ℕ) (a b : Ord) : Prop := RF (b, k) a

theorem RF_eq (t : Idx) : RF t = stepF t (fun t' _ => RF t') :=
  WellFounded.fix_eq _ _ _

/-- The true internal relations. -/
def relR : RelF := fun j x y => R j x y

/-- The true top predicates of the height-`γ` structure. -/
def topR (γ : Ord) : TopF := fun j x => R j x γ

/-- Σ₁-elementarity at layer `k` for the true structures. -/
def Elem (k : ℕ) (a b : Ord) : Prop := ElemL relR (topR a) (topR b) k a b

/-- Absoluteness of the recursion: the stage relations agree with the true ones on
everything a layer-`k` formula can read. -/
theorem elem_stage {k : ℕ} {a b : Ord} (hab : a < b) :
    ElemL (fun j x y => ∃ _ : y < b, RF (y, j) x)
      (fun j x => ∃ _ : a < b, RF (a, j) x)
      (fun j x => ∃ _ : j < k, RF (b, j) x)
      k a b ↔ Elem k a b := by
  unfold Elem ElemL
  refine forall_congr' fun m => forall_congr' fun n => forall_congr' fun D =>
    forall_congr' fun bb => forall_congr' fun r => forall_congr' fun p =>
    forall_congr' fun hn => forall_congr' fun hp => ?_
  refine iff_congr (sat_congr fun y hy => diagM_congr ?_ ?_)
    (sat_congr fun y hy => diagM_congr ?_ ?_)
  · intro j _ x _ z hz
    have hza : cat r p y z < a := cat_bound hn hp hy z hz
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hza.trans hab, h⟩⟩
  · intro j _ x _ _
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hab, h⟩⟩
  · intro j _ x _ z hz
    have hzb : cat r p y z < b := cat_bound hn (fun i hi => (hp i hi).trans hab) hy z hz
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hzb, h⟩⟩
  · intro j _ x _ hallow
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hallow, h⟩⟩

/-- The defining equation of `R`. -/
theorem R_iff {k : ℕ} {a b : Ord} : R k a b ↔ a < b ∧ Elem k a b := by
  unfold R
  rw [RF_eq]
  exact ⟨fun ⟨hab, h⟩ => ⟨hab, (elem_stage hab).mp h⟩,
    fun ⟨hab, h⟩ => ⟨hab, (elem_stage hab).mpr h⟩⟩

/-- Strictness. -/
theorem R_lt {k : ℕ} {a b : Ord} (h : R k a b) : a < b := (R_iff.mp h).1

/-- Transitivity: Σ₁-elementarity composes, because both steps use the same middle
structure `𝔄^b_k`. -/
theorem R_trans {k : ℕ} {a b c : Ord} (h₁ : R k a b) (h₂ : R k b c) : R k a c := by
  obtain ⟨hab, e₁⟩ := R_iff.mp h₁
  obtain ⟨hbc, e₂⟩ := R_iff.mp h₂
  refine R_iff.mpr ⟨hab.trans hbc, ?_⟩
  intro m n D bb r p hn hp
  exact (e₁ m n D bb r p hn hp).trans (e₂ m n D bb r p hn fun i hi => (hp i hi).trans hab)

end Por
