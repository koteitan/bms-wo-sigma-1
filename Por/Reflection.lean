/-
`listTuple`, `listTuple_lt` and `mem_listTuple` are adapted from koteitan, bms-elem-pattern,
`lean/Pattern/Reflect.lean` (https://github.com/koteitan/bms-elem-pattern, CC BY-SA 4.0).
Changes: ported to Lean 4.33.1. The proof of `reflect` is new.
-/
import Por.Relation

/-!
# Finite reflection

This file proves `reflect`, the reflection clause of the label interface of the BMS
layer (`BM4.LabelSystem.reflect`), for the relation `R`.

The proof writes the whole atomic diagram of the finite configuration as one Σ₁
formula: the parameters are the labels in `X`, the witnesses are `y₀ < ⋯ < y_{s-1}`,
and the matrix is the diagram itself. It reads the relations of all layers `k < r`
and the top predicates of the layers `m < n`. The old labels witness it below `β`.
`R n α β` reflects it below `α`, and the new witnesses have the same diagram.
-/

open Classical Cardinal Ordinal

namespace Por

/-- A finite set of ordinals as a tuple of length `X.card`. -/
noncomputable def listTuple (X : Finset Ord) : ℕ → Ord :=
  fun i => X.toList.getD i 0

theorem listTuple_lt {X : Finset Ord} {α : Ord} (hX : ∀ x ∈ X, x < α) :
    ∀ i < X.card, listTuple X i < α := by
  intro i hi
  have hi' : i < X.toList.length := by simpa using hi
  unfold listTuple
  rw [List.getD_eq_getElem _ _ hi']
  exact hX _ (Finset.mem_toList.mp (List.getElem_mem hi'))

theorem mem_listTuple {X : Finset Ord} {x : Ord} (hx : x ∈ X) :
    ∃ i < X.card, listTuple X i = x := by
  obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp (Finset.mem_toList.mpr hx)
  refine ⟨i, by simpa using hi, ?_⟩
  unfold listTuple
  rw [List.getD_eq_getElem _ _ hi, hix]

/-- Finite reflection. If `R n α β`, then every finite configuration `y` in `[α, β)` over
parameters `X < α` has a copy `y'` below `α` with the same relations to `X` and among
itself (all layers `k < r`), and with `R m (y' i) α` whenever `R m (y i) β` (`m < n`). -/
theorem reflect (r n : ℕ) (α β : Ord) (hn : n < r) (h : R n α β)
    (X : Finset Ord) (hX : ∀ x ∈ X, x < α)
    (s : ℕ) (y : ℕ → Ord) (hs : 0 < s) (hy : ∀ i j, i < j → j < s → y i < y j)
    (hyα : ∀ i, i < s → α ≤ y i) (hyβ : ∀ i, i < s → y i < β) :
    ∃ y' : ℕ → Ord,
      (∀ i j, i < j → j < s → y' i < y' j) ∧
      (∀ i, i < s → y' i < α) ∧
      (∀ x ∈ X, x < y' 0) ∧
      (∀ x ∈ X, ∀ i, i < s → ∀ k, k < r → R k x (y i) → R k x (y' i)) ∧
      (∀ i j, i < s → j < s → ∀ k, k < r → R k (y i) (y j) → R k (y' i) (y' j)) ∧
      (∀ i, i < s → ∀ m, m < n → R m (y i) β → R m (y' i) α) := by
  obtain ⟨_, e⟩ := R_iff.mp h
  have hp : ∀ i < X.card, listTuple X i < α := listTuple_lt hX
  -- the formula holds in the structure of height `β`, witnessed by `y`
  have hβ : Sat relR (topR β) (below n) β r (X.card + s)
      {diagM relR (topR β) (below n) r (X.card + s) (cat X.card (listTuple X) y)} s X.card
      (listTuple X) :=
    ⟨y, hyβ, Set.mem_singleton _⟩
  -- reflect it into the structure of height `α`
  obtain ⟨y', hy', hD⟩ := (e r (X.card + s) _ s X.card (listTuple X) le_rfl hp).mpr hβ
  have hE : diagM relR (topR α) (below n) r (X.card + s) (cat X.card (listTuple X) y') =
      diagM relR (topR β) (below n) r (X.card + s) (cat X.card (listTuple X) y) :=
    Set.mem_singleton_iff.mp hD
  refine ⟨y', ?_, hy', ?_, ?_, ?_, ?_⟩
  · intro i j hij hj
    have := lt_iff_of_diagM_eq hE (a := X.card + i) (b := X.card + j) (by omega) (by omega)
    simp only [cat_right] at this
    exact this.mpr (hy i j hij hj)
  · intro x hx
    obtain ⟨t, ht, rfl⟩ := mem_listTuple hx
    have := lt_iff_of_diagM_eq hE (a := t) (b := X.card + 0) (by omega) (by omega)
    simp only [cat_right, cat_left ht] at this
    exact this.mpr ((hX _ hx).trans_le (hyα 0 hs))
  · intro x hx i hi k hk hR
    obtain ⟨t, ht, rfl⟩ := mem_listTuple hx
    have := rel_iff_of_diagM_eq hE (j := k) (a := t) (b := X.card + i) hk (by omega) (by omega)
    simp only [cat_right, cat_left ht] at this
    exact this.mpr hR
  · intro i j hi hj k hk hR
    have := rel_iff_of_diagM_eq hE (j := k) (a := X.card + i) (b := X.card + j) hk (by omega)
      (by omega)
    simp only [cat_right] at this
    exact this.mpr hR
  · intro i hi m hm hR
    have := top_iff_of_diagM_eq hE (j := m) (a := X.card + i) (by omega) (by omega) hm
    simp only [cat_right] at this
    exact this.mpr hR

end Por
