/-
Adapted from koteitan, 1y-wo-por, `Por/Closure.lean` (https://github.com/koteitan/1y-wo-por),
which adapts `Form`, `witHeight`, `witHeight_lt`, `next`, `lt_next`, `next_lt`, `wit_below`,
`tower`, `lam`, `tower_lt`, `tower_mono`, `tower_le_lam`, `lam_lt`, `lt_lam`, `exists_tower` of
koteitan, bms-elem-pattern, `lean/Pattern/Chain.lean`
(https://github.com/koteitan/bms-elem-pattern, CC BY-SA 4.0). Changes: the formulas are those
of `Por.Formula` of this repository (binary relations, unary top predicates).
-/
import Por.Relation
import Por.Omega1

/-!
# Closure points below ω₁

`Good γ` says that the structure of height `γ` is a Σ₁-elementary substructure of
the structure of height `ω₁`, in the full language with the top predicates of `ω₁`.

This file closes a countable `γ` under witnesses: `next γ` bounds a witness of every
true Σ₁ statement with parameters below `γ`, and `lam γ` is the supremum of
`γ, next γ, next (next γ), …`. It proves `lam γ < ω₁`, `γ < lam γ` and
`Good (lam γ)` (`lam_good`).
-/

open Classical Cardinal Ordinal

namespace Por

/-- `(γ; <, R, Top^{ω₁}) ≼_{Σ₁} (ω₁; <, R, Top^{ω₁})` (full language, top predicates of `ω₁`). -/
def Good (γ : Ord) : Prop :=
  ∀ (m n : ℕ) (D : Set (Diag m n)) (bb r : ℕ) (p : ℕ → Ord), n ≤ r + bb →
    (∀ i < r, p i < γ) →
    (Sat relR (topR Om) full γ m n D bb r p ↔ Sat relR (topR Om) full Om m n D bb r p)

/-- Formulas: signature bound, size, matrix, number of witnesses, number of parameters. -/
abbrev Form : Type := Σ m n : ℕ, Set (Diag m n) × ℕ × ℕ

/-- The height of a chosen witness of a true Σ₁ statement in `ω₁` (`0` otherwise). -/
noncomputable def witHeight (φ : Form) (p : ℕ → Ord) : Ord :=
  match φ with
  | ⟨m, n, D, bb, r⟩ =>
    if h : Sat relR (topR Om) full Om m n D bb r p then
      (Finset.range bb).sup fun i => Order.succ (Classical.choose h i)
    else 0

theorem witHeight_lt (φ : Form) (p : ℕ → Ord) : witHeight φ p < Om := by
  obtain ⟨m, n, D, bb, r⟩ := φ
  simp only [witHeight]
  split_ifs with h
  · refine (Finset.sup_lt_iff (lt_of_le_of_lt bot_le om_pos)).mpr fun i hi => ?_
    exact om_succ_lt ((Classical.choose_spec h).1 i (Finset.mem_range.mp hi))
  · exact om_pos

/-- One closure step. -/
noncomputable def next (γ : Ord) : Ord :=
  Order.succ (max γ (⨆ q : Form × List ℕ, witHeight q.1 (params γ q.2)))

theorem lt_next (γ : Ord) : γ < next γ :=
  lt_of_le_of_lt (le_max_left _ _) (Order.lt_succ _)

theorem next_lt {γ : Ord} (h : γ < Om) : next γ < Om :=
  om_succ_lt (max_lt h (Ordinal.iSup_lt_omega_one fun _ => witHeight_lt _ _))

theorem wit_below {γ : Ord} (hγ : γ < Om) {m n : ℕ} {D : Set (Diag m n)} {bb r : ℕ}
    {p : ℕ → Ord} (hp : ∀ i < r, p i < γ) (h : Sat relR (topR Om) full Om m n D bb r p) :
    ∃ y : ℕ → Ord, (∀ i < bb, y i < next γ) ∧
      diagM relR (topR Om) full m n (cat r p y) ∈ D := by
  obtain ⟨l, hl⟩ := exists_params hγ hp
  have hc : ∀ q : ℕ → Ord, cat r (params γ l) q = cat r p q :=
    fun q => cat_congr_left hl
  have h' : Sat relR (topR Om) full Om m n D bb r (params γ l) := by
    obtain ⟨y, hy, hD⟩ := h
    exact ⟨y, hy, by rw [hc]; exact hD⟩
  refine ⟨Classical.choose h', fun i hi => ?_, ?_⟩
  · have hw : witHeight ⟨m, n, D, bb, r⟩ (params γ l) =
        (Finset.range bb).sup fun i => Order.succ (Classical.choose h' i) := by
      simp only [witHeight, dif_pos h']
    have h1 : Order.succ (Classical.choose h' i) ≤ witHeight ⟨m, n, D, bb, r⟩ (params γ l) := by
      rw [hw]
      exact Finset.le_sup (f := fun i => Order.succ (Classical.choose h' i))
        (Finset.mem_range.mpr hi)
    have h2 : witHeight ⟨m, n, D, bb, r⟩ (params γ l) ≤
        ⨆ q : Form × List ℕ, witHeight q.1 (params γ q.2) :=
      Ordinal.le_iSup (fun q : Form × List ℕ => witHeight q.1 (params γ q.2))
        (⟨m, n, D, bb, r⟩, l)
    exact ((Order.lt_succ _).trans_le (h1.trans (h2.trans (le_max_right γ _)))).trans
      (Order.lt_succ _)
  · have := (Classical.choose_spec h').2
    rwa [hc] at this

/-- `γ, next γ, next (next γ), …` -/
noncomputable def tower (γ : Ord) : ℕ → Ord
  | 0 => γ
  | t + 1 => next (tower γ t)

noncomputable def lam (γ : Ord) : Ord := ⨆ t, tower γ t

theorem tower_lt {γ : Ord} (hγ : γ < Om) : ∀ t, tower γ t < Om
  | 0 => hγ
  | t + 1 => next_lt (tower_lt hγ t)

theorem tower_mono (γ : Ord) {t t' : ℕ} (h : t ≤ t') : tower γ t ≤ tower γ t' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (lt_next _).le

theorem tower_le_lam (γ : Ord) (t : ℕ) : tower γ t ≤ lam γ :=
  Ordinal.le_iSup (fun t => tower γ t) t

theorem lam_lt {γ : Ord} (hγ : γ < Om) : lam γ < Om :=
  Ordinal.iSup_lt_omega_one (tower_lt hγ)

theorem lt_lam (γ : Ord) : γ < lam γ :=
  (lt_next γ).trans_le (tower_le_lam γ 1)

theorem exists_tower {γ : Ord} {p : ℕ → Ord} :
    ∀ k, (∀ i < k, p i < lam γ) → ∃ t, ∀ i < k, p i < tower γ t
  | 0, _ => ⟨0, fun i hi => absurd hi (by omega)⟩
  | k + 1, hp => by
    obtain ⟨t, ht⟩ := exists_tower k fun i hi => hp i (by omega)
    obtain ⟨t', ht'⟩ := Ordinal.lt_iSup_iff.mp (hp k (by omega))
    refine ⟨max t t', fun i hi => ?_⟩
    rcases (by omega : i < k ∨ i = k) with h | rfl
    · exact (ht i h).trans_le (tower_mono γ (le_max_left _ _))
    · exact ht'.trans_le (tower_mono γ (le_max_right _ _))

/-- The closure points are Σ₁-elementary in `ω₁`. -/
theorem lam_good {γ : Ord} (hγ : γ < Om) : Good (lam γ) := by
  intro m n D bb r p _ hp
  constructor
  · rintro ⟨y, hy, hD⟩
    exact ⟨y, fun i hi => (hy i hi).trans (lam_lt hγ), hD⟩
  · intro h
    obtain ⟨t, ht⟩ := exists_tower r hp
    obtain ⟨y, hy, hD⟩ := wit_below (tower_lt hγ t) ht h
    exact ⟨y, fun i hi => (hy i hi).trans_le (tower_le_lam γ (t + 1)), hD⟩

end Por
