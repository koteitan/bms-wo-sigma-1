/-
Adapted from koteitan, 1y-wo-por, `Por/Formula.lean` (https://github.com/koteitan/1y-wo-por).
Changes: the relations `Rel_j` are binary and the top predicates `Top_j` are unary (there is
no root index), and the visible top predicates are those of the layers `j < k`.
-/
import Por.Tuple

/-!
# Atomic diagrams and Σ₁ formulas

This file defines the Σ₁ formulas of the structures `𝔄^γ_k`. A formula is a set
`D` of atomic diagrams (`Diag m n`) and a number of existential witnesses.
`Sat` says that some witnesses below the height make the diagram fall in `D`.
`ElemL` is Σ₁-elementarity at layer `k`: it compares the two heights on
every formula that only reads the top predicates of the layers `j < k`.

It proves that a diagram only depends on the bits it can read (`diagM_congr`,
`sat_congr`), and that hiding bits is a function of the full diagram
(`maskD`, `sat_mask`). So a layer-restricted formula is a full formula.
-/

open Classical Cardinal Ordinal

namespace Por

/-- Atomic diagram of an `n`-tuple with signature bound `m`: the `<` bits, the binary
`Rel_j` bits and the unary `Top_j` bits for `j < m`. A finite type. -/
abbrev Diag (m n : ℕ) :=
  (Fin n → Fin n → Bool) × (Fin m → Fin n → Fin n → Bool) × (Fin m → Fin n → Bool)

/-- Internal relations `Rel_j(x,y)`. -/
abbrev RelF := ℕ → Ord → Ord → Prop
/-- Top predicates `Top_j(x)`. -/
abbrev TopF := ℕ → Ord → Prop

/-- The atomic diagram of `v` (first `n` entries). The bit `Top_j(v a)` is only read
when `allow j`; otherwise it is `false`. -/
noncomputable def diagM (rel : RelF) (top : TopF) (allow : ℕ → Prop) (m n : ℕ)
    (v : ℕ → Ord) : Diag m n :=
  (fun a b => decide (v a < v b),
   fun j a b => decide (rel j (v a) (v b)),
   fun j a => decide (allow j ∧ top j (v a)))

/-- `∃ y₀ … y_{bb-1} < M, D(diag(p₀ … p_{r-1}, y₀ … y_{bb-1}))`: a Σ₁ formula with `r`
parameters, evaluated in the structure of height `M`. -/
def Sat (rel : RelF) (top : TopF) (allow : ℕ → Prop) (M : Ord) (m n : ℕ)
    (D : Set (Diag m n)) (bb r : ℕ) (p : ℕ → Ord) : Prop :=
  ∃ y : ℕ → Ord, (∀ i < bb, y i < M) ∧ diagM rel top allow m n (cat r p y) ∈ D

/-- Every top bit is visible. -/
def full : ℕ → Prop := fun _ => True

/-- Visible top bits at layer `k`: the layers `j < k`. -/
def below (k : ℕ) : ℕ → Prop := fun j => j < k

/-- Σ₁-elementarity at layer `k` between the height-`a` structure (top predicates
`topA`) and the height-`b` structure (top predicates `topB`). -/
def ElemL (rel : RelF) (topA topB : TopF) (k : ℕ) (a b : Ord) : Prop :=
  ∀ (m n : ℕ) (D : Set (Diag m n)) (bb r : ℕ) (p : ℕ → Ord),
    n ≤ r + bb → (∀ i < r, p i < a) →
    (Sat rel topA (below k) a m n D bb r p ↔ Sat rel topB (below k) b m n D bb r p)

/-- The diagram only reads the visible bits. -/
theorem diagM_congr {rel rel' : RelF} {top top' : TopF} {allow : ℕ → Prop} {m n : ℕ}
    {v : ℕ → Ord}
    (hrel : ∀ j < m, ∀ a < n, ∀ b < n, (rel j (v a) (v b) ↔ rel' j (v a) (v b)))
    (htop : ∀ j < m, ∀ a < n, allow j → (top j (v a) ↔ top' j (v a))) :
    diagM rel top allow m n v = diagM rel' top' allow m n v := by
  unfold diagM
  congr 1
  congr 1
  · funext j a b
    exact decide_eq_decide.mpr (hrel j j.2 a a.2 b b.2)
  · funext j a
    exact decide_eq_decide.mpr (and_congr_right fun h => htop j j.2 a a.2 h)

theorem sat_congr {rel rel' : RelF} {top top' : TopF} {allow : ℕ → Prop} {M : Ord}
    {m n : ℕ} {D : Set (Diag m n)} {bb r : ℕ} {p : ℕ → Ord}
    (h : ∀ y : ℕ → Ord, (∀ i < bb, y i < M) →
      diagM rel top allow m n (cat r p y) = diagM rel' top' allow m n (cat r p y)) :
    Sat rel top allow M m n D bb r p ↔ Sat rel' top' allow M m n D bb r p := by
  unfold Sat
  refine exists_congr fun y => and_congr_right fun hy => ?_
  rw [h y hy]

/-- Hiding bits is a function of the full diagram. -/
noncomputable def maskD {m n : ℕ} (allow : ℕ → Prop) (d : Diag m n) : Diag m n :=
  (d.1, d.2.1, fun j a => decide (allow j) && d.2.2 j a)

theorem diagM_mask (rel : RelF) (top : TopF) (allow : ℕ → Prop) (m n : ℕ)
    (v : ℕ → Ord) :
    diagM rel top allow m n v = maskD allow (diagM rel top full m n v) := by
  unfold diagM maskD full
  congr 1
  congr 1
  funext j a
  by_cases h : allow j <;> simp [h]

/-- A layer-restricted formula is a full formula with a masked matrix. -/
theorem sat_mask {rel : RelF} {top : TopF} {allow : ℕ → Prop} {M : Ord} {m n : ℕ}
    {D : Set (Diag m n)} {bb r : ℕ} {p : ℕ → Ord} :
    Sat rel top allow M m n D bb r p ↔ Sat rel top full M m n (maskD allow ⁻¹' D) bb r p := by
  unfold Sat
  simp only [Set.mem_preimage, ← diagM_mask]

/-! ## Reading bits of equal diagrams -/

theorem lt_iff_of_diagM_eq {rel : RelF} {top top' : TopF} {allow : ℕ → Prop} {m n : ℕ}
    {v w : ℕ → Ord} (h : diagM rel top allow m n v = diagM rel top' allow m n w)
    {a b : ℕ} (ha : a < n) (hb : b < n) : (v a < v b ↔ w a < w b) := by
  have := congrFun (congrFun (congrArg Prod.fst h) ⟨a, ha⟩) ⟨b, hb⟩
  simpa [diagM] using this

theorem rel_iff_of_diagM_eq {rel : RelF} {top top' : TopF} {allow : ℕ → Prop} {m n : ℕ}
    {v w : ℕ → Ord} (h : diagM rel top allow m n v = diagM rel top' allow m n w)
    {j a b : ℕ} (hj : j < m) (ha : a < n) (hb : b < n) :
    (rel j (v a) (v b) ↔ rel j (w a) (w b)) := by
  have := congrFun (congrFun (congrFun (congrArg (fun d : Diag m n => d.2.1) h) ⟨j, hj⟩)
    ⟨a, ha⟩) ⟨b, hb⟩
  simpa [diagM] using this

theorem top_iff_of_diagM_eq {rel : RelF} {top top' : TopF} {allow : ℕ → Prop} {m n : ℕ}
    {v w : ℕ → Ord} (h : diagM rel top allow m n v = diagM rel top' allow m n w)
    {j a : ℕ} (hj : j < m) (ha : a < n) (hallow : allow j) :
    (top j (v a) ↔ top' j (w a)) := by
  have := congrFun (congrFun (congrArg (fun d : Diag m n => d.2.2) h) ⟨j, hj⟩) ⟨a, ha⟩
  simpa [diagM, hallow] using this

end Por
