/-
Copied from koteitan, bms-elem-pattern, `lean/Bm4/Defs.lean`
(https://github.com/koteitan/bms-elem-pattern, CC BY-SA 4.0), which takes it from koteitan,
dh-bms-wf-formal (https://github.com/koteitan/dh-bms-wf-formal). Changes: ported to Lean 4.33.1 (no other change).
-/
/-
  BM4 (Bashicu Matrix System ver. 4): arrays, parents, ancestors, one-step expansion.
  Follows Part I–II of the paper (Definitions 1.1, 2.1, 5.1).
-/
import Mathlib

open Classical

namespace BM4

/-- An `r`-row array of length `len`. Column `i` is `col i : ℕ → ℕ` (row `k ↦` entry).
The paper's `A ∈ (ℕ^r)^ℓ` only has entries at `i ∈ Pos(A) = {0,…,len-1}` and `k < r`; here
`col` is total and the values outside that range are junk, so the parent/ancestor relations
below carry `k < r` and `i ∈ Pos(A)` as side conditions, exactly as Definition 2.1 does. -/
structure Arr (r : ℕ) where
  len : ℕ
  col : ℕ → ℕ → ℕ

variable {r : ℕ}

/-- `parentRel A cand k j i`: `j` is the `k`-parent of `i`, given the structural
candidate relation `cand` for row `k`: `j` is a valid structural candidate and every
larger structural candidate is invalid.

The last two conjuncts are Definition 2.1's side conditions `k < r` and `i ∈ Pos(A)`.  They are
placed last only so that the projections of the first four keep their names; `parent_row_lt` and
`parent_target_lt` in `Bm4/Basic.lean` read them off.  `j ∈ Pos(A)` follows from `j < i`. -/
def parentRel (A : Arr r) (cand : ℕ → ℕ → Prop) (k : ℕ) (j i : ℕ) : Prop :=
  j < i ∧ cand j i ∧ A.col j k < A.col i k ∧
    (∀ j', j < j' → j' < i → cand j' i → A.col i k ≤ A.col j' k) ∧ k < r ∧ i < A.len

/-- Strict `k`-ancestor relation `j ≺ᴬₖ i`, by recursion on the row `k`.
Structural `0`-candidates are all `j < i`; structural `(k+1)`-candidates are strict `k`-ancestors. -/
def anc (A : Arr r) : ℕ → ℕ → ℕ → Prop
  | 0 => Relation.TransGen (parentRel A (fun j i => j < i) 0)
  | k + 1 => Relation.TransGen (parentRel A (anc A k) (k + 1))

/-- Structural `k`-candidates. -/
def cand (A : Arr r) : ℕ → ℕ → ℕ → Prop
  | 0 => fun j i => j < i
  | k + 1 => anc A k

/-- `parent A k j i`: `j` is the `k`-parent of `i`. -/
def parent (A : Arr r) (k : ℕ) : ℕ → ℕ → Prop := parentRel A (cand A k) k

/-- Non-strict ancestor `j ≼ᴬₖ i`. -/
def ancEq (A : Arr r) (k j i : ℕ) : Prop := j = i ∨ anc A k j i

/-- `i` has a `k`-parent. -/
def HasParent (A : Arr r) (k i : ℕ) : Prop := ∃ j, parent A k j i

/-! ### Expansion (Definition 5.1) -/

/-- The columns of `G ⌢ B₀ ⌢ B₁ ⌢ ⋯` (infinitely many copies): `p` is the bad root,
`m` the maximal parent row of the last column `c = A.len - 1`, `s = c - p` the length of the
bad part. Position `p + q*s + j` (with `j < s`) is column `j` of copy `q`. -/
noncomputable def tildeCol (A : Arr r) (p m s : ℕ) : ℕ → ℕ → ℕ := fun i k =>
  if i < p then A.col i k
  else
    let q := (i - p) / s
    let j := (i - p) % s
    if k < m ∧ ancEq A k p (p + j) then A.col (p + j) k + q * (A.col (A.len - 1) k - A.col p k)
    else A.col (p + j) k

/-- The last column has a parent in some row `k < r`. -/
def LastHasParent (A : Arr r) : Prop :=
  0 < A.len ∧ ∃ k < r, HasParent A k (A.len - 1)

/-- Maximal parent row `m₀` of the last column (meaningful only when `LastHasParent A`). -/
noncomputable def m₀ (A : Arr r) : ℕ :=
  Nat.findGreatest (fun k => HasParent A k (A.len - 1)) (r - 1)

/-- Position `p` of the `m₀`-parent of the last column. -/
noncomputable def badRoot (A : Arr r) : ℕ :=
  if h : HasParent A (m₀ A) (A.len - 1) then Classical.choose h else 0

/-- Remove the last column. -/
def dropLast (A : Arr r) : Arr r := ⟨A.len - 1, A.col⟩

/-- `A[N]`, Definition 5.1. -/
noncomputable def expand (A : Arr r) (N : ℕ) : Arr r :=
  if A.len = 0 then A
  else if LastHasParent A then
    let p := badRoot A
    let s := A.len - 1 - p
    ⟨p + (N + 1) * s, tildeCol A p (m₀ A) s⟩
  else dropLast A

/-! ### Standard initial arrays, BM4, and the main statements -/

/-- `E_r = ((0,…,0),(1,…,1))`. -/
def E (r : ℕ) : Arr r := ⟨2, fun i _ => if i = 0 then 0 else 1⟩

/-- Arrays reachable from `E r` by finitely many expansions (this is BM4 with `r` rows). -/
inductive Reachable (r : ℕ) : Arr r → Prop
  | init : Reachable r (E r)
  | step {A : Arr r} (N : ℕ) : Reachable r A → Reachable r (expand A N)

/-- The expansion sequence `A₀ = A`, `A_{t+1} = A_t[n_t]`. -/
noncomputable def seq (A : Arr r) (n : ℕ → ℕ) : ℕ → Arr r
  | 0 => A
  | t + 1 => expand (seq A n t) (n t)

/-- An element of BM4 with `r` rows, i.e. an array reachable from `E r`. -/
def Elt (r : ℕ) : Type := {A : Arr r // Reachable r A}

/-- **Definition 1.1**: BM4 itself — the union over all row counts `r` of the arrays reachable
from `E r`.  An element carries its row count, which the array alone does not determine. -/
abbrev Elts : Type := Σ r : ℕ, Elt r

/-- One-step expansion relation on BM4 (Section 22): `A R B` iff `B ≠ ∅` and `A = B[n]`.
As in the paper, `R` is a relation *on BM4*; membership is carried by the type `Elt r`, not
written into the relation. -/
def R (r : ℕ) (A B : Elt r) : Prop :=
  0 < B.1.len ∧ ∃ n, A.1 = expand B.1 n

/-- The same relation on BM4 itself (Section 22).  Expansion does not change the number of rows,
so `A R B` forces `A` and `B` to have the same row count. -/
def R' (A B : Elts) : Prop := ∃ h : A.1 = B.1, R B.1 (h ▸ A.2) B.2

end BM4
