/-
Copied from koteitan, bms-elem-pattern, `lean/Bm4/Expand.lean`
(https://github.com/koteitan/bms-elem-pattern, CC BY-SA 4.0), which takes it from koteitan,
dh-bms-wf-formal (https://github.com/koteitan/dh-bms-wf-formal). Changes: ported to Lean 4.33.1 (no other change).
-/
/-
  Connecting `expand` (Definition 5.1) with the bad-root data used in the copy lemma.
-/
import Bm4.CopyPaper.Char

open Classical

namespace BM4

variable {r : ℕ} {A : Arr r}

theorem expand_of_len_zero (h : A.len = 0) (N : ℕ) : expand A N = A := by
  simp [expand, h]

theorem expand_of_not_lastHasParent (h0 : A.len ≠ 0) (h : ¬ LastHasParent A) (N : ℕ) :
    expand A N = dropLast A := by
  simp [expand, h0, h]

theorem m₀_hasParent (h : LastHasParent A) : HasParent A (m₀ A) (A.len - 1) := by
  obtain ⟨_, k, hk, hp⟩ := h
  exact Nat.findGreatest_spec (P := fun k => HasParent A k (A.len - 1)) (by omega) hp

theorem m₀_lt (hr : 0 < r) : m₀ A < r := by
  have : m₀ A ≤ r - 1 := Nat.findGreatest_le (P := fun k => HasParent A k (A.len - 1)) (r - 1)
  omega

theorem le_m₀ {k : ℕ} (hk : k < r) (hp : HasParent A k (A.len - 1)) : k ≤ m₀ A :=
  Nat.le_findGreatest (by omega) hp

theorem badRoot_parent (h : LastHasParent A) : parent A (m₀ A) (badRoot A) (A.len - 1) := by
  have hp := m₀_hasParent h
  unfold badRoot
  rw [dif_pos hp]
  exact Classical.choose_spec hp

/-- The data of Definition 5.1 for `A[N]`: the bad root, its row, and the number of copies. -/
noncomputable def toBadRoot (h : LastHasParent A) (N : ℕ) : BadRoot A :=
  ⟨badRoot A, m₀ A, N, badRoot_parent h⟩

theorem toBadRoot_p (h : LastHasParent A) (N : ℕ) : (toBadRoot h N).p = badRoot A := rfl
theorem toBadRoot_m (h : LastHasParent A) (N : ℕ) : (toBadRoot h N).m = m₀ A := rfl
theorem toBadRoot_N (h : LastHasParent A) (N : ℕ) : (toBadRoot h N).N = N := rfl

/-- `A[N]` **is** the array `Ã` of Definition 5.1. -/
theorem expand_eq (h : LastHasParent A) (N : ℕ) : expand A N = (toBadRoot h N).tA := by
  have h0 : A.len ≠ 0 := by have := h.1; omega
  simp only [expand, h0, if_false, h, if_true]
  rfl

theorem expand_col (h : LastHasParent A) (N : ℕ) : (expand A N).col = (toBadRoot h N).tA.col := by
  rw [expand_eq h N]

theorem expand_len (h : LastHasParent A) (N : ℕ) :
    (expand A N).len = (toBadRoot h N).p + (N + 1) * (toBadRoot h N).s := by
  rw [expand_eq h N]; rfl

/-- The last column of `A[N]` is column `s - 1` of copy `N`. -/
theorem expand_last (h : LastHasParent A) (N : ℕ) :
    (expand A N).len - 1 = (toBadRoot h N).pos N ((toBadRoot h N).s - 1) := by
  rw [expand_len h N]
  unfold BadRoot.pos
  have := (toBadRoot h N).s_pos
  rw [add_mul, one_mul]
  omega

/-- Expansion does not change the number of rows (built into `Arr r`); it changes the length. -/
theorem expand_len_pos (h : LastHasParent A) (N : ℕ) : 0 < (expand A N).len := by
  rw [expand_len h N]
  have := (toBadRoot h N).s_pos
  nlinarith

end BM4
