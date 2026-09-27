/-
Copied from koteitan, bms-elem-pattern, `lean/Bm4/Copy.lean`
(https://github.com/koteitan/bms-elem-pattern, CC BY-SA 4.0), which takes it from koteitan,
dh-bms-wf-formal (https://github.com/koteitan/dh-bms-wf-formal). Changes: ported to Lean 4.33.1; the proof of `col_pos` splits the `if` by hand; the file comment no longer mentions the closed-form variant, which is not included.
-/
/-
  Setup for the copy lemma (Theorem 6.3).

  Given a bad root `p` which is the `m`-parent of the last column `c`, the array
  `G ⌢ B₀ ⌢ B₁ ⌢ ⋯` has columns `tildeCol A p m s`. This file fixes that data (`BadRoot`),
  its positions `pos q j`, and its entries.

  The proof of the copy lemma itself lives in `Bm4/CopyPaper/`, which follows the paper
  (six claims (C1)–(C6) and the assembly of Proposition 6.11).
-/
import Bm4.Basic

open Classical

namespace BM4

variable {r : ℕ}

/-- Data of Definition 5.1: `p` is the `m`-parent of the last column `c = A.len - 1`, and
`N + 1` is the number of copies of the bad part.
No maximality of `m` is needed for the structural copy lemma. -/
structure BadRoot (A : Arr r) where
  p : ℕ
  m : ℕ
  N : ℕ
  hpar : parent A m p (A.len - 1)

namespace BadRoot

variable {A : Arr r} (b : BadRoot A)

/-- Length of the bad part `B₀ = (A_p, …, A_{c-1})`. -/
def s : ℕ := A.len - 1 - b.p

/-- Position of column `j` of copy `q`. -/
def pos (q j : ℕ) : ℕ := b.p + q * b.s + j

/-- `Δ_k = C(k) - P(k)`. -/
def Δ (k : ℕ) : ℕ := A.col (A.len - 1) k - A.col b.p k

/-- Column `j` of the bad part ascends in row `k`. -/
def Asc (k j : ℕ) : Prop := k < b.m ∧ ancEq A k b.p (b.p + j)

/-- `Ã = A[N] = G ⌢ B₀ ⌢ ⋯ ⌢ B_N`, of length `p + (N+1)s` (Definition 5.1).
The column function is defined at every position; only the positions below the length are
columns of `Ã`. -/
noncomputable def tA : Arr r := ⟨b.p + (b.N + 1) * b.s, tildeCol A b.p b.m b.s⟩

theorem tA_len : b.tA.len = b.p + (b.N + 1) * b.s := rfl

theorem p_lt_c : b.p < A.len - 1 := parent_lt b.hpar

theorem s_pos : 0 < b.s := Nat.sub_pos_of_lt b.p_lt_c

theorem p_add_s : b.p + b.s = A.len - 1 := Nat.add_sub_cancel' b.p_lt_c.le

theorem val_p_lt_c : A.col b.p b.m < A.col (A.len - 1) b.m := parent_val_lt b.hpar

theorem anc_p_c {k : ℕ} (hk : k ≤ b.m) : anc A k b.p (A.len - 1) :=
  anc_mono hk (anc_of_parent b.hpar)

/-! ### Positions -/

theorem pos_zero_zero : b.pos 0 0 = b.p := by simp [pos]

theorem pos_zero (j : ℕ) : b.pos 0 j = b.p + j := by simp [pos]

theorem p_le_pos (q j : ℕ) : b.p ≤ b.pos q j := by unfold pos; omega

theorem pos_lt_pos_same {q i j : ℕ} (h : i < j) : b.pos q i < b.pos q j := by unfold pos; omega

theorem pos_lt_pos_same_iff {q i j : ℕ} : b.pos q i < b.pos q j ↔ i < j := by unfold pos; omega

theorem pos_lt_pos_of_lt {a q i j : ℕ} (ha : a < q) (hi : i < b.s) : b.pos a i < b.pos q j := by
  unfold pos
  have : (a + 1) * b.s ≤ q * b.s := Nat.mul_le_mul_right _ ha
  nlinarith

theorem pos_inj {a q i j : ℕ} (hi : i < b.s) (hj : j < b.s) (h : b.pos a i = b.pos q j) :
    a = q ∧ i = j := by
  unfold pos at h
  have h' : a * b.s + i = q * b.s + j := by omega
  rcases lt_trichotomy a q with hlt | heq | hgt
  · exact absurd h' (by
      have : (a + 1) * b.s ≤ q * b.s := Nat.mul_le_mul_right _ hlt
      nlinarith)
  · subst heq; omega
  · exact absurd h' (by
      have : (q + 1) * b.s ≤ a * b.s := Nat.mul_le_mul_right _ hgt
      nlinarith)

/-- Every position `≥ p` is `pos q j` for a unique `q` and `j < s`. -/
theorem exists_pos {x : ℕ} (hx : b.p ≤ x) : ∃ q j, j < b.s ∧ x = b.pos q j := by
  refine ⟨(x - b.p) / b.s, (x - b.p) % b.s, Nat.mod_lt _ b.s_pos, ?_⟩
  unfold pos
  have := Nat.div_add_mod' (x - b.p) b.s
  omega

theorem pos_lt_c_iff {q j : ℕ} (hj : j < b.s) : b.pos q j < A.len - 1 ↔ q = 0 := by
  unfold pos
  constructor
  · intro h
    by_contra hq
    have : 1 * b.s ≤ q * b.s := Nat.mul_le_mul_right _ (Nat.pos_of_ne_zero hq)
    have := b.p_add_s
    omega
  · rintro rfl
    have := b.p_add_s
    omega

/-! ### Entries of the expanded array -/

theorem col_lt {i k : ℕ} (hi : i < b.p) : b.tA.col i k = A.col i k := by
  simp [tA, tildeCol, hi]

theorem col_pos {q j : ℕ} (hj : j < b.s) (k : ℕ) :
    b.tA.col (b.pos q j) k =
      if b.Asc k j then A.col (b.p + j) k + q * b.Δ k else A.col (b.p + j) k := by
  have hnot : ¬ b.pos q j < b.p := not_lt.mpr (b.p_le_pos q j)
  have h1 : b.pos q j - b.p = j + b.s * q := by unfold pos; ring_nf; omega
  have hdiv : (j + b.s * q) / b.s = q := by
    rw [Nat.add_mul_div_left _ _ b.s_pos, Nat.div_eq_of_lt hj, zero_add]
  have hmod : (j + b.s * q) % b.s = j := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  by_cases hc : b.Asc k j
  · rw [if_pos hc]
    have hc' : k < b.m ∧ ancEq A k b.p (b.p + j) := hc
    simp only [tA, tildeCol, hnot, if_false, h1, hdiv, hmod, Δ]
    rw [if_pos hc']
  · rw [if_neg hc]
    have hc' : ¬ (k < b.m ∧ ancEq A k b.p (b.p + j)) := hc
    simp only [tA, tildeCol, hnot, if_false, h1, hdiv, hmod]
    rw [if_neg hc']

theorem col_pos_asc {q j k : ℕ} (hj : j < b.s) (h : b.Asc k j) :
    b.tA.col (b.pos q j) k = A.col (b.p + j) k + q * b.Δ k := by
  rw [col_pos b hj, if_pos h]

theorem col_pos_not_asc {q j k : ℕ} (hj : j < b.s) (h : ¬ b.Asc k j) :
    b.tA.col (b.pos q j) k = A.col (b.p + j) k := by
  rw [col_pos b hj, if_neg h]

/-- Positions `< c` keep their entries. -/
theorem col_prefix {x k : ℕ} (hx : x < A.len - 1) : b.tA.col x k = A.col x k := by
  rcases lt_or_ge x b.p with h | h
  · exact b.col_lt h
  · obtain ⟨q, j, hj, rfl⟩ := b.exists_pos h
    have hq : q = 0 := (b.pos_lt_c_iff hj).mp hx
    subst hq
    rw [col_pos b hj]
    simp [pos_zero]

/-- Positions of the common prefix `G ⌢ B₀` are positions of `Ã`. -/
theorem lt_tA_len_of_lt_c {x : ℕ} (hx : x < A.len - 1) : x < b.tA.len := by
  have h1 := b.p_add_s
  have h2 : 1 * b.s ≤ (b.N + 1) * b.s := Nat.mul_le_mul_right _ (by omega)
  simp only [tA]
  omega

/-- `D_j⁽ᑫ⁾` is a column of `Ã` exactly when `q ≤ N` and `j < s`. -/
theorem pos_lt_tA_len {q j : ℕ} (hq : q ≤ b.N) (hj : j < b.s) : b.pos q j < b.tA.len := by
  have : (q + 1) * b.s ≤ (b.N + 1) * b.s := Nat.mul_le_mul_right _ (by omega)
  simp only [tA, pos]
  nlinarith

/-- Conversely, a position of `Ã` lies in one of the copies `B₀,…,B_N`. -/
theorem le_N_of_pos_lt_tA_len {q j : ℕ} (h : b.pos q j < b.tA.len) : q ≤ b.N := by
  by_contra hcon
  push Not at hcon
  have hle : (b.N + 1) * b.s ≤ q * b.s := Nat.mul_le_mul_right _ hcon
  simp only [tA, pos] at h
  omega

/-- Prefix invariance for the expanded array (Lemma 3.1). -/
theorem anc_tA_prefix {x : ℕ} (hx : x < A.len - 1) (k y : ℕ) :
    anc b.tA k y x ↔ anc A k y x :=
  anc_congr_iff (fun x' hx' k' => b.col_prefix (lt_of_le_of_lt hx' hx))
    (b.lt_tA_len_of_lt_c hx) (by omega) y

theorem parent_tA_prefix {x : ℕ} (hx : x < A.len - 1) (k y : ℕ) :
    parent b.tA k y x ↔ parent A k y x :=
  parent_congr_iff (fun x' hx' k' => b.col_prefix (lt_of_le_of_lt hx' hx))
    (b.lt_tA_len_of_lt_c hx) (by omega) y

theorem cand_tA_prefix {x : ℕ} (hx : x < A.len - 1) (k y : ℕ) :
    cand b.tA k y x ↔ cand A k y x :=
  cand_congr_iff (fun x' hx' k' => b.col_prefix (lt_of_le_of_lt hx' hx))
    (b.lt_tA_len_of_lt_c hx) (by omega) y

/-! ### Ascension and convexity -/

/-- The leading column always ascends in rows `k < m`. -/
theorem asc_zero {k : ℕ} (hk : k < b.m) : b.Asc k 0 := ⟨hk, by simp [ancEq]⟩

theorem not_asc_of_ge {k j : ℕ} (hk : b.m ≤ k) : ¬ b.Asc k j := fun h => absurd h.1 (not_lt.mpr hk)

/-- If `D_j` ascends in row `k` and `D_i` is a structural `k`-candidate of `D_j`, then `D_i`
ascends in row `k` (Lemma 4.1 applied as in Lemma 6.4, Case 1). -/
theorem asc_of_cand {k i j : ℕ} (hasc : b.Asc k j) (hc : cand A k (b.p + i) (b.p + j)) :
    b.Asc k i := by
  refine ⟨hasc.1, ?_⟩
  have hij : b.p + i < b.p + j := cand_lt hc
  have hanc : anc A k b.p (b.p + j) := anc_of_ancEq_of_ne hasc.2 (by omega)
  exact convex_cand hanc (Nat.le_add_right _ _) (Or.inr hc)

/-- If `D_i` is a structural `k`-candidate of `C` and `k < m`, then `D_i` ascends in row `k`. -/
theorem asc_of_cand_c {k i : ℕ} (hk : k < b.m) (hc : cand A k (b.p + i) (A.len - 1)) :
    b.Asc k i :=
  ⟨hk, convex_cand (b.anc_p_c hk.le) (Nat.le_add_right _ _) (Or.inr hc)⟩

/-- `D_i ≼ₖ C` (non-strict) and `k < m` also give ascension. -/
theorem asc_of_ancEq_c {k i : ℕ} (hk : k < b.m) (hc : ancEq A k (b.p + i) (A.len - 1)) :
    b.Asc k i :=
  ⟨hk, convex_cand (b.anc_p_c hk.le) (Nat.le_add_right _ _) (by
    rcases hc with h | h
    · exact Or.inl h
    · exact Or.inr (cand_of_anc h))⟩

/-- Ascending columns have `P(k) ≤ D_i(k)`. -/
theorem val_p_le_of_asc {k i : ℕ} (h : b.Asc k i) : A.col b.p k ≤ A.col (b.p + i) k := by
  rcases h.2 with h' | h'
  · rw [← h']
  · exact (anc_val_lt h').le

/-- Columns of the bad part that are structural `m`-candidates of `C` other than `P` have
`m`-entry `≥ C(m)` (Lemma 6.9 / 6.10). -/
theorem val_c_le_of_cand_m {i : ℕ} (hi : 0 < i) (hlt : b.p + i < A.len - 1)
    (hc : cand A b.m (b.p + i) (A.len - 1)) : A.col (A.len - 1) b.m ≤ A.col (b.p + i) b.m :=
  parent_max b.hpar (by omega) hlt hc

/-! ### More on positions -/

/-- Any `y < pos q j` is in `G`, in an earlier copy, or earlier in the same copy. -/
theorem lt_pos_cases {q j y : ℕ} (hj : j < b.s) (hy : y < b.pos q j) :
    y < b.p ∨ ∃ a i, i < b.s ∧ y = b.pos a i ∧ (a < q ∨ (a = q ∧ i < j)) := by
  rcases lt_or_ge y b.p with h | h
  · exact Or.inl h
  · obtain ⟨a, i, hi, rfl⟩ := b.exists_pos h
    refine Or.inr ⟨a, i, hi, rfl, ?_⟩
    rcases lt_trichotomy a q with hlt | heq | hgt
    · exact Or.inl hlt
    · subst heq; exact Or.inr ⟨rfl, (b.pos_lt_pos_same_iff).mp hy⟩
    · exact absurd hy (not_lt.mpr (b.pos_lt_pos_of_lt hgt hj).le)

/-- Position of a `k`-ancestor of `D_j⁽ᑫ⁾` in the expanded array: it lies in the common prefix
`G`, in a strictly earlier copy, or strictly earlier in the same copy.  Only `y ≺ₖ x → y < x`
is used, so this is the positional content of `lt_pos_cases`; it is the case split the paper
performs in Remark 19.2. -/
theorem anc_tA_cases (k : ℕ) {q j y : ℕ} (hj : j < b.s) (h : anc b.tA k y (b.pos q j)) :
    y < b.p ∨ (∃ a < q, ∃ i < b.s, y = b.pos a i) ∨ ∃ i < j, y = b.pos q i := by
  rcases b.lt_pos_cases hj (anc_lt h) with hy | ⟨a, i, hi, rfl, hcase⟩
  · exact Or.inl hy
  · rcases hcase with hlt | ⟨rfl, hij⟩
    · exact Or.inr (Or.inl ⟨a, hlt, i, hi, rfl⟩)
    · exact Or.inr (Or.inr ⟨i, hij, rfl⟩)

/-- Positions strictly between `pos q i` and `pos q j` (with `j < s`) are `pos q i'`, `i < i' < j`. -/
theorem between_same_copy {q i j y : ℕ} (hj : j < b.s) (h1 : b.pos q i < y) (h2 : y < b.pos q j) :
    ∃ i', y = b.pos q i' ∧ i < i' ∧ i' < j := by
  have hy : b.p ≤ y := (b.p_le_pos q i).trans h1.le
  obtain ⟨a, i', hi', rfl⟩ := b.exists_pos hy
  have hij : i < j := by
    have := h1.trans h2
    exact (b.pos_lt_pos_same_iff).mp this
  have hi : i < b.s := hij.trans hj
  rcases lt_trichotomy a q with hlt | heq | hgt
  · exact absurd h1 (not_lt.mpr (b.pos_lt_pos_of_lt hlt hi').le)
  · subst heq
    exact ⟨i', rfl, (b.pos_lt_pos_same_iff).mp h1, (b.pos_lt_pos_same_iff).mp h2⟩
  · exact absurd h2 (not_lt.mpr (b.pos_lt_pos_of_lt hgt hj).le)

/-- Positions strictly between `pos (q-1) i` and `pos q 0` (`q > 0`) are `pos (q-1) i'`, `i < i' < s`. -/
theorem between_prev_copy {q i y : ℕ} (hq : 0 < q) (h1 : b.pos (q - 1) i < y) (h2 : y < b.pos q 0) :
    ∃ i', y = b.pos (q - 1) i' ∧ i < i' ∧ i' < b.s := by
  have hy : b.p ≤ y := (b.p_le_pos _ i).trans h1.le
  obtain ⟨a, i', hi', rfl⟩ := b.exists_pos hy
  rcases lt_trichotomy a (q - 1) with hlt | heq | hgt
  · exact absurd h1 (not_lt.mpr (b.pos_lt_pos_of_lt hlt hi').le)
  · subst heq
    exact ⟨i', rfl, (b.pos_lt_pos_same_iff).mp h1, hi'⟩
  · have hqa : q ≤ a := by omega
    exact absurd h2 (not_lt.mpr (by
      unfold pos
      have : q * b.s ≤ a * b.s := Nat.mul_le_mul_right _ hqa
      omega))

theorem pos_eq_add (q i : ℕ) : b.pos q i = (b.p + i) + q * b.s := by unfold pos; ring

theorem lt_c_of_lt_s {i : ℕ} (hi : i < b.s) : b.p + i < A.len - 1 := by
  have := b.p_add_s; omega

theorem lt_s_of_lt_c {i : ℕ} (hi : b.p + i < A.len - 1) : i < b.s := by
  have := b.p_add_s; omega

/-! ### Values -/

theorem val_p_add_Δ {k : ℕ} (hk : k ≤ b.m) : A.col b.p k + b.Δ k = A.col (A.len - 1) k := by
  unfold Δ
  have := anc_val_lt (b.anc_p_c hk)
  omega

/-- Columns of earlier copies that are structural `k`-candidates of `C` (with `k ≤ m`) have
`k`-entry at least `P(k)` in the expanded array. -/
theorem val_p_le_earlier {k a i : ℕ} (hk : k ≤ b.m) (hi : i < b.s)
    (hc : cand A k (b.p + i) (A.len - 1)) : A.col b.p k ≤ b.tA.col (b.pos a i) k := by
  rcases lt_or_eq_of_le hk with hlt | heq
  · have hasc : b.Asc k i := b.asc_of_cand_c hlt hc
    rw [b.col_pos_asc hi hasc]
    exact (b.val_p_le_of_asc hasc).trans (Nat.le_add_right _ _)
  · subst heq
    rw [b.col_pos_not_asc hi (b.not_asc_of_ge le_rfl)]
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp
    · exact (b.val_p_lt_c.le).trans (b.val_c_le_of_cand_m hi0 (b.lt_c_of_lt_s hi) hc)

/-- `P` is a structural `k`-candidate of `D_j` whenever `j > 0` and `pos q j` has an earlier-copy
candidate, i.e. `CandForm` supplies `ancEq (k-1) p (p+j)`; here in the form needed later. -/
theorem cand_p_of_ancEq_pred {k j : ℕ} (hj : 0 < j)
    (h : k = 0 ∨ ∃ k', k = k' + 1 ∧ ancEq A k' b.p (b.p + j)) : cand A k b.p (b.p + j) := by
  rcases h with rfl | ⟨k', rfl, h⟩
  · exact (Nat.lt_add_of_pos_right hj)
  · exact anc_of_ancEq_of_ne h (by omega)

/-- If the parent of `D_j` (in `A`) lies in `G`, or `j = 0` with `q = 0`, the target entry is
unchanged. -/
theorem target_unchanged {k q j y : ℕ} (hj : j < b.s) (hex : ¬ (j = 0 ∧ 0 < q ∧ k < b.m))
    (hy : y < b.p) (hp : parent A k y (b.p + j)) :
    b.tA.col (b.pos q j) k = A.col (b.p + j) k := by
  rw [b.col_pos hj]
  split_ifs with hasc
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · have hq : q = 0 := by
        by_contra hq
        exact hex ⟨rfl, Nat.pos_of_ne_zero hq, hasc.1⟩
      subst hq; simp
    · exfalso
      have hanc : anc A k b.p (b.p + j) := anc_of_ancEq_of_ne hasc.2 (by omega)
      have := parent_max hp hy (by omega) (cand_of_anc hanc)
      exact absurd (anc_val_lt hanc) (not_lt.mpr this)
  · rfl

/-- A `k`-parent of the last column `c`, for any row `k ≤ m`, sits inside `B₀`. -/
theorem exists_parent_c {k : ℕ} (hk : k ≤ b.m) :
    ∃ i, i < b.s ∧ parent A k (b.p + i) (A.len - 1) := by
  obtain ⟨b', hb', hpar⟩ := anc_last_step (b.anc_p_c hk)
  have hpb : b.p ≤ b' := ancEq_le hb'
  refine ⟨b' - b.p, ?_, ?_⟩
  · have := parent_lt hpar; have := b.p_add_s; omega
  · rwa [Nat.add_sub_cancel' hpb]

end BadRoot

end BM4
