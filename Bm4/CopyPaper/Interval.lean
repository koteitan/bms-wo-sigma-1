/-
Copied from koteitan, bms-elem-pattern, `lean/Bm4/CopyPaper/Interval.lean`
(https://github.com/koteitan/bms-elem-pattern, CC BY-SA 4.0), which takes it from koteitan,
dh-bms-wf-formal (https://github.com/koteitan/dh-bms-wf-formal). Changes: ported to Lean 4.33.1 (no other change).
-/
/-
  The paper's route to the copy lemma (§6.1–6.9).

  This file provides the shared interface: interval-internal parents (Definition 6.1 and
  Lemma 6.2) and the six claims (C1)–(C6) of Theorem 6.3 as named predicates, so that each
  local lemma of §6.3–6.8 can be stated with exactly the hypotheses the paper gives it.

  Only the bad-root setup of `Bm4/Copy.lean` is used here — the shortcut proof of the same
  theorem lives on the branch `feature/closed-form` and is not part of this route.
-/
import Bm4.Copy

open Classical

namespace BM4

variable {r : ℕ} {A : Arr r}

/-! ### Interval-internal candidates and parents (Definition 6.1)

An interval `I` of consecutive positions is the half-open range `[lo, hi)`, so that the paper's
`X ∈ I` reads `lo ≤ X ∧ X < hi`.  Definition 6.1 names two sets of positions of `I`: the
structural `k`-candidates `Candᴵₖ(X)` and the valid ones `ECandᴵₖ(X)`; when the latter is
nonempty its last position is the internal `k`-parent `IntParᴵₖ(X)`.

For a target `X ∈ I` the right end removes nothing, because a structural candidate of `X` lies
left of `X`: `intCand_iff_succ`, `intECand_iff_succ` and `intPar_iff_succ` below say that every
interval `[lo, hi)` with `i < hi` gives the same three notions as `[lo, i + 1)`.  This is why
the local lemmas of §6.3–6.8 may take `hi := i + 1`. -/

/-- `Candᴵₖ(i)` for `I = [lo, hi)`: `j` is an internal structural `k`-candidate of `i`.
Validity is *not* required here — Definition 6.1 keeps the two sets apart, and (6.5) in the
proof of `(C3)ₖ` is a statement about this one. -/
def IntCand (A : Arr r) (lo hi k j i : ℕ) : Prop :=
  lo ≤ j ∧ j < hi ∧ cand A k j i

/-- `ECandᴵₖ(i)` for `I = [lo, hi)`: `j` is an internal valid `k`-candidate of `i`.
The last two conjuncts are Definition 2.1's side conditions `k < r` and `i ∈ Pos(A)`, which
Definition 6.1 inherits by taking `X ∈ I ⊆ Pos(A)`; they are placed last so that the first
four keep their projection names. -/
def IntECand (A : Arr r) (lo hi k j i : ℕ) : Prop :=
  lo ≤ j ∧ j < hi ∧ cand A k j i ∧ A.col j k < A.col i k ∧ k < r ∧ i < A.len

/-- `ECandᴵₖ(i) ⊆ Candᴵₖ(i)`. -/
theorem intCand_of_intECand {lo hi k j i : ℕ} (h : IntECand A lo hi k j i) :
    IntCand A lo hi k j i :=
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- What separates the two sets of Definition 6.1: validity, together with Definition 2.1's
side conditions. -/
theorem intECand_iff {lo hi k j i : ℕ} :
    IntECand A lo hi k j i ↔
      IntCand A lo hi k j i ∧ A.col j k < A.col i k ∧ k < r ∧ i < A.len :=
  ⟨fun h => ⟨intCand_of_intECand h, h.2.2.2⟩, fun h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩⟩

/-- The right end of the interval is immaterial for a target inside it. -/
theorem intCand_iff_succ {lo hi k j i : ℕ} (hi' : i < hi) :
    IntCand A lo hi k j i ↔ IntCand A lo (i + 1) k j i :=
  ⟨fun h => ⟨h.1, by have := cand_lt h.2.2; omega, h.2.2⟩,
   fun h => ⟨h.1, by have := cand_lt h.2.2; omega, h.2.2⟩⟩

/-- The right end of the interval is immaterial for a target inside it. -/
theorem intECand_iff_succ {lo hi k j i : ℕ} (hi' : i < hi) :
    IntECand A lo hi k j i ↔ IntECand A lo (i + 1) k j i :=
  ⟨fun h => ⟨h.1, by have := cand_lt h.2.2.1; omega, h.2.2⟩,
   fun h => ⟨h.1, by have := cand_lt h.2.2.1; omega, h.2.2⟩⟩

/-- Lemma 6.2 (1): if some internal valid candidate exists, the direct `k`-parent lies at or
right of the left end of the interval. (Together with the maximality built into `parent`, this
identifies it with the internal parent.) -/
theorem le_of_parent_of_intECand {lo hi k j i y : ℕ} (hj : IntECand A lo hi k j i)
    (hp : parent A k y i) : lo ≤ y := by
  rcases le_or_gt j y with h | h
  · exact hj.1.trans h
  · exact absurd hj.2.2.2.1 (not_lt.mpr (parent_max hp h (cand_lt hj.2.2.1) hj.2.2.1))

/-- Lemma 6.2 (1), existence half: an internal valid candidate produces a parent. -/
theorem exists_parent_of_intECand {lo hi k j i : ℕ} (hj : IntECand A lo hi k j i) :
    ∃ y, parent A k y i ∧ lo ≤ y := by
  obtain ⟨y, hy⟩ := exists_parent_of_valid hj.2.2.2.2.1 hj.2.2.2.2.2 hj.2.2.1 hj.2.2.2.1
  exact ⟨y, hy, le_of_parent_of_intECand hj hy⟩

/-- Lemma 6.2 (1), membership half: for a target `i ∈ I`, that parent belongs to `I`. -/
theorem parent_mem_of_intECand {lo hi k j i : ℕ} (hi' : i < hi) (hj : IntECand A lo hi k j i) :
    ∃ y, parent A k y i ∧ lo ≤ y ∧ y < hi := by
  obtain ⟨y, hy, hlo⟩ := exists_parent_of_intECand hj
  exact ⟨y, hy, hlo, lt_trans (parent_lt hy) hi'⟩

/-- Lemma 6.2 (2): with no internal valid candidate, every `k`-parent is left of the interval. -/
theorem parent_lt_of_no_intECand {lo hi k i y : ℕ} (hi' : i < hi)
    (h : ∀ j, ¬ IntECand A lo hi k j i) (hp : parent A k y i) : y < lo := by
  by_contra hy
  exact h y ⟨not_lt.mp hy, lt_trans (parent_lt hp) hi', parent_cand hp, parent_val_lt hp,
    parent_row_lt hp, parent_target_lt hp⟩

/-- Lemma 6.2 (3): an ancestor chain that stays at or above `lo` never leaves the interval,
so ancestry inside the interval is iterated internal parenthood. This is the form used below:
an ancestor `y ≥ lo` of `x` is reached through parents that are all `≥ lo`. -/
theorem anc_of_intermediate {lo k y x : ℕ} (h : anc A k y x) (hy : lo ≤ y) :
    ∃ u, lo ≤ u ∧ parent A k u x ∧ ancEq A k y u := by
  obtain ⟨u, hu, hux⟩ := anc_last_step h
  exact ⟨u, hy.trans (ancEq_le hu), hux, hu⟩

/-- Definition 6.1, the interval-internal parent: `y` is the `I`-internal `k`-parent
`IntParᴵₖ(i)` of `i` when it is the **last** position of `ECandᴵₖ(i)` — an internal valid
`k`-candidate of `i` that is `≥` every internal valid `k`-candidate of `i`.
(`ECandᴵₖ(i) ≠ ∅` is the paper's side condition; it is exactly `∃ j, IntECand A lo hi k j i`,
which the first component below provides.) -/
def IntPar (A : Arr r) (lo hi k y i : ℕ) : Prop :=
  IntECand A lo hi k y i ∧ ∀ j, IntECand A lo hi k j i → j ≤ y

/-- The right end of the interval is immaterial for a target inside it. -/
theorem intPar_iff_succ {lo hi k y i : ℕ} (hi' : i < hi) :
    IntPar A lo hi k y i ↔ IntPar A lo (i + 1) k y i := by
  simp only [IntPar, intECand_iff_succ hi']

/-- The last element of `ECandᴵₖ(i)` is unique, so `IntParᴵₖ(i)` is well defined. -/
theorem intPar_unique {lo hi k y y' i : ℕ} (h : IntPar A lo hi k y i)
    (h' : IntPar A lo hi k y' i) : y = y' :=
  le_antisymm (h'.2 y h.1) (h.2 y' h'.1)

/-- Lemma 6.2 (1), identification half: when `ECandᴵₖ(i) ≠ ∅`, the direct `k`-parent of `i`
in the whole array *is* the internal parent `IntParᴵₖ(i)`. -/
theorem intPar_of_parent {lo hi k j i y : ℕ} (hi' : i < hi) (hj : IntECand A lo hi k j i)
    (hp : parent A k y i) : IntPar A lo hi k y i := by
  refine ⟨⟨le_of_parent_of_intECand hj hp, lt_trans (parent_lt hp) hi', parent_cand hp,
    parent_val_lt hp, parent_row_lt hp, parent_target_lt hp⟩, ?_⟩
  intro j' hj'
  by_contra hlt
  push Not at hlt
  exact absurd hj'.2.2.2.1 (not_lt.mpr (parent_max hp hlt (cand_lt hj'.2.2.1) hj'.2.2.1))

/-- **Lemma 6.2 (1)** in the paper's own words: if `ECandᴵₖ(X) ≠ ∅` then the direct `k`-parent
of `X` in the whole array exists, belongs to `I`, and equals `IntParᴵₖ(X)`. -/
theorem parent_eq_intPar {lo hi k j i : ℕ} (hi' : i < hi) (hj : IntECand A lo hi k j i) :
    ∃ y, parent A k y i ∧ lo ≤ y ∧ y < hi ∧ IntPar A lo hi k y i := by
  obtain ⟨y, hy, hlo, hhi⟩ := parent_mem_of_intECand hi' hj
  exact ⟨y, hy, hlo, hhi, intPar_of_parent hi' hj hy⟩

/-- The converse half: the internal `k`-parent really is the `k`-parent of the whole array. -/
theorem parent_of_intPar {lo hi k y i : ℕ} (hi' : i < hi) (h : IntPar A lo hi k y i) :
    parent A k y i := by
  obtain ⟨z, hz, -⟩ := exists_parent_of_intECand h.1
  have hzy : z = y := intPar_unique (intPar_of_parent hi' h.1 hz) h
  rwa [hzy] at hz

/-- **Lemma 6.2 (3)**, faithfully: 「Y, X ∈ I について Y ≺ₖ X であることは、X から内部親を反復する
鎖が I を出る前に Y に達することと同値である」 — for `y, x` in the interval, `y ≺ₖ x` holds **iff**
the chain obtained by iterating the internal parent from `x` reaches `y`.  Every step of that
chain stays in `I` by construction (`IntPar` requires `lo ≤ ·` and `· < hi`), which is the
paper's 「I を出る前に」.

`anc_of_intermediate` above is only the last-step half of the left-to-right direction; the
equivalence the paper states is this one. -/
theorem anc_iff_intPar_transGen {lo hi k y x : ℕ} (hy : lo ≤ y) (hx : x < hi) :
    anc A k y x ↔ Relation.TransGen (fun u v => IntPar A lo hi k u v) y x := by
  constructor
  · intro h
    rw [anc_eq_transGen] at h
    induction h with
    | @single x hp =>
      exact .single (intPar_of_parent hx
        ⟨hy, lt_trans (parent_lt hp) hx, parent_cand hp, parent_val_lt hp, parent_row_lt hp,
          parent_target_lt hp⟩ hp)
    | @tail m x hym hp ih =>
      refine (ih (lt_trans (parent_lt hp) hx)).tail ?_
      have hm : lo ≤ m := hy.trans (anc_lt (anc_iff.mpr hym)).le
      exact intPar_of_parent hx
        ⟨hm, lt_trans (parent_lt hp) hx, parent_cand hp, parent_val_lt hp, parent_row_lt hp,
          parent_target_lt hp⟩ hp
  · intro h
    induction h with
    | @single x hp => exact anc_of_parent (parent_of_intPar hx hp)
    | @tail m x _ hp ih =>
      exact anc_of_anc_of_parent (ih (lt_trans (cand_lt hp.1.2.2.1) hx))
        (parent_of_intPar hx hp)

/-! ### The six claims of Theorem 6.3 -/

namespace BadRoot

variable (b : BadRoot A)

/-- (C1)ₖ: ancestry inside one copy mirrors ancestry inside the bad part of `A`.
`q ≤ N` is the paper's range `q = 0,…,N` of copies of `Ã = A[N]`. -/
def Claim1 (k : ℕ) : Prop :=
  ∀ q ≤ b.N, ∀ i j, i < b.s → j < b.s →
    (anc b.tA k (b.pos q i) (b.pos q j) ↔ anc A k (b.p + i) (b.p + j))

/-- (C2)ₖ: ancestry from `G` into a copy mirrors ancestry into the bad part. -/
def Claim2 (k : ℕ) : Prop :=
  ∀ q ≤ b.N, ∀ j E, j < b.s → E < b.p →
    (anc b.tA k E (b.pos q j) ↔ anc A k E (b.p + j))

/-- (C3)ₖ (`k < m₀`): the bridge from a copy to the head of the next one. -/
def Claim3 (k : ℕ) : Prop :=
  ∀ q ≤ b.N, ∀ i, 0 < q → i < b.s →
    (anc b.tA k (b.pos (q - 1) i) (b.pos q 0) ↔ anc A k (b.p + i) (A.len - 1))

/-- (C4): for `q ≥ 1` and `k ≥ m₀`, every `k`-ancestor of `P⁽�q⁾` lies in `G`. -/
def Claim4 : Prop :=
  ∀ k, b.m ≤ k → ∀ q y, 0 < q → anc b.tA k y (b.pos q 0) → y < b.p

/-- (C5)ₖ: the direct parent of a non-leading column does not jump to an earlier copy. -/
def Claim5 (k : ℕ) : Prop :=
  ∀ q j y, j < b.s → 0 < j → parent b.tA k y (b.pos q j) →
    y < b.p ∨ ∃ i, y = b.pos q i

/-- (C6)ₖ: ancestry from an earlier copy is independent of which later copy is the target.
The paper's range is `0 ≤ a < c' < N`, so that `c' + 1` is still a copy of `Ã`. -/
def Claim6 (k : ℕ) : Prop :=
  ∀ a c', a < c' → c' + 1 ≤ b.N → ∀ i j, i < b.s → j < b.s →
    (anc b.tA k (b.pos a i) (b.pos c' j) ↔ anc b.tA k (b.pos a i) (b.pos (c' + 1) j))

/-! ### Elementary consequences of the setup, used by several local lemmas -/

/-- Positions in a copy are `≥ p`. -/
theorem p_le_pos' (q j : ℕ) : b.p ≤ b.pos q j := b.p_le_pos q j

/-- The `k`-entry of a column of `Bq` in terms of the entry in `B₀`. -/
theorem col_pos_eq {q j k : ℕ} (hj : j < b.s) :
    b.tA.col (b.pos q j) k =
      if b.Asc k j then A.col (b.p + j) k + q * b.Δ k else A.col (b.p + j) k :=
  b.col_pos hj k

end BadRoot

end BM4
