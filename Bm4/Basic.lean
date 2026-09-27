/-
Copied from koteitan, bms-elem-pattern, `lean/Bm4/Basic.lean`
(https://github.com/koteitan/bms-elem-pattern, CC BY-SA 4.0), which takes it from koteitan,
dh-bms-wf-formal (https://github.com/koteitan/dh-bms-wf-formal). Changes: ported to Lean 4.33.1 (no other change).
-/
/-
  Basic properties of parents and ancestors: Lemma 2.2, prefix invariance (Lemma 3.1),
  convexity of parent candidates (Lemma 4.1).
-/
import Bm4.Defs

open Classical

namespace BM4

variable {r : ℕ}

theorem anc_eq_transGen (A : Arr r) (k : ℕ) :
    anc A k = Relation.TransGen (parent A k) := by
  cases k <;> rfl

theorem anc_iff {A : Arr r} {k j i : ℕ} :
    anc A k j i ↔ Relation.TransGen (parent A k) j i := by
  rw [anc_eq_transGen]

/-- Lemma 2.2 (1): a strict `k`-ancestor is to the left and has a smaller `k`-entry. -/
theorem anc_lt_and_val_lt {A : Arr r} {k j i : ℕ} (h : anc A k j i) :
    j < i ∧ A.col j k < A.col i k := by
  rw [anc_eq_transGen] at h
  induction h with
  | single hp => exact ⟨hp.1, hp.2.2.1⟩
  | tail _ hp ih => exact ⟨ih.1.trans hp.1, ih.2.trans hp.2.2.1⟩

theorem anc_lt {A : Arr r} {k j i : ℕ} (h : anc A k j i) : j < i :=
  (anc_lt_and_val_lt h).1

theorem anc_val_lt {A : Arr r} {k j i : ℕ} (h : anc A k j i) : A.col j k < A.col i k :=
  (anc_lt_and_val_lt h).2

theorem ancEq_le {A : Arr r} {k j i : ℕ} (h : ancEq A k j i) : j ≤ i := by
  rcases h with rfl | h
  · exact le_rfl
  · exact (anc_lt h).le

theorem anc_trans {A : Arr r} {k a b c : ℕ} (h₁ : anc A k a b) (h₂ : anc A k b c) :
    anc A k a c := by
  rw [anc_eq_transGen] at *
  exact h₁.trans h₂

theorem anc_of_parent {A : Arr r} {k j i : ℕ} (h : parent A k j i) : anc A k j i := by
  rw [anc_eq_transGen]; exact .single h

theorem anc_of_anc_of_parent {A : Arr r} {k a b c : ℕ} (h₁ : anc A k a b) (h₂ : parent A k b c) :
    anc A k a c :=
  anc_trans h₁ (anc_of_parent h₂)

theorem anc_of_parent_of_anc {A : Arr r} {k a b c : ℕ} (h₁ : parent A k a b) (h₂ : anc A k b c) :
    anc A k a c :=
  anc_trans (anc_of_parent h₁) h₂

theorem ancEq_trans {A : Arr r} {k a b c : ℕ} (h₁ : ancEq A k a b) (h₂ : ancEq A k b c) :
    ancEq A k a c := by
  rcases h₁ with rfl | h₁
  · exact h₂
  rcases h₂ with rfl | h₂
  · exact Or.inr h₁
  · exact Or.inr (anc_trans h₁ h₂)

theorem ancEq_refl (A : Arr r) (k i : ℕ) : ancEq A k i i := Or.inl rfl

theorem anc_of_ancEq_of_ne {A : Arr r} {k j i : ℕ} (h : ancEq A k j i) (hne : j ≠ i) :
    anc A k j i := by
  rcases h with rfl | h
  · exact absurd rfl hne
  · exact h

/-- Structural candidates are to the left. -/
theorem cand_lt {A : Arr r} {k j i : ℕ} (h : cand A k j i) : j < i := by
  cases k with
  | zero => exact h
  | succ k => exact anc_lt h

theorem cand_succ {A : Arr r} {k j i : ℕ} : cand A (k + 1) j i ↔ anc A k j i := Iff.rfl



theorem cand_zero {A : Arr r} {j i : ℕ} : cand A 0 j i ↔ j < i := Iff.rfl

/-- Unfolding `parent`. -/
theorem parent_iff {A : Arr r} {k j i : ℕ} :
    parent A k j i ↔ j < i ∧ cand A k j i ∧ A.col j k < A.col i k ∧
      (∀ j', j < j' → j' < i → cand A k j' i → A.col i k ≤ A.col j' k) ∧
      k < r ∧ i < A.len := Iff.rfl

theorem parent_lt {A : Arr r} {k j i : ℕ} (h : parent A k j i) : j < i := h.1
theorem parent_cand {A : Arr r} {k j i : ℕ} (h : parent A k j i) : cand A k j i := h.2.1
theorem parent_val_lt {A : Arr r} {k j i : ℕ} (h : parent A k j i) : A.col j k < A.col i k :=
  h.2.2.1
theorem parent_max {A : Arr r} {k j i : ℕ} (h : parent A k j i) {j' : ℕ} (hj : j < j')
    (hi : j' < i) (hc : cand A k j' i) : A.col i k ≤ A.col j' k :=
  h.2.2.2.1 j' hj hi hc

/-- Definition 2.1's side condition `k < r`. -/
theorem parent_row_lt {A : Arr r} {k j i : ℕ} (h : parent A k j i) : k < r := h.2.2.2.2.1

/-- Definition 2.1's side condition `i ∈ Pos(A)`. -/
theorem parent_target_lt {A : Arr r} {k j i : ℕ} (h : parent A k j i) : i < A.len := h.2.2.2.2.2

/-- A `(k+1)`-parent is a strict `k`-ancestor. -/
theorem parent_succ_anc {A : Arr r} {k j i : ℕ} (h : parent A (k + 1) j i) : anc A k j i :=
  h.2.1

/-- Lemma 2.2 (2), one step: `j ≺ₖ₊₁ i → j ≺ₖ i`. -/
theorem anc_succ_anc {A : Arr r} {k j i : ℕ} (h : anc A (k + 1) j i) : anc A k j i := by
  rw [anc_eq_transGen] at h
  induction h with
  | single hp => exact parent_succ_anc hp
  | tail _ hp ih => exact anc_trans ih (parent_succ_anc hp)

/-- Lemma 2.2 (2): `h ≤ k` and `j ≺ₖ i` imply `j ≺ₕ i`. -/
theorem anc_mono {A : Arr r} {h k j i : ℕ} (hk : h ≤ k) (hanc : anc A k j i) : anc A h j i := by
  induction hk with
  | refl => exact hanc
  | step _ ih => exact ih (anc_succ_anc hanc)

/-- A strict `k`-ancestor is a structural `k`-candidate. -/
theorem cand_of_anc {A : Arr r} {k j i : ℕ} (h : anc A k j i) : cand A k j i := by
  cases k with
  | zero => exact anc_lt h
  | succ k => exact anc_succ_anc h

theorem ancEq_mono {A : Arr r} {h k j i : ℕ} (hk : h ≤ k) (hanc : ancEq A k j i) :
    ancEq A h j i := by
  rcases hanc with rfl | hanc
  · exact Or.inl rfl
  · exact Or.inr (anc_mono hk hanc)

/-- The `k`-parent is unique. This is the step the paper's proof of Lemma 2.2 (3) rests on;
the statement of 2.2 (3) itself is `ancEq_single_finite_chain` below. -/
theorem parent_unique {A : Arr r} {k j j' i : ℕ} (h : parent A k j i) (h' : parent A k j' i) :
    j = j' := by
  rcases lt_trichotomy j j' with hlt | heq | hgt
  · exact absurd h'.2.2.1 (not_lt.mpr (h.2.2.2.1 j' hlt h'.1 h'.2.1))
  · exact heq
  · exact absurd h.2.2.1 (not_lt.mpr (h'.2.2.2.1 j hgt h.1 h.2.1))

/-- The last step of an ancestor chain. -/
theorem anc_last_step {A : Arr r} {k j i : ℕ} (h : anc A k j i) :
    ∃ b, ancEq A k j b ∧ parent A k b i := by
  rw [anc_eq_transGen] at h
  obtain ⟨b, hb, hbi⟩ := Relation.TransGen.tail'_iff.mp h
  refine ⟨b, ?_, hbi⟩
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp hb with rfl | hb
  · exact Or.inl rfl
  · exact Or.inr (anc_iff.mpr hb)

/-- Lemma 2.2 (4): two `k`-ancestors of the same column are comparable along the chain. -/
theorem anc_of_anc_of_anc_of_lt {A : Arr r} {k u v w : ℕ} (hu : anc A k u w) (hv : anc A k v w)
    (huv : u < v) : anc A k u v := by
  rw [anc_eq_transGen] at hu
  induction hu with
  | single hp =>
    obtain ⟨b, hb, hbw⟩ := anc_last_step hv
    have hb' : b = _ := parent_unique hbw hp
    subst hb'
    rcases hb with rfl | hb
    · exact absurd huv (lt_irrefl _)
    · exact absurd (anc_lt hb) (not_lt.mpr huv.le)
  | @tail m w' _ hp ih =>
    obtain ⟨b, hb, hbw⟩ := anc_last_step hv
    have hb' : b = m := parent_unique hbw hp
    subst hb'
    rcases hb with rfl | hb
    · exact anc_iff.mpr (by assumption)
    · exact ih hb

/-- **Lemma 2.2 (3)**: 「固定した i, k に対し、i の非狭義 k-祖先全体は一本の有限鎖をなす。」
For fixed `i` and `k`, the collection of all non-strict `k`-ancestors of `i` is a single
finite chain.  The three words of that sentence are the three conjuncts:

* *鎖* (chain): `u ≼ₖ i` holds exactly when `u` is reached from `i` by iterating the `k`-parent
  zero or more times, i.e. the reflexive-transitive closure of `parent A k`;
* *一本* (a single one, no branching): any two non-strict `k`-ancestors of `i` are comparable —
  the smaller one is a strict `k`-ancestor of the larger;
* *有限* (finite): they all lie in `{0, …, i}`.

The paper proves it from 「親が高々一つであること」, which is `parent_unique` above. -/
theorem ancEq_single_finite_chain (A : Arr r) (k i : ℕ) :
    (∀ u, ancEq A k u i ↔ Relation.ReflTransGen (parent A k) u i) ∧
    (∀ u v, ancEq A k u i → ancEq A k v i → u < v → anc A k u v) ∧
    {u | ancEq A k u i}.Finite := by
  refine ⟨fun u => ?_, fun u v hu hv huv => ?_, ?_⟩
  · constructor
    · rintro (rfl | h)
      · exact Relation.ReflTransGen.refl
      · exact (anc_iff.mp h).to_reflTransGen
    · intro h
      rcases Relation.reflTransGen_iff_eq_or_transGen.mp h with heq | h
      · exact Or.inl heq.symm
      · exact Or.inr (anc_iff.mpr h)
  · rcases hu with heq | hu
    · exact absurd huv (by have := ancEq_le hv; omega)
    · rcases hv with rfl | hv
      · exact hu
      · exact anc_of_anc_of_anc_of_lt hu hv huv
  · refine Set.Finite.subset (Set.finite_Iic i) ?_
    intro u hu
    exact Set.mem_Iic.mpr (ancEq_le hu)

/-- If some valid structural candidate exists, a parent exists. -/
theorem exists_parent_of_valid {A : Arr r} {k j i : ℕ} (hk : k < r) (hi : i < A.len)
    (hc : cand A k j i) (hv : A.col j k < A.col i k) : ∃ p, parent A k p i := by
  classical
  let P : ℕ → Prop := fun j' => cand A k j' i ∧ A.col j' k < A.col i k
  have hj : j < i := cand_lt hc
  have hP : P j := ⟨hc, hv⟩
  have hex : ∃ p, P p ∧ ∀ p', P p' → p' ≤ p := by
    refine ⟨Nat.findGreatest P i, ?_, ?_⟩
    · exact Nat.findGreatest_spec (P := P) hj.le hP
    · intro p' hp'
      exact Nat.le_findGreatest (cand_lt hp'.1).le hp'
  obtain ⟨p, ⟨hpc, hpv⟩, hmax⟩ := hex
  refine ⟨p, cand_lt hpc, hpc, hpv, ?_, hk, hi⟩
  intro j' hpj' _ hc'
  by_contra hlt
  push Not at hlt
  exact absurd (hmax j' ⟨hc', hlt⟩) (not_le.mpr hpj')

/-! ### Prefix invariance (Lemma 3.1) -/

/-- Two arrays agreeing on all positions `≤ i`, both having `i` as a position, have the same
`k`-ancestors of `i`.  (Lemma 3.1 for two arrays; `anc_prefix` is the paper's statement.) -/
theorem anc_congr {A B : Arr r} (k : ℕ) :
    ∀ i j, anc A k j i → (∀ x ≤ i, ∀ k', A.col x k' = B.col x k') → i < B.len →
      anc B k j i := by
  induction k generalizing A B with
  | zero =>
    intro i j h
    rw [anc_eq_transGen] at h ⊢
    induction h with
    | @single i hp =>
      intro hag hlen
      refine .single ⟨hp.1, hp.2.1, ?_, ?_, hp.2.2.2.2.1, hlen⟩
      · rw [← hag _ hp.1.le, ← hag i le_rfl]; exact hp.2.2.1
      · intro j' h1 h2 h3
        rw [← hag j' h2.le, ← hag i le_rfl]; exact hp.2.2.2.1 j' h1 h2 h3
    | @tail m i _ hp ih =>
      intro hag hlen
      have hag' : ∀ x ≤ m, ∀ k', A.col x k' = B.col x k' :=
        fun x hx k' => hag x (hx.trans hp.1.le) k'
      refine (ih hag' (by have := hp.1; omega)).tail ⟨hp.1, hp.2.1, ?_, ?_, hp.2.2.2.2.1, hlen⟩
      · rw [← hag m hp.1.le, ← hag i le_rfl]; exact hp.2.2.1
      · intro j' h1 h2 h3
        rw [← hag j' h2.le, ← hag i le_rfl]; exact hp.2.2.2.1 j' h1 h2 h3
  | succ k ihk =>
    intro i j h
    have hagB : ∀ i j, anc B k j i → (∀ x ≤ i, ∀ k', A.col x k' = B.col x k') → i < A.len →
        anc A k j i :=
      fun i j h hag hlen => ihk (A := B) (B := A) i j h (fun x hx k' => (hag x hx k').symm) hlen
    rw [anc_eq_transGen] at h ⊢
    induction h with
    | @single i hp =>
      intro hag hlen
      refine .single ⟨hp.1, ihk i _ hp.2.1 hag hlen, ?_, ?_, hp.2.2.2.2.1, hlen⟩
      · rw [← hag _ hp.1.le, ← hag i le_rfl]; exact hp.2.2.1
      · intro j' h1 h2 h3
        rw [← hag j' h2.le, ← hag i le_rfl]
        exact hp.2.2.2.1 j' h1 h2 (hagB i j' h3 hag hp.2.2.2.2.2)
    | @tail m i _ hp ih =>
      intro hag hlen
      have hag' : ∀ x ≤ m, ∀ k', A.col x k' = B.col x k' :=
        fun x hx k' => hag x (hx.trans hp.1.le) k'
      refine (ih hag' (by have := hp.1; omega)).tail
        ⟨hp.1, ihk i m hp.2.1 hag hlen, ?_, ?_, hp.2.2.2.2.1, hlen⟩
      · rw [← hag m hp.1.le, ← hag i le_rfl]; exact hp.2.2.1
      · intro j' h1 h2 h3
        rw [← hag j' h2.le, ← hag i le_rfl]
        exact hp.2.2.2.1 j' h1 h2 (hagB i j' h3 hag hp.2.2.2.2.2)

theorem anc_congr_iff {A B : Arr r} {k i : ℕ} (hag : ∀ x ≤ i, ∀ k', A.col x k' = B.col x k')
    (hA : i < A.len) (hB : i < B.len) (j : ℕ) : anc A k j i ↔ anc B k j i :=
  ⟨fun h => anc_congr k i j h hag hB,
   fun h => anc_congr k i j h (fun x hx k' => (hag x hx k').symm) hA⟩

theorem cand_congr_iff {A B : Arr r} {k i : ℕ} (hag : ∀ x ≤ i, ∀ k', A.col x k' = B.col x k')
    (hA : i < A.len) (hB : i < B.len) (j : ℕ) : cand A k j i ↔ cand B k j i := by
  cases k with
  | zero => exact Iff.rfl
  | succ k => exact anc_congr_iff hag hA hB j

theorem parent_congr_iff {A B : Arr r} {k i : ℕ} (hag : ∀ x ≤ i, ∀ k', A.col x k' = B.col x k')
    (hA : i < A.len) (hB : i < B.len) (j : ℕ) : parent A k j i ↔ parent B k j i := by
  have hv : ∀ x ≤ i, A.col x k = B.col x k := fun x hx => hag x hx k
  constructor
  · rintro ⟨h1, h2, h3, h4, hk, -⟩
    refine ⟨h1, (cand_congr_iff hag hA hB j).mp h2, ?_, ?_, hk, hB⟩
    · rw [← hv j h1.le, ← hv i le_rfl]; exact h3
    · intro j' hj hi hc
      rw [← hv j' hi.le, ← hv i le_rfl]
      exact h4 j' hj hi ((cand_congr_iff hag hA hB j').mpr hc)
  · rintro ⟨h1, h2, h3, h4, hk, -⟩
    refine ⟨h1, (cand_congr_iff hag hA hB j).mpr h2, ?_, ?_, hk, hA⟩
    · rw [hv j h1.le, hv i le_rfl]; exact h3
    · intro j' hj hi hc
      rw [hv j' hi.le, hv i le_rfl]
      exact h4 j' hj hi ((cand_congr_iff hag hA hB j').mp hc)

theorem ancEq_congr_iff {A B : Arr r} {k i : ℕ} (hag : ∀ x ≤ i, ∀ k', A.col x k' = B.col x k')
    (hA : i < A.len) (hB : i < B.len) (j : ℕ) : ancEq A k j i ↔ ancEq B k j i := by
  unfold ancEq; rw [anc_congr_iff hag hA hB]

/-- **Lemma 3.1**: let `m ≤ ℓ` and let the prefix be `A↾m = (A_0,…,A_{m-1})`.  For positions of
the prefix the `k`-ancestor relation computed in `A↾m` and in `A` agree. -/
theorem anc_prefix (A : Arr r) {m : ℕ} (hm : m ≤ A.len) {k j i : ℕ} (hi : i < m) :
    anc (⟨m, A.col⟩ : Arr r) k j i ↔ anc A k j i :=
  anc_congr_iff (A := (⟨m, A.col⟩ : Arr r)) (B := A) (fun _ _ _ => rfl) hi (by omega) j

/-- Exit point of an ancestor chain: if `y < p ≤ v` and `y ≺ₖ v`, the chain from `v` has a
last element `u ≥ p`, whose parent `y' < p` is a non-strict ancestor-or-equal of `y`.

The paper has no numbered statement here. This is the formal content of the step it takes
informally in §6.5 and §6.6 — 「`D_j` から `k`-親鎖を左へたどる」, following the parent chain
leftwards until it leaves a region — used in the proofs of Lemmas 6.6 and 6.7. -/
theorem anc_exit_point {A : Arr r} {k y v p : ℕ} (h : anc A k y v) (hy : y < p) (hv : p ≤ v) :
    ∃ u y', p ≤ u ∧ ancEq A k u v ∧ parent A k y' u ∧ y' < p ∧ ancEq A k y y' := by
  rw [anc_eq_transGen] at h
  induction h with
  | @single v hp =>
    exact ⟨v, y, hv, Or.inl rfl, hp, hy, Or.inl rfl⟩
  | @tail m v hym hp ih =>
    rcases lt_or_ge m p with hm | hm
    · exact ⟨v, m, hv, Or.inl rfl, hp, hm, Or.inr (anc_iff.mpr hym)⟩
    · obtain ⟨u, y', hu, huv, hy'u, hy', hyy'⟩ := ih hm
      exact ⟨u, y', hu, ancEq_trans huv (Or.inr (anc_of_parent hp)), hy'u, hy', hyy'⟩

/-! ### Convexity of parent candidates (Lemma 4.1) -/

/-- Core of Lemma 4.1: if `u` is the `k`-parent of `v` and `w` is a structural `k`-candidate
of `v` strictly between them, then `w` is a strict `k`-descendant of `u`. -/
theorem anc_of_parent_of_between {A : Arr r} {k u v : ℕ} (huv : parent A k u v) :
    ∀ w, u < w → w < v → cand A k w v → anc A k u w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro huw hwv hcw
  have hcu : cand A k u w := by
    cases k with
    | zero => exact huw
    | succ k => exact anc_of_anc_of_anc_of_lt (parent_succ_anc huv) hcw huw
  have hw_inv : A.col v k ≤ A.col w k := parent_max huv huw hwv hcw
  have hvu : A.col u k < A.col w k := lt_of_lt_of_le (parent_val_lt huv) hw_inv
  obtain ⟨z, hz⟩ := exists_parent_of_valid (parent_row_lt huv)
    (by have := parent_target_lt huv; omega) hcu hvu
  have huz : u ≤ z := by
    by_contra h
    push Not at h
    exact absurd hvu (not_lt.mpr (parent_max hz h huw hcu))
  rcases huz.lt_or_eq with hlt | heq
  · have hzw : z < w := parent_lt hz
    have hcz : cand A k z v := by
      cases k with
      | zero => exact hzw.trans hwv
      | succ k => exact anc_trans (parent_cand hz) hcw
    exact anc_of_anc_of_parent (ih z hzw hlt (hzw.trans hwv) hcz) hz
  · subst heq
    exact anc_of_parent hz

/-- Lemma 4.1 (convexity). For `k = 0` the side condition follows from `w ≤ v`; for `k > 0`
it says that `w` is a non-strict `(k-1)`-ancestor of `v`. -/
theorem convex {A : Arr r} {k u v w : ℕ} (huv : anc A k u v) (huw : u ≤ w) (hwv : w ≤ v)
    (hc : w = v ∨ cand A k w v) : ancEq A k u w := by
  rw [anc_eq_transGen] at huv
  induction huv with
  | @single v hp =>
    rcases eq_or_lt_of_le huw with rfl | huw'
    · exact Or.inl rfl
    rcases eq_or_lt_of_le hwv with rfl | hwv'
    · exact Or.inr (anc_of_parent hp)
    have hcw : cand A k w v := hc.resolve_left (ne_of_lt hwv')
    exact Or.inr (anc_of_parent_of_between hp w huw' hwv' hcw)
  | @tail m v hum hp ih =>
    have hum' : anc A k u m := anc_iff.mpr hum
    rcases le_or_gt m w with hmw | hwm
    · rcases eq_or_lt_of_le hmw with rfl | hmw'
      · exact Or.inr hum'
      rcases eq_or_lt_of_le hwv with rfl | hwv'
      · exact Or.inr (anc_of_anc_of_parent hum' hp)
      have hcw : cand A k w v := hc.resolve_left (ne_of_lt hwv')
      exact Or.inr (anc_trans hum' (anc_of_parent_of_between hp w hmw' hwv' hcw))
    · apply ih hwm.le
      right
      cases k with
      | zero => exact hwm
      | succ k =>
        have hcw : anc A k w v := hc.resolve_left (ne_of_lt (hwm.trans (parent_lt hp)))
        exact anc_of_anc_of_anc_of_lt hcw (parent_succ_anc hp) hwm

/-- Convexity for `k = 0`. -/
theorem convex_zero {A : Arr r} {u v w : ℕ} (huv : anc A 0 u v) (huw : u ≤ w) (hwv : w ≤ v) :
    ancEq A 0 u w :=
  convex huv huw hwv (by
    rcases eq_or_lt_of_le hwv with rfl | h
    · exact Or.inl rfl
    · exact Or.inr h)

/-- Convexity for `k + 1`: `w` a non-strict `k`-ancestor of `v` between `u ≺ₖ₊₁ v` gives `u ≼ₖ₊₁ w`. -/
theorem convex_succ {A : Arr r} {k u v w : ℕ} (huv : anc A (k + 1) u v) (huw : u ≤ w)
    (hwv : ancEq A k w v) : ancEq A (k + 1) u w :=
  convex huv huw (ancEq_le hwv) (by
    rcases hwv with rfl | h
    · exact Or.inl rfl
    · exact Or.inr h)

/-- Convexity, uniform form: `w` a non-strict structural candidate of `v` (`w = v ∨ cand`). -/
theorem convex_cand {A : Arr r} {k u v w : ℕ} (huv : anc A k u v) (huw : u ≤ w)
    (hc : w = v ∨ cand A k w v) : ancEq A k u w :=
  convex huv huw (by
    rcases hc with rfl | h
    · exact le_rfl
    · exact (cand_lt h).le) hc

end BM4
