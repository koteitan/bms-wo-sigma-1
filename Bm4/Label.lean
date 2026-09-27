/-
Copied from koteitan, bms-elem-pattern, `lean/Bm4/Label.lean`
(https://github.com/koteitan/bms-elem-pattern, CC BY-SA 4.0), which takes it from koteitan,
dh-bms-wf-formal (https://github.com/koteitan/dh-bms-wf-formal). Changes: ported to Lean 4.33.1 (no other change).
-/
/-
  Part IV: stable labels and height descent (Definition 18.1, Proposition 19.1),
  relative to an abstract `LabelSystem` (the interface provided by Part III).
-/
import Bm4.Expand

open Classical

universe u

namespace BM4

/-- The label interface for arrays with a fixed row count `r`: a well-founded linear order of
labels, relations `◁ₖ` that are strict and transitive, and finite pattern reflection
(Theorem 17.1) for `n < r`.

Changed from the original interface: the row count `r` is a parameter, and the fields
`rel_mono` and `init` are removed.  Proposition 19.1 uses neither; `init` was only used to label
the initial array `E r`. -/
structure LabelSystem (r : ℕ) where
  Lab : Type u
  [linOrd : LinearOrder Lab]
  [wf : WellFoundedLT Lab]
  rel : ℕ → Lab → Lab → Prop
  rel_lt : ∀ {k a b}, rel k a b → a < b
  rel_trans : ∀ {k a b c}, rel k a b → rel k b c → rel k a c
  reflect : ∀ (n : ℕ) (α β : Lab), n < r → rel n α β →
    ∀ (X : Finset Lab), (∀ x ∈ X, x < α) →
    ∀ (s : ℕ) (y : ℕ → Lab), 0 < s → (∀ i j, i < j → j < s → y i < y j) →
      (∀ i, i < s → α ≤ y i) → (∀ i, i < s → y i < β) →
    ∃ y' : ℕ → Lab,
      (∀ i j, i < j → j < s → y' i < y' j) ∧
      (∀ i, i < s → y' i < α) ∧
      (∀ x ∈ X, x < y' 0) ∧
      (∀ x ∈ X, ∀ i, i < s → ∀ k, k < r → rel k x (y i) → rel k x (y' i)) ∧
      (∀ i j, i < s → j < s → ∀ k, k < r → rel k (y i) (y j) → rel k (y' i) (y' j)) ∧
      (∀ i, i < s → ∀ m, m < n → rel m (y i) β → rel m (y' i) α)

attribute [instance] LabelSystem.linOrd LabelSystem.wf

variable {r : ℕ} (S : LabelSystem.{u} r)

/-- Definition 18.1: a stable label on `A`. Only positions `< A.len` matter. -/
def Stable (A : Arr r) (f : ℕ → S.Lab) : Prop :=
  (∀ i j, i < j → j < A.len → f i < f j) ∧
  (∀ k, k < r → ∀ i j, j < A.len → anc A k i j → S.rel k (f i) (f j))

/-- Height of a label: the label of the last column. -/
def ht (A : Arr r) (f : ℕ → S.Lab) : S.Lab := f (A.len - 1)

theorem Stable.mono {A : Arr r} {f : ℕ → S.Lab} (hf : Stable S A f) {i j : ℕ} (hij : i < j)
    (hj : j < A.len) : f i < f j := hf.1 i j hij hj

theorem Stable.rel {A : Arr r} {f : ℕ → S.Lab} (hf : Stable S A f) {k i j : ℕ} (hk : k < r)
    (hj : j < A.len) (h : anc A k i j) : S.rel k (f i) (f j) := hf.2 k hk i j hj h

/-- Stability only depends on the columns below the length. -/
theorem stable_congr {A B : Arr r} (hlen : B.len ≤ A.len)
    (hcol : ∀ x, x < B.len → ∀ k, A.col x k = B.col x k) {f : ℕ → S.Lab}
    (hf : Stable S A f) : Stable S B f := by
  refine ⟨fun i j hij hj => hf.mono S hij (hj.trans_le hlen), ?_⟩
  intro k hk i j hj h
  have h' : anc A k i j :=
    (anc_congr_iff (fun x hx k' => hcol x (hx.trans_lt hj) k') (hj.trans_le hlen) hj i).mpr h
  exact hf.rel S hk (hj.trans_le hlen) h'

/-! ### Case 1 of Proposition 19.1: deletion -/

theorem descent_drop {A : Arr r} {f : ℕ → S.Lab} (hf : Stable S A f)
    (h0 : 0 < (dropLast A).len) :
    Stable S (dropLast A) f ∧ ht S (dropLast A) f < ht S A f := by
  refine ⟨stable_congr S (A := A) (B := dropLast A) (by simp [dropLast]) (fun _ _ _ => rfl) hf, ?_⟩
  unfold ht dropLast
  simp only
  have : 0 < A.len - 1 := h0
  exact hf.mono S (by omega) (by omega)

/-! ### Case 2 of Proposition 19.1: copying -/

namespace BadRoot

variable {A : Arr r} (b : BadRoot A)

/-- The array `G ⌢ B₀ ⌢ ⋯ ⌢ B_q` (this is `A[q]`). -/
noncomputable def Aq (q : ℕ) : Arr r := ⟨b.p + (q + 1) * b.s, b.tA.col⟩

theorem Aq_len (q : ℕ) : (b.Aq q).len = b.pos (q + 1) 0 := by
  simp [Aq, pos]

theorem Aq_col (q : ℕ) : (b.Aq q).col = b.tA.col := rfl

/-- **Lemma 3.1** for `A[q] = Ã↾(p+(q+1)s)`: for positions of `A[q]` the `k`-ancestor relation
computed in `A[q]` and in `Ã = A[N]` agree. -/
theorem anc_Aq_iff {q : ℕ} (hq : q ≤ b.N) (k y : ℕ) {x : ℕ} (hx : x < (b.Aq q).len) :
    anc (b.Aq q) k y x ↔ anc b.tA k y x := by
  refine anc_congr_iff (A := b.Aq q) (B := b.tA) (fun _ _ _ => rfl) hx ?_ y
  have hmul : (q + 1) * b.s ≤ (b.N + 1) * b.s := Nat.mul_le_mul_right _ (by omega)
  simp only [Aq] at hx
  simp only [tA]
  omega

/-- Invariants of the label `g` on `A[q]` during the construction of Proposition 19.1. -/
structure Inv (f : ℕ → S.Lab) (q : ℕ) (g : ℕ → S.Lab) : Prop where
  stable : Stable S (b.Aq q) g
  onG : ∀ x, x < b.p → g x = f x
  last : ∀ i, i < b.s → g (b.pos q i) = f (b.p + i)
  below : ∀ x, x < b.pos q 0 → g x < f b.p

theorem inv_zero {f : ℕ → S.Lab} (hf : Stable S A f) (hlen : 0 < A.len) : b.Inv S f 0 f := by
  have hc : A.len - 1 < A.len := by omega
  refine ⟨?_, fun _ _ => rfl, fun i _ => by simp [pos], fun x hx => ?_⟩
  · refine stable_congr S ?_ ?_ hf
    · rw [b.Aq_len]; unfold pos; have := b.p_add_s; omega
    · intro x hx k
      rw [b.Aq_len] at hx
      have hx' : x < A.len - 1 := by unfold pos at hx; have := b.p_add_s; omega
      exact (b.col_prefix hx').symm
  · rw [b.pos_zero_zero] at hx
    exact hf.mono S hx (b.p_lt_c.trans hc)

/-- Positions below `pos (q+2) 0` fall into three regions. -/
theorem region_cases {q x : ℕ} (hx : x < b.pos (q + 2) 0) :
    x < b.pos q 0 ∨ (∃ i, i < b.s ∧ x = b.pos q i) ∨ (∃ i, i < b.s ∧ x = b.pos (q + 1) i) := by
  rcases lt_or_ge x (b.pos q 0) with h | h
  · exact Or.inl h
  · obtain ⟨a, i, hi, rfl⟩ := b.exists_pos ((b.p_le_pos q 0).trans h)
    have ha1 : q ≤ a := by
      by_contra hlt
      push Not at hlt
      exact absurd h (not_le.mpr (b.pos_lt_pos_of_lt hlt hi))
    have ha2 : a < q + 2 := by
      by_contra hge
      push Not at hge
      exact absurd hx (not_lt.mpr (by
        unfold pos
        have : (q + 2) * b.s ≤ a * b.s := Nat.mul_le_mul_right _ hge
        omega))
    rcases Nat.lt_or_ge a (q + 1) with h1 | h1
    · have : a = q := by omega
      subst this; exact Or.inr (Or.inl ⟨i, hi, rfl⟩)
    · have : a = q + 1 := by omega
      subst this; exact Or.inr (Or.inr ⟨i, hi, rfl⟩)

theorem pos_sub (q i : ℕ) : b.pos q i - b.pos q 0 = i := by unfold pos; omega

theorem pos_lt_pos_succ_zero {q i : ℕ} (hi : i < b.s) : b.pos q i < b.pos (q + 1) 0 :=
  b.pos_lt_pos_of_lt (Nat.lt_succ_self q) hi

theorem pos_zero_le_pos (q i : ℕ) : b.pos q 0 ≤ b.pos q i := by unfold pos; omega

/-- The inductive step of Proposition 19.1. -/
theorem inv_succ (hm : b.m < r) {f : ℕ → S.Lab} (hf : Stable S A f) (hlen : 0 < A.len)
    {q : ℕ} (hq1 : q + 1 ≤ b.N) {g : ℕ → S.Lab} (hg : b.Inv S f q g) :
    ∃ g', b.Inv S f (q + 1) g' := by
  have hc : A.len - 1 < A.len := by omega
  have hpc : b.p < A.len - 1 := b.p_lt_c
  set α := f b.p with hα
  set β := f (A.len - 1) with hβ
  set y : ℕ → S.Lab := fun i => f (b.p + i) with hy
  set X : Finset S.Lab := (Finset.range (b.pos q 0)).image g with hX
  have hXlt : ∀ x ∈ X, x < α := by
    intro x hx
    rw [hX, Finset.mem_image] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    exact hg.below z (Finset.mem_range.mp hz)
  have hrel : S.rel b.m α β := hf.rel S hm hc (anc_of_parent b.hpar)
  have hymono : ∀ i j, i < j → j < b.s → y i < y j := fun i j hij hj =>
    hf.mono S (by omega) ((b.lt_c_of_lt_s hj).trans hc)
  have hyge : ∀ i, i < b.s → α ≤ y i := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp [hy, hα]
    · exact (hf.mono S (by omega) ((b.lt_c_of_lt_s hi).trans hc)).le
  have hylt : ∀ i, i < b.s → y i < β := fun i hi => hf.mono S (b.lt_c_of_lt_s hi) hc
  obtain ⟨y', hy'mono, hy'lt, hXy', hpres1, hpres2, hpres3⟩ :=
    S.reflect b.m α β hm hrel X hXlt b.s y b.s_pos hymono hyge hylt
  -- the new label
  let g' : ℕ → S.Lab := fun x =>
    if x < b.pos q 0 then g x
    else if x < b.pos (q + 1) 0 then y' (x - b.pos q 0)
    else f (b.p + (x - b.pos (q + 1) 0))
  have g'_lo : ∀ x, x < b.pos q 0 → g' x = g x := fun x hx => by simp [g', hx]
  have g'_mid : ∀ i, i < b.s → g' (b.pos q i) = y' i := by
    intro i hi
    have h1 : ¬ b.pos q i < b.pos q 0 := not_lt.mpr (b.pos_zero_le_pos q i)
    have h2 : b.pos q i < b.pos (q + 1) 0 := b.pos_lt_pos_succ_zero hi
    simp [g', h1, h2, b.pos_sub]
  have g'_hi : ∀ i, i < b.s → g' (b.pos (q + 1) i) = y i := by
    intro i hi
    have h1 : ¬ b.pos (q + 1) i < b.pos q 0 :=
      not_lt.mpr ((b.pos_lt_pos_of_lt (Nat.lt_succ_self q) b.s_pos).le.trans
        (b.pos_zero_le_pos _ i))
    have h2 : ¬ b.pos (q + 1) i < b.pos (q + 1) 0 := not_lt.mpr (b.pos_zero_le_pos _ i)
    simp [g', h1, h2, b.pos_sub, hy]
  have hgX : ∀ x, x < b.pos q 0 → g x ∈ X := fun x hx =>
    Finset.mem_image.mpr ⟨x, Finset.mem_range.mpr hx, rfl⟩
  refine ⟨g', ?_, ?_, ?_, ?_⟩
  · -- stability on A[q+1]
    constructor
    · -- monotone
      intro i j hij hj
      rw [b.Aq_len] at hj
      rcases b.region_cases hj with hj1 | ⟨j', hj', rfl⟩ | ⟨j', hj', rfl⟩
      · have hi1 : i < b.pos q 0 := hij.trans hj1
        rw [g'_lo i hi1, g'_lo j hj1]
        exact hg.stable.mono S hij (by rw [b.Aq_len]; exact hj1.trans (b.pos_lt_pos_succ_zero b.s_pos))
      · rw [g'_mid j' hj']
        rcases lt_or_ge i (b.pos q 0) with hi1 | hi1
        · rw [g'_lo i hi1]
          have h0 : y' 0 ≤ y' j' := by
            rcases Nat.eq_zero_or_pos j' with rfl | hj0
            · exact le_rfl
            · exact (hy'mono 0 j' hj0 hj').le
          exact lt_of_lt_of_le (hXy' _ (hgX i hi1)) h0
        · obtain ⟨a, i', hi', rfl⟩ := b.exists_pos ((b.p_le_pos q 0).trans hi1)
          have ha : a = q := by
            rcases lt_trichotomy a q with h | h | h
            · exact absurd hi1 (not_le.mpr (b.pos_lt_pos_of_lt h hi'))
            · exact h
            · exact absurd hij (not_lt.mpr (b.pos_lt_pos_of_lt h hj').le)
          subst ha
          rw [g'_mid i' hi']
          exact hy'mono i' j' ((b.pos_lt_pos_same_iff).mp hij) hj'
      · rw [g'_hi j' hj']
        rcases lt_or_ge i (b.pos q 0) with hi1 | hi1
        · rw [g'_lo i hi1]
          exact lt_of_lt_of_le (hg.below i hi1) (hyge j' hj')
        · rcases lt_or_ge i (b.pos (q + 1) 0) with hi2 | hi2
          · obtain ⟨a, i', hi', rfl⟩ := b.exists_pos ((b.p_le_pos q 0).trans hi1)
            have ha : a = q := by
              rcases lt_trichotomy a q with h | h | h
              · exact absurd hi1 (not_le.mpr (b.pos_lt_pos_of_lt h hi'))
              · exact h
              · exact absurd hi2 (not_lt.mpr (by
                  unfold pos
                  have : (q + 1) * b.s ≤ a * b.s := Nat.mul_le_mul_right _ h
                  omega))
            subst ha
            rw [g'_mid i' hi']
            exact lt_of_lt_of_le (hy'lt i' hi') (hyge j' hj')
          · obtain ⟨a, i', hi', rfl⟩ := b.exists_pos ((b.p_le_pos _ 0).trans hi2)
            have ha : a = q + 1 := by
              rcases lt_trichotomy a (q + 1) with h | h | h
              · exact absurd hi2 (not_le.mpr (b.pos_lt_pos_of_lt h hi'))
              · exact h
              · exact absurd hij (not_lt.mpr (b.pos_lt_pos_of_lt h hj').le)
            subst ha
            rw [g'_hi i' hi']
            exact hymono i' j' ((b.pos_lt_pos_same_iff).mp hij) hj'
    · -- ancestor relations
      intro k hk i j hj h
      rw [b.Aq_len] at hj
      rw [b.anc_Aq_iff (q := q + 1) (by omega) k i
        (by rw [b.Aq_len]; exact hj)] at h
      rcases b.region_cases hj with hj1 | ⟨j', hj', rfl⟩ | ⟨j', hj', rfl⟩
      · -- (a) target before B_q
        have hi1 : i < b.pos q 0 := (anc_lt h).trans hj1
        rw [g'_lo i hi1, g'_lo j hj1]
        exact hg.stable.rel S hk (by rw [b.Aq_len]; exact hj1.trans (b.pos_lt_pos_succ_zero b.s_pos))
          ((b.anc_Aq_iff (by omega) k i
            (by rw [b.Aq_len]; exact hj1.trans (b.pos_lt_pos_succ_zero b.s_pos))).mpr h)
      · -- (b) target in the old last copy B_q
        have hrel0 : S.rel k (g i) (f (b.p + j')) := by
          have := hg.stable.rel S hk (by rw [b.Aq_len]; exact b.pos_lt_pos_succ_zero hj')
            ((b.anc_Aq_iff (by omega) k i
              (by rw [b.Aq_len]; exact b.pos_lt_pos_succ_zero hj')).mpr h)
          rwa [hg.last j' hj'] at this
        rw [g'_mid j' hj']
        rcases b.anc_tA_cases k hj' h with hi1 | ⟨a, ha, i', hi', rfl⟩ | ⟨i', hi'j, rfl⟩
        · have hi1' : i < b.pos q 0 := hi1.trans_le (b.p_le_pos q 0)
          rw [g'_lo i hi1']
          exact hpres1 _ (hgX i hi1') j' hj' k hk hrel0
        · have hi1' : b.pos a i' < b.pos q 0 := b.pos_lt_pos_of_lt ha hi'
          rw [g'_lo _ hi1']
          exact hpres1 _ (hgX _ hi1') j' hj' k hk hrel0
        · have hi' : i' < b.s := hi'j.trans hj'
          rw [g'_mid i' hi']
          rw [hg.last i' hi'] at hrel0
          exact hpres2 i' j' hi' hj' k hk hrel0
      · -- (c)–(f) target in the new copy B_{q+1}.  The paper splits on where the ancestor
        -- sits (Remark 19.2): inside `B_{q+1}` (c), in `G` (d), in `B_a` with `a < q` (e),
        -- or in the adjacent `B_q` (f); each case uses its own result of §6.
        have hC := b.theorem_6_3
        rw [g'_hi j' hj']
        rcases b.anc_tA_cases k hj' h with hi1 | ⟨a, ha, i', hi', rfl⟩ | ⟨i', hi'j, rfl⟩
        · -- (d) ancestor in `G`: the copy lemma (C2) moves it back to `A`
          have hi1' : i < b.pos q 0 := hi1.trans_le (b.p_le_pos q 0)
          rw [g'_lo i hi1', hg.onG i hi1]
          exact hf.rel S hk ((b.lt_c_of_lt_s hj').trans hc)
            ((hC.2.1 k (q + 1) hq1 j' i hj' hi1).mp h)
        · rcases Nat.lt_or_ge a q with haq | haq
          · -- (e) two or more copies back: (C6) with `b = q` gives (19.7), and prefix
            -- invariance (Lemma 3.1, here `anc_Aq_iff`) turns it into (19.8) inside `A[q]`
            have hlt : b.pos a i' < b.pos q 0 := b.pos_lt_pos_of_lt haq hi'
            rw [g'_lo _ hlt]
            have hanc : anc b.tA k (b.pos a i') (b.pos q j') :=
              (hC.2.2.2.2.2 k a q haq hq1 i' j' hi' hj').mpr h
            have := hg.stable.rel S hk (by rw [b.Aq_len]; exact b.pos_lt_pos_succ_zero hj')
              ((b.anc_Aq_iff (by omega) k _
                (by rw [b.Aq_len]; exact b.pos_lt_pos_succ_zero hj')).mpr hanc)
            rwa [hg.last j' hj'] at this
          · -- (f) adjacent copies: Corollary 6.12 supplies (19.10)
            have ha' : a = q := by omega
            subst ha'
            obtain ⟨hkm, hiC, hpj⟩ := b.corollary_6_12 hi' hj' h
            rw [g'_mid i' hi']
            have h1 : S.rel k (y i') β := hf.rel S hk hc hiC
            have h2 : S.rel k (y' i') α := hpres3 i' hi' k hkm h1
            rcases Nat.eq_zero_or_pos j' with rfl | hj0
            · simpa [hy, hα] using h2
            · have h3 : S.rel k α (y j') :=
                hf.rel S hk ((b.lt_c_of_lt_s hj').trans hc) (anc_of_ancEq_of_ne hpj (by omega))
              exact S.rel_trans h2 h3
        · -- (c) ancestor inside the new copy: the copy lemma (C1)
          have hi' : i' < b.s := hi'j.trans hj'
          rw [g'_hi i' hi']
          exact hf.rel S hk ((b.lt_c_of_lt_s hj').trans hc)
            ((hC.1 k (q + 1) hq1 i' j' hi' hj').mp h)
  · intro x hx
    rw [g'_lo x (hx.trans_le (b.p_le_pos q 0))]
    exact hg.onG x hx
  · exact g'_hi
  · intro x hx
    rcases lt_or_ge x (b.pos q 0) with h1 | h1
    · rw [g'_lo x h1]; exact hg.below x h1
    · obtain ⟨a, i', hi', rfl⟩ := b.exists_pos ((b.p_le_pos q 0).trans h1)
      have ha : a = q := by
        rcases lt_trichotomy a q with h | h | h
        · exact absurd h1 (not_le.mpr (b.pos_lt_pos_of_lt h hi'))
        · exact h
        · exact absurd hx (not_lt.mpr (by
            unfold pos
            have : (q + 1) * b.s ≤ a * b.s := Nat.mul_le_mul_right _ h
            omega))
      subst ha
      rw [g'_mid i' hi']
      exact hy'lt i' hi'

theorem inv_exists (hm : b.m < r) {f : ℕ → S.Lab} (hf : Stable S A f) (hlen : 0 < A.len) (q : ℕ)
    (hq : q ≤ b.N) : ∃ g, b.Inv S f q g := by
  induction q with
  | zero => exact ⟨f, b.inv_zero S hf hlen⟩
  | succ q ih =>
    obtain ⟨g, hg⟩ := ih (by omega)
    exact b.inv_succ S hm hf hlen hq hg

end BadRoot

/-- **Proposition 19.1** (height descent): one expansion of a nonempty array with a stable label
yields, if nonempty, a stable label of strictly smaller height. -/
theorem descent {A : Arr r} {f : ℕ → S.Lab} (hf : Stable S A f) (h0 : 0 < A.len) (N : ℕ)
    (h0' : 0 < (expand A N).len) :
    ∃ g, Stable S (expand A N) g ∧ ht S (expand A N) g < ht S A f := by
  have hne : A.len ≠ 0 := by omega
  by_cases h : LastHasParent A
  · set b := toBadRoot h N with hb
    have hr : 0 < r := by obtain ⟨_, k, hk, _⟩ := h; omega
    have hm : b.m < r := m₀_lt hr
    obtain ⟨g, hg⟩ := b.inv_exists S hm hf h0 N le_rfl
    have heq : expand A N = b.Aq N := expand_eq h N
    refine ⟨g, heq ▸ hg.stable, ?_⟩
    unfold ht
    rw [expand_last h N, hg.last (b.s - 1) (by have := b.s_pos; omega)]
    have h1 : b.p + (b.s - 1) < A.len - 1 := b.lt_c_of_lt_s (by have := b.s_pos; omega)
    exact hf.mono S h1 (by omega)
  · rw [expand_of_not_lastHasParent hne h N] at h0' ⊢
    exact ⟨f, descent_drop S hf h0'⟩

end BM4
