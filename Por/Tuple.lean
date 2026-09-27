/-
Adapted from koteitan, bms-elem-pattern, `lean/Pattern/Basic.lean`
(https://github.com/koteitan/bms-elem-pattern, CC BY-SA 4.0), through `Por/Tuple.lean` of
koteitan, 1y-wo-por (https://github.com/koteitan/1y-wo-por): `cat`, `cat_left`, `cat_right`,
`cat_lt`, `cat_congr_left`, `cat_bound`. Changes: ported to Lean 4.33.1.
-/
import Mathlib

/-!
# Tuples of ordinals

This file defines `Ord` (the ordinals of universe 0) and `cat`, which glues two
sequences. It proves the small facts about `cat` that the other files use:
the left part is kept, the right part is shifted, and a bound on both parts bounds
the result.
-/

open Classical Cardinal Ordinal

namespace Por

abbrev Ord := Ordinal.{0}

/-- Concatenation: the first `k` entries come from `p`, the rest from `q`. -/
def cat (k : ℕ) (p q : ℕ → Ord) : ℕ → Ord :=
  fun i => if i < k then p i else q (i - k)

theorem cat_left {k : ℕ} {p q : ℕ → Ord} {i : ℕ} (hi : i < k) : cat k p q i = p i := by
  simp [cat, hi]

theorem cat_right {k : ℕ} {p q : ℕ → Ord} (i : ℕ) : cat k p q (k + i) = q i := by
  simp [cat]

theorem cat_lt {k m : ℕ} {p x : ℕ → Ord} {B : Ord} (hp : ∀ i < k, p i < B)
    (hx : ∀ i < m, x i < B) : ∀ i < k + m, cat k p x i < B := by
  intro i hi
  unfold cat
  split_ifs with h
  · exact hp i h
  · exact hx _ (by omega)

theorem cat_congr_left {k : ℕ} {p p' q : ℕ → Ord} (h : ∀ i < k, p i = p' i) :
    cat k p q = cat k p' q := by
  funext i
  unfold cat
  split_ifs with hi
  · exact h i hi
  · rfl

theorem cat_bound {r bb n : ℕ} {p y : ℕ → Ord} {M : Ord} (hn : n ≤ r + bb)
    (hp : ∀ i < r, p i < M) (hy : ∀ i < bb, y i < M) : ∀ a < n, cat r p y a < M :=
  fun a ha => cat_lt hp hy a (by omega)

end Por
