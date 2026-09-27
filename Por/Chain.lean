/-
Adapted from koteitan, 1y-wo-por, `Por/Chain.lean` (https://github.com/koteitan/1y-wo-por),
whose chain `cC` follows `lamChain` of koteitan, bms-elem-pattern, `lean/Pattern/Chain.lean`
(https://github.com/koteitan/bms-elem-pattern, CC BY-SA 4.0). Changes: there is no root index,
so the absoluteness induction runs over the layer alone.
-/
import Por.Closure

/-!
# The chain

At a good `α < ω₁`, the top predicates of height `α` agree with those of `ω₁`
below `α` (`top_abs`). The proof is an induction on the layer.

The chain `cC 0 < cC 1 < ⋯` is made of closure points, so all of them are good.
Any two members are related at every layer (`chain_R`).
-/

open Classical Cardinal Ordinal

namespace Por

/-- One step of the absoluteness induction. -/
theorem sat_abs {α : Ord} (hα : Good α) {j : ℕ}
    (ih : ∀ i < j, ∀ x < α, (R i x α ↔ R i x Om))
    {m n : ℕ} {D : Set (Diag m n)} {bb r : ℕ} {p : ℕ → Ord}
    (hn : n ≤ r + bb) (hp : ∀ i < r, p i < α) :
    Sat relR (topR α) (below j) α m n D bb r p ↔
      Sat relR (topR Om) (below j) Om m n D bb r p := by
  have h1 : Sat relR (topR α) (below j) α m n D bb r p ↔
      Sat relR (topR Om) (below j) α m n D bb r p := by
    refine sat_congr fun y hy => diagM_congr (fun _ _ _ _ _ _ => Iff.rfl) ?_
    intro i _ a ha hallow
    exact ih i hallow _ (cat_bound hn hp hy a ha)
  rw [h1]
  exact sat_mask.trans ((hα m n _ bb r p hn hp).trans sat_mask.symm)

/-- Absoluteness of the top predicates at a good `α`: `Top^α = Top^{ω₁}` below `α`. -/
theorem top_abs {α : Ord} (hα : Good α) (hαΩ : α < Om) (j : ℕ) :
    ∀ x < α, (R j x α ↔ R j x Om) := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro x hx
    rw [R_iff, R_iff]
    refine ⟨fun ⟨_, e⟩ => ⟨hx.trans hαΩ, ?_⟩, fun ⟨_, e⟩ => ⟨hx, ?_⟩⟩
    · intro m n D bb r p hn hp
      rw [← sat_abs hα ih hn (fun i hi => (hp i hi).trans hx)]
      exact e m n D bb r p hn hp
    · intro m n D bb r p hn hp
      rw [sat_abs hα ih hn (fun i hi => (hp i hi).trans hx)]
      exact e m n D bb r p hn hp

/-- `lam 0 < lam (lam 0) < ⋯`, all good. -/
noncomputable def cC : ℕ → Ord
  | 0 => lam 0
  | t + 1 => lam (cC t)

theorem cC_lt : ∀ t, cC t < Om
  | 0 => lam_lt om_pos
  | t + 1 => lam_lt (cC_lt t)

theorem cC_strictMono : StrictMono cC :=
  strictMono_nat_of_lt_succ fun t => lt_lam (cC t)

theorem cC_good : ∀ t, Good (cC t)
  | 0 => lam_good om_pos
  | t + 1 => lam_good (cC_lt t)

/-- Members of the chain are related at every layer. -/
theorem chain_R {i j : ℕ} (hij : i < j) (k : ℕ) : R k (cC i) (cC j) := by
  have hlt : cC i < cC j := cC_strictMono hij
  refine R_iff.mpr ⟨hlt, ?_⟩
  intro m n D bb r p hn hp
  have hA : ∀ {γ : Ord}, Good γ → γ < Om → ∀ {q : ℕ → Ord}, (∀ i < r, q i < γ) →
      (Sat relR (topR γ) (below k) γ m n D bb r q ↔
        Sat relR (topR Om) full Om m n (maskD (below k) ⁻¹' D) bb r q) := by
    intro γ hγ hγΩ q hq
    rw [← hγ m n _ bb r q hn hq, ← sat_mask]
    refine sat_congr fun y hy => diagM_congr (fun _ _ _ _ _ _ => Iff.rfl) ?_
    intro i' _ a ha _
    exact top_abs hγ hγΩ i' _ (cat_bound hn hq hy a ha)
  rw [hA (cC_good i) (cC_lt i) hp, hA (cC_good j) (cC_lt j) fun i' hi' => (hp i' hi').trans hlt]

end Por
