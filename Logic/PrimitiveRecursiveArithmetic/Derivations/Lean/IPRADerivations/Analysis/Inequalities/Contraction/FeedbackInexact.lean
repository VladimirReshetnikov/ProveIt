import IPRADerivations.Analysis.Inequalities.Contraction.WeightedFeedback

/-!
# Inexact iteration budgets and the finite Neumann producer

Packet: `analysis/ipra_certified_continuation_2026-11-19`, `paper/sections/03_feedback.tex`, Sections
"Inexact iteration and genuinely simultaneous error budgets" and "A finite Neumann producer", in the setting of
`Analysis/WeightedFeedback` (`Cert`):

* `inexact_budget` (`eq:feedback-inexact`, cleared by `2ⁿ`): for two trajectories in the domain with defects
  `|u_{j+1,i} − T_i(u_j)| ≤ ε_j w_i`, `|v_{j+1,i} − T_i(v_j)| ≤ η_j w_i` and `|u_{0,k} − v_{0,k}| ≤ E₀ w_k`,
  `2ⁿ |u_{n,i} − v_{n,i}| ≤ (E₀ + ∑_{j<n} 2^{j+1} (ε_j + η_j)) w_i` ("This proof handles all coupled
  coordinates at once": the bound is carried componentwise for all coordinates by the scaled contraction);
* `neumann_identity` (the residual identity `(I − A) z_n = b − Aⁿ b`, without subtraction):
  `z_n + Aⁿ b = A z_n + b` for `z₀ = 0`, `z_{n+1} = A z_n + b`;
* `neumann_power` ("If `|b_i| ≤ B w_i`, the contraction lemma for the linear map gives
  `|(Aⁿ b)_i| ≤ B 2^{−n} w_i`"): `2ⁿ (Aⁿ b)_i ≤ B w_i` for natural `b`.
-/

namespace LeanProofs.IPRA.Analysis.FeedbackInexact

open_ipra
open LeanProofs.IPRA.Analysis.WeightedFeedback (Cert contract_scaled)
open LeanProofs.IPRA.Analysis.WeightedRowContraction (half_contract_row)
open LeanProofs.IPRA.Probability.EventAlgebraMetric (wsum)
open LeanProofs.IPRA.Probability.BayesEvents (wsum_mul wsum_zero)
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.Probability.ClipLaws (ad_triangle)

variable {n m : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

variable {a : Fin m → Fin m → PTm n} {w : Fin m → PTm n} {T : (Fin m → PTm n) → Fin m → PTm n}
  {D : (Fin m → PTm n) → Prop}

/-! ## Inexact iteration -/

/-- The cleared budget `E₀ + ∑_{j<n} 2^{j+1} (ε_j + η_j)`. -/
def budget (E₀ : PTm n) (ε η : ℕ → PTm n) : ℕ → PTm n
  | 0 => E₀
  | k + 1 => budget E₀ ε η k + num (2 ^ (k + 1)) * (ε k + η k)

/-- `eq:feedback-inexact`, cleared: `2ⁿ |u_{n,i} − v_{n,i}| ≤ budget_n w_i`. -/
theorem inexact_budget (C : Cert Γ a w T D) {u v : ℕ → Fin m → PTm n} (hu : ∀ j, D (u j)) (hv : ∀ j, D (v j))
    {E₀ : PTm n} {ε η : ℕ → PTm n} (h0 : ∀ k, Γ ⊢[PRAAx] le (ad (u 0 k) (v 0 k)) (E₀ * w k))
    (hε : ∀ j i, Γ ⊢[PRAAx] le (ad (u (j + 1) i) (T (u j) i)) (ε j * w i))
    (hη : ∀ j i, Γ ⊢[PRAAx] le (ad (v (j + 1) i) (T (v j) i)) (η j * w i)) :
    ∀ k i, Γ ⊢[PRAAx] le (num (2 ^ k) * ad (u k i) (v k i)) (budget E₀ ε η k * w i)
  | 0, i => by
    have h := h0 i
    show Γ ⊢[PRAAx] le (num 1 * ad (u 0 i) (v 0 i)) (E₀ * w i)
    ipra_le sl h
  | k + 1, i => by
    have c := contract_scaled C (hu k) (hv k) (s := num (2 ^ k)) (r := budget E₀ ε η k)
      (fun j => inexact_budget C hu hv h0 hε hη k j) i
    have t1 := ad_triangle (Γ := Γ) (u (k + 1) i) (T (u k) i) (v (k + 1) i)
    have t2 := ad_triangle (Γ := Γ) (T (u k) i) (T (v k) i) (v (k + 1) i)
    have e1 := hε k i
    have e2 := hη k i
    show Γ ⊢[PRAAx] le (num (2 ^ (k + 1)) * ad (u (k + 1) i) (v (k + 1) i))
      ((budget E₀ ε η k + num (2 ^ (k + 1)) * (ε k + η k)) * w i)
    ipra_le 2 ^ (k + 1) * (sl t1 + sl t2 + sl e1 + sl e2) + sl c using push_cast; ring

/-! ## The finite Neumann producer -/

theorem toG_wsum {α : Type} (u f : α → PTm n) (L : List α) :
    Groth.ι (Q.mk Γ (wsum u f L)) = (L.map fun r => Groth.ι (Q.mk Γ (u r)) * Groth.ι (Q.mk Γ (f r))).sum := by
  induction L with
  | nil => simp [wsum, Q.mk_zero]
  | cons r L ih => simp [wsum, Q.mk_add, Q.mk_mul, map_add, map_mul, ih]

/-- `Aⁿ b`. -/
def apow (a : Fin m → Fin m → PTm n) (b : Fin m → PTm n) : ℕ → Fin m → PTm n
  | 0 => b
  | k + 1 => fun i => wsum (a i) (apow a b k) (List.finRange m)

/-- `z₀ = 0`, `z_{n+1} = A z_n + b`. -/
def neu (a : Fin m → Fin m → PTm n) (b : Fin m → PTm n) : ℕ → Fin m → PTm n
  | 0 => fun _ => zero
  | k + 1 => fun i => wsum (a i) (neu a b k) (List.finRange m) + b i

/-- The residual identity `z_n + Aⁿ b = A z_n + b`. -/
theorem neumann_identity (a : Fin m → Fin m → PTm n) (b : Fin m → PTm n) :
    ∀ k i, Γ ⊢[PRAAx] neu a b k i + apow a b k i ≐ wsum (a i) (neu a b k) (List.finRange m) + b i
  | 0, i => by
    have z := natEq (wsum_zero (Γ := Γ) (a i) (List.finRange m))
    apply deriveNat
    show Groth.ι (Q.mk Γ (zero + b i)) = Groth.ι (Q.mk Γ (wsum (a i) (fun _ => zero) (List.finRange m) + b i))
    simp only [Q.mk_add, map_add] at z ⊢
    rw [z]
  | k + 1, i => by
    have ih : ∀ j, Groth.ι (Q.mk Γ (neu a b k j)) + Groth.ι (Q.mk Γ (apow a b k j)) =
        Groth.ι (Q.mk Γ (neu a b (k + 1) j)) := fun j => by
      have := natEq (neumann_identity a b k j : Γ ⊢[PRAAx] _)
      simpa [Q.mk_add, map_add, neu] using this
    apply deriveNat
    show Groth.ι (Q.mk Γ (wsum (a i) (neu a b k) (List.finRange m) + b i +
        wsum (a i) (apow a b k) (List.finRange m))) =
      Groth.ι (Q.mk Γ (wsum (a i) (neu a b (k + 1)) (List.finRange m) + b i))
    simp only [Q.mk_add, map_add, toG_wsum]
    rw [show (List.finRange m).map (fun r => Groth.ι (Q.mk Γ (a i r)) * Groth.ι (Q.mk Γ (neu a b (k + 1) r))) =
        (List.finRange m).map (fun r => Groth.ι (Q.mk Γ (a i r)) * Groth.ι (Q.mk Γ (neu a b k r)) +
          Groth.ι (Q.mk Γ (a i r)) * Groth.ι (Q.mk Γ (apow a b k r))) from
        List.map_congr_left fun r _ => by rw [← ih r]; ring]
    rw [List.sum_map_add]
    ring

/-- `2ⁿ (Aⁿ b)_i ≤ B w_i` from the half certificate and `b_i ≤ B w_i`. -/
theorem neumann_power (hhalf : ∀ i, Γ ⊢[PRAAx] le (two * wsum (a i) w (List.finRange m)) (w i))
    {b : Fin m → PTm n} {B : PTm n} (hb : ∀ i, Γ ⊢[PRAAx] le (b i) (B * w i)) :
    ∀ k i, Γ ⊢[PRAAx] le (num (2 ^ k) * apow a b k i) (B * w i)
  | 0, i => by
    have h := hb i
    show Γ ⊢[PRAAx] le (num 1 * b i) (B * w i)
    ipra_le sl h
  | k + 1, i => by
    have hg : Γ ⊢[PRAAx] le (num (2 ^ k) * apow a b (k + 1) i)
        (wsum (a i) (fun j => num (2 ^ k) * apow a b k j) (List.finRange m)) := by
      show Γ ⊢[PRAAx] le (num (2 ^ k) * wsum (a i) (apow a b k) (List.finRange m))
        (wsum (a i) (fun j => num (2 ^ k) * apow a b k j) (List.finRange m))
      ipra_le 0 with natEq (wsum_mul (Γ := Γ) (a i) (apow a b k) (num (2 ^ k)) (List.finRange m))
    have c := half_contract_row (a i) w (fun j => num (2 ^ k) * apow a b k j) (List.finRange m)
      (fun j _ => neumann_power hhalf hb k j) (hhalf i) hg
    ipra_le sl c using push_cast; ring

end LeanProofs.IPRA.Analysis.FeedbackInexact
