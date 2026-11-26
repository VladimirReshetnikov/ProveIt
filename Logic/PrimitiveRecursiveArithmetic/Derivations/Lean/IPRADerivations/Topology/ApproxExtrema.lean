import IPRADerivations.Analysis.Inequalities.WeightedComparison.WeightedComparison

/-!
# Approximate extrema and the certified interval of the uniform metric

Packet: `topology/general_topology_ipra_2026-11-19`, `paper/sections/04_metric.tex`, Corollary
`cor:approximate-extrema` ("choose a largest rational approximation, at `x_k`. For every `x`,
`v(x) ≤ v(p_{σ(x)}) + η ≤ q_{σ(x)} + 2η ≤ q_{x_k} + 2η ≤ v(x_k) + 3η`") and the certified interval
`[Q_k − η, Q_k + 2η]` of Theorem `thm:computable-uniform-metric`, for natural terms: net values `v(p_i)`,
rational approximations `q_i` (cleared to a common scale) and the error `η`.

* `exists_max`, `exists_min`: the finite list of approximations has a largest and a smallest entry, as iPRA
  disjunctions over the net index (`isMax`, `isMin`, by `Analysis/WeightedComparison.max_exists` with unit and
  shifted weights);
* `max_le`, `min_ge`: in the branch of the extremal index `j`, every `q_i ≤ q_j` (resp. `q_j ≤ q_i`);
* `approx_max`: `v(x) ≤ v(p_i) + η`, `v(p_i) ≤ q_i + η`, `q_j ≤ v(p_j) + η` and `q_i ≤ q_j` give
  `v(x) ≤ v(p_j) + 3η`; `approx_min` is the symmetric bound `v(p_j) ≤ v(x) + 3η`;
* `sup_upper`: `h(x) ≤ Q + 2η` for the maximal approximation `Q = q_j` (the upper endpoint of the certified
  interval; the lower endpoint `Q ≤ h(p_j) + η` is the approximation hypothesis at `j`).
-/

namespace LeanProofs.IPRA.Topology.ApproxExtrema

open_ipra
open LeanProofs.IPRA.Analysis.WeightedComparison (lconj ldisj lconj_elim R max_exists)

variable {n m : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `q_j` is the largest entry. -/
def isMax (q : Fin m → PTm n) (j : Fin m) : Fm PTm n :=
  lconj (List.finRange m) fun i => R q (fun _ => one) i j

/-- `q_j` is the smallest entry. -/
def isMin (q : Fin m → PTm n) (j : Fin m) : Fm PTm n :=
  lconj (List.finRange m) fun i => R (fun _ => one) (fun k => succ (q k)) i j

theorem exists_max (q : Fin m → PTm n) {b : Fin m} {L : List (Fin m)} (hL : List.finRange m = b :: L) :
    Γ ⊢[PRAAx] ldisj (List.finRange m) (isMax q) := by
  have h := max_exists (Γ := Γ) q (fun _ => one) (fun _ => le_refl _) b L
  rw [← hL] at h
  exact h

theorem exists_min (q : Fin m → PTm n) {b : Fin m} {L : List (Fin m)} (hL : List.finRange m = b :: L) :
    Γ ⊢[PRAAx] ldisj (List.finRange m) (isMin q) := by
  have h := max_exists (Γ := Γ) (fun _ => one) (fun k => succ (q k)) (fun k => by ipra_le 𝔟 (q k)) b L
  rw [← hL] at h
  exact h

theorem max_le (q : Fin m → PTm n) (j i : Fin m) : (isMax q j :: Γ) ⊢[PRAAx] le (q i) (q j) := by
  have h : (isMax q j :: Γ) ⊢[PRAAx] le (q i * one) (q j * one) :=
    lconj_elim (Prf.hyp0 : (isMax q j :: Γ) ⊢[PRAAx] isMax q j) (List.mem_finRange i)
  ipra_le sl h

theorem min_ge (q : Fin m → PTm n) (j i : Fin m) : (isMin q j :: Γ) ⊢[PRAAx] le (q j) (q i) := by
  have h : (isMin q j :: Γ) ⊢[PRAAx] le (one * succ (q j)) (one * succ (q i)) :=
    lconj_elim (Prf.hyp0 : (isMin q j :: Γ) ⊢[PRAAx] isMin q j) (List.mem_finRange i)
  ipra_le sl h

variable {vx vi vj qi qj η : PTm n}

/-- `cor:approximate-extrema`: `v(x) ≤ v(p_j) + 3η` at the index of the largest approximation. -/
theorem approx_max (h₁ : Γ ⊢[PRAAx] le vx (vi + η)) (h₂ : Γ ⊢[PRAAx] le vi (qi + η))
    (h₃ : Γ ⊢[PRAAx] le qj (vj + η)) (hmax : Γ ⊢[PRAAx] le qi qj) :
    Γ ⊢[PRAAx] le vx (vj + num 3 * η) := by
  ipra_le sl h₁ + sl h₂ + sl h₃ + sl hmax

/-- The approximate minimum: `v(p_j) ≤ v(x) + 3η` at the index of the smallest approximation. -/
theorem approx_min (h₁ : Γ ⊢[PRAAx] le vi (vx + η)) (h₂ : Γ ⊢[PRAAx] le qi (vi + η))
    (h₃ : Γ ⊢[PRAAx] le vj (qj + η)) (hmin : Γ ⊢[PRAAx] le qj qi) :
    Γ ⊢[PRAAx] le vj (vx + num 3 * η) := by
  ipra_le sl h₁ + sl h₂ + sl h₃ + sl hmin

/-- The upper endpoint of the certified interval: `h(x) ≤ Q + 2η` for the maximal approximation `Q = q_j`. -/
theorem sup_upper (h₁ : Γ ⊢[PRAAx] le vx (vi + η)) (h₂ : Γ ⊢[PRAAx] le vi (qi + η))
    (hmax : Γ ⊢[PRAAx] le qi qj) : Γ ⊢[PRAAx] le vx (qj + num 2 * η) := by
  ipra_le sl h₁ + sl h₂ + sl hmax

end LeanProofs.IPRA.Topology.ApproxExtrema
