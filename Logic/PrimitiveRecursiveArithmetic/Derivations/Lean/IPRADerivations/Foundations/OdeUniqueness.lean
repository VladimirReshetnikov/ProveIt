import IPRADerivations.Foundations.DiscreteGronwall
import IPRADerivations.Probability.MedianWeighted
import IPRADerivations.Foundations.EigenvalueBound
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.Header

/-!
# Quantitative uniqueness of controlled flows at the nodes

Packet: `foundations/ipra_local_global`, `paper/04_ode.tex`, Theorem `thm:ode-unique` ("Quantitative
uniqueness", `eq:ode-uniquefinite`) and the comparison of perturbed fields (`eq:ode-perturbation`).

Two controlled candidates are compared at the nodes `j t/N`, `j ≤ N`. In cleared natural numbers, the value
of candidate `i` at node `j` is `Yᵢ(j)`, its signed Euler displacement `h F(Yᵢ(j))` is `Pᵢ(j) − Mᵢ(j)`
(two natural tables, so no signed arithmetic is needed), and its controlled defect at the step `j → j + 1`
is bounded by `Cᵢ(j)` (`C h² + 2^{-p}` in `eq:ode-controlled`):

  `|Yᵢ(j+1) + Mᵢ(j) − (Yᵢ(j) + Pᵢ(j))| ≤ Cᵢ(j)`.

The field enters only through a Lipschitz comparison of the two displacements, with growth factor
`A/k = L h` and a field discrepancy `ε(j)` (zero for one field; `h ε` for two fields within `ε`):

  `k |(P₁ + M₂) − (P₂ + M₁)| ≤ A |Y₁ − Y₂| + k ε`.

* `step_tri`: `|Y₁' − Y₂'| ≤ C₁ + C₂ + |Y₁ − Y₂| + |d₁ − d₂|`, the triangle inequality through the two
  Euler predictions, with every displacement moved to the other side;
* `unique_step`: `k e(j+1) ≤ (k + A) e(j) + k (C₁ + C₂ + ε)` for `e(j) = |Y₁(j) − Y₂(j)|`, the recurrence
  `e_{j+1} ≤ (1 + L t/N) e_j + (C₁ + C₂)(t/N)² + 2·2^{-p}` of the paper (and, with `Cᵢ = 0`, the
  perturbation recurrence `e_{j+1} ≤ (1 + L h) e_j + h ε`);
* `recurrence`: the same for every `j < N`, from the universal step hypotheses;
* `uniqueness_nodes`: with `k = k₀ + 1 ≥ N`, `e(N) ≤ 3^A (e(0) + ∑_{j<N} δ(j))`, `δ = C₁ + C₂ + ε`
  (`DiscreteGronwall.gronwall_three`);
* `uniqueness_const` (`eq:ode-uniquefinite`): for a constant defect `δ` and `e(0) ≤ η`,
  `e(N) ≤ 3^A (η + N δ)`, i.e. `G ((C₁ + C₂) T²/N + 2 (N + 1) 2^{-p})` with `η = 2·2^{-p}`.

The choice of `N` and `p` from a requested accuracy and the passage to equality of the two name
families (regularity and reindexing) are not derived here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.OdeUniqueness

open_ipra
open LeanProofs.IPRA.Probability.Variance (ad sum_const_of)
open LeanProofs.IPRA.Foundations.EigenvalueBound (ad_le_of le_add_ad)
open LeanProofs.IPRA.Foundations.DiscreteGronwall (gronwall_three)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## One step -/

/-- `|y₁' − y₂'| ≤ c₁ + c₂ + |y₁ − y₂| + |(p₁ − m₁) − (p₂ − m₂)|`. -/
theorem step_tri {y₁ y₁' y₂ y₂' p₁ m₁ p₂ m₂ c₁ c₂ : PTm n}
    (d₁ : Γ ⊢[PRAAx] le (ad (y₁' + m₁) (y₁ + p₁)) c₁)
    (d₂ : Γ ⊢[PRAAx] le (ad (y₂' + m₂) (y₂ + p₂)) c₂) :
    Γ ⊢[PRAAx] le (ad y₁' y₂') (c₁ + c₂ + ad y₁ y₂ + ad (p₁ + m₂) (p₂ + m₁)) := by
  refine ad_le_of ?_ ?_
  · have a1 := le_add_ad (Γ := Γ) (y₁' + m₁) (y₁ + p₁)
    have a2 := le_add_ad (Γ := Γ) y₁ y₂
    have a3 := le_add_ad (Γ := Γ) (p₁ + m₂) (p₂ + m₁)
    have a4 := le_add_ad (Γ := Γ) (y₂ + p₂) (y₂' + m₂)
    ipra_le sl a1 + sl a2 + sl a3 + sl a4 + sl d₁ + sl d₂
  · have b1 := le_add_ad (Γ := Γ) (y₁ + p₁) (y₁' + m₁)
    have b2 := le_add_ad (Γ := Γ) y₂ y₁
    have b3 := le_add_ad (Γ := Γ) (p₂ + m₁) (p₁ + m₂)
    have b4 := le_add_ad (Γ := Γ) (y₂' + m₂) (y₂ + p₂)
    ipra_le sl b1 + sl b2 + sl b3 + sl b4 + sl d₁ + sl d₂

/-- The error recurrence `k e' ≤ (k + A) e + k (c₁ + c₂ + ε)`. -/
theorem unique_step {y₁ y₁' y₂ y₂' p₁ m₁ p₂ m₂ c₁ c₂ k A ε : PTm n}
    (d₁ : Γ ⊢[PRAAx] le (ad (y₁' + m₁) (y₁ + p₁)) c₁)
    (d₂ : Γ ⊢[PRAAx] le (ad (y₂' + m₂) (y₂ + p₂)) c₂)
    (lip : Γ ⊢[PRAAx] le (k * ad (p₁ + m₂) (p₂ + m₁)) (A * ad y₁ y₂ + k * ε)) :
    Γ ⊢[PRAAx] le (k * ad y₁' y₂') ((k + A) * ad y₁ y₂ + k * (c₁ + c₂ + ε)) := by
  have t := step_tri d₁ d₂
  ipra_le 𝔞 k * sl t + sl lip

/-! ## All nodes -/

section Nodes

variable (Y₁ Y₂ P₁ M₁ P₂ M₂ C₁ C₂ E : PTm 2)

/-- The error table `e(j) = |Y₁(j) − Y₂(j)|`. -/
abbrev eB : PTm 2 := ad Y₁ Y₂
/-- The defect table `δ(j) = C₁(j) + C₂(j) + ε(j)`. -/
abbrev dB : PTm 2 := C₁ + C₂ + E

theorem eB_at (j x : PTm n) : inst2 (eB Y₁ Y₂) j x = ad (inst2 Y₁ j x) (inst2 Y₂ j x) := by
  simp [inst2, PTm.subst_add, PTm.subst_monus]

theorem dB_at (j x : PTm n) :
    inst2 (dB C₁ C₂ E) j x = inst2 C₁ j x + inst2 C₂ j x + inst2 E j x := by
  simp [inst2, PTm.subst_add]

/-- The controlled defect of a candidate at every step `j < N`. -/
abbrev DefHyp (Y P M C : PTm 2) (N x : PTm n) : Fm PTm n :=
  Fm.all (lt (var 0) (Syn.shift N) ⟶
    le (ad (inst2 Y (succ (var 0)) (Syn.shift x) + inst2 M (var 0) (Syn.shift x))
        (inst2 Y (var 0) (Syn.shift x) + inst2 P (var 0) (Syn.shift x)))
      (inst2 C (var 0) (Syn.shift x)))

/-- The Lipschitz comparison of the two displacements at every step `j < N`. -/
abbrev LipHyp (N x k A : PTm n) : Fm PTm n :=
  Fm.all (lt (var 0) (Syn.shift N) ⟶
    le (Syn.shift k * ad (inst2 P₁ (var 0) (Syn.shift x) + inst2 M₂ (var 0) (Syn.shift x))
          (inst2 P₂ (var 0) (Syn.shift x) + inst2 M₁ (var 0) (Syn.shift x)))
      (Syn.shift A * ad (inst2 Y₁ (var 0) (Syn.shift x)) (inst2 Y₂ (var 0) (Syn.shift x)) +
        Syn.shift k * inst2 E (var 0) (Syn.shift x)))

theorem shift_add (a b : PTm n) : Syn.shift (a + b) = Syn.shift a + Syn.shift b := by
  simp [Syn.shift, PTm.subst_add]

variable {Y₁ Y₂ P₁ M₁ P₂ M₂ C₁ C₂ E}

/-- The error recurrence at every node `j < N`. -/
theorem recurrence {N x k A : PTm n}
    (h₁ : Γ ⊢[PRAAx] DefHyp Y₁ P₁ M₁ C₁ N x) (h₂ : Γ ⊢[PRAAx] DefHyp Y₂ P₂ M₂ C₂ N x)
    (hl : Γ ⊢[PRAAx] LipHyp Y₁ Y₂ P₁ M₁ P₂ M₂ E N x k A) :
    Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (Syn.shift k * inst2 (eB Y₁ Y₂) (succ (var 0)) (Syn.shift x))
        (Syn.shift (k + A) * inst2 (eB Y₁ Y₂) (var 0) (Syn.shift x) +
          Syn.shift k * inst2 (dB C₁ C₂ E) (var 0) (Syn.shift x))) := by
  refine .allI (.impI ?_)
  have a := Prf.impE h₁.allOpen.wk Prf.hyp0
  have b := Prf.impE h₂.allOpen.wk Prf.hyp0
  have c := Prf.impE hl.allOpen.wk Prf.hyp0
  rw [eB_at, eB_at, dB_at, shift_add]
  have s := unique_step a b c
  exact le_congr (.eqRefl _) (by apply deriveNat; ipra_simps; try ring) s

/-- `thm:ode-unique` at the nodes: `e(N) ≤ 3^A (e(0) + ∑_{j<N} δ(j))` for `N ≤ k = k₀ + 1`. -/
theorem uniqueness_nodes {N d k₀ A x : PTm n} (hk : Γ ⊢[PRAAx] N + d ≐ succ k₀)
    (h₁ : Γ ⊢[PRAAx] DefHyp Y₁ P₁ M₁ C₁ N x) (h₂ : Γ ⊢[PRAAx] DefHyp Y₂ P₂ M₂ C₂ N x)
    (hl : Γ ⊢[PRAAx] LipHyp Y₁ Y₂ P₁ M₁ P₂ M₂ E N x (succ k₀) A) :
    Γ ⊢[PRAAx] le (ad (inst2 Y₁ N x) (inst2 Y₂ N x))
      (pw (num 3) A * (ad (inst2 Y₁ zero x) (inst2 Y₂ zero x) + ap2 (sumF (dB C₁ C₂ E)) N x)) := by
  have g := gronwall_three (eB Y₁ Y₂) (dB C₁ C₂ E) x N d k₀ A hk (recurrence h₁ h₂ hl)
  rw [eB_at, eB_at] at g; exact g

/-- `eq:ode-uniquefinite`: for a constant defect `δ` and initial separation `e(0) ≤ η`,
`e(N) ≤ 3^A (η + N δ)`. -/
theorem uniqueness_const {N d k₀ A x δ η : PTm n} (hk : Γ ⊢[PRAAx] N + d ≐ succ k₀)
    (h₁ : Γ ⊢[PRAAx] DefHyp Y₁ P₁ M₁ C₁ N x) (h₂ : Γ ⊢[PRAAx] DefHyp Y₂ P₂ M₂ C₂ N x)
    (hl : Γ ⊢[PRAAx] LipHyp Y₁ Y₂ P₁ M₁ P₂ M₂ E N x (succ k₀) A)
    (hδ : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst2 (dB C₁ C₂ E) (var 0) (Syn.shift x) ≐ Syn.shift δ)))
    (h0 : Γ ⊢[PRAAx] le (ad (inst2 Y₁ zero x) (inst2 Y₂ zero x)) η) :
    Γ ⊢[PRAAx] le (ad (inst2 Y₁ N x) (inst2 Y₂ N x)) (pw (num 3) A * (η + N * δ)) := by
  have u := uniqueness_nodes hk h₁ h₂ hl
  have sc := natEq (sum_const_of (dB C₁ C₂ E) N δ x hδ)
  ipra_le sl u + 𝔞 (pw (num 3) A) * sl h0 using
    linear_combination (-𝔞 (pw (num 3) A)) * sc

end Nodes

end LeanProofs.IPRA.Foundations.OdeUniqueness
