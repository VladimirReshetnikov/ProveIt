import IPRADerivations.Analysis.GaussianEulerLogarithmicIntervalName
import IPRADerivations.Analysis.GaussianScalarExponentialProductTail

/-!
# Absolute bounds for original logarithmic compact quadratures

Each original sampled row has the finite majorant of the logarithmic
integrand. Summing over the actual grid and applying its original weight
multiplies that majorant by exactly the interval length.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicCompactBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerLogarithmicCompactName (evaluatorF fixedData raw_evaluator_at)
open GaussianEulerLogarithmicMultiplier (majorant lipschitz)
open GaussianEulerLogarithmicIntervalName (data nameF name_at)
open GaussianCompactRiemannName (sampleBody sampleData quadrature grid grid_inside sample_body_at mesh precision)
open GaussianEulerCompactAdditivity (intervalSource domain_of_inside)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded)
open GaussianScalarExponentialProductTail (termsBounded sum_bound)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem original_grid_row_bound (p i N j z R B a C E T : PTm n)
    (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    bounded (inst2 (sampleBody evaluatorF) i (sampleData p N a C E (fixedData j R E T z B))) (majorant j R E T) one := by
  let t := grid i N a C E
  have ha := h.andE₂.andE₁
  have hE := h.andE₁.andE₂.andE₁
  have time := domain_of_inside t a C E T ha hE h.andE₂.andE₂ (grid_inside i N a C E ha hE hN (le_of_lt hi))
  have sample := GaussianEulerLogarithmicCompactName.sample_bound p j z R B E T (fstT t) (sndT t) (.andI h.andE₁ time)
  have binding := (sample_body_at (Γ := Γ) evaluatorF i p N a C E (fixedData j R E T z B)).eqTrans
    (raw_evaluator_at p t j R E T z B)
  exact bound_congr binding.eqSymm (.eqRefl _) (.eqRefl _) sample

theorem original_grid_bound (p N j z R B a C E T : PTm n)
    (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    bounded (quadrature evaluatorF p N a C E (fixedData j R E T z B)) (C*majorant j R E T) E := by
  let sh (x : PTm n) := Syn.shift x
  have hs : Γ.map Fm.shift ⊢[PRAAx] intervalSource (sh z) (sh R) (sh B) (sh a) (sh C) (sh E) (sh T) :=
    by simpa [Fm.shift,Syn.shift,sh] using h.shift
  have ns : Γ.map Fm.shift ⊢[PRAAx] le one (sh N) := by simpa [Fm.shift,Syn.shift,one,sh] using hN.shift
  have rows : Γ ⊢[PRAAx] termsBounded (sampleBody evaluatorF) N (sampleData p N a C E (fixedData j R E T z B)) (majorant j R E T) one := by
    refine .allI (.impI ?_)
    simpa [termsBounded,Syn.shift,sh] using original_grid_row_bound (sh p) (var 0) (sh N) (sh j) (sh z) (sh R)
      (sh B) (sh a) (sh C) (sh E) (sh T) hs.wk ns.wk Prf.hyp0
  have hE := h.andE₁.andE₂.andE₁
  have hD : Γ ⊢[PRAAx] le one (E*N) := positive_product _ _ hE hN
  have finite := sum_bound _ _ _ _ _ (le_refl one) rows
  have scaled := bounded_product _ _ _ _ _ _ hD (le_refl one)
    (GaussianRationalRiemannRefinement.weight_bound C E N hE hN) finite
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (positive_product _ _ hD (le_refl one)) hE (le_congr (.eqRefl _) (by ipra_ring) (le_refl _)) scaled

theorem original_compact_bound (p j z R B a C E T : PTm n) (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) : Γ ⊢[PRAAx]
    bounded (ap2 nameF p (data j z R B a C E T)) (C*majorant j R E T) E :=
  bound_congr (name_at p j z R B a C E T).eqSymm (.eqRefl _) (.eqRefl _)
    (original_grid_bound (precision p T) (mesh p (lipschitz j R E T) T) j z R B a C E T h
      (GaussianCompactRiemannName.mesh_positive _ _ _))

theorem actual_original_logarithmic_compact_absolute_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (intervalSource (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      bounded (ap2 nameF (var 0) (data (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)))
        (var 6*majorant (var 1) (var 3) (var 7) (var 8)) (var 7)) :=
  closeUniv 9 (.impI (original_compact_bound _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicCompactBound
