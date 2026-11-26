import IPRADerivations.Analysis.Polynomials.RootFinding.Adequacy.GaussianRootSamples
import IPRADerivations.Analysis.RationalArithmetic.Distances.GaussianRationalDistanceOrder
import IPRADerivations.Analysis.Polynomials.Horner.GaussianRationalHornerPerturbation

/-!
# Coherence of the actual approximate root-product coefficients

The original coefficient-name condition and both actual factorization
errors imply the source bound 4·2^(-E(t)) for u≥t. The two polynomials are
the actual reconstructed outputs, with the same descending coefficient
order as the sampled polynomials. No output-coherence premise is used.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRootCoefficientCoherence

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (distanceBounded)
open LeanProofs.IPRA.Analysis.GaussianRationalDistanceOrder
  (distance_congr distance_symmetric distance_radius_mono distance_triangle_same)
open LeanProofs.IPRA.Analysis.GaussianRootSamples
  (polynomial productPolynomial polynomial_coefficient coefficient_error)
open LeanProofs.IPRA.Analysis.GaussianRootSchedule
  (four precision toleranceDenominator tolerance_positive tolerance_monotone)
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (CN CN_at)
open LeanProofs.IPRA.Analysis.GaussianFactorParameters (monicRD)
open LeanProofs.IPRA.Analysis.GaussianRationalHornerPerturbation (coefficientErrors)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)

variable {n : ℕ} {Γ : List (Fm PTm n)}

alias reversed_coefficient_index := Common.monus_succ_lt

theorem sampled_coefficient_distance (a : PR 3) (N R t u x j : PTm n)
    (hCN : Γ ⊢[PRAAx] CN a N x) (hj : Γ ⊢[PRAAx] lt j N)
    (htu : Γ ⊢[PRAAx] le t u) : Γ ⊢[PRAAx]
    distanceBounded (entry (polynomial a N R t x) (succ j))
      (entry (polynomial a N R u x) (succ j)) two (toleranceDenominator N R t) := by
  let D := toleranceDenominator N R t
  let F := toleranceDenominator N R u
  have dpos : Γ ⊢[PRAAx] le one D := tolerance_positive _ _ _
  have fpos : Γ ⊢[PRAAx] le one F := tolerance_positive _ _ _
  have df : Γ ⊢[PRAAx] le D F := tolerance_monotone _ _ _ _ htu
  have source : Γ ⊢[PRAAx] distanceBounded
      (entry (polynomial a N R t x) (succ j)) (entry (polynomial a N R u x) (succ j)) (D+F) (D*F) :=
    distance_congr (polynomial_coefficient a N R t x j hj).eqSymm
      (polynomial_coefficient a N R u x j hj).eqSymm (.eqRefl _) (.eqRefl _)
      (CN_at a N x (monus N (succ j)) (precision N R t) (precision N R u) hCN
        (reversed_coefficient_index _ _ hj))
  have budget : Γ ⊢[PRAAx] le ((D+F)*D) (two*(D*F)) :=
    le_congr (.eqRefl _) (by ipra_ring)
      (mul_le_mul_right D (add_le_add₂ df (le_refl F)))
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ dpos fpos) dpos budget source

theorem product_coefficient_distance (step a : PR 3) (N R t u x j : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hCN : Γ ⊢[PRAAx] CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (hj : Γ ⊢[PRAAx] lt j N)
    (htu : Γ ⊢[PRAAx] le t u) : Γ ⊢[PRAAx]
    distanceBounded (entry (productPolynomial step a N R t x) (succ j))
      (entry (productPolynomial step a N R u x) (succ j)) four (toleranceDenominator N R t) := by
  have dpos := tolerance_positive (Γ := Γ) N R t
  have fpos := tolerance_positive (Γ := Γ) N R u
  have first := distance_symmetric _ _ _ _ dpos (coefficient_error step a N R t x (succ j) hRD hN hj)
  have middle := sampled_coefficient_distance a N R t u x j hCN hj htu
  have last := distance_radius_mono _ _ _ _ one (toleranceDenominator N R t) fpos dpos
    (le_congr (one_mul _).eqSymm (one_mul _).eqSymm (tolerance_monotone N R t u htu))
    (coefficient_error step a N R u x (succ j) hRD hN hj)
  have combined := distance_triangle_same _ _ _ _ _ _ dpos
    (distance_triangle_same _ _ _ _ _ _ dpos first middle) last
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold four; ipra_ring) (.eqRefl _) combined

theorem product_coefficient_errors (step a : PR 3) (N R t u x : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hCN : Γ ⊢[PRAAx] CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (htu : Γ ⊢[PRAAx] le t u) : Γ ⊢[PRAAx]
    coefficientErrors (productPolynomial step a N R t x) (productPolynomial step a N R u x)
      N four (toleranceDenominator N R t) := by
  refine .allI (.impI ?_)
  have rd : Γ.map Fm.shift ⊢[PRAAx] monicRD step := by
    simpa only [Fm.shift,GaussianFactorParameters.subst_monicRD] using hRD.shift
  have cn : Γ.map Fm.shift ⊢[PRAAx] CN a (Syn.shift N) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianCoefficientNameBounds.subst_CN,Syn.shift] using hCN.shift
  have hn : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,Syn.shift] using hN.shift
  have tu : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift t) (Syn.shift u) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using htu.shift
  simpa only [Syn.shift,GaussianRootSamples.subst_productPolynomial,
    GaussianRootSchedule.subst_four,GaussianRootSchedule.subst_toleranceDenominator] using
    product_coefficient_distance step a (Syn.shift N) (Syn.shift R) (Syn.shift t) (Syn.shift u)
      (Syn.shift x) (var 0) rd.wk cn.wk hn.wk Prf.hyp0 tu.wk

theorem root_product_coefficient_coherence_closed (step a : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (monicRD step ⟶ CN a (var 0) (var 4) ⟶ le one (var 0) ⟶ le (var 2) (var 3) ⟶
      coefficientErrors (productPolynomial step a (var 0) (var 1) (var 2) (var 4))
        (productPolynomial step a (var 0) (var 1) (var 3) (var 4)) (var 0) four
          (toleranceDenominator (var 0) (var 1) (var 2))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI
    (product_coefficient_errors _ _ _ _ _ _ _ (Prf.wk hyp2) hyp2 Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianRootCoefficientCoherence
