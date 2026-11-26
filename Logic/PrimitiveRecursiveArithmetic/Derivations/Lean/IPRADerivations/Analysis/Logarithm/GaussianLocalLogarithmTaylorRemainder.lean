import IPRADerivations.Analysis.Logarithm.GaussianFiniteLogarithmTaylorRemainder
import IPRADerivations.Analysis.Logarithm.GaussianLocalLogarithmName
import IPRADerivations.Analysis.Names.Rates.GaussianNamedInverseRate
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaCanonicalExponent

/-!
# Arbitrary-order Taylor remainder for the original local Gaussian logarithm

The degree-(m) polynomial is the ordinary Mercator sum. The original
rounded logarithm sample has the geometric tail
(R^{m+1}/((m+1)(N-R)N^m)) plus its dyadic observation error.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianLocalLogarithmTaylorRemainder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFiniteLogarithmPolynomial (value sourceTerm)
open GaussianFiniteLogarithmTaylorRemainder (numerator denominator denominator_positive)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianLocalLogarithmName (source point pointF point_at)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianRationalHorner (ofGaussian ofGaussian_represents positive_product)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_radius_mono distance_triangle_same)
open GaussianRationalMetric (bounded bounded_of_cleared distanceBounded)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num monus pred)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def polynomial (m z N : PTm n) : PTm n := value m (ofGaussian z N)
def observationNumerator (p m R N : PTm n) : PTm n := numerator R m*unit p+denominator R N m
def observationDenominator (p m R N : PTm n) : PTm n := denominator R N m*unit p

@[simp] theorem subst_polynomial {l : ℕ} (σ : Fin n → PTm l) (m z N : PTm n) :
    Syn.subst σ (polynomial m z N) = polynomial (Syn.subst σ m) (Syn.subst σ z) (Syn.subst σ N) :=
  by simp [polynomial]

@[simp] theorem subst_observationNumerator {l : ℕ} (σ : Fin n → PTm l) (p m R N : PTm n) :
    Syn.subst σ (observationNumerator p m R N) =
      observationNumerator (Syn.subst σ p) (Syn.subst σ m) (Syn.subst σ R) (Syn.subst σ N) :=
  by simp [observationNumerator]

@[simp] theorem subst_observationDenominator {l : ℕ} (σ : Fin n → PTm l) (p m R N : PTm n) :
    Syn.subst σ (observationDenominator p m R N) =
      observationDenominator (Syn.subst σ p) (Syn.subst σ m) (Syn.subst σ R) (Syn.subst σ N) :=
  by simp [observationDenominator]

theorem half_disk_radius_strict (R N : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hR : Γ ⊢[PRAAx] le (two*R) N) :
    Γ ⊢[PRAAx] lt R N := by
  refine .orE (zero_or_succ R) ?_ ?_
  · exact le_congr (congrSucc Prf.hyp0).eqSymm (.eqRefl _) hN.wk
  · have positive : (R ≐ succ (pred R)) :: Γ ⊢[PRAAx] le one R :=
      le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ _)
    have next : (R ≐ succ (pred R)) :: Γ ⊢[PRAAx] le (succ R) (two*R) :=
      le_congr (by ipra_ring) (by ipra_ring) (add_le_add_right R positive)
    exact le_trans next hR.wk

theorem radius_strict (z R N : PTm n) (h : Γ ⊢[PRAAx] source z R N) : Γ ⊢[PRAAx] lt R N :=
  half_disk_radius_strict R N h.andE₁ h.andE₂.andE₂

private theorem relative_disk (z R N : PTm n) (h : Γ ⊢[PRAAx] source z R N) :
    Γ ⊢[PRAAx] bounded (ofGaussian z N) R N :=
  bounded_of_cleared _ _ _ _ _ h.andE₁ h.andE₁ (ofGaussian_represents _ _ h.andE₁)
    (le_congr (mul_comm _ _) (.eqRefl _) (mul_le_mul_right (N*N) h.andE₂.andE₁))

theorem finite_comparison_at_radius (L m z R N A D : PTm n) (h : Γ ⊢[PRAAx] source z R N)
    (hm : Γ ⊢[PRAAx] le m (L+two)) (hD : Γ ⊢[PRAAx] le one D) (hAD : Γ ⊢[PRAAx] lt A D)
    (hw : Γ ⊢[PRAAx] bounded (ofGaussian z N) A D) :
    Γ ⊢[PRAAx] distanceBounded (GaussianFiniteLogarithmSampler.sample z N L) (polynomial m z N)
      (numerator A m) (denominator A D m) := by
  let w := ofGaussian z N
  let r := monus (L+two) m
  have e := GaussianRationalFiniteSum.sum_index_congr sourceTerm (eq_add_of_le hm).eqSymm (.eqRefl w)
  have read := e.eqTrans (GaussianFiniteLogarithmSampler.value_eq_original_sample z N L h.andE₁)
  exact distance_congr read (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianFiniteLogarithmTaylorRemainder.remainder m r w A D hD hAD hw)

private theorem earlier_rounding (p j z R N : PTm n) (h : Γ ⊢[PRAAx] source z R N) :
    Γ ⊢[PRAAx] distanceBounded (point p z R N)
      (GaussianFiniteLogarithmSampler.sample z N (DyadicComplexLogarithm.precision (p+j))) one (unit p) := by
  let U := DyadicComplexLogarithm.unit p
  let E := DyadicComplexLogarithm.unit (p+j)
  have hU := GaussianLocalLogarithmName.unit_positive (Γ := Γ) p
  have hE := GaussianLocalLogarithmName.unit_positive (Γ := Γ) (p+j)
  have order : Γ ⊢[PRAAx] le U E :=
    le_congr (one_mul _) ((mul_comm _ _).eqTrans (DyadicComplexLogarithm.unit_add p j).eqSymm)
      (mul_le_mul_right U (unit_positive j))
  have first := distance_symmetric _ _ _ _ hU (GaussianLocalLogarithmName.ordered_distance p j z R N h)
  have second := distance_radius_mono _ _ _ _ (num 4) U hE hU (mul_le_mul_right _ order |> fun b => le_congr (mul_comm _ _) (mul_comm _ _) b)
    (GaussianLocalLogarithmName.observation_distance (p+j) z R N h.andE₁)
  have sum := distance_triangle_same _ _ _ _ _ _ hU first second
  have fit : Γ ⊢[PRAAx] le ((num 9+num 4)*unit p) (one*U) :=
    le_congr (.eqRefl _) (congrMul (.eqRefl _) (GaussianLocalLogarithmName.unit_factor p)).eqSymm
      (le_of_eq_add (d := num 3*unit p) (by ipra_ring))
  exact distance_congr (point_at p z R N).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ one (unit p) hU (unit_positive p) fit sum)

theorem remainder_at_radius (p m z R N A D : PTm n) (h : Γ ⊢[PRAAx] source z R N)
    (hD : Γ ⊢[PRAAx] le one D) (hAD : Γ ⊢[PRAAx] lt A D) (hw : Γ ⊢[PRAAx] bounded (ofGaussian z N) A D) :
    Γ ⊢[PRAAx] distanceBounded (point p z R N) (polynomial m z N)
      (observationNumerator p m A D) (observationDenominator p m A D) := by
  let L := DyadicComplexLogarithm.precision (p+m)
  have hd := denominator_positive A D m hD hAD
  have hm : Γ ⊢[PRAAx] le m (L+two) :=
    le_trans (le_add_left m p) (le_trans (le_add_right _ _) (le_add_right _ _))
  have raw := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ (unit_positive p) hd
    (earlier_rounding p m z R N h) (finite_comparison_at_radius L m z R N A D h hm hD hAD hw)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold observationNumerator; ipra_ring) (mul_comm _ _) raw

theorem original_remainder (p m z R N : PTm n) (h : Γ ⊢[PRAAx] source z R N) :
    Γ ⊢[PRAAx] distanceBounded (point p z R N) (polynomial m z N)
      (observationNumerator p m R N) (observationDenominator p m R N) :=
  remainder_at_radius p m z R N R N h h.andE₁ (radius_strict z R N h) (relative_disk z R N h)

theorem rate_at_radius (m z R N C E : PTm n) (h : Γ ⊢[PRAAx] source z R N)
    (hE : Γ ⊢[PRAAx] le one E) (hCE : Γ ⊢[PRAAx] lt C E) (hw : Γ ⊢[PRAAx] bounded (ofGaussian z N) C E) :
    Γ ⊢[PRAAx] independentRate pointF constantF (GaussianLocalLogarithmName.data z R N) (polynomial m z N)
      (numerator C m) (denominator C E m) := by
  refine .allI (.allI ?_)
  let sh (u : PTm n) := Syn.shift (Syn.shift u)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  let D := denominator (sh C) (sh E) (sh m)
  let A := numerator (sh C) (sh m)
  have hs : Δ ⊢[PRAAx] source (sh z) (sh R) (sh N) := by simpa [Δ,Fm.shift,Syn.shift,sh] using h.shift.shift
  have hEs : Δ ⊢[PRAAx] le one (sh E) := by simpa [Δ,Fm.shift,Syn.shift,sh,one] using hE.shift.shift
  have hCs : Δ ⊢[PRAAx] lt (sh C) (sh E) := by simpa [Δ,Fm.shift,Syn.shift,sh] using hCE.shift.shift
  have hws : Δ ⊢[PRAAx] bounded (ofGaussian (sh z) (sh N)) (sh C) (sh E) :=
    by simpa [Δ,Fm.shift,Syn.shift,sh] using hw.shift.shift
  have hd := denominator_positive (sh C) (sh E) (sh m) hEs hCs
  have h₁ := positive_product _ _ hd (unit_positive p)
  have h₂ := positive_product _ _ h₁ (unit_positive q)
  have grow : Δ ⊢[PRAAx] le
      (observationNumerator p (sh m) (sh C) (sh E)*rateDenominator D p q)
      (rateNumerator A D p q*observationDenominator p (sh m) (sh C) (sh E)) :=
    le_of_eq_add (d := D*D*unit p*unit p) (by unfold observationNumerator observationDenominator rateNumerator rateDenominator A D; ipra_ring)
  have near := distance_radius_mono _ _ _ _ _ _ h₁ h₂ grow (remainder_at_radius p (sh m) (sh z) (sh R) (sh N) (sh C) (sh E) hs hEs hCs hws)
  simpa only [independentRate,GaussianLocalLogarithmName.subst_data,subst_polynomial,
    GaussianFiniteLogarithmTaylorRemainder.subst_numerator,GaussianFiniteLogarithmTaylorRemainder.subst_denominator,
    GaussianLocalLogarithmName.point,rateDenominator,Syn.shift,sh,Δ,p,q,A,D] using
    distance_congr (.eqRefl _) (constant_at q (polynomial (sh m) (sh z) (sh N))).eqSymm (.eqRefl _) (.eqRefl _) near

theorem rate (m z R N : PTm n) (h : Γ ⊢[PRAAx] source z R N) :
    Γ ⊢[PRAAx] independentRate pointF constantF (GaussianLocalLogarithmName.data z R N) (polynomial m z N)
      (numerator R m) (denominator R N m) :=
  rate_at_radius m z R N R N h h.andE₁ (radius_strict z R N h) (relative_disk z R N h)

theorem actual_local_Mercator_Taylor_remainder_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let p := var 0
     let m := var 1
     let z := var 2
     let R := var 3
     let N := var 4
     source z R N ⟶ distanceBounded (point p z R N) (polynomial m z N)
       (observationNumerator p m R N) (observationDenominator p m R N)) :=
  closeUniv 5 (.impI (original_remainder _ _ _ _ _ Prf.hyp0))

theorem actual_local_Mercator_Taylor_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (let m := var 0
     let z := var 1
     let R := var 2
     let N := var 3
     source z R N ⟶ independentRate pointF constantF (GaussianLocalLogarithmName.data z R N) (polynomial m z N)
       (numerator R m) (denominator R N m)) :=
  closeUniv 4 (.impI (rate _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianLocalLogarithmTaylorRemainder
