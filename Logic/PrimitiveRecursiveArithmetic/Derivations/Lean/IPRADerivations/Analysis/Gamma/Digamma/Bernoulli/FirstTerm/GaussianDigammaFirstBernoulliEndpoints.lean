import IPRADerivations.Analysis.Gamma.Digamma.Bernoulli.FirstTerm.GaussianDigammaFirstBernoulliPanelSum
import IPRADerivations.Analysis.Stirling.AllOrders.PowerIntegrals.GaussianStirlingAllOrderPowerIntegralMesh

/-!
# Exact antiderivative endpoint correction in the first digamma panel

The inverse-square and inverse-cube primitives, multiplied by the
actual partial-fraction coefficients, combine to the trapezoidal
endpoint average of the original reciprocal function.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianDigammaFirstBernoulliEndpoints

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianDigammaFirstBernoulliPanelSum (squareCoeff cubeCoeff)
open GaussianStirlingAllOrderPowerIntegralMeshCells (primitive)
open GaussianStirlingAllOrderDiscreteParts (sub)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalHorner (positive_product)
open RationalAlgebra (add_congr multiply_congr negative_congr)
open RationalArithmetic (add add_guard multiply)
open RationalNonnegativePowers (fraction_congr)
open RationalNormalForm (normalize_well_formed)
open RationalRepresentations (represents_add represents_multiply represents_negative)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def trapezoid (U B : PTm n) : PTm n := add (fraction B (two*U)) (fraction B (two*(U+B)))

def endpointCorrection (U B : PTm n) : PTm n :=
  sub (multiply (squareCoeff U B) (sub (primitive 2 U B) (primitive 2 (U+B) B)))
    (multiply (cubeCoeff U B) (sub (primitive 3 U B) (primitive 3 (U+B) B)))

theorem exact_correction (U B : PTm n) (hU : Γ ⊢[PRAAx] le one U) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] endpointCorrection U B ≐ trapezoid U B := by
  let V := U+B
  let E := two*(U*U)
  let F := two*(V*V)
  let BB := B*B
  let a := fraction B U
  let b := fraction B V
  let c := fraction BB E
  let d := fraction BB F
  have hV : Γ ⊢[PRAAx] le one V := le_trans hU (le_add_right _ _)
  have h2 := RationalAlgebra.two_positive (Γ := Γ)
  have hE := positive_product _ _ h2 (positive_product _ _ hU hU)
  have hF := positive_product _ _ h2 (positive_product _ _ hV hV)
  have hBB := positive_product _ _ hB hB
  have squares (u : PTm n) : Γ ⊢[PRAAx] primitive 2 u B ≐ fraction B u :=
    fraction_congr (pw_one _) ((congrMul (.eqRefl one) (pw_one _)).eqTrans (one_mul _))
  have cubes (u : PTm n) : Γ ⊢[PRAAx] primitive 3 u B ≐ fraction BB (two*(u*u)) := by
    have eq (x : PTm n) : Γ ⊢[PRAAx] pw x two ≐ x*x :=
      (pw_succ x one).eqTrans (congrMul (pw_one x) (.eqRefl x))
    exact fraction_congr (eq B) (congrMul (.eqRefl two) (eq u))
  have pre : Γ ⊢[PRAAx] endpointCorrection U B ≐
      sub (multiply (squareCoeff U B) (sub a b)) (multiply (cubeCoeff U B) (sub c d)) :=
    add_congr (multiply_congr (.eqRefl _) (add_congr (squares U) (negative_congr (squares V))))
      (negative_congr (multiply_congr (.eqRefl _) (add_congr (cubes U) (negative_congr (cubes V)))))
  refine pre.eqTrans ?_
  have p := represents_add _ _ _ _ _ _ (fraction_represents B U hU)
    (represents_negative _ _ _ (fraction_represents B V hV))
  have q := represents_add _ _ _ _ _ _ (fraction_represents BB E hE)
    (represents_negative _ _ _ (fraction_represents BB F hF))
  have s := represents_multiply _ _ _ _ _ _ (fraction_represents (two*U+B) B hB) p
  have t := represents_multiply _ _ _ _ _ _ (fraction_represents (U*V) BB hBB) q
  have rep := represents_add _ _ _ _ _ _ s (represents_negative _ _ _ t)
  have hP := positive_product _ _ (positive_product _ _ hB (positive_product _ _ hU hV))
    (positive_product _ _ hBB (positive_product _ _ hE hF))
  have hu := positive_product _ _ h2 hU
  have hv := positive_product _ _ h2 hV
  have rep' := represents_add _ _ _ _ _ _ (fraction_represents B (two*U) hu) (fraction_represents B (two*V) hv)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (add_guard _ _) (add_guard _ _) rep rep' hP
    (positive_product _ _ hu hv)
  apply ZT.derive
  dsimp only [V,BB,E,F]
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_neg,ZT.toZ_ofNat]
  ipra_simps
  ring

theorem actual_first_digamma_Bernoulli_endpoint_correction_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (le one (var 0) ⋏ le one (var 1) ⟶ endpointCorrection (var 0) (var 1) ≐ trapezoid (var 0) (var 1)) :=
  closeUniv 2 (.impI (exact_correction _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianDigammaFirstBernoulliEndpoints
