import IPRADerivations.Analysis.Barnes.Names.FactorialTaylor.GaussianBarnesCanonicalNamedFactorialTaylor
import IPRADerivations.Analysis.Barnes.Names.GaussianBarnesCanonicalNamed
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalTaylorDerivativeOrderInvariance

/-!
# Rational binding of the named Barnes factorial Taylor evaluator

At a constant rational name the evaluator agrees with the original
cofinal factorial name. The comparison permits every buffer that retains
the requested order and arbitrary representatives of the input name.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedFactorialTaylorBinding

open_ipra
open ComplexLogarithmRemainder (bounded_mono)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalNamedFactorialTaylor (clock data frozenData nameF proper retains sample_at)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (recode_fixed unit_monotone)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNameArithmetic (recode_congr)
open GaussianNameEquivalence (crossEquivalent cross_at cross_trans)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical positive_product)
open GaussianRationalL1 (rawDen rawGaussian)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "F" => GaussianBarnesCanonicalTaylorProductDerivativeName.nameF
local notation "fd" => GaussianBarnesCanonicalTaylorProductDerivativeName.data
local notation "namedSource" => GaussianBarnesCanonicalNamedDemand.source

private theorem widen (z R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] source z (R+one) B :=
  .andI hz.andE₁ (bounded_mono hz.andE₂ (le_of_eq_add (d := B) (by ipra_ring)))

private theorem constant_observations (p q z R B e : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF constantF) p (data (ofGaussian z B) R e))
      (ap2 F q (fd z (R+one) B e e)) (unit p+unit q) (unit p*unit q) := by
  let x := ofGaussian z B
  let k := clock p R e
  let y := ap2 constantF k x
  have hy := GaussianBarnesCanonicalNamedDemand.native_source constantF k x R
    (GaussianBarnesCanonicalNamed.constant_source z R B hz)
  have same : Γ ⊢[PRAAx] ofGaussian (rawGaussian y) (rawDen y) ≐ x :=
    (recode_congr (constant_at k x)).eqTrans (recode_fixed x (ofGaussian_canonical z B hz.andE₁))
  have near := GaussianBarnesCanonicalTaylorDerivativeChart.cofinal_cross (rawGaussian y) z (R+one) (rawDen y) B e e
    (widen _ _ _ hy) (widen _ _ _ hz) (retains e) same
  have obs := cross_at F F (frozenData constantF k x R e) (fd z (R+one) B e e) (succ p) q near
  have grow := unit_monotone (Γ := Γ) (le_succ_self p)
  have fit : Γ ⊢[PRAAx] le ((unit (succ p)+unit q)*(unit p*unit q)) ((unit p+unit q)*(unit (succ p)*unit q)) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add₂ (le_refl (unit p*unit (succ p)*unit q)) (mul_le_mul_right (unit q*unit q) grow))
  have widened := distance_radius_mono _ _ _ _ (unit p+unit q) (unit p*unit q)
    (positive_product _ _ (unit_positive (succ p)) (unit_positive q))
    (positive_product _ _ (unit_positive p) (unit_positive q)) fit obs
  exact distance_congr (sample_at constantF p x R e).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) widened

theorem constant_cross (z R B J e : PTm n) (hz : Γ ⊢[PRAAx] source z R B) (he : Γ ⊢[PRAAx] le e (previous J)) :
    Γ ⊢[PRAAx] crossEquivalent (nameF constantF) F (data (ofGaussian z B) R e) (fd z (R+one) B J e) := by
  have canonical : Γ ⊢[PRAAx] crossEquivalent (nameF constantF) F (data (ofGaussian z B) R e) (fd z (R+one) B e e) := by
    let sh (t : PTm n) := Syn.shift (Syn.shift t)
    let Δ := (Γ.map Fm.shift).map Fm.shift
    have h : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hz.shift.shift
    refine .allI (.allI ?_)
    simpa [crossEquivalent,sh,Syn.shift,Δ,GaussianBarnesCanonicalTaylorProductDerivativeName.data,
      GaussianBarnesCanonicalTaylorProductDerivativeName.coefficientData,LeanProofs.IPRA.Analysis.Products.fact,one] using
      constant_observations (var 1) (var 0) (sh z) (sh R) (sh B) (sh e) h
  exact cross_trans _ _ _ _ _ _ canonical
    (GaussianBarnesCanonicalTaylorDerivativeOrderInvariance.cofinal_cross z (R+one) B e J e (widen _ _ _ hz) (retains e) he)

theorem bind (f : PR 2) (x z R B J e : PTm n)
    (hf : Γ ⊢[PRAAx] namedSource f x R) (hz : Γ ⊢[PRAAx] source z R B) (he : Γ ⊢[PRAAx] le e (previous J))
    (hx : Γ ⊢[PRAAx] crossEquivalent f constantF x (ofGaussian z B)) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) F (data x R e) (fd z (R+one) B J e) :=
  cross_trans _ _ _ _ _ _ (proper f constantF x (ofGaussian z B) R e hf (GaussianBarnesCanonicalNamed.constant_source z R B hz) hx)
    (constant_cross z R B J e hz he)

theorem actual_named_Barnes_factorial_Taylor_rational_binding_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (let x := var 0
       let z := var 1
       let R := var 2
       let B := var 3
       let J := var 4
       let e := var 5
       (namedSource f x R ⋏ source z R B) ⟶ le e (previous J) ⟶ crossEquivalent f constantF x (ofGaussian z B) ⟶
         crossEquivalent (nameF f) F (data x R e) (fd z (R+one) B J e)) :=
  closeUniv 6 (.impI (.impI (.impI (bind f _ _ _ _ _ _ Prf.hyp1.wk.andE₁ Prf.hyp1.wk.andE₂ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedFactorialTaylorBinding
