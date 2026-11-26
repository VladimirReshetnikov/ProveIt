import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerUpperTailPointwise
import IPRADerivations.Analysis.Optimization.RationalConvexEndpointBudget

/-!
# Original Gaussian product bounds respect positive scalar order

The two real factors retain their actual independently decoded scalar
numerators and denominators. Squaring the genuine original scalar order
and canceling only its positive denominator transports the original
Gaussian product norm bound. No magnitude or product output law is a premise.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPositiveScalarProductBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qmul canonical positive_product represents represents_congr)
open GaussianRationalMetric (bounded)
open GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open GaussianPositiveRealArithmetic (positive sign numerator natural_representation)
open RationalSupMetric (denominatorOf)
open RationalGaussianEmbedding (embed native canonical_axis_roundtrip embed_from_representation)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem native_product_norm (q A : PTm n) : Γ ⊢[PRAAx]
    ComplexLogarithmRemainder.normSq (ComplexLogarithmRemainder.mul q (native (ZT.ofNat A))) ≐
      ComplexLogarithmRemainder.normSq q*(A*A) := by
  have h := ComplexLogarithmRemainder.normSq_mul (Γ := Γ) q (native (ZT.ofNat A))
  have v : Γ ⊢[PRAAx] ComplexLogarithmRemainder.normSq (native (ZT.ofNat A)) ≐ A*A := by
    simpa [native,GaussianDominantPairAlgebra.radiusNumerator] using
      GaussianDominantPairAlgebra.radius_numerator_norm (Γ := Γ) A
  exact h.eqTrans (congrMul (.eqRefl _) v)

theorem product_representation (q u : PTm n) (hu : Γ ⊢[PRAAx] canonical u)
    (hp : Γ ⊢[PRAAx] positive u) : Γ ⊢[PRAAx]
    represents (qmul q u) (ComplexLogarithmRemainder.mul (rawGaussian q)
      (native (ZT.ofNat (numerator (fstT u))))) (rawDen q*denominatorOf (fstT u)) := by
  have e := canonical_axis_roundtrip u hu hp.andE₁
  have ur := embed_from_representation _ _ _ (natural_representation _ hp.andE₂)
  have r := GaussianRationalHorner.qmul_represents _ _ _ _ _ _ (raw_den_positive q)
    (RationalArgmin.denominator_positive (fstT u)) (raw_represents q) ur
  exact represents_congr (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl q) e) (GaussianRootAlgebra.equal_refl _) (.eqRefl _) r

/-- A smaller nonnegative real factor gives a smaller norm of the actual
product with any raw Gaussian rational. -/
theorem product_bound_monotone (q u v A B : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hu : Γ ⊢[PRAAx] canonical u) (hv : Γ ⊢[PRAAx] canonical v)
    (hp : Γ ⊢[PRAAx] positive u) (ha : Γ ⊢[PRAAx] RationalGaussianEmbedding.axis v)
    (ho : Γ ⊢[PRAAx] RationalArgmin.rationalLE (fstT u) (fstT v))
    (hb : Γ ⊢[PRAAx] bounded (qmul q v) A B) : Γ ⊢[PRAAx] bounded (qmul q u) A B := by
  let X := numerator (fstT u)
  let Y := numerator (fstT v)
  let E := denominatorOf (fstT u)
  let F := denominatorOf (fstT v)
  let D := rawDen q
  let Q := ComplexLogarithmRemainder.normSq (rawGaussian q)
  have hE := RationalArgmin.denominator_positive (Γ := Γ) (fstT u)
  have hF := RationalArgmin.denominator_positive (Γ := Γ) (fstT v)
  have pv : Γ ⊢[PRAAx] positive v := .andI ha
    (GaussianRationalL1.nonnegative_of_lower _ _ hp.andE₂ ho)
  have clear := GaussianRationalMetric.comparison_to_cleared _ _ X Y E F
    (natural_representation _ hp.andE₂) (natural_representation _ pv.andE₂) ho
  have squared := sq_le_sq clear
  have old := GaussianRationalMetric.bounded_to_cleared _ _ (D*F) A B
    (positive_product _ _ (raw_den_positive q) hF) hB (product_representation q v hv pv) hb
  have old' : Γ ⊢[PRAAx] le ((B*B)*(Q*(Y*Y))) ((A*A)*((D*F)*(D*F))) :=
    le_congr (congrMul (.eqRefl _) (native_product_norm (rawGaussian q) Y)) (.eqRefl _) old
  have term1 := mul_le_mul_right (B*B*Q) squared
  have term2 := mul_le_mul_right (E*E) old'
  have both : Γ ⊢[PRAAx] le ((F*F)*((B*B)*(Q*(X*X))))
      ((F*F)*((A*A)*((D*E)*(D*E)))) := by
    have first : Γ ⊢[PRAAx] le ((F*F)*((B*B)*(Q*(X*X)))) ((B*B)*(Q*(Y*Y))*(E*E)) :=
      le_congr (by ipra_ring) (by ipra_ring) term1
    have last : Γ ⊢[PRAAx] le ((B*B)*(Q*(Y*Y))*(E*E)) ((F*F)*((A*A)*((D*E)*(D*E)))) :=
      le_congr (.eqRefl _) (by ipra_ring) term2
    exact le_trans first last
  apply GaussianRationalMetric.bounded_of_cleared _ _ (D*E) A B
    (positive_product _ _ (raw_den_positive q) hE) hB (product_representation q u hu hp)
  exact le_congr (congrMul (.eqRefl _) (native_product_norm (rawGaussian q) X)).eqSymm (.eqRefl _)
    (RationalValueBounds.positive_cancel (positive_product _ _ hF hF) both)

theorem actual_positive_scalar_product_norm_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 4) ⋏ (canonical (var 1) ⋏ canonical (var 2))) ⟶
      (positive (var 1) ⋏ RationalGaussianEmbedding.axis (var 2)) ⟶
      RationalArgmin.rationalLE (fstT (var 1)) (fstT (var 2)) ⟶
      bounded (qmul (var 0) (var 2)) (var 3) (var 4) ⟶
      bounded (qmul (var 0) (var 1)) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (product_bound_monotone _ _ _ _ _
    hyp2.wk.andE₁ hyp2.wk.andE₂.andE₁ hyp2.wk.andE₂.andE₂ hyp2.andE₁ hyp2.andE₂ Prf.hyp1 Prf.hyp0)))))

theorem actual_positive_real_factor_product_representation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((canonical (var 1) ⋏ positive (var 1)) ⟶
      represents (qmul (var 0) (var 1)) (ComplexLogarithmRemainder.mul (rawGaussian (var 0))
        (native (ZT.ofNat (numerator (fstT (var 1)))))) (rawDen (var 0)*denominatorOf (fstT (var 1)))) :=
  closeUniv 2 (.impI (product_representation _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianPositiveScalarProductBound
