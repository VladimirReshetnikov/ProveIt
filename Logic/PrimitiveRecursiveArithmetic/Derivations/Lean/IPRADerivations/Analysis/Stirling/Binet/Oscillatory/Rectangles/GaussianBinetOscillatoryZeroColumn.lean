import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.Rectangles.GaussianBinetOscillatorySineQuotient
import IPRADerivations.Analysis.Exponential.Estimates.GaussianRationalExponentialTangent

/-!
# Exact zero-time value of the regularized sine column

At the first damping grid point both imaginary exponents vanish.
Every original exponential sample is exactly one, so the normalized
primitive is one and the original length supplies the removable value.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBinetOscillatoryZeroColumn

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetCosinePrimitive (cosineValue)
open GaussianBinetExponentialIntegralGrid (row value exponent cell_at left_endpoint)
open GaussianBinetExponentialPanel (sample)
open GaussianBinetImaginaryExponentialIntegral (coefficient)
open GaussianBinetImaginaryExponentialScale (coefficient_congr exponent_scale)
open GaussianBinetOscillatoryColumns (columnTarget damping)
open GaussianBinetOscillatoryPanelFactor (polarity)
open GaussianCompactRiemannName (sampleBody sampleData fraction_congr)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalFiniteSum (sum)
open GaussianRationalHorner (ofGaussian_canonical positive_product qmul qzero)
open GaussianRationalNaturalScale (natScale_as_product naturalPoint)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalRiemannRefinement (constantBody constant_sum weight)
open GaussianRationalSyntheticDivision (qmul_congr qadd_congr qone qmul_zero_right)
open GaussianReciprocalHorner (qmul_one_right)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "f" => sampleBody GaussianBinetExponentialIntegralGrid.evaluatorF

private theorem sample_cast (p C : PTm n) {x y : PTm n} (h : Γ ⊢[PRAAx] x ≐ y) : Γ ⊢[PRAAx]
    sample p x C ≐ sample p y C :=
  congrAp2 GaussianBinetExponentialPanel.expoF (.eqRefl p) (congrPairT (.eqRefl C) h)

private theorem sample_zero (p C : PTm n) : Γ ⊢[PRAAx] sample p qzero C ≐ qone := by
  have e : Γ ⊢[PRAAx] exponent qzero (one*zero) one ≐ qzero :=
    (qmul_commutative _ _).eqTrans (qmul_zero_right _)
  exact (sample_cast p C e.eqSymm).eqTrans (left_endpoint p qzero C one one (le_refl one))

private theorem zero_angle (s : Bool) (A B T N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] coefficient (A*(T*zero)) (B*N) (polarity s) ≐ qzero := by
  have e : Γ ⊢[PRAAx] fraction (T*zero) N ≐ qzero :=
    (fraction_congr _ _ _ _ (by ipra_ring) (.eqRefl _)).eqTrans (GaussianCompactZeroWidth.zero_fraction N hN)
  exact (exponent_scale s A B (T*zero) N hB hN).eqSymm.eqTrans
    ((qmul_congr (.eqRefl _) e).eqTrans (qmul_zero_right _))

private theorem constant_panel (i p c C M : PTm n) (hc : Γ ⊢[PRAAx] c ≐ qzero) : Γ ⊢[PRAAx]
    inst2 f i (sampleData p M one one one (pairT c C)) ≐ inst2 constantBody i qone := by
  have eq : Γ ⊢[PRAAx] exponent c (one*i) M ≐ qzero :=
    (qmul_congr hc (.eqRefl _)).eqTrans ((qmul_commutative _ _).eqTrans (qmul_zero_right _))
  rw [GaussianRationalRiemannRefinement.constant_entry]
  exact (cell_at i p c C one M).eqTrans ((sample_cast p C eq).eqTrans (sample_zero p C))

private theorem constant_integral (p c C M : PTm n) (hc : Γ ⊢[PRAAx] c ≐ qzero)
    (hM : Γ ⊢[PRAAx] le one M) : Γ ⊢[PRAAx] value p c C one M ≐ qone := by
  let x := sampleData p M one one one (pairT c C)
  have terms : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual f constantBody M x qone := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    have sh : Γ.map Fm.shift ⊢[PRAAx] s c ≐ qzero := by simpa [Fm.shift,Syn.shift,s] using hc.shift
    simpa only [x,s,Syn.shift,GaussianCompactRiemannName.subst_sampleData,subst_pairT,GaussianRationalSyntheticDivision.subst_qone,
      one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using constant_panel (var 0) (s p) (s c) (s C) (s M) sh.wk
  have sumEq := (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ terms).eqTrans
    ((constant_sum qone M).eqTrans ((natScale_as_product M qone).eqTrans (qmul_one_right _ (ofGaussian_canonical _ _ (le_refl one)))))
  have w : Γ ⊢[PRAAx] weight one one M ≐ fraction one M := fraction_congr _ _ _ _ (.eqRefl _) (one_mul M)
  exact (qmul_congr w sumEq).eqTrans
    ((GaussianEulerDampedTimeRate.fraction_product one M M one hM (le_refl one)).eqTrans
      ((fraction_congr _ _ _ _ (one_mul M) (by ipra_ring)).eqTrans (GaussianRationalExponentialTangent.fraction_one M hM)))

private theorem mean_one : Γ ⊢[PRAAx] GaussianBinetArctangentCosineLaplace.mean qone qone ≐ (qone : PTm n) := by
  have f₁ := GaussianRationalExponentialTangent.fraction_one (Γ := Γ) (one : PTm n) (le_refl one)
  have a : Γ ⊢[PRAAx] GaussianRationalHorner.qadd qone qone ≐ fraction two one :=
    (qadd_congr f₁.eqSymm f₁.eqSymm).eqTrans ((GaussianRationalQuadratureSquareCells.fraction_add_same one one one (le_refl one)).eqTrans
      (fraction_congr _ _ _ _ (by ipra_ring) (.eqRefl _)))
  have h₂ := le_succ_self (Γ := Γ) one
  exact (qmul_congr (.eqRefl _) a).eqTrans
    ((GaussianEulerDampedTimeRate.fraction_product one two two one h₂ (le_refl one)).eqTrans
      ((fraction_congr _ _ _ _ (one_mul two) (by ipra_ring)).eqTrans (GaussianRationalExponentialTangent.fraction_one two h₂)))

theorem zero_column_at (j p M X Y D sign A B R U L N : PTm n) (hj : Γ ⊢[PRAAx] j ≐ zero) (hB : Γ ⊢[PRAAx] le one B)
    (hM : Γ ⊢[PRAAx] le one M) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    columnTarget j p M X Y D sign A B R U L N ≐ fraction A B := by
  let T := D*L
  let C := U*T
  let r := p+N
  let e := damping p X Y D sign T j N R
  have ht := congrMul (.eqRefl T) hj
  have time : Γ ⊢[PRAAx] fraction (T*j) N ≐ fraction (T*zero) N := fraction_congr _ _ _ _ ht (.eqRefl _)
  have ed : Γ ⊢[PRAAx] e ≐ qone :=
    (sample_cast r (R*T) (qmul_congr (.eqRefl _) time)).eqTrans (left_endpoint r _ (R*T) T N hN)
  have a (s : Bool) : Γ ⊢[PRAAx] coefficient (A*(T*j)) (B*N) (polarity s) ≐ qzero :=
    (coefficient_congr s (congrMul (.eqRefl A) ht) (.eqRefl _)).eqTrans (zero_angle s A B T N hB hN)
  have e₁ := constant_integral r _ (C*one) M (a true) hM
  have e₂ := constant_integral r _ (C*one) M (a false) hM
  have cz : Γ ⊢[PRAAx] cosineValue r (A*(T*j)) (B*N) C one M ≐ qone :=
    (qmul_congr (.eqRefl _) (qadd_congr e₁ e₂)).eqTrans mean_one
  have cc := qmul_one_right (fraction A B) (ofGaussian_canonical _ _ hB)
  exact (qmul_congr ed ((qmul_congr (.eqRefl _) cz).eqTrans cc)).eqTrans
    ((qmul_commutative _ _).eqTrans cc)

theorem zero_column (p M X Y D sign A B R U L N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hM : Γ ⊢[PRAAx] le one M) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    columnTarget zero p M X Y D sign A B R U L N ≐ fraction A B :=
  zero_column_at zero p M X Y D sign A B R U L N (.eqRefl _) hB hM hN

end LeanProofs.IPRA.Analysis.GaussianBinetOscillatoryZeroColumn
