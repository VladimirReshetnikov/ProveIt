import IPRADerivations.Analysis.Integration.CompactGrids.Splits.GaussianCompactNamedAdditivity

/-!
# Literal zero-width compact quadrature

The actual original weight is zero, so every actual original observation
is the canonical Gaussian zero, including raw evaluator values. This
supplies the equal-cutoff case of a genuine finite interval split.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCompactZeroWidth

open_ipra
open GaussianCompactRiemannName (sample quadrature)
open GaussianRationalHorner (qzero)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem native_zero : Γ ⊢[PRAAx] GaussianRootAlgebra.equal
    (ComplexLogarithmRemainder.scale zero ComplexLogarithmRemainder.oneCode) ComplexLogarithmRemainder.zeroCode := by
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_zero,GaussianRootAlgebra.im_zero]
  all_goals ipra_simps
  all_goals ring

theorem zero_fraction (D : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    GaussianRationalHorner.ofGaussian (ComplexLogarithmRemainder.scale zero ComplexLogarithmRemainder.oneCode) D ≐ qzero :=
  (GaussianCompactRiemannName.fraction_congr _ _ _ _ (by ipra_ring : Γ ⊢[PRAAx] zero ≐ D*zero)
    (by ipra_ring : Γ ⊢[PRAAx] D ≐ D*one)).eqTrans
    ((GaussianCompactRiemannSplit.fraction_cancel D zero one hD (le_refl one)).eqTrans
      (GaussianGammaFiniteValueProperness.fraction_equal _ _ one (le_refl one) native_zero))

theorem quadrature_zero (F : PR 3) (s N a E x : PTm n) (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    quadrature F s N a zero E x ≐ qzero :=
  (GaussianRationalSyntheticDivision.qmul_congr (zero_fraction (E*N) (GaussianRationalHorner.positive_product _ _ hE hN)) (.eqRefl _)).eqTrans
    (GaussianRationalSyntheticDivision.qmul_zero_left _)

theorem sample_zero (F : PR 3) (p a E L T x : PTm n) (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx]
    sample F p a zero E L T x ≐ qzero := quadrature_zero F _ _ _ _ _ hE (GaussianCompactRiemannName.mesh_positive p L T)

theorem observation_zero (F : PR 3) (p a E L T x : PTm n) (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx]
    ap2 (GaussianCompactRiemannName.nameF F) p (GaussianCompactRiemannName.data a zero E L T x) ≐ qzero :=
  (GaussianCompactRiemannName.name_at F p a zero E L T x).eqTrans (sample_zero F p a E L T x hE)

/-- The zero representative may carry any numerical data. Only actual
zero observations, not raw parameter eta, are used. -/
theorem name_zero (F : PR 3) (a E L T x y : PTm n)
    (h : Γ ⊢[PRAAx] GaussianCompactRiemannName.input F a zero E L T x) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianCompactRiemannName.nameF F) GaussianNameRingLaws.zeroF (GaussianCompactRiemannName.data a zero E L T x) y := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ zero
    (GaussianCompactRiemannName.name_regular F a zero E L T x h) (GaussianNameRingLaws.zero_fast y)
  have es : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift E) := by simpa [Fm.shift,Syn.shift] using h.andE₂.andE₁.shift
  refine .allI ?_
  have actual := GaussianRationalDistanceOrder.distance_congr
    (observation_zero F (var 0) (Syn.shift a) (Syn.shift E) (Syn.shift L) (Syn.shift T) (Syn.shift x) es).eqSymm
    (GaussianNameRingLaws.zero_at (var 0) (Syn.shift y)).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianRationalPowerDifference.distance_refl_zero (qzero : PTm (n+1)) (unit (var 0)) (unit_positive (var 0)))
  simpa only [GaussianCompactRiemannName.subst_data,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using actual

theorem actual_original_zero_width_quadrature_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 3) ⋏ le one (var 1)) ⟶ quadrature F (var 0) (var 1) (var 2) zero (var 3) (var 4) ≐ qzero) :=
  closeUniv 5 (.impI (quadrature_zero F _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem actual_original_zero_width_observation_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 2) ⟶ ap2 (GaussianCompactRiemannName.nameF F) (var 0)
      (GaussianCompactRiemannName.data (var 1) zero (var 2) (var 3) (var 4) (var 5)) ≐ qzero) :=
  closeUniv 6 (.impI (observation_zero F _ _ _ _ _ _ Prf.hyp0))
theorem actual_original_zero_width_name_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (GaussianCompactRiemannName.input F (var 0) zero (var 1) (var 2) (var 3) (var 4) ⟶
      crossEquivalent (GaussianCompactRiemannName.nameF F) GaussianNameRingLaws.zeroF
        (GaussianCompactRiemannName.data (var 0) zero (var 1) (var 2) (var 3) (var 4)) (var 5)) :=
  closeUniv 6 (.impI (name_zero F _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianCompactZeroWidth
