import IPRADerivations.Analysis.Stirling.Binet.Bose.CompactIntegrand.Quadrature.GaussianBinetBoseCompact
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianCompactScalarMajorant

/-!
# Width bound for the original second-Binet compact quadrature

Multiplying the uniform pointwise bound by the physical width
bounds every original observation on a positive panel.
-/

set_option autoImplicit false
set_option maxHeartbeats 390000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBoseCompactBound

open_ipra
open GaussianBinetArctangentQuadrature (fixedData subst_fixedData)
open GaussianBinetBoseCompact (nameF data evaluatorF evaluator_at gain source tag_lower)
open GaussianBinetLaplaceStrip (tagNumerator)
open GaussianCompactRiemannName (grid grid_inside sampleBody sampleData sample_body_at quadrature mesh mesh_positive precision)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (positive_product qzero)
open GaussianRationalMetric (bounded)
open GaussianRationalRiemannRefinement (leftSum termsDistance constantBody constant_entry)
open GaussianRationalSyntheticDivision (qmul_congr qmul_zero_right)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem quadrature_bound (p M X Y D sign A C E : PTm n) (hz : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source X D sign)
    (hA : Γ ⊢[PRAAx] le one A) (hE : Γ ⊢[PRAAx] le one E) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] bounded (quadrature evaluatorF p M (E+A) C E (fixedData X Y D sign)) (C*D) (E*(num 4*X)) := by
  let f := sampleBody evaluatorF
  let x := sampleData p M (E+A) C E (fixedData X Y D sign)
  have rows : Γ ⊢[PRAAx] termsDistance f constantBody M x qzero D (num 4*X) := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (s M)::Γ.map Fm.shift
    let t := grid (var 0) (s M) (s E+s A) (s C) (s E)
    have zs : Δ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source (s X) (s D) (s sign) := by
      simpa [Δ,s,Fm.shift,Syn.shift,GaussianRightHalfPlaneLogarithm.source,GaussianRightHalfPlaneArgument.source] using hz.shift.wk
    have as' : Δ ⊢[PRAAx] le one (s A) := (Order.shift_one_le hA).wk
    have es : Δ ⊢[PRAAx] le one (s E) := (Order.shift_one_le hE).wk
    have ms : Δ ⊢[PRAAx] le one (s M) := (Order.shift_one_le hM).wk
    have hi : Δ ⊢[PRAAx] GaussianCompactRiemannName.inside (s E+s A) (s C) (s E) t :=
      grid_inside (var 0) (s M) (s E+s A) (s C) (s E) (le_trans es (le_add_right _ _)) es ms (le_of_lt Prf.hyp0)
    have ha := (tag_lower (s A) (s C) (s E) t as' es hi).andE₁
    have hX4 := positive_product _ _ (by ipra_le 3 : Δ ⊢[PRAAx] le one (num 4)) zs.andE₁.andE₁
    have v := GaussianBinetBoseIntegrandBound.observation_bound (s p) (s X) (s Y) (s D) (s sign)
      (tagNumerator t) (sndT t) zs ha hi.andE₂.andE₁
    have read := (sample_body_at (Γ := Δ) evaluatorF (var 0) (s p) (s M) (s E+s A) (s C) (s E)
      (fixedData (s X) (s Y) (s D) (s sign))).eqTrans (evaluator_at (s p) t (s X) (s Y) (s D) (s sign))
    rw [constant_entry]
    simpa only [f,x,Δ,s,Syn.shift,GaussianCompactRiemannName.subst_sampleData,subst_fixedData,
      GaussianRationalHorner.subst_qzero,PTm.subst_add,PTm.subst_mul,PTm.subst_num] using
      (GaussianReconstructionRoots.distance_zero_iff _ _ _ hX4).iffMpr
        (GaussianRationalReciprocal.bound_congr read.eqSymm (.eqRefl _) (.eqRefl _) v)
  have hX4 := positive_product _ _ (by ipra_le 3 : Γ ⊢[PRAAx] le one (num 4)) hz.andE₁.andE₁
  have zeroSum : Γ ⊢[PRAAx] GaussianRationalFiniteSum.sum constantBody M qzero ≐ qzero :=
    (GaussianRationalRiemannRefinement.constant_sum qzero M).eqTrans (GaussianRationalFactorialEulerSums.scale_zero_value M)
  have zeroInt : Γ ⊢[PRAAx] leftSum constantBody M qzero C E ≐ qzero :=
    (qmul_congr (.eqRefl _) zeroSum).eqTrans (qmul_zero_right _)
  exact (GaussianReconstructionRoots.distance_zero_iff _ _ _ (positive_product _ _ hE hX4)).iffMp
    (distance_congr (.eqRefl _) zeroInt (.eqRefl _) (.eqRefl _)
      (GaussianCompactScalarMajorant.common_mesh_distance f constantBody M x qzero C E D (num 4*X) hM hE hX4 rows))

theorem name_bound (p X Y D sign T A C E : PTm n) (h : Γ ⊢[PRAAx] source X D sign T A C E) :
    Γ ⊢[PRAAx] bounded (ap2 nameF p (data X Y D sign T A C E)) (C*D) (E*(num 4*X)) :=
  GaussianRationalReciprocal.bound_congr
    (GaussianCompactRiemannName.name_at evaluatorF p (E+A) C E (gain D E T) T (fixedData X Y D sign)).eqSymm
    (.eqRefl _) (.eqRefl _)
    (quadrature_bound (precision p T) (mesh p (gain D E T) T) X Y D sign A C E
      h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂.andE₁ (mesh_positive p (gain D E T) T))

theorem actual_second_Binet_positive_compact_width_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 1) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      bounded (ap2 nameF (var 0) (data (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)))
        (var 7*var 3) (var 8*(num 4*var 1))) :=
  closeUniv 9 (.impI (name_bound _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetBoseCompactBound
