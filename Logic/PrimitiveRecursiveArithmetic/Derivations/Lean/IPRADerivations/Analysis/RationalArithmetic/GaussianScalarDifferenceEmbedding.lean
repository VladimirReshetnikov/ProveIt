import IPRADerivations.Analysis.Names.RationalGaussianNameEmbedding
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayOrder

/-!
# Exact scalar differences and Euclidean width transport

Normalized scalar addition and negation embed as the actual normalized
Gaussian difference, including arbitrary raw scalar encodings. At
canonical real-axis endpoints this identifies their literal Gaussian
difference. A scalar width radius therefore transfers with exactly the
same numerator and denominator to the actual Gaussian endpoint width.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianScalarDifferenceEmbedding

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalGaussianEmbedding (embed canonical_axis_roundtrip axis)
open GaussianRationalHorner (canonical)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- No scalar canonicality or sign assumptions are needed. -/
theorem embed_difference (a b : PTm n) : Γ ⊢[PRAAx]
    embed (RationalArithmetic.add a (RationalArithmetic.negative b)) ≐ qsub (embed a) (embed b) :=
  (RationalGaussianEmbedding.embed_add a (RationalArithmetic.negative b)).eqTrans
    (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) (RationalGaussianEmbedding.embed_negative b))

theorem endpoint_difference (X Y : PTm n) (hX : Γ ⊢[PRAAx] canonical X ⋏ axis X)
    (hY : Γ ⊢[PRAAx] canonical Y ⋏ axis Y) : Γ ⊢[PRAAx]
    embed (RationalArithmetic.add (fstT X) (RationalArithmetic.negative (fstT Y))) ≐ qsub X Y :=
  (embed_difference (fstT X) (fstT Y)).eqTrans
    (GaussianRationalSyntheticDivision.qsub_congr (canonical_axis_roundtrip X hX.andE₁ hX.andE₂)
      (canonical_axis_roundtrip Y hY.andE₁ hY.andE₂))

theorem scalar_difference_distance (a X Y A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hX : Γ ⊢[PRAAx] canonical X ⋏ axis X) (hY : Γ ⊢[PRAAx] canonical Y ⋏ axis Y)
    (h : Γ ⊢[PRAAx] RationalValueBounds.radius a (RationalArithmetic.add (fstT X) (RationalArithmetic.negative (fstT Y))) A B) : Γ ⊢[PRAAx]
    distanceBounded (embed a) (qsub X Y) A B :=
  distance_congr (.eqRefl _) (endpoint_difference X Y hX hY) (.eqRefl _) (.eqRefl _)
    (RationalGaussianNameEmbedding.distance_from_radius _ _ _ _ hB h)

/-- The finite rational panel width and the actual Gaussian endpoint
difference retain precisely the original scalar error radius. -/
theorem width_distance (W M X Y A B : PTm n) (hM : Γ ⊢[PRAAx] le one M) (hB : Γ ⊢[PRAAx] le one B)
    (hX : Γ ⊢[PRAAx] canonical X ⋏ axis X) (hY : Γ ⊢[PRAAx] canonical Y ⋏ axis Y)
    (h : Γ ⊢[PRAAx] RationalValueBounds.radius (GaussianEuclideanDistanceName.fraction W M)
      (RationalArithmetic.add (fstT X) (RationalArithmetic.negative (fstT Y))) A B) : Γ ⊢[PRAAx]
    distanceBounded (GaussianPositiveRationalLogarithm.fraction W M) (qsub X Y) A B :=
  distance_congr (GaussianEulerDecayOrder.fraction_embedding W M hM) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (scalar_difference_distance _ X Y A B hB hX hY h)

theorem actual_raw_scalar_difference_embedding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (embed (RationalArithmetic.add (var 0) (RationalArithmetic.negative (var 1))) ≐ qsub (embed (var 0)) (embed (var 1))) :=
  closeUniv 2 (embed_difference _ _)

theorem actual_canonical_axis_endpoint_difference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (((canonical (var 0) ⋏ axis (var 0)) ⋏ (canonical (var 1) ⋏ axis (var 1))) ⟶
      embed (RationalArithmetic.add (fstT (var 0)) (RationalArithmetic.negative (fstT (var 1)))) ≐ qsub (var 0) (var 1)) :=
  closeUniv 2 (.impI (endpoint_difference _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_scalar_width_radius_transport_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le one (var 1) ⋏ le one (var 5)) ⟶
      (((canonical (var 2) ⋏ axis (var 2)) ⋏ (canonical (var 3) ⋏ axis (var 3))) ⟶
        RationalValueBounds.radius (GaussianEuclideanDistanceName.fraction (var 0) (var 1))
          (RationalArithmetic.add (fstT (var 2)) (RationalArithmetic.negative (fstT (var 3)))) (var 4) (var 5) ⟶
          distanceBounded (GaussianPositiveRationalLogarithm.fraction (var 0) (var 1)) (qsub (var 2) (var 3)) (var 4) (var 5))) :=
  closeUniv 6 (.impI (.impI (.impI (width_distance _ _ _ _ _ _
    Prf.hyp0.wk.wk.andE₁ Prf.hyp0.wk.wk.andE₂ Prf.hyp0.wk.andE₁ Prf.hyp0.wk.andE₂ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianScalarDifferenceEmbedding
