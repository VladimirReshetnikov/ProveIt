import IPRADerivations.Analysis.GaussianEulerIntegrationByPartsGrid
import IPRADerivations.Analysis.GaussianRationalQuadratureDifference

/-!
# Exact weighted linear assembly of the original Euler IBP operator

The actual operator quadrature is exactly z/B times the literal
power-decay quadrature minus the actual time-weighted boundary
quadrature. This is a finite program identity, including empty meshes
and raw encodings. Analytic limiting statements remain separate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsQuadrature

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIntegrationByPartsLinear (primitive originalProduct)
open GaussianEulerIntegrationByPartsGrid (operator operatorF endpointF operator_at endpoint_grid_at)
open GaussianEulerIntegrationByPartsGridObservation (rawF raw_grid_at)
open GaussianEulerIntegrandName (fixedData)
open GaussianCompactRiemannName (sampleBody sampleData quadrature sample_body_at)
open GaussianRationalFiniteSum (multiplyBody multiply_body_at sum sum_multiply termsEqual sum_congr_bounded)
open GaussianRationalQuadratureDifference (differenceBody difference_body_at finite_sum_difference)
open GaussianRationalRiemannRefinement (weight)
open GaussianRationalHorner (qmul ofGaussian)
open GaussianRationalMetric (qsub)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr)
open GaussianReciprocalHorner (qmul_associative)
open GaussianRationalPowerAlgebra (qmul_commutative)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem original_operator_difference (p z B a b : PTm n) : Γ ⊢[PRAAx]
    operator p z B a b ≐ qsub (qmul (ofGaussian z B) (originalProduct p z B a b)) (primitive p z B a b) :=
  (GaussianRationalRoundedPower.multiplication_difference (originalProduct p z B a b) (ofGaussian z B)
    (GaussianPositiveRationalLogarithm.fraction a b)).eqSymm.eqTrans
    (qsub_congr (qmul_commutative _ _) (qmul_commutative _ _))

theorem original_row_difference (i p N z B a C E : PTm n) : Γ ⊢[PRAAx]
    inst2 (sampleBody operatorF) i (sampleData p N a C E (fixedData z B)) ≐
      inst2 (differenceBody (multiplyBody (sampleBody rawF)) (sampleBody endpointF)) i
        (pairT (pairT (ofGaussian z B) (sampleData p N a C E (fixedData z B))) (sampleData p N a C E (fixedData z B))) := by
  let d := sampleData p N a C E (fixedData z B)
  let v := ofGaussian z B
  have op := (sample_body_at (Γ := Γ) operatorF i p N a C E (fixedData z B)).eqTrans
    ((operator_at p z B (a*N+C*i) (E*N)).eqTrans (original_operator_difference p z B (a*N+C*i) (E*N)))
  have normal : Γ ⊢[PRAAx] inst2 (sampleBody operatorF) i d ≐
      qsub (qmul v (inst2 (sampleBody rawF) i d)) (inst2 (sampleBody endpointF) i d) :=
    op.eqTrans (qsub_congr (qmul_congr (.eqRefl v) (raw_grid_at i p N z B a C E).eqSymm) (endpoint_grid_at i p z B a C E N).eqSymm)
  have product := multiply_body_at (Γ := Γ) (sampleBody rawF) v i d
  exact normal.eqTrans ((qsub_congr product.eqSymm (.eqRefl _)).eqTrans
    (difference_body_at (multiplyBody (sampleBody rawF)) (sampleBody endpointF) i (pairT v d) d).eqSymm)

private theorem commute_outer (a b c : PTm n) : Γ ⊢[PRAAx] qmul a (qmul b c) ≐ qmul b (qmul a c) :=
  (qmul_associative a b c).eqSymm.eqTrans ((qmul_congr (qmul_commutative a b) (.eqRefl c)).eqTrans (qmul_associative b a c))

/-- All rows, weights and data are the actual original programs.
No source, point-value, derivative or quadrature law is supplied. -/
theorem original_operator_quadrature_difference (p N z B a C E : PTm n) : Γ ⊢[PRAAx]
    quadrature operatorF p N a C E (fixedData z B) ≐ qsub
      (qmul (ofGaussian z B) (quadrature rawF p N a C E (fixedData z B)))
      (quadrature endpointF p N a C E (fixedData z B)) := by
  let d := sampleData p N a C E (fixedData z B)
  let v := ofGaussian z B
  let w := weight C E N
  let f := multiplyBody (sampleBody rawF)
  let g := sampleBody endpointF
  have rows : Γ ⊢[PRAAx] termsEqual (sampleBody operatorF) (differenceBody f g) N d (pairT (pairT v d) d) := by
    refine .allI (.impI ?_)
    simpa only [termsEqual,d,v,f,g,GaussianCompactRiemannName.subst_sampleData,GaussianEulerIntegrandName.subst_fixedData,
      GaussianRationalHorner.subst_ofGaussian,subst_pairT,Syn.shift] using
      original_row_difference (Γ := _ :: Γ.map Fm.shift) (var 0) (Syn.shift p) (Syn.shift N) (Syn.shift z) (Syn.shift B)
        (Syn.shift a) (Syn.shift C) (Syn.shift E)
  have sums : Γ ⊢[PRAAx] sum (sampleBody operatorF) N d ≐ qsub (sum f N (pairT v d)) (sum g N d) :=
    (GaussianRationalFiniteSum.sum_congr_bounded (sampleBody operatorF) (differenceBody f g) N d (pairT (pairT v d) d) rows).eqTrans
    (finite_sum_difference f g N (pairT v d) d)
  have separated := (qmul_congr (.eqRefl w) sums).eqTrans
    (GaussianRationalRoundedPower.multiplication_difference w (sum f N (pairT v d)) (sum g N d)).eqSymm
  have product : Γ ⊢[PRAAx] qmul w (sum f N (pairT v d)) ≐ qmul v (qmul w (sum (sampleBody rawF) N d)) :=
    (qmul_congr (.eqRefl w) (sum_multiply (sampleBody rawF) v N d)).eqTrans (commute_outer w v _)
  exact separated.eqTrans (qsub_congr product (.eqRefl _))

theorem actual_original_Euler_IBP_quadrature_linear_assembly_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (quadrature operatorF (var 0) (var 1) (var 4) (var 5) (var 6) (fixedData (var 2) (var 3)) ≐ qsub
      (qmul (ofGaussian (var 2) (var 3)) (quadrature rawF (var 0) (var 1) (var 4) (var 5) (var 6) (fixedData (var 2) (var 3))))
      (quadrature endpointF (var 0) (var 1) (var 4) (var 5) (var 6) (fixedData (var 2) (var 3)))) :=
  closeUniv 7 (original_operator_quadrature_difference _ _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsQuadrature
