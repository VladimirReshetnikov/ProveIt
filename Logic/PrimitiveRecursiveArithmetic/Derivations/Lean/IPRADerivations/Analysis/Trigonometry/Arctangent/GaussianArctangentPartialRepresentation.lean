import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentPartialQuadrature
import IPRADerivations.Analysis.Names.Rates.GaussianNamedDiagonalRate

/-!
# Independence of the fraction representing an arctangent endpoint

Equal encoded rational endpoints have literally equal partial sums on a
common refined denominator. The native mesh error compares each coarse
name with this common observation and gives exact name equivalence.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentPartialRepresentation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianArctangentPartialQuadrature (clearing observation mesh sample nameF data sample_at name_regular
  finite_refinement mesh_positive)
open GaussianArctangentExponentialPrefix (prefixValue subst_prefixValue)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNamedDiagonalRate (diagonalRate cross_of_diagonal_rate)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)
open GaussianRationalMetric (distanceBounded comparison_to_cleared)
open RationalCubeMidpoint (fraction fraction_represents)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem cleared_equal_of_fractions (A B C D : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (he : Γ ⊢[PRAAx] RationalArgmin.rationalEq (fraction A B) (fraction C D)) :
    Γ ⊢[PRAAx] A*D ≐ C*B := by
  have left := comparison_to_cleared _ _ A C B D (fraction_represents A B hB)
    (fraction_represents C D hD) (RationalArgmin.eq_le he)
  have right := comparison_to_cleared _ _ C A D B (fraction_represents C D hD)
    (fraction_represents A B hB) (RationalArgmin.eq_le he.eqSymm)
  exact le_antisymm (le_congr (mul_comm _ _) (.eqRefl _) left)
    (le_congr (mul_comm _ _) (.eqRefl _) right)

private theorem other_endpoint_bound (A B C D : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hA : Γ ⊢[PRAAx] le A B) (he : Γ ⊢[PRAAx] A*D ≐ C*B) :
    Γ ⊢[PRAAx] le C D := by
  apply RationalValueBounds.positive_cancel hB
  exact le_congr (he.eqTrans (mul_comm _ _)) (.eqRefl _) (le_mul_mono hA (le_refl _))

theorem common_observation (A B C D N : PTm n) (he : Γ ⊢[PRAAx] A*D ≐ C*B) :
    Γ ⊢[PRAAx] observation A B (D*N) ≐ observation C D (B*N) := by
  have endpoint : Γ ⊢[PRAAx] A*(D*N) ≐ C*(B*N) :=
    (by ipra_ring : Γ ⊢[PRAAx] A*(D*N) ≐ (A*D)*N).eqTrans
      ((congrMul he (.eqRefl N)).eqTrans (by ipra_ring))
  have size : Γ ⊢[PRAAx] B*(D*N) ≐ D*(B*N) := by ipra_ring
  simpa only [observation,subst_prefixValue,GaussianArctangentPartialQuadrature.subst_clearing,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    (Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (prefixValue (var 0) (var 1) (clearing (var 1)) : PTm 2)
      (σ := ![A*(D*N), B*(D*N)]) (σ' := ![C*(B*N), D*(B*N)])
      (fun i => by fin_cases i; exact endpoint; exact size))

private theorem refined_dyadic (A B E p : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hA : Γ ⊢[PRAAx] le A B) (hE : Γ ⊢[PRAAx] le one E) :
    Γ ⊢[PRAAx] distanceBounded (observation A B (E*mesh p)) (sample p A B) one (unit p) :=
  distance_radius_mono _ _ _ _ _ _ (mesh_positive p) (unit_positive p)
    (le_of_eq_add (d := zero) (by unfold mesh; ipra_ring))
    (finite_refinement A B (mesh p) E hB hA (mesh_positive p) hE)

theorem representation_sample_distance (A B C D p : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hA : Γ ⊢[PRAAx] le A B) (he : Γ ⊢[PRAAx] A*D ≐ C*B) :
    Γ ⊢[PRAAx] distanceBounded (sample p A B) (sample p C D) (one+one) (unit p) := by
  have hc := other_endpoint_bound A B C D hB hA he
  have left := refined_dyadic A B D p hB hA hD
  have right := refined_dyadic C D B p hD hc hB
  exact distance_triangle_same _ _ _ _ _ _ (unit_positive p)
    (distance_symmetric _ _ _ _ (unit_positive p) left)
    (distance_congr (common_observation A B C D (mesh p) he).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) right)

theorem representation_cross (A B C D : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hA : Γ ⊢[PRAAx] le A B) (he : Γ ⊢[PRAAx] A*D ≐ C*B) :
    Γ ⊢[PRAAx] crossEquivalent nameF nameF (data A B) (data C D) := by
  apply cross_of_diagonal_rate _ _ _ _ (one+one) (name_regular A B hB hA)
    (name_regular C D hD (other_endpoint_bound A B C D hB hA he))
  refine .allI ?_
  let a := Syn.shift A
  let b := Syn.shift B
  let c := Syn.shift C
  let d := Syn.shift D
  let p : PTm (n+1) := var 0
  have hb : Γ.map Fm.shift ⊢[PRAAx] le one b := by simpa [Fm.shift,Syn.shift,b] using hB.shift
  have hd : Γ.map Fm.shift ⊢[PRAAx] le one d := by simpa [Fm.shift,Syn.shift,d] using hD.shift
  have ha : Γ.map Fm.shift ⊢[PRAAx] le a b := by simpa [Fm.shift,Syn.shift,a,b] using hA.shift
  have eq : Γ.map Fm.shift ⊢[PRAAx] a*d ≐ c*b := by
    simpa only [Fm.shift,Fm.subst_eq,PTm.subst_mul,Syn.shift,a,b,c,d] using he.shift
  simpa only [diagonalRate,GaussianArctangentPartialQuadrature.subst_data,PTm.subst_add,
    PTm.subst_succ,PTm.subst_zero,Syn.shift,a,b,c,d,p] using
    distance_congr (sample_at p a b).eqSymm (sample_at p c d).eqSymm
      (.eqRefl _) (.eqRefl _) (representation_sample_distance a b c d p hb hd ha eq)

theorem equal_fraction_cross (A B C D : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hA : Γ ⊢[PRAAx] le A B) (he : Γ ⊢[PRAAx] RationalArgmin.rationalEq (fraction A B) (fraction C D)) :
    Γ ⊢[PRAAx] crossEquivalent nameF nameF (data A B) (data C D) :=
  representation_cross A B C D hB hD hA (cleared_equal_of_fractions A B C D hB hD he)

theorem actual_partial_arctangent_fraction_independent_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ le one (var 3) ⟶ le (var 0) (var 1) ⟶
      RationalArgmin.rationalEq (fraction (var 0) (var 1)) (fraction (var 2) (var 3)) ⟶
      crossEquivalent nameF nameF (data (var 0) (var 1)) (data (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (equal_fraction_cross _ _ _ _ hyp2.wk hyp2 Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianArctangentPartialRepresentation
