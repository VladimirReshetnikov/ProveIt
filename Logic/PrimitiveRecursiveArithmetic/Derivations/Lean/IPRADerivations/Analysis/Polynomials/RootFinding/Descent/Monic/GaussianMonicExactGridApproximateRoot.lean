import IPRADerivations.Analysis.Polynomials.RootFinding.Descent.Monic.GaussianMonicGridApproximateRoot
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.WeightedSums.GaussianRationalDerivativeSum

/-!
# The literal source derivative mesh in the actual bounded grid root search

The exact original coefficient derivative sum supplies L_P and the actual
integer ceiling ceil(4 L_P / epsilon). The already constructed approximate
root and nearest-grid program prove a successful stored test before the
same actual least scan is used. No grid, search, slope, mesh or residual
conclusion is assumed.
-/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

namespace LeanProofs.IPRA.Analysis.GaussianMonicExactGridApproximateRoot

open_ipra
open GaussianMonicGridApproximateRoot
  (radius disk witness input sourceInput input_of_source input_degree input_height input_length input_monic
   input_coefficients input_numerator input_denominator input_tolerance witness_residual witness_disk
   check data scanBody selected scan_accept scan_zero least_rejects)
open GaussianRationalHorner (evaluate)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalSquareGrid (grid nearest nearestIndex)
open GaussianRationalReciprocal (bound_congr)
open GaussianCoefficientNameBounds (bounded_radius_mono)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def L (C N A : PTm n) : PTm n := GaussianRationalDerivativeSum.L C N (disk A)
def mesh (C N A p q : PTm n) : PTm n := GaussianRationalDerivativeSum.mesh C N (disk A) p q
def rounded (C N A p q : PTm n) : PTm n := nearest (radius A) (mesh C N A p q) (witness C N p q)
def witnessIndex (C N A p q : PTm n) : PTm n := nearestIndex (radius A) (mesh C N A p q) (witness C N p q)
def root (C N A p q : PTm n) : PTm n :=
  entry (grid (radius A) (mesh C N A p q)) (selected C (radius A) (mesh C N A p q) p q)
ipra_subst L
ipra_subst mesh
ipra_subst rounded
ipra_subst witnessIndex
ipra_subst root

theorem mesh_positive (C N A p q : PTm n) (h : Γ ⊢[PRAAx] input C N A p q) : Γ ⊢[PRAAx] le one (mesh C N A p q) :=
  GaussianRationalDerivativeSum.mesh_positive _ _ _ _ _ (input_numerator _ _ _ _ _ h) (input_denominator _ _ _ _ _ h)
theorem source_L (C N A p q : PTm n) (h : Γ ⊢[PRAAx] sourceInput C N A p q) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (GaussianEuclideanDistanceName.fraction one one) (L C N A) ⋏
      RationalArgmin.rationalLE (GaussianRationalDerivativeSum.derivativeSum C N (disk A)) (L C N A) :=
  .andI (GaussianRationalDerivativeSum.L_one_bound _ _ _)
    (GaussianRationalDerivativeSum.L_derivative_bound _ _ _ (input_length _ _ _ _ _ (input_of_source _ _ _ _ _ h)))
theorem exact_mesh (C N A p q : PTm n) : Γ ⊢[PRAAx]
    mesh C N A p q ≐ GaussianDescentClockArithmetic.ceiling
      (GaussianRationalDerivativeSum.four*GaussianRationalDerivativeSum.numerator C N (disk A)*q)
      (GaussianRationalVariableHornerBudget.denominator C*p) := .eqRefl _
theorem mesh_least (C N A p q K : PTm n) (h : Γ ⊢[PRAAx] sourceInput C N A p q)
    (hK : Γ ⊢[PRAAx] le (GaussianRationalDerivativeSum.four*GaussianRationalDerivativeSum.numerator C N (disk A)*q)
      (GaussianRationalVariableHornerBudget.denominator C*p*K)) : Γ ⊢[PRAAx] le (mesh C N A p q) K :=
  GaussianRationalDerivativeSum.mesh_least _ _ _ _ _ _ (input_numerator _ _ _ _ _ (input_of_source _ _ _ _ _ h)) hK

theorem rounded_variation (C N A p q : PTm n) (h : Γ ⊢[PRAAx] input C N A p q) : Γ ⊢[PRAAx]
    distanceBounded (evaluate C (witness C N p q)) (evaluate C (rounded C N A p q)) p (GaussianRationalDerivativeSum.four*q) := by
  have hm := mesh_positive C N A p q h
  have old := witness_disk C N A p q h
  have new := GaussianRationalSquareGrid.nearest_bound (radius A) (mesh C N A p q) (witness C N p q) hm old
  have rootU : Γ ⊢[PRAAx] bounded (witness C N p q) (disk A) one :=
    GaussianCoefficientNameBounds.bounded_radius_mono_one
      (le_of_eq_add (a := radius A) (b := disk A) (d := radius A+one) (by unfold disk; ipra_ring)) old
  have roundU : Γ ⊢[PRAAx] bounded (rounded C N A p q) (disk A) one :=
    GaussianCoefficientNameBounds.bounded_radius_mono_one (le_add_right (two*radius A) one) new
  exact GaussianRationalDerivativeSum.mesh_evaluation_bound C N (disk A) (witness C N p q) (rounded C N A p q) p q
    (input_length _ _ _ _ _ h) rootU roundU (input_numerator _ _ _ _ _ h) (input_denominator _ _ _ _ _ h)
    (GaussianRationalSquareGrid.nearest_distance (radius A) (mesh C N A p q) (witness C N p q) hm old)

theorem rounded_residual (C N A p q : PTm n) (h : Γ ⊢[PRAAx] input C N A p q) : Γ ⊢[PRAAx]
    bounded (evaluate C (rounded C N A p q)) p q := by
  have hq := input_denominator C N A p q h
  have h2q := GaussianRationalHorner.positive_product _ _ (le_succ_self one) hq
  have h4q := GaussianRationalHorner.positive_product _ _ GaussianDescentClockArithmetic.four_positive hq
  have budget : Γ ⊢[PRAAx] le (p*(two*q)) (p*(GaussianRationalDerivativeSum.four*q)) :=
    le_of_eq_add (d := two*p*q) (by unfold GaussianRationalDerivativeSum.four; ipra_ring)
  have half := GaussianRationalDistanceOrder.distance_radius_mono _ _ p (GaussianRationalDerivativeSum.four*q) p (two*q) h4q h2q
    budget (rounded_variation C N A p q h)
  have reverse := GaussianRationalDistanceOrder.distance_symmetric _ _ p (two*q) h2q half
  have combined := GaussianRationalPowerDifference.bounded_sum_same _ _ p p (two*q) h2q (witness_residual C N A p q h) reverse
  have value := GaussianRationalLinearProduct.add_sub_right (Γ := Γ) (evaluate C (witness C N p q)) (evaluate C (rounded C N A p q))
    (GaussianRationalHorner.horner_canonical _ _ _)
  have evalBound : Γ ⊢[PRAAx] bounded (evaluate C (rounded C N A p q)) (p+p) (two*q) :=
    bound_congr value (.eqRefl _) (.eqRefl _) combined
  exact bounded_radius_mono _ _ _ _ _ h2q hq (le_congr (by ipra_ring) (by ipra_ring) (le_refl (two*p*q))) evalBound

theorem constructive_witness (C N A p q : PTm n) (h : Γ ⊢[PRAAx] input C N A p q) : Γ ⊢[PRAAx]
    lt (witnessIndex C N A p q) (length (grid (radius A) (mesh C N A p q))) ⋏
      bounded (evaluate C (entry (grid (radius A) (mesh C N A p q)) (witnessIndex C N A p q))) p q := by
  have old := witness_disk C N A p q h
  have lookup := GaussianRationalSquareGrid.nearest_lookup (radius A) (mesh C N A p q) (witness C N p q) old
  have value : Γ ⊢[PRAAx] evaluate C (entry (grid (radius A) (mesh C N A p q)) (witnessIndex C N A p q)) ≐
      evaluate C (rounded C N A p q) := congrAp3 GaussianRationalHorner.hornerF (.eqRefl _) (.eqRefl _) lookup
  exact .andI (GaussianRationalSquareGrid.nearest_index_bound _ _ _ old)
    (bound_congr value.eqSymm (.eqRefl _) (.eqRefl _) (rounded_residual C N A p q h))

theorem search_found (C N A p q : PTm n) (h : Γ ⊢[PRAAx] input C N A p q) : Γ ⊢[PRAAx]
    lt (selected C (radius A) (mesh C N A p q) p q) (length (grid (radius A) (mesh C N A p q))) ⋏
      ((inst2 scanBody (selected C (radius A) (mesh C N A p q) p q) (data C (radius A) (mesh C N A p q) p q) ≐ zero) ⋏
        le (selected C (radius A) (mesh C N A p q) p q) (witnessIndex C N A p q)) := by
  have actual := constructive_witness C N A p q h
  exact Search.search_found (scan_zero _ _ _ _ _ _ (.andE₂ actual)) (.andE₁ actual)

theorem root_residual (C N A p q : PTm n) (h : Γ ⊢[PRAAx] input C N A p q) : Γ ⊢[PRAAx]
    bounded (evaluate C (root C N A p q)) p q := scan_accept _ _ _ _ _ _ (.andE₁ (.andE₂ (search_found C N A p q h)))
theorem root_canonical (C N A p q : PTm n) (h : Γ ⊢[PRAAx] input C N A p q) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (root C N A p q) := GaussianRationalSquareGrid.grid_entry_canonical _ _ _
      (mesh_positive C N A p q h) (.andE₁ (search_found C N A p q h))
theorem selected_bound (C N A p q : PTm n) (h : Γ ⊢[PRAAx] input C N A p q) : Γ ⊢[PRAAx]
    lt (selected C (radius A) (mesh C N A p q) p q)
      (GaussianRationalSquareGrid.side (radius A) (mesh C N A p q)*GaussianRationalSquareGrid.side (radius A) (mesh C N A p q)) :=
  lt_congr (.eqRefl _) (GaussianRationalSquareGrid.grid_length _ _) (.andE₁ (search_found C N A p q h))
theorem root_disk (C N A p q : PTm n) (h : Γ ⊢[PRAAx] input C N A p q) : Γ ⊢[PRAAx]
    bounded (root C N A p q) (radius A) one := by
  have hq := input_denominator C N A p q h
  have small : Γ ⊢[PRAAx] le (p*one) (one*q) := le_congr (by ipra_ring) (by ipra_ring) (input_tolerance C N A p q h)
  exact GaussianEuclideanResidualRadius.residual_radius C (root C N A p q) N A
    (input_degree _ _ _ _ _ h) (input_height _ _ _ _ _ h) (input_length _ _ _ _ _ h)
    (input_monic _ _ _ _ _ h) (input_coefficients _ _ _ _ _ h)
    (bounded_radius_mono _ _ _ _ _ hq (le_refl one) small (root_residual C N A p q h))

theorem source_result (C N A p q : PTm n) (h : Γ ⊢[PRAAx] sourceInput C N A p q) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (root C N A p q) ⋏
      (bounded (evaluate C (root C N A p q)) p q ⋏ bounded (root C N A p q) (radius A) one) :=
  .andI (root_canonical _ _ _ _ _ (input_of_source _ _ _ _ _ h))
    (.andI (root_residual _ _ _ _ _ (input_of_source _ _ _ _ _ h)) (root_disk _ _ _ _ _ (input_of_source _ _ _ _ _ h)))


def output (C N A p q : PTm n) : PTm n := pairT (root C N A p q)
  (pairT (selected C (radius A) (mesh C N A p q) p q)
    (pairT (grid (radius A) (mesh C N A p q)) (pairT (mesh C N A p q) (pairT (L C N A) (radius A)))))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (C N A p q : PTm n) : PTm n := PTm.app outputF ![C,N,A,p,q]
ipra_subst output
ipra_subst run
theorem program_at (C N A p q : PTm n) : Γ ⊢[PRAAx] run C N A p q ≐ output C N A p q := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![C,N,A,p,q]
theorem returned_root (C N A p q : PTm n) : Γ ⊢[PRAAx] fstT (run C N A p q) ≐ root C N A p q :=
  (program_at C N A p q).fstE
theorem returned_index (C N A p q : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run C N A p q)) ≐ selected C (radius A) (mesh C N A p q) p q :=
  (congrFst (congrSnd (program_at C N A p q))).eqTrans (snd_pair _ _).fstE
theorem returned_grid (C N A p q : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run C N A p q))) ≐ grid (radius A) (mesh C N A p q) := by
  have t1 := (program_at (Γ := Γ) C N A p q).sndE
  have t2 := t1.sndE
  exact t2.fstE
theorem returned_mesh (C N A p q : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run C N A p q)))) ≐ mesh C N A p q := by
  have t1 := (program_at (Γ := Γ) C N A p q).sndE
  have t2 := t1.sndE
  have t3 := t2.sndE
  exact t3.fstE
theorem returned_L (C N A p q : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (sndT (run C N A p q))))) ≐ L C N A := by
  have t1 := (program_at (Γ := Γ) C N A p q).sndE
  have t2 := t1.sndE
  have t3 := t2.sndE
  have t4 := t3.sndE
  exact t4.fstE
theorem returned_radius (C N A p q : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (sndT (run C N A p q))))) ≐ radius A := by
  have t1 := (program_at (Γ := Γ) C N A p q).sndE
  have t2 := t1.sndE
  have t3 := t2.sndE
  have t4 := t3.sndE
  exact t4.sndE
theorem returned_lookup (C N A p q : PTm n) : Γ ⊢[PRAAx]
    entry (fstT (sndT (sndT (run C N A p q)))) (fstT (sndT (run C N A p q))) ≐ fstT (run C N A p q) :=
  (LeanProofs.IPRA.Foundations.SequenceComposition.entry_congr (returned_grid C N A p q) (returned_index C N A p q)).eqTrans
    (returned_root C N A p q).eqSymm
theorem returned_result (C N A p q : PTm n) (h : Γ ⊢[PRAAx] sourceInput C N A p q) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (fstT (run C N A p q)) ⋏
      (bounded (evaluate C (fstT (run C N A p q))) p q ⋏
        bounded (fstT (run C N A p q)) (sndT (sndT (sndT (sndT (sndT (run C N A p q)))))) one) := by
  have actual := source_result C N A p q h
  exact .andI (GaussianRationalHorner.canonical_congr (returned_root C N A p q) (.andE₁ actual))
    (.andI (bound_congr (congrAp3 GaussianRationalHorner.hornerF (.eqRefl _) (.eqRefl _) (returned_root C N A p q)).eqSymm
      (.eqRefl _) (.eqRefl _) (.andE₁ (.andE₂ actual)))
      (bound_congr (returned_root C N A p q).eqSymm (returned_radius C N A p q).eqSymm (.eqRefl _) (.andE₂ (.andE₂ actual))))

theorem actual_source_derivative_mesh_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (mesh (var 0) (var 1) (var 2) (var 3) (var 4) ≐ GaussianDescentClockArithmetic.ceiling
      (GaussianRationalDerivativeSum.four*GaussianRationalDerivativeSum.numerator (var 0) (var 1) (disk (var 2))*var 4)
      (GaussianRationalVariableHornerBudget.denominator (var 0)*var 3)) := closeUniv 5 (exact_mesh _ _ _ _ _)
theorem actual_source_mesh_least_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (sourceInput (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      le (GaussianRationalDerivativeSum.four*GaussianRationalDerivativeSum.numerator (var 0) (var 1) (disk (var 2))*var 4)
        (GaussianRationalVariableHornerBudget.denominator (var 0)*var 3*var 5) ⟶
      le (mesh (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5)) :=
  closeUniv 6 (.impI (.impI (mesh_least _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_source_mesh_variation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sourceInput (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ distanceBounded
      (evaluate (var 0) (witness (var 0) (var 1) (var 3) (var 4)))
      (evaluate (var 0) (rounded (var 0) (var 1) (var 2) (var 3) (var 4))) (var 3) (GaussianRationalDerivativeSum.four*var 4)) :=
  closeUniv 5 (.impI (rounded_variation _ _ _ _ _ (input_of_source _ _ _ _ _ Prf.hyp0)))
theorem actual_source_constructive_grid_witness_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sourceInput (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      (lt (witnessIndex (var 0) (var 1) (var 2) (var 3) (var 4))
        (length (grid (radius (var 2)) (mesh (var 0) (var 1) (var 2) (var 3) (var 4)))) ⋏
      bounded (evaluate (var 0) (entry (grid (radius (var 2)) (mesh (var 0) (var 1) (var 2) (var 3) (var 4)))
        (witnessIndex (var 0) (var 1) (var 2) (var 3) (var 4)))) (var 3) (var 4))) :=
  closeUniv 5 (.impI (constructive_witness _ _ _ _ _ (input_of_source _ _ _ _ _ Prf.hyp0)))
theorem actual_source_exact_grid_root_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sourceInput (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      (GaussianRationalHorner.canonical (root (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
        (bounded (evaluate (var 0) (root (var 0) (var 1) (var 2) (var 3) (var 4))) (var 3) (var 4) ⋏
          bounded (root (var 0) (var 1) (var 2) (var 3) (var 4)) (radius (var 2)) one))) :=
  closeUniv 5 (.impI (source_result _ _ _ _ _ Prf.hyp0))
theorem actual_source_exact_grid_size_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sourceInput (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      lt (selected (var 0) (radius (var 2)) (mesh (var 0) (var 1) (var 2) (var 3) (var 4)) (var 3) (var 4))
        (GaussianRationalSquareGrid.side (radius (var 2)) (mesh (var 0) (var 1) (var 2) (var 3) (var 4))*
          GaussianRationalSquareGrid.side (radius (var 2)) (mesh (var 0) (var 1) (var 2) (var 3) (var 4)))) :=
  closeUniv 5 (.impI (selected_bound _ _ _ _ _ (input_of_source _ _ _ _ _ Prf.hyp0)))
theorem actual_least_grid_rejection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (lt (var 5) (selected (var 0) (radius (var 2)) (mesh (var 0) (var 1) (var 2) (var 3) (var 4)) (var 3) (var 4)) ⟶
      neg (bounded (evaluate (var 0) (entry (grid (radius (var 2)) (mesh (var 0) (var 1) (var 2) (var 3) (var 4))) (var 5))) (var 3) (var 4))) :=
  closeUniv 6 (.impI (least_rejects _ _ _ _ _ _ Prf.hyp0))
theorem actual_exact_grid_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) := closeUniv 5 (program_at _ _ _ _ _)
theorem actual_returned_grid_lookup_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (entry (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))))
      (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))) ≐ fstT (run (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (returned_lookup _ _ _ _ _)
theorem actual_returned_exact_grid_root_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sourceInput (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      (GaussianRationalHorner.canonical (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4))) ⋏
        (bounded (evaluate (var 0) (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4)))) (var 3) (var 4) ⋏
          bounded (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4)))
            (sndT (sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))))) one))) :=
  closeUniv 5 (.impI (returned_result _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianMonicExactGridApproximateRoot
