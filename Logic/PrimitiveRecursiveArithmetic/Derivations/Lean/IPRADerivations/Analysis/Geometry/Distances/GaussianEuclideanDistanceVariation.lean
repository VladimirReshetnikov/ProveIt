import IPRADerivations.Analysis.Geometry.Distances.GaussianEuclideanDistanceName

/-!
# Euclidean finite-set distance variation for actual original point lists

An original directed finite cover transfers an actual finite hit. Applied
to the literal Euclidean argmin/square-root witness, this proves point and
set variation of actual rational distance samples. Genuine point-name CN
then yields the exact Hausdorff budget plus both sample dyadic errors.
No minimizing-index choice, distance-variation law or output-name law is
supplied as a premise. All numerical inputs remain object variables.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceVariation

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalCover (hit cover close hit_intro)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (distanceBounded)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.Analysis.GaussianEuclideanPointDistance (unit unit_positive subst_unit lower)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName
  (pointCN shifted distanceSample hit_triangle upper_of_representations fraction_represents)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Instantiate the original directed cover at a genuine stored index. -/
theorem cover_at (S T C D i : PTm n) (h : Γ ⊢[PRAAx] cover S T C D)
    (hi : Γ ⊢[PRAAx] lt i (length S)) : Γ ⊢[PRAAx] hit (entry S i) T C D := by
  have shape : cover S T C D = .all (lt (var 0) (length (Syn.shift S)) ⟶
      hit (entry (Syn.shift S) (var 0)) (Syn.shift T) (Syn.shift C) (Syn.shift D)) := by
    simp only [cover,hit,Syn.shift,subst_entry,Syn.subst_var,Syn.shift_var,Fin.succ_zero_eq_one]
  have hh := h
  rw [shape] at hh
  have rule : Γ ⊢[PRAAx] lt i (length S) ⟶ hit (entry S i) T C D := by
    simpa only [Fm.subst_imp,subst_lt,subst_length,GaussianEuclideanDistanceName.subst_hit,
      subst_entry,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hh.allE i
  exact .impE rule hi

/-- A genuine finite hit and the actual original cover give a finite hit
in the other list, with exact independent rational error budgets. -/
theorem hit_transfer (z S T A B C D : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hCover : Γ ⊢[PRAAx] cover S T C D) (hHit : Γ ⊢[PRAAx] hit z S A B) : Γ ⊢[PRAAx]
    hit z T (A*D+C*B) (B*D) := by
  refine .exE hHit ?_
  let E : Fm PTm (n+1) := lt (var 0) (length (Syn.shift S)) ⋏
    distanceBounded (Syn.shift z) (entry (Syn.shift S) (var 0)) (Syn.shift A) (Syn.shift B)
  have bp : E :: Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,Syn.shift] using hB.shift.wk
  have dp : E :: Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift D) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,Syn.shift] using hD.shift.wk
  have cc : E :: Γ.map Fm.shift ⊢[PRAAx] cover (Syn.shift S) (Syn.shift T) (Syn.shift C) (Syn.shift D) := by
    simpa only [Fm.shift,GaussianRationalCover.subst_cover,Syn.shift] using hCover.shift.wk
  have found := cover_at (Syn.shift S) (Syn.shift T) (Syn.shift C) (Syn.shift D) (var 0) cc
    (Prf.andE₁ (Prf.hyp0 : E :: Γ.map Fm.shift ⊢[PRAAx] E))
  have moved := hit_triangle (Syn.shift z) (entry (Syn.shift S) (var 0)) (Syn.shift T)
    (Syn.shift A) (Syn.shift B) (Syn.shift C) (Syn.shift D) bp dp (Prf.andE₂ Prf.hyp0) found
  simpa only [E,Fm.shift,GaussianEuclideanDistanceName.subst_hit,PTm.subst_add,PTm.subst_mul,Syn.shift] using moved

/-- One-sided variation of literal finite Euclidean minima/square roots.
The sole square-root error is the source sample's 2^-l. -/
theorem lower_upper (z w S T k l A B C D : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hzw : Γ ⊢[PRAAx] distanceBounded z w A B) (hCover : Γ ⊢[PRAAx] cover S T C D) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (lower z T k) (lower w S l)
      ((A*D+C*B)*unit l+B*D) (B*D*unit l) := by
  let L := GaussianEuclideanPointDistance.root w S l
  let E := GaussianEuclideanPointDistance.denominator w S*unit l
  have ep : Γ ⊢[PRAAx] le one E := positive_product _ _
    (GaussianEuclideanPointDistance.denominator_positive w S) (unit_positive l)
  have el := positive_product (Γ := Γ) _ _ ep (unit_positive l)
  have eld := positive_product (Γ := Γ) _ _ el hD
  have denom := positive_product (Γ := Γ) _ _ hB eld
  have actual := GaussianEuclideanPointDistance.lower_bound_to_hit w S l L E hS ep (RationalArgmin.reflexive _)
  have across := hit_transfer w S T (L*unit l+E) (E*unit l) C D el hD hCover actual
  have moved := hit_triangle z w T A B _ _ hB eld hzw across
  have bound := GaussianEuclideanPointDistance.hit_to_lower_bound z T k _ _ denom moved
  have cleared := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (GaussianEuclideanPointDistance.lower_represents (Γ := Γ) z T k) (fraction_represents _ _ denom) bound
  exact upper_of_representations _ _ _ _ L E _ _
    (positive_product _ _ (GaussianEuclideanPointDistance.denominator_positive z T) (unit_positive k)) ep
    (GaussianEuclideanPointDistance.lower_represents z T k) (GaussianEuclideanPointDistance.lower_represents w S l)
    (le_congr (by ipra_ring) (by ipra_ring) cleared)

def sampleNumerator (C D m l : PTm n) : PTm n := C*unit m*unit l+D*(unit m+unit l)
def sampleDenominator (D m l : PTm n) : PTm n := D*(unit m*unit l)

ipra_subst sampleNumerator
ipra_subst sampleDenominator

theorem sample_denominator_positive (D m l : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    le one (sampleDenominator D m l) := positive_product _ _ hD (positive_product _ _ (unit_positive _) (unit_positive _))

/-- The point-name and square-root errors fit the original distance-name
budgets while preserving the Hausdorff C/D contribution exactly. -/
theorem sample_budget (C D m l : PTm n) : Γ ⊢[PRAAx] le
    ((((unit (shifted m)+unit (shifted l))*D+C*(unit (shifted m)*unit (shifted l)))*unit (shifted l)+
      (unit (shifted m)*unit (shifted l))*D)*sampleDenominator D m l)
    (sampleNumerator C D m l*((unit (shifted m)*unit (shifted l))*D*unit (shifted l))) := by
  have scaled := le_mul_mono (le_refl (D*D)) (GaussianEuclideanDistanceName.variation_budget (Γ := Γ) m l)
  exact le_congr (by unfold sampleDenominator; ipra_ring) (by unfold sampleNumerator; ipra_ring)
    (add_le_add_right (C*unit (shifted m)*unit (shifted l)*unit (shifted l)*D*unit m*unit l) scaled)

/-- A genuine directed original cover and point CN imply a literal
one-sided comparison between the two actual Euclidean distance samples. -/
theorem sample_upper (point : PR 2) (S T x m l C D : PTm n)
    (hCN : Γ ⊢[PRAAx] pointCN point x) (hS : Γ ⊢[PRAAx] le one (length S))
    (hD : Γ ⊢[PRAAx] le one D) (hCover : Γ ⊢[PRAAx] cover S T C D) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (distanceSample point T x m) (distanceSample point S x l)
      (sampleNumerator C D m l) (sampleDenominator D m l) :=
  RationalValueBounds.upper_mono _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ (unit_positive _) (unit_positive _)) hD |> fun h => positive_product _ _ h (unit_positive _))
    (lower_upper _ _ _ _ _ _ _ _ _ _ hS (positive_product _ _ (unit_positive _) (unit_positive _)) hD
      (GaussianEuclideanDistanceName.point_cn_at point x (shifted m) (shifted l) hCN) hCover)
    (sample_budget C D m l)

/-- Both original directed covers give the exact Hausdorff budget plus the
two ordinary dyadic sample errors, for arbitrary stored point codes. -/
theorem sample_radius (point : PR 2) (S T x m l C D : PTm n)
    (hCN : Γ ⊢[PRAAx] pointCN point x) (hS : Γ ⊢[PRAAx] le one (length S))
    (hT : Γ ⊢[PRAAx] le one (length T)) (hD : Γ ⊢[PRAAx] le one D)
    (hClose : Γ ⊢[PRAAx] close S T C D) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (distanceSample point T x m) (distanceSample point S x l)
      (sampleNumerator C D m l) (sampleDenominator D m l) :=
  RationalValueBounds.radius_of_upper _ _ _ _ (sample_upper point S T x m l C D hCN hS hD (Prf.andE₁ hClose))
    (RationalValueBounds.upper_congr (.eqRefl _) (.eqRefl _) (by unfold sampleNumerator; ipra_ring)
      (by unfold sampleDenominator; ipra_ring) (sample_upper point T S x l m C D hCN hT hD (Prf.andE₂ hClose)))

theorem checker_sample_radius (point : PR 2) (S T x m l C D : PTm n)
    (hCN : Γ ⊢[PRAAx] pointCN point x) (hS : Γ ⊢[PRAAx] le one (length S))
    (hT : Γ ⊢[PRAAx] le one (length T)) (hD : Γ ⊢[PRAAx] le one D)
    (hCheck : Γ ⊢[PRAAx] GaussianRationalCover.check S T C D ≐ one) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (distanceSample point T x m) (distanceSample point S x l)
      (sampleNumerator C D m l) (sampleDenominator D m l) :=
  sample_radius point S T x m l C D hCN hS hT hD ((GaussianRationalCover.checker_reflection S T C D).iffMp hCheck)

/-! The actual PR7 program returns both original Euclidean distance samples
and the exact independent-denominator variation budget. -/
def output (point : PR 2) (S T x m l C D : PTm n) : PTm n :=
  pairT (distanceSample point T x m) (pairT (distanceSample point S x l)
    (pairT (sampleNumerator C D m l) (sampleDenominator D m l)))
def outputF (point : PR 2) : PR 7 := PTm.toPR (output point (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
def run (point : PR 2) (S T x m l C D : PTm n) : PTm n := PTm.app (outputF point) ![S,T,x,m,l,C,D]

ipra_subst output
ipra_subst run

theorem program_at (point : PR 2) (S T x m l C D : PTm n) : Γ ⊢[PRAAx]
    run point S T x m l C D ≐ output point S T x m l C D := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output point (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7) ![S,T,x,m,l,C,D]

theorem output_left (point : PR 2) (S T x m l C D : PTm n) : Γ ⊢[PRAAx]
    fstT (run point S T x m l C D) ≐ distanceSample point T x m :=
  (program_at point S T x m l C D).fstE
theorem output_right (point : PR 2) (S T x m l C D : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run point S T x m l C D)) ≐ distanceSample point S x l :=
  (program_at point S T x m l C D).sndE.fstE
theorem output_numerator (point : PR 2) (S T x m l C D : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run point S T x m l C D))) ≐ sampleNumerator C D m l :=
  (program_at point S T x m l C D).sndE.sndE.fstE
theorem output_denominator (point : PR 2) (S T x m l C D : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (run point S T x m l C D))) ≐ sampleDenominator D m l :=
  (program_at point S T x m l C D).sndE.sndE.sndE

theorem program_certificate (point : PR 2) (S T x m l C D : PTm n)
    (hCN : Γ ⊢[PRAAx] pointCN point x) (hS : Γ ⊢[PRAAx] le one (length S))
    (hT : Γ ⊢[PRAAx] le one (length T)) (hD : Γ ⊢[PRAAx] le one D)
    (hClose : Γ ⊢[PRAAx] close S T C D) : Γ ⊢[PRAAx]
    le one (sndT (sndT (sndT (run point S T x m l C D)))) ⋏
      RationalValueBounds.radius (fstT (run point S T x m l C D)) (fstT (sndT (run point S T x m l C D)))
        (fstT (sndT (sndT (run point S T x m l C D)))) (sndT (sndT (sndT (run point S T x m l C D)))) :=
  .andI (le_congr (.eqRefl _) (output_denominator point S T x m l C D).eqSymm (sample_denominator_positive D m l hD))
    (RationalValueBounds.radius_congr (output_left point S T x m l C D).eqSymm (output_right point S T x m l C D).eqSymm
      (output_numerator point S T x m l C D).eqSymm (output_denominator point S T x m l C D).eqSymm
      (sample_radius point S T x m l C D hCN hS hT hD hClose))

theorem finite_hit_cover_transfer_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le one (var 4) ⟶ le one (var 6) ⟶ cover (var 1) (var 2) (var 5) (var 6) ⟶
      hit (var 0) (var 1) (var 3) (var 4) ⟶ hit (var 0) (var 2) (var 3*var 6+var 5*var 4) (var 4*var 6)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (hit_transfer _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

theorem finite_euclidean_distance_variation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (le one (length (var 2)) ⟶ le one (var 7) ⟶ le one (var 9) ⟶
      distanceBounded (var 0) (var 1) (var 6) (var 7) ⟶ cover (var 2) (var 3) (var 8) (var 9) ⟶
      RationalValueBounds.upper (lower (var 0) (var 3) (var 4)) (lower (var 1) (var 2) (var 5))
        ((var 6*var 9+var 8*var 7)*unit (var 5)+var 7*var 9) (var 7*var 9*unit (var 5))) :=
  closeUniv 10 (.impI (.impI (.impI (.impI (.impI
    (lower_upper _ _ _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))

theorem euclidean_distance_sample_variation_closed (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (pointCN point (var 2) ⟶ le one (length (var 0)) ⟶ le one (length (var 1)) ⟶ le one (var 6) ⟶
      close (var 0) (var 1) (var 5) (var 6) ⟶
        RationalValueBounds.radius (distanceSample point (var 1) (var 2) (var 3)) (distanceSample point (var 0) (var 2) (var 4))
          (sampleNumerator (var 5) (var 6) (var 3) (var 4)) (sampleDenominator (var 6) (var 3) (var 4))) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI
    (sample_radius _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))

theorem euclidean_distance_checker_variation_closed (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (pointCN point (var 2) ⟶ le one (length (var 0)) ⟶ le one (length (var 1)) ⟶ le one (var 6) ⟶
      GaussianRationalCover.check (var 0) (var 1) (var 5) (var 6) ≐ one ⟶
        RationalValueBounds.radius (distanceSample point (var 1) (var 2) (var 3)) (distanceSample point (var 0) (var 2) (var 4))
          (sampleNumerator (var 5) (var 6) (var 3) (var 4)) (sampleDenominator (var 6) (var 3) (var 4))) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI
    (checker_sample_radius _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))

theorem euclidean_distance_variation_program_closed (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (run point (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ≐ output point (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (program_at _ _ _ _ _ _ _ _)

theorem euclidean_distance_variation_certificate_closed (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (pointCN point (var 2) ⟶ le one (length (var 0)) ⟶ le one (length (var 1)) ⟶ le one (var 6) ⟶
      close (var 0) (var 1) (var 5) (var 6) ⟶
        (le one (sndT (sndT (sndT (run point (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)))))) ⋏
          RationalValueBounds.radius (fstT (run point (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)))
            (fstT (sndT (run point (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))))
            (fstT (sndT (sndT (run point (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)))))
            (sndT (sndT (sndT (run point (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)))))) := by
  apply closeUniv 7
  refine .impI (.impI (.impI (.impI (.impI ?_))))
  exact program_certificate _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

end LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceVariation
