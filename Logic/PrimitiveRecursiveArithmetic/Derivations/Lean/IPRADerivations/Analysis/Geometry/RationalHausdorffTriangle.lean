import IPRADerivations.Analysis.RationalArithmetic.RationalHausdorff
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.CommonLemmas

/-!
# Triangle inequality for the actual independently scaled rational outputs

Finite-demand `lem:aggregate-calculus`, clause 1. Original-coordinate radius
contracts compose by the exact rational cross identity and positive
cancellation of the middle coordinate denominator. Bounded existential
elimination composes the actual original-list cover witnesses.

Each pair's own computed Hausdorff numerator and denominator satisfies its
original cover contract. Composition and the already proved characterization
therefore yield the triangle inequality with three independent computed
scales. No comparison of independently normalized grids or separate scale
invariance theorem is assumed.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.RationalHausdorffTriangle

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.RationalSupMetric
open LeanProofs.IPRA.Analysis.RationalHausdorff
open LeanProofs.IPRA.Foundations
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.Foundations.GapDecision (zabs zabs_congr zabs_tri)
open LeanProofs.IPRA.Foundations.FiniteHausdorff (sum_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem abs_scale (c : PTm n) (u : ZT n) : Γ ⊢[PRAAx] zabs (ZT.ofNat c * u) ≐ c * zabs u := by
  have equal : ZT.toZ Γ (ZT.ofNat c * u) = ZT.toZ Γ (⟨c * u.pos, c * u.neg⟩ : ZT n) := by
    rw [ZT.toZ_mul, ZT.toZ_ofNat]
    simp only [ZT.toZ, Q.mk_mul, map_mul]
    ring
  exact (zabs_congr equal).eqTrans (Probability.MedianWeighted.ad_mul c u.pos u.neg)

private alias positive_cancel := Common.mul_cancel_le

/-- The middle denominator clears the exact rational cross triangle. -/
theorem cross_triangle_identity (x y z k : PTm n) :
    Γ ⊢[PRAAx] ZT.eq
      (ZT.ofNat (rationalDenominator y k) * crossNumerator x z k)
      (ZT.ofNat (rationalDenominator z k) * crossNumerator x y k +
        ZT.ofNat (rationalDenominator x k) * crossNumerator y z k) := by
  ipra_lc [crossNumerator]

theorem cross_triangle (x y z k : PTm n) :
    Γ ⊢[PRAAx] le (rationalDenominator y k * zabs (crossNumerator x z k))
      (rationalDenominator z k * zabs (crossNumerator x y k) +
        rationalDenominator x k * zabs (crossNumerator y z k)) := by
  have identity := ZT.toZ_eq (cross_triangle_identity (Γ := Γ) x y z k)
  have sum : ZT.toZ Γ (ZT.ofNat (rationalDenominator y k) * crossNumerator x z k) =
      ZT.toZ Γ (ZT.ofNat (rationalDenominator z k) * crossNumerator x y k) +
        ZT.toZ Γ (ZT.ofNat (rationalDenominator x k) * crossNumerator y z k) := by
    simpa only [ZT.toZ_add] using identity
  exact le_congr (abs_scale _ _) (congrAdd (abs_scale _ _) (abs_scale _ _)) (zabs_tri sum)

/-- Only the decoded positive middle coordinate denominator is cancelled.
The radius denominators themselves may be zero in this cleared inequality. -/
theorem coordinateRadius_triangle (x y z k A B C D : PTm n)
    (hxy : Γ ⊢[PRAAx] coordinateRadius x y k A B) (hyz : Γ ⊢[PRAAx] coordinateRadius y z k C D) :
    Γ ⊢[PRAAx] coordinateRadius x z k (A * D + C * B) (B * D) := by
  have triangle : Γ ⊢[PRAAx] le
      (rationalDenominator y k * ((B * D) * zabs (crossNumerator x z k)))
      ((rationalDenominator z k * D) * (B * zabs (crossNumerator x y k)) +
        (rationalDenominator x k * B) * (D * zabs (crossNumerator y z k))) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (B * D) (cross_triangle x y z k))
  have bounds := sum_mono
    (le_mul_mono (le_refl (rationalDenominator z k * D)) hxy)
    (le_mul_mono (le_refl (rationalDenominator x k * B)) hyz)
  have joined : Γ ⊢[PRAAx] le
      (rationalDenominator y k * ((B * D) * zabs (crossNumerator x z k)))
      (rationalDenominator y k * ((A * D + C * B) * denominatorProduct x z k)) :=
    le_trans triangle (le_congr (.eqRefl _) (by unfold denominatorProduct; ipra_ring) bounds)
  exact positive_cancel (rationalDenominator_one_le y k) joined

theorem pointRadius_triangle (x y z d A B C D : PTm n)
    (hxy : Γ ⊢[PRAAx] pointRadius x y d A B) (hyz : Γ ⊢[PRAAx] pointRadius y z d C D) :
    Γ ⊢[PRAAx] pointRadius x z d (A * D + C * B) (B * D) := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift d) :: Γ.map Fm.shift
  have first : Δ ⊢[PRAAx] pointRadius (Syn.shift x) (Syn.shift y) (Syn.shift d) (Syn.shift A) (Syn.shift B) := by
    simpa only [Fm.shift, subst_pointRadius, Syn.shift] using hxy.shift.wk
  have second : Δ ⊢[PRAAx] pointRadius (Syn.shift y) (Syn.shift z) (Syn.shift d) (Syn.shift C) (Syn.shift D) := by
    simpa only [Fm.shift, subst_pointRadius, Syn.shift] using hyz.shift.wk
  have result := coordinateRadius_triangle (Syn.shift x) (Syn.shift y) (Syn.shift z) (var 0)
    (Syn.shift A) (Syn.shift B) (Syn.shift C) (Syn.shift D)
    (pointRadius_at _ _ _ _ _ _ first Prf.hyp0) (pointRadius_at _ _ _ _ _ _ second Prf.hyp0)
  simpa only [Δ, Syn.shift, PTm.subst_add, PTm.subst_mul] using result

/-! ## Compose actual raw-list witnesses, sealing both local indices -/

theorem extend_hit (S T U d A B C D i j : PTm n)
    (hij : Γ ⊢[PRAAx] pointRadius (entry S i) (entry T j) d A B)
    (hjk : Γ ⊢[PRAAx] originalHit .left .right T U d C D j) :
    Γ ⊢[PRAAx] originalHit .left .right S U d (A * D + C * B) (B * D) i := by
  refine .exE hjk ?_
  let E : Fm PTm (n + 1) := lt (var 0) (length (Syn.shift U)) ⋏
    pointRadius (entry (Syn.shift T) (Syn.shift j)) (entry (Syn.shift U) (var 0)) (Syn.shift d) (Syn.shift C) (Syn.shift D)
  have first : E :: Γ.map Fm.shift ⊢[PRAAx]
      pointRadius (entry (Syn.shift S) (Syn.shift i)) (entry (Syn.shift T) (Syn.shift j)) (Syn.shift d) (Syn.shift A) (Syn.shift B) := by
    simpa only [Fm.shift, subst_pointRadius, MasterCertificate.subst_entry, Syn.shift] using hij.shift.wk
  have result := originalHit_intro .left .right (Syn.shift S) (Syn.shift U) (Syn.shift d)
    (Syn.shift A * Syn.shift D + Syn.shift C * Syn.shift B) (Syn.shift B * Syn.shift D) (Syn.shift i) (var 0)
    (Prf.andE₁ (Prf.hyp0 : E :: Γ.map Fm.shift ⊢[PRAAx] E))
    (pointRadius_triangle _ _ _ _ _ _ _ _ first (Prf.andE₂ Prf.hyp0))
  simpa only [E, source, Fm.shift, subst_originalHit, PTm.subst_add, PTm.subst_mul, Syn.shift] using result

theorem hit_triangle (S T U d A B C D i : PTm n)
    (hST : Γ ⊢[PRAAx] originalHit .left .right S T d A B i)
    (hTU : Γ ⊢[PRAAx] originalCover .left .right T U d C D) :
    Γ ⊢[PRAAx] originalHit .left .right S U d (A * D + C * B) (B * D) i := by
  refine .exE hST ?_
  let E : Fm PTm (n + 1) := lt (var 0) (length (Syn.shift T)) ⋏
    pointRadius (entry (Syn.shift S) (Syn.shift i)) (entry (Syn.shift T) (var 0)) (Syn.shift d) (Syn.shift A) (Syn.shift B)
  have cover : Γ.map Fm.shift ⊢[PRAAx] originalCover .left .right (Syn.shift T) (Syn.shift U) (Syn.shift d) (Syn.shift C) (Syn.shift D) := by
    simpa only [Fm.shift, subst_originalCover, Syn.shift] using hTU.shift
  have hit := originalCover_at .left .right (Syn.shift T) (Syn.shift U) (Syn.shift d) (Syn.shift C) (Syn.shift D)
    (var 0) cover.wk (Prf.andE₁ (Prf.hyp0 : E :: Γ.map Fm.shift ⊢[PRAAx] E))
  have result := extend_hit (Syn.shift S) (Syn.shift T) (Syn.shift U) (Syn.shift d)
    (Syn.shift A) (Syn.shift B) (Syn.shift C) (Syn.shift D) (Syn.shift i) (var 0) (Prf.andE₂ Prf.hyp0) hit
  simpa only [E, source, Fm.shift, subst_originalHit, PTm.subst_add, PTm.subst_mul, Syn.shift] using result

theorem originalCover_triangle (S T U d A B C D : PTm n)
    (hST : Γ ⊢[PRAAx] originalCover .left .right S T d A B)
    (hTU : Γ ⊢[PRAAx] originalCover .left .right T U d C D) :
    Γ ⊢[PRAAx] originalCover .left .right S U d (A * D + C * B) (B * D) := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (Syn.shift S)) :: Γ.map Fm.shift
  have first : Δ ⊢[PRAAx] originalCover .left .right (Syn.shift S) (Syn.shift T) (Syn.shift d) (Syn.shift A) (Syn.shift B) := by
    simpa only [Fm.shift, subst_originalCover, Syn.shift] using hST.shift.wk
  have second : Δ ⊢[PRAAx] originalCover .left .right (Syn.shift T) (Syn.shift U) (Syn.shift d) (Syn.shift C) (Syn.shift D) := by
    simpa only [Fm.shift, subst_originalCover, Syn.shift] using hTU.shift.wk
  have result := hit_triangle (Syn.shift S) (Syn.shift T) (Syn.shift U) (Syn.shift d)
    (Syn.shift A) (Syn.shift B) (Syn.shift C) (Syn.shift D) (var 0)
    (originalCover_at .left .right _ _ _ _ _ _ first Prf.hyp0) second
  simpa only [Δ, source, Syn.shift, PTm.subst_add, PTm.subst_mul] using result

#print axioms cross_triangle_identity
#print axioms coordinateRadius_triangle
#print axioms pointRadius_triangle
#print axioms extend_hit
#print axioms originalCover_triangle

theorem originalCover_radius_congr (S T d : PTm n) {A A' B B' : PTm n}
    (hA : Γ ⊢[PRAAx] A ≐ A') (hB : Γ ⊢[PRAAx] B ≐ B')
    (h : Γ ⊢[PRAAx] originalCover .left .right S T d A B) :
    Γ ⊢[PRAAx] originalCover .left .right S T d A' B' := by
  have input : Γ ⊢[PRAAx] (originalCover .left .right (var 0) (var 1) (var 2) (var 3) (var 4)).subst ![S, T, d, A, B] := by
    simpa using h
  have output := Prf.eqSubst (originalCover .left .right (var 0) (var 1) (var 2) (var 3) (var 4))
    ![S, T, d, A, B] ![S, T, d, A', B']
    (fun i => by fin_cases i <;> first | exact hA | exact hB | exact .eqRefl _) input
  simpa using output

theorem reverse_cover (S T d A B : PTm n) :
    originalCover .right .left S T d A B = originalCover .left .right T S d A B := rfl

theorem originalClose_triangle (S T U d A B C D : PTm n)
    (hST : Γ ⊢[PRAAx] originalClose S T d A B) (hTU : Γ ⊢[PRAAx] originalClose T U d C D) :
    Γ ⊢[PRAAx] originalClose S U d (A * D + C * B) (B * D) := by
  have forward := originalCover_triangle S T U d A B C D (Prf.andE₁ hST) (Prf.andE₁ hTU)
  have backward : Γ ⊢[PRAAx] originalCover .left .right U S d (C * B + A * D) (D * B) :=
    originalCover_triangle U T S d C D A B (Prf.andE₂ hTU) (Prf.andE₂ hST)
  exact .andI forward (originalCover_radius_congr U S d (add_comm _ _) (mul_comm _ _) backward)

/-! ## Instantiate each edge at its own computed rational Hausdorff value -/

theorem own_cover (S T d : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hT : Γ ⊢[PRAAx] le one (length T)) :
    Γ ⊢[PRAAx] originalClose S T d (numerator S T d) (denominator S T d) :=
  original_close_of_bound S T d _ _ hS hT (le_congr (.eqRefl _) (mul_comm _ _) (le_refl _))

theorem own_cover_composite (S T U d : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hT : Γ ⊢[PRAAx] le one (length T))
    (hU : Γ ⊢[PRAAx] le one (length U)) :
    Γ ⊢[PRAAx] originalClose S U d
      (numerator S T d * denominator T U d + numerator T U d * denominator S T d)
      (denominator S T d * denominator T U d) :=
  originalClose_triangle S T U d _ _ _ _ (own_cover S T d hS hT) (own_cover T U d hT hU)

/-- The actual pair-scale triangle. The three denominators are computed
independently for `S,T`, `T,U` and `S,U`. -/
theorem rational_triangle (S T U d : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hT : Γ ⊢[PRAAx] le one (length T))
    (hU : Γ ⊢[PRAAx] le one (length U)) :
    Γ ⊢[PRAAx] le ((denominator S T d * denominator T U d) * numerator S U d)
      ((numerator S T d * denominator T U d + numerator T U d * denominator S T d) * denominator S U d) :=
  bound_of_original_close S U d _ _ (own_cover_composite S T U d hS hT hU)

/-- The same inequality stated directly on the actual exported PR codes. -/
theorem code_triangle (S T U d : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hT : Γ ⊢[PRAAx] le one (length T))
    (hU : Γ ⊢[PRAAx] le one (length U)) :
    Γ ⊢[PRAAx] le ((sndT (ap3 codeF S T d) * sndT (ap3 codeF T U d)) * fstT (ap3 codeF S U d))
      ((fstT (ap3 codeF S T d) * sndT (ap3 codeF T U d) + fstT (ap3 codeF T U d) * sndT (ap3 codeF S T d)) *
        sndT (ap3 codeF S U d)) :=
  le_congr (congrMul (congrMul (code_denominator S T d).eqSymm (code_denominator T U d).eqSymm)
    (code_numerator S U d).eqSymm)
    (congrMul (congrAdd (congrMul (code_numerator S T d).eqSymm (code_denominator T U d).eqSymm)
      (congrMul (code_numerator T U d).eqSymm (code_denominator S T d).eqSymm)) (code_denominator S U d).eqSymm)
    (rational_triangle S T U d hS hT hU)

theorem triangle_checker (S T U d : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hT : Γ ⊢[PRAAx] le one (length T))
    (hU : Γ ⊢[PRAAx] le one (length U)) :
    Γ ⊢[PRAAx] apply5 checkerF S U d
      (numerator S T d * denominator T U d + numerator T U d * denominator S T d)
      (denominator S T d * denominator T U d) ≐ one :=
  checker_complete S U d _ _ (own_cover_composite S T U d hS hT hU)

/-! ## Actual PR rational addition and closed runtime endpoints -/

def summedRadius (A B C D : PTm n) : PTm n := pairT (A * D + C * B) (B * D)
def summedRadiusF : PR 4 := PTm.toPR (summedRadius (var 0) (var 1) (var 2) (var 3))

@[simp] theorem subst_summedRadius {m : ℕ} (σ : Fin n → PTm m) (A B C D : PTm n) :
    Syn.subst σ (summedRadius A B C D) = summedRadius (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ C) (Syn.subst σ D) := by
  simp [summedRadius]

theorem summedRadius_at (A B C D : PTm n) :
    Γ ⊢[PRAAx] FiniteQueryDemand.apply4 summedRadiusF A B C D ≐ summedRadius A B C D := by
  have h := toPR_eq (Γ := Γ) (summedRadius (var 0) (var 1) (var 2) (var 3) : PTm 4) ![A, B, C, D]
  simpa [summedRadiusF, FiniteQueryDemand.apply4] using h

theorem summedRadius_positive (A B C D : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] le one (sndT (FiniteQueryDemand.apply4 summedRadiusF A B C D)) :=
  le_congr (one_mul one)
    ((congrSnd (summedRadius_at A B C D)).eqTrans (snd_pair _ _)).eqSymm (le_mul_mono hB hD)

theorem summed_radius_program_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((FiniteQueryDemand.apply4 summedRadiusF (var 0) (var 1) (var 2) (var 3) ≐
        pairT (var 0 * var 3 + var 2 * var 1) (var 1 * var 3)) ⋏
        (le one (var 1) ⟶ le one (var 3) ⟶
          le one (sndT (FiniteQueryDemand.apply4 summedRadiusF (var 0) (var 1) (var 2) (var 3))))) :=
  closeUniv 4 (.andI (summedRadius_at _ _ _ _) (.impI (.impI (summedRadius_positive _ _ _ _ Prf.hyp1 Prf.hyp0))))

theorem point_triangle_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (pointRadius (var 0) (var 1) (var 3) (var 4) (var 5) ⟶
        pointRadius (var 1) (var 2) (var 3) (var 6) (var 7) ⟶
        pointRadius (var 0) (var 2) (var 3) (var 4 * var 7 + var 6 * var 5) (var 5 * var 7)) :=
  closeUniv 8 (.impI (.impI (pointRadius_triangle _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem original_close_triangle_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (originalClose (var 0) (var 1) (var 3) (var 4) (var 5) ⟶
        originalClose (var 1) (var 2) (var 3) (var 6) (var 7) ⟶
        originalClose (var 0) (var 2) (var 3) (var 4 * var 7 + var 6 * var 5) (var 5 * var 7)) :=
  closeUniv 8 (.impI (.impI (originalClose_triangle _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

def triangleFormula : Fm PTm 4 :=
  le one (length (var 0)) ⟶ le one (length (var 1)) ⟶ le one (length (var 2)) ⟶
    le ((denominator (var 0) (var 1) (var 3) * denominator (var 1) (var 2) (var 3)) * numerator (var 0) (var 2) (var 3))
      ((numerator (var 0) (var 1) (var 3) * denominator (var 1) (var 2) (var 3) +
        numerator (var 1) (var 2) (var 3) * denominator (var 0) (var 1) (var 3)) * denominator (var 0) (var 2) (var 3))

theorem rational_triangle_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 triangleFormula :=
  closeUniv 4 (.impI (.impI (.impI (rational_triangle _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

def codeTriangleFormula : Fm PTm 4 :=
  le one (length (var 0)) ⟶ le one (length (var 1)) ⟶ le one (length (var 2)) ⟶
    le ((sndT (ap3 codeF (var 0) (var 1) (var 3)) * sndT (ap3 codeF (var 1) (var 2) (var 3))) *
      fstT (ap3 codeF (var 0) (var 2) (var 3)))
      ((fstT (ap3 codeF (var 0) (var 1) (var 3)) * sndT (ap3 codeF (var 1) (var 2) (var 3)) +
        fstT (ap3 codeF (var 1) (var 2) (var 3)) * sndT (ap3 codeF (var 0) (var 1) (var 3))) *
        sndT (ap3 codeF (var 0) (var 2) (var 3)))

theorem code_triangle_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 codeTriangleFormula :=
  closeUniv 4 (.impI (.impI (.impI (code_triangle _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem triangle_checker_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (le one (length (var 0)) ⟶ le one (length (var 1)) ⟶ le one (length (var 2)) ⟶
        (apply5 checkerF (var 0) (var 2) (var 3)
          (numerator (var 0) (var 1) (var 3) * denominator (var 1) (var 2) (var 3) +
            numerator (var 1) (var 2) (var 3) * denominator (var 0) (var 1) (var 3))
          (denominator (var 0) (var 1) (var 3) * denominator (var 1) (var 2) (var 3)) ≐ one)) :=
  closeUniv 4 (.impI (.impI (.impI (triangle_checker _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

#print axioms originalClose_triangle
#print axioms own_cover_composite
#print axioms rational_triangle
#print axioms code_triangle
#print axioms summedRadius_positive
#print axioms summed_radius_program_closed
#print axioms point_triangle_closed
#print axioms original_close_triangle_closed
#print axioms rational_triangle_closed
#print axioms code_triangle_closed
#print axioms triangle_checker_closed

end LeanProofs.IPRA.Analysis.RationalHausdorffTriangle
