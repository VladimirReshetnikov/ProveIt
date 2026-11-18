import IPRADerivations.Analysis.RationalHausdorffTriangle
import IPRADerivations.Foundations.FiniteHausdorffConcat

/-!
# Concatenation at the original rational-coordinate interface

Finite-demand `lem:aggregate-calculus`, clause 2. The append lists are the
actual primitive-recursive sequence constructors. An original cover witness
is inserted into the corresponding append block, and the source index is
split using the actual first-block length. The two input Hausdorff values
keep their independently computed denominators. Their exact rational maximum
is represented by the maximum of the two cross products over the product
denominator; the resulting bound is against the append pair's own scale.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.RationalHausdorffConcat

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.RationalHausdorff
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition
  (length append append_length append_left append_right append_right_at)
open LeanProofs.IPRA.Foundations.FiniteHausdorffConcat (suffix_range left_range right_range)
open LeanProofs.IPRA.Foundations.DemandClosure (maximum maximum_left maximum_right maximum_le)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem coordinateRadius_congr {x x' y y' k A B : PTm n}
    (hx : Γ ⊢[PRAAx] x ≐ x') (hy : Γ ⊢[PRAAx] y ≐ y')
    (h : Γ ⊢[PRAAx] coordinateRadius x y k A B) : Γ ⊢[PRAAx] coordinateRadius x' y' k A B := by
  have numerator : ZT.toZ Γ (crossNumerator x y k) = ZT.toZ Γ (crossNumerator x' y' k) := by
    simp only [crossNumerator, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_ofNat]
    rw [rationalNumerator_value_congr hx k, rationalNumerator_value_congr hy k,
      natEq (rationalDenominator_congr hx k), natEq (rationalDenominator_congr hy k)]
  exact le_congr (congrMul (.eqRefl _) (Foundations.GapDecision.zabs_congr numerator))
    (congrMul (.eqRefl _) (congrMul (rationalDenominator_congr hx k) (rationalDenominator_congr hy k))) h

theorem pointRadius_congr {x x' y y' d A B : PTm n}
    (hx : Γ ⊢[PRAAx] x ≐ x') (hy : Γ ⊢[PRAAx] y ≐ y')
    (h : Γ ⊢[PRAAx] pointRadius x y d A B) : Γ ⊢[PRAAx] pointRadius x' y' d A B := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift d) :: Γ.map Fm.shift
  have hxs : Δ ⊢[PRAAx] Syn.shift x ≐ Syn.shift x' := by
    simpa only [Fm.shift, Fm.subst_eq, Syn.shift] using hx.shift.wk
  have hys : Δ ⊢[PRAAx] Syn.shift y ≐ Syn.shift y' := by
    simpa only [Fm.shift, Fm.subst_eq, Syn.shift] using hy.shift.wk
  have hs : Δ ⊢[PRAAx] pointRadius (Syn.shift x) (Syn.shift y) (Syn.shift d) (Syn.shift A) (Syn.shift B) := by
    simpa only [Fm.shift, subst_pointRadius, Syn.shift] using h.shift.wk
  exact coordinateRadius_congr hxs hys (pointRadius_at _ _ _ _ _ _ hs Prf.hyp0)

#print axioms pointRadius_congr

/-- Insert a witness in the first target block. -/
theorem append_hit_left (S S' T T' d A B i : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (length S))
    (h : Γ ⊢[PRAAx] originalHit .left .right S T d A B i) :
    Γ ⊢[PRAAx] originalHit .left .right (append S S') (append T T') d A B i := by
  refine .exE h ?_
  let E : Fm PTm (n+1) := lt (var 0) (length (Syn.shift T)) ⋏
    pointRadius (entry (Syn.shift S) (Syn.shift i)) (entry (Syn.shift T) (var 0))
      (Syn.shift d) (Syn.shift A) (Syn.shift B)
  have rangeI : E :: Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift i) (length (Syn.shift S)) := by
    simpa only [Fm.shift, subst_lt, Foundations.SequenceComposition.subst_length, Syn.shift] using hi.shift.wk
  have rangeJ : E :: Γ.map Fm.shift ⊢[PRAAx] lt (var 0) (length (Syn.shift T)) :=
    .andE₁ (Prf.hyp0 : E :: Γ.map Fm.shift ⊢[PRAAx] E)
  have radius := pointRadius_congr (append_left (b := Syn.shift S') rangeI).eqSymm
    (append_left (b := Syn.shift T') rangeJ).eqSymm (Prf.andE₂ Prf.hyp0)
  have result := originalHit_intro .left .right (append (Syn.shift S) (Syn.shift S'))
    (append (Syn.shift T) (Syn.shift T')) (Syn.shift d) (Syn.shift A) (Syn.shift B) (Syn.shift i) (var 0)
    (left_range _ _ _ rangeJ) radius
  simpa only [E, source, Fm.shift, subst_originalHit, Foundations.SequenceComposition.subst_append, Syn.shift] using result

#print axioms append_hit_left

/-- Insert a witness in the second block, using the actual prefix length. -/
theorem append_hit_right (S S' T T' d A B i : PTm n)
    (hi : Γ ⊢[PRAAx] le (length S) i)
    (hr : Γ ⊢[PRAAx] lt i (length S + length S'))
    (h : Γ ⊢[PRAAx] originalHit .left .right S' T' d A B (monus i (length S))) :
    Γ ⊢[PRAAx] originalHit .left .right (append S S') (append T T') d A B i := by
  refine .exE h ?_
  let E : Fm PTm (n+1) := lt (var 0) (length (Syn.shift T')) ⋏
    pointRadius (entry (Syn.shift S') (monus (Syn.shift i) (length (Syn.shift S))))
      (entry (Syn.shift T') (var 0)) (Syn.shift d) (Syn.shift A) (Syn.shift B)
  have rangeI : E :: Γ.map Fm.shift ⊢[PRAAx] le (length (Syn.shift S)) (Syn.shift i) := by
    simpa only [Fm.shift, subst_le, Foundations.SequenceComposition.subst_length, Syn.shift] using hi.shift.wk
  have rangeR : E :: Γ.map Fm.shift ⊢[PRAAx]
      lt (Syn.shift i) (length (Syn.shift S) + length (Syn.shift S')) := by
    simpa only [Fm.shift, subst_lt, Foundations.SequenceComposition.subst_length, PTm.subst_add, Syn.shift] using hr.shift.wk
  have rangeJ : E :: Γ.map Fm.shift ⊢[PRAAx] lt (var 0) (length (Syn.shift T')) :=
    .andE₁ (Prf.hyp0 : E :: Γ.map Fm.shift ⊢[PRAAx] E)
  have radius := pointRadius_congr (append_right_at (b := Syn.shift S') rangeI rangeR).eqSymm
    (append_right (a := Syn.shift T) rangeJ).eqSymm (Prf.andE₂ Prf.hyp0)
  have result := originalHit_intro .left .right (append (Syn.shift S) (Syn.shift S'))
    (append (Syn.shift T) (Syn.shift T')) (Syn.shift d) (Syn.shift A) (Syn.shift B) (Syn.shift i)
    (length (Syn.shift T) + var 0) (right_range _ _ _ rangeJ) radius
  simpa only [E, source, Fm.shift, subst_originalHit, Foundations.SequenceComposition.subst_append,
    Foundations.SequenceComposition.subst_length, PTm.subst_monus, Syn.shift] using result

#print axioms append_hit_right

theorem originalCover_append (S S' T T' d A B : PTm n)
    (h : Γ ⊢[PRAAx] originalCover .left .right S T d A B)
    (h' : Γ ⊢[PRAAx] originalCover .left .right S' T' d A B) :
    Γ ⊢[PRAAx] originalCover .left .right (append S S') (append T T') d A B := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (Syn.shift (append S S'))) :: Γ.map Fm.shift
  have first : Δ ⊢[PRAAx] originalCover .left .right (Syn.shift S) (Syn.shift T)
      (Syn.shift d) (Syn.shift A) (Syn.shift B) := by
    simpa only [Fm.shift, subst_originalCover, Syn.shift] using h.shift.wk
  have second : Δ ⊢[PRAAx] originalCover .left .right (Syn.shift S') (Syn.shift T')
      (Syn.shift d) (Syn.shift A) (Syn.shift B) := by
    simpa only [Fm.shift, subst_originalCover, Syn.shift] using h'.shift.wk
  have rangeI : Δ ⊢[PRAAx] lt (var 0) (length (append (Syn.shift S) (Syn.shift S'))) := by
    simpa only [Δ, Syn.shift, Foundations.SequenceComposition.subst_append] using
      (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (length (Syn.shift (append S S'))))
  have total := lt_congr (.eqRefl _) (append_length _ _) rangeI
  have result : Δ ⊢[PRAAx] originalHit .left .right (append (Syn.shift S) (Syn.shift S'))
      (append (Syn.shift T) (Syn.shift T')) (Syn.shift d) (Syn.shift A) (Syn.shift B) (var 0) := by
    refine .orE (lt_or_le (var 0) (length (Syn.shift S))) ?_ ?_
    · exact append_hit_left _ _ _ _ _ _ _ _ Prf.hyp0
        (originalCover_at .left .right _ _ _ _ _ _ first.wk Prf.hyp0)
    · exact append_hit_right _ _ _ _ _ _ _ _ Prf.hyp0 total.wk
        (originalCover_at .left .right _ _ _ _ _ _ second.wk (suffix_range Prf.hyp0 total.wk))
  simpa only [Δ, source, Syn.shift, Foundations.SequenceComposition.subst_append] using result

#print axioms originalCover_append

private theorem reverse_cover_forward (S T d A B : PTm n)
    (h : Γ ⊢[PRAAx] originalCover .right .left S T d A B) :
    Γ ⊢[PRAAx] originalCover .left .right T S d A B := h

private theorem reverse_cover_backward (S T d A B : PTm n)
    (h : Γ ⊢[PRAAx] originalCover .left .right T S d A B) :
    Γ ⊢[PRAAx] originalCover .right .left S T d A B := h

theorem originalClose_append (S S' T T' d A B : PTm n)
    (h : Γ ⊢[PRAAx] originalClose S T d A B)
    (h' : Γ ⊢[PRAAx] originalClose S' T' d A B) :
    Γ ⊢[PRAAx] originalClose (append S S') (append T T') d A B := by
  have first : Γ ⊢[PRAAx] originalCover .left .right S T d A B := .andE₁ h
  have first' : Γ ⊢[PRAAx] originalCover .left .right S' T' d A B := .andE₁ h'
  have back := reverse_cover_forward S T d A B (Prf.andE₂ h)
  have back' := reverse_cover_forward S' T' d A B (Prf.andE₂ h')
  have forward := originalCover_append S S' T T' d A B first first'
  have backward := reverse_cover_backward (append S S') (append T T') d A B
    (originalCover_append T T' S S' d A B back back')
  exact .andI forward backward

#print axioms originalClose_append

/-- Numerator of the exact maximum of two independent nonnegative rationals. -/
def maximumNumerator (A B C D : PTm n) : PTm n := maximum (A*D) (C*B)
def maximumDenominator (_A B _C D : PTm n) : PTm n := B*D
def maximumCode (A B C D : PTm n) : PTm n := pairT (maximumNumerator A B C D) (maximumDenominator A B C D)
def maximumF : PR 4 := PTm.toPR (maximumCode (var 0) (var 1) (var 2) (var 3))

@[simp] theorem subst_maximumNumerator {m : ℕ} (σ : Fin n → PTm m) (A B C D : PTm n) :
    Syn.subst σ (maximumNumerator A B C D) = maximumNumerator (Syn.subst σ A) (Syn.subst σ B)
      (Syn.subst σ C) (Syn.subst σ D) := by simp [maximumNumerator]
@[simp] theorem subst_maximumDenominator {m : ℕ} (σ : Fin n → PTm m) (A B C D : PTm n) :
    Syn.subst σ (maximumDenominator A B C D) = maximumDenominator (Syn.subst σ A) (Syn.subst σ B)
      (Syn.subst σ C) (Syn.subst σ D) := by simp [maximumDenominator]
@[simp] theorem subst_maximumCode {m : ℕ} (σ : Fin n → PTm m) (A B C D : PTm n) :
    Syn.subst σ (maximumCode A B C D) = maximumCode (Syn.subst σ A) (Syn.subst σ B)
      (Syn.subst σ C) (Syn.subst σ D) := by simp [maximumCode]

theorem maximum_program (A B C D : PTm n) : Γ ⊢[PRAAx]
    ConciseIPRA.PTm.app maximumF ![A,B,C,D] ≐ maximumCode A B C D := by
  simpa [maximumF] using toPR_eq (Γ := Γ) (maximumCode (var 0) (var 1) (var 2) (var 3) : PTm 4) ![A,B,C,D]

theorem maximum_positive (A B C D : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx] le one (maximumDenominator A B C D) :=
  le_congr (one_mul one) (.eqRefl _) (le_mul_mono hB hD)

/-- The exported rational maximum has the exact universal upper-bound property. -/
theorem maximum_least (A B C D U V : PTm n)
    (h1 : Γ ⊢[PRAAx] le (V*(A*D)) (U*(B*D)))
    (h2 : Γ ⊢[PRAAx] le (V*(C*B)) (U*(B*D))) :
    Γ ⊢[PRAAx] le (V*maximumNumerator A B C D) (U*maximumDenominator A B C D) := by
  refine .orE (le_total (A*D) (C*B)) ?_ ?_
  · have eqMax : (le (A*D) (C*B) :: Γ) ⊢[PRAAx] maximum (A*D) (C*B) ≐ C*B :=
      le_antisymm (maximum_le Prf.hyp0 (le_refl _)) (maximum_right _ _)
    exact le_congr (congrMul (.eqRefl _) eqMax).eqSymm (.eqRefl _) h2.wk
  · have eqMax : (le (C*B) (A*D) :: Γ) ⊢[PRAAx] maximum (A*D) (C*B) ≐ A*D :=
      le_antisymm (maximum_le (le_refl _) Prf.hyp0) (maximum_left _ _)
    exact le_congr (congrMul (.eqRefl _) eqMax).eqSymm (.eqRefl _) h1.wk

#print axioms maximum_least

theorem maximum_left_bound (A B C D : PTm n) :
    Γ ⊢[PRAAx] le (maximumDenominator A B C D * A) (maximumNumerator A B C D * B) :=
  le_congr (by simp only [maximumDenominator]; ipra_ring) (.eqRefl _)
    (mul_le_mul_right B (maximum_left (A*D) (C*B)))

theorem maximum_right_bound (A B C D : PTm n) :
    Γ ⊢[PRAAx] le (maximumDenominator A B C D * C) (maximumNumerator A B C D * D) :=
  le_congr (by simp only [maximumDenominator]; ipra_ring) (.eqRefl _)
    (mul_le_mul_right D (maximum_right (A*D) (C*B)))

theorem maximum_upper_bound (A B C D U V : PTm n)
    (h1 : Γ ⊢[PRAAx] le (V*A) (U*B)) (h2 : Γ ⊢[PRAAx] le (V*C) (U*D)) :
    Γ ⊢[PRAAx] le (V*maximumNumerator A B C D) (U*maximumDenominator A B C D) :=
  maximum_least A B C D U V
    (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right D h1))
    (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right B h2))

theorem maximum_code_numerator (A B C D : PTm n) : Γ ⊢[PRAAx]
    fstT (ConciseIPRA.PTm.app maximumF ![A,B,C,D]) ≐ maximumNumerator A B C D :=
  (congrFst (maximum_program A B C D)).eqTrans (fst_pair _ _)

theorem maximum_code_denominator (A B C D : PTm n) : Γ ⊢[PRAAx]
    sndT (ConciseIPRA.PTm.app maximumF ![A,B,C,D]) ≐ maximumDenominator A B C D :=
  (congrSnd (maximum_program A B C D)).eqTrans (snd_pair _ _)

def radiusNumerator (S S' T T' d : PTm n) : PTm n :=
  maximumNumerator (numerator S T d) (denominator S T d) (numerator S' T' d) (denominator S' T' d)
def radiusDenominator (S S' T T' d : PTm n) : PTm n :=
  maximumDenominator (numerator S T d) (denominator S T d) (numerator S' T' d) (denominator S' T' d)

@[simp] theorem subst_radiusNumerator {m : ℕ} (σ : Fin n → PTm m) (S S' T T' d : PTm n) :
    Syn.subst σ (radiusNumerator S S' T T' d) = radiusNumerator (Syn.subst σ S) (Syn.subst σ S')
      (Syn.subst σ T) (Syn.subst σ T') (Syn.subst σ d) := by simp [radiusNumerator]
@[simp] theorem subst_radiusDenominator {m : ℕ} (σ : Fin n → PTm m) (S S' T T' d : PTm n) :
    Syn.subst σ (radiusDenominator S S' T T' d) = radiusDenominator (Syn.subst σ S) (Syn.subst σ S')
      (Syn.subst σ T) (Syn.subst σ T') (Syn.subst σ d) := by simp [radiusDenominator]

theorem maximum_own_covers (S S' T T' d : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hS' : Γ ⊢[PRAAx] le one (length S'))
    (hT : Γ ⊢[PRAAx] le one (length T)) (hT' : Γ ⊢[PRAAx] le one (length T')) :
    Γ ⊢[PRAAx] originalClose S T d (radiusNumerator S S' T T' d) (radiusDenominator S S' T T' d) ⋏
      originalClose S' T' d (radiusNumerator S S' T T' d) (radiusDenominator S S' T T' d) := by
  refine .andI (original_close_of_bound _ _ _ _ _ hS hT ?_)
    (original_close_of_bound _ _ _ _ _ hS' hT' ?_)
  · exact le_congr (by simp only [radiusDenominator, maximumDenominator]; ipra_ring) (.eqRefl _)
      (mul_le_mul_right (denominator S T d) (maximum_left _ _))
  · exact le_congr (by simp only [radiusDenominator, maximumDenominator]; ipra_ring) (.eqRefl _)
      (mul_le_mul_right (denominator S' T' d) (maximum_right _ _))

#print axioms maximum_own_covers

/-- Original-coordinate covers at the exact maximum of the two actual H values. -/
theorem concatenated_cover (S S' T T' d : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hS' : Γ ⊢[PRAAx] le one (length S'))
    (hT : Γ ⊢[PRAAx] le one (length T)) (hT' : Γ ⊢[PRAAx] le one (length T')) :
    Γ ⊢[PRAAx] originalClose (append S S') (append T T') d
      (radiusNumerator S S' T T' d) (radiusDenominator S S' T T' d) := by
  have h := maximum_own_covers S S' T T' d hS hS' hT hT'
  exact originalClose_append S S' T T' d _ _ (Prf.andE₁ h) (Prf.andE₂ h)

#print axioms concatenated_cover

/-- Clause 2 with three independently computed rational scales. -/
theorem rational_concatenation (S S' T T' d : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hS' : Γ ⊢[PRAAx] le one (length S'))
    (hT : Γ ⊢[PRAAx] le one (length T)) (hT' : Γ ⊢[PRAAx] le one (length T')) :
    Γ ⊢[PRAAx] le
      (radiusDenominator S S' T T' d * numerator (append S S') (append T T') d)
      (radiusNumerator S S' T T' d * denominator (append S S') (append T T') d) :=
  bound_of_original_close _ _ _ _ _ (concatenated_cover S S' T T' d hS hS' hT hT')

theorem concatenation_checker (S S' T T' d : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hS' : Γ ⊢[PRAAx] le one (length S'))
    (hT : Γ ⊢[PRAAx] le one (length T)) (hT' : Γ ⊢[PRAAx] le one (length T')) :
    Γ ⊢[PRAAx] apply5 checkerF (append S S') (append T T') d
      (radiusNumerator S S' T T' d) (radiusDenominator S S' T T' d) ≐ one :=
  checker_complete _ _ _ _ _ (concatenated_cover S S' T T' d hS hS' hT hT')

theorem code_concatenation (S S' T T' d : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hS' : Γ ⊢[PRAAx] le one (length S'))
    (hT : Γ ⊢[PRAAx] le one (length T)) (hT' : Γ ⊢[PRAAx] le one (length T')) :
    Γ ⊢[PRAAx] le
      (sndT (ConciseIPRA.PTm.app maximumF ![numerator S T d, denominator S T d,
        numerator S' T' d, denominator S' T' d]) * fstT (ap3 codeF (append S S') (append T T') d))
      (fstT (ConciseIPRA.PTm.app maximumF ![numerator S T d, denominator S T d,
        numerator S' T' d, denominator S' T' d]) * sndT (ap3 codeF (append S S') (append T T') d)) :=
  le_congr (congrMul (maximum_code_denominator _ _ _ _).eqSymm (code_numerator _ _ _).eqSymm)
    (congrMul (maximum_code_numerator _ _ _ _).eqSymm (code_denominator _ _ _).eqSymm)
    (rational_concatenation S S' T T' d hS hS' hT hT')

theorem concatenation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (length (var 0)) ⟶ le one (length (var 1)) ⟶ le one (length (var 2)) ⟶ le one (length (var 3)) ⟶
      le (radiusDenominator (var 0) (var 1) (var 2) (var 3) (var 4) *
        numerator (append (var 0) (var 1)) (append (var 2) (var 3)) (var 4))
        (radiusNumerator (var 0) (var 1) (var 2) (var 3) (var 4) *
          denominator (append (var 0) (var 1)) (append (var 2) (var 3)) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (rational_concatenation _ _ _ _ _
    (Prf.hyp (by simp)) (Prf.hyp (by simp)) Prf.hyp1 Prf.hyp0)))))

theorem concatenation_checker_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (length (var 0)) ⟶ le one (length (var 1)) ⟶ le one (length (var 2)) ⟶ le one (length (var 3)) ⟶
      apply5 checkerF (append (var 0) (var 1)) (append (var 2) (var 3)) (var 4)
        (radiusNumerator (var 0) (var 1) (var 2) (var 3) (var 4))
        (radiusDenominator (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ one) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (concatenation_checker _ _ _ _ _
    (Prf.hyp (by simp)) (Prf.hyp (by simp)) Prf.hyp1 Prf.hyp0)))))

theorem maximum_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (ConciseIPRA.PTm.app maximumF ![var 0,var 1,var 2,var 3] ≐ maximumCode (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (maximum_program _ _ _ _)

theorem concatenated_cover_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (length (var 0)) ⟶ le one (length (var 1)) ⟶ le one (length (var 2)) ⟶ le one (length (var 3)) ⟶
      originalClose (append (var 0) (var 1)) (append (var 2) (var 3)) (var 4)
        (radiusNumerator (var 0) (var 1) (var 2) (var 3) (var 4))
        (radiusDenominator (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (concatenated_cover _ _ _ _ _
    (Prf.hyp (by simp)) (Prf.hyp (by simp)) Prf.hyp1 Prf.hyp0)))))

theorem maximum_laws_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 1) ⟶ le one (var 3) ⟶
      le one (maximumDenominator (var 0) (var 1) (var 2) (var 3)) ⋏
      (le (maximumDenominator (var 0) (var 1) (var 2) (var 3) * var 0)
        (maximumNumerator (var 0) (var 1) (var 2) (var 3) * var 1) ⋏
      (le (maximumDenominator (var 0) (var 1) (var 2) (var 3) * var 2)
        (maximumNumerator (var 0) (var 1) (var 2) (var 3) * var 3) ⋏
      (le (var 5*var 0) (var 4*var 1) ⟶ le (var 5*var 2) (var 4*var 3) ⟶
        le (var 5*maximumNumerator (var 0) (var 1) (var 2) (var 3))
          (var 4*maximumDenominator (var 0) (var 1) (var 2) (var 3)))))) :=
  closeUniv 6 (.impI (.impI (.andI (maximum_positive _ _ _ _ Prf.hyp1 Prf.hyp0)
    (.andI (maximum_left_bound _ _ _ _) (.andI (maximum_right_bound _ _ _ _)
      (.impI (.impI (maximum_upper_bound _ _ _ _ _ _ Prf.hyp1 Prf.hyp0))))))))

#print axioms maximum_program
#print axioms maximum_positive
#print axioms maximum_left_bound
#print axioms maximum_right_bound
#print axioms maximum_upper_bound
#print axioms maximum_code_numerator
#print axioms maximum_code_denominator
#print axioms rational_concatenation
#print axioms concatenation_checker
#print axioms code_concatenation
#print axioms concatenation_closed
#print axioms concatenation_checker_closed
#print axioms maximum_program_closed
#print axioms concatenated_cover_closed
#print axioms maximum_laws_closed

end LeanProofs.IPRA.Analysis.RationalHausdorffConcat
