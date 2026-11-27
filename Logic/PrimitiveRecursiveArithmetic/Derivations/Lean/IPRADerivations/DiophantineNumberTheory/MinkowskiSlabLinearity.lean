import IPRADerivations.DiophantineNumberTheory.MinkowskiSlabInterval
import IPRADerivations.DiophantineNumberTheory.MinkowskiWellFormed
import IPRADerivations.Analysis.RationalArithmetic.RationalAlgebra
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.RationalIdentities.RationalSumLinearity
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.RationalIdentities.RationalSumAdditivity
import IPRADerivations.Core.Header

/-!
# Actual slab bodies are symmetric and midpoint closed

Actual vector negation and midpoint transport through the runtime rational
dot program as literal canonical scalar code equalities. Finite-sum
homogeneity and additivity are applied to actual term programs. From the
original row inequalities we derive symmetry and midpoint closure of every
facet, including their canonical output vector guards.

Rows are still supplied in lattice coordinates. Physical basis transport,
the doubled-coordinate Inside checker and specialized extraction remain
separate; no geometric closure or output membership is a premise here.
-/

set_option maxRecDepth 8192

namespace LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiSlabLinearity

open_ipra exports
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open LeanProofs.IPRA.Analysis.RationalArithmetic (multiply negative recode recode_equal)
open LeanProofs.IPRA.Analysis.RationalAlgebra
open LeanProofs.IPRA.Analysis.RationalFiniteSum (term termwiseEq sum_ext)
open LeanProofs.IPRA.Analysis.RationalSumLinearity (scaledBody scaledSum scaled_term sum_homogeneous)
open LeanProofs.IPRA.Analysis.RationalSumAdditivity (addedBody addedSum added_term sum_additive)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalEq rationalLE rationalLE_congr)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiCenterVectors
  (oppositeVector midpointVector opposite_lookup midpoint_lookup subst_oppositeVector subst_midpointVector)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiCenters (midpoint)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiSlabInterval
  (dot productBody product_at rowMember facetsMember subst_dot subst_rowMember subst_facetsMember)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiWellFormed (vectorGuard)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem value_equal_of_code {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) :
    Γ ⊢[PRAAx] rationalEq a b := Analysis.RationalArgmin.rationalEq_congr (.eqRefl _) h (.eqRefl _)

theorem dot_opposite (N c q : PTm n) : Γ ⊢[PRAAx]
    dot N c (oppositeVector N q) ≐ negative (dot N c q) := by
  have terms : Γ ⊢[PRAAx] termwiseEq productBody (scaledBody productBody) N
      (pairT c (oppositeVector N q)) (pairT minusOne (pairT c q)) := by
    refine .allI (.impI ?_)
    have left := (product_at (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift)
      (Syn.shift c) (oppositeVector (Syn.shift N) (Syn.shift q)) (var 0)).eqTrans
      ((multiply_congr (.eqRefl _) (opposite_lookup _ _ _ Prf.hyp0)).eqTrans
        ((multiply_negative _ _).eqTrans (negative_minus_multiply _)))
    have right := (scaled_term (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift)
      productBody (var 0) minusOne (pairT (Syn.shift c) (Syn.shift q))).eqTrans
      (multiply_congr (.eqRefl _) (product_at _ _ _))
    simpa only [Syn.shift,subst_pairT,subst_oppositeVector,subst_minusOne] using
      value_equal_of_code (left.eqTrans right.eqSymm)
  exact (sum_ext _ _ _ _ _ terms).eqTrans
    ((sum_homogeneous productBody N minusOne (pairT c q)).eqTrans
      (negative_minus_multiply (dot N c q)).eqSymm)

theorem dot_midpoint (N c q r : PTm n) : Γ ⊢[PRAAx]
    dot N c (midpointVector N q r) ≐ midpoint (dot N c q) (dot N c r) := by
  have terms : Γ ⊢[PRAAx] termwiseEq productBody
      (scaledBody (addedBody productBody productBody)) N (pairT c (midpointVector N q r))
        (pairT Analysis.RationalAlgebra.half (pairT (pairT c q) (pairT c r))) := by
    refine .allI (.impI ?_)
    have left := (product_at (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift)
      (Syn.shift c) (midpointVector (Syn.shift N) (Syn.shift q) (Syn.shift r)) (var 0)).eqTrans
      ((multiply_congr (.eqRefl _) (midpoint_lookup _ _ _ _ Prf.hyp0)).eqTrans
        ((multiply_midpoint _ _ _).eqTrans (midpoint_half_add _ _)))
    have right := (scaled_term (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift)
      (addedBody productBody productBody) (var 0) Analysis.RationalAlgebra.half
        (pairT (pairT (Syn.shift c) (Syn.shift q)) (pairT (Syn.shift c) (Syn.shift r)))).eqTrans
      ((multiply_congr (.eqRefl _) (added_term productBody productBody (var 0)
        (pairT (Syn.shift c) (Syn.shift q)) (pairT (Syn.shift c) (Syn.shift r)))).eqTrans
          (multiply_congr (.eqRefl _) (add_congr (product_at _ _ _) (product_at _ _ _))))
    simpa only [Syn.shift,subst_pairT,subst_midpointVector,subst_half] using
      value_equal_of_code (left.eqTrans right.eqSymm)
  exact (sum_ext _ _ _ _ _ terms).eqTrans
    ((sum_homogeneous (addedBody productBody productBody) N Analysis.RationalAlgebra.half (pairT (pairT c q) (pairT c r))).eqTrans
      ((multiply_congr (.eqRefl _) (sum_additive productBody productBody N (pairT c q) (pairT c r))).eqTrans
        (midpoint_half_add (dot N c q) (dot N c r)).eqSymm))

theorem row_opposite (N c b q : PTm n) (h : Γ ⊢[PRAAx] rowMember N c b q) :
    Γ ⊢[PRAAx] rowMember N c b (oppositeVector N q) := by
  have e := dot_opposite (Γ := Γ) N c q
  have lower := negative_antitone _ _ (Prf.andE₂ h)
  have upper := negative_antitone _ _ (Prf.andE₁ h)
  have double := Analysis.RationalArgmin.transitive
    (rationalLE_congr (.eqRefl _) (negative_involution b) upper)
    (Analysis.RationalArgmin.eq_le (recode_equal b))
  exact .andI (rationalLE_congr (.eqRefl _) e.eqSymm lower)
    (rationalLE_congr e.eqSymm (.eqRefl _) double)

theorem row_midpoint (N c b q r : PTm n) (hq : Γ ⊢[PRAAx] rowMember N c b q)
    (hr : Γ ⊢[PRAAx] rowMember N c b r) : Γ ⊢[PRAAx] rowMember N c b (midpointVector N q r) := by
  have e := dot_midpoint (Γ := Γ) N c q r
  have lo := midpoint_monotone _ _ _ _ (Prf.andE₁ hq) (Prf.andE₁ hr)
  have hi := midpoint_monotone _ _ _ _ (Prf.andE₂ hq) (Prf.andE₂ hr)
  have lower := Analysis.RationalArgmin.transitive (Analysis.RationalArgmin.eq_le (recode_equal (negative b)).eqSymm)
    (rationalLE_congr (midpoint_self (negative b)) (.eqRefl _) lo)
  have upper := Analysis.RationalArgmin.transitive (rationalLE_congr (.eqRefl _) (midpoint_self b) hi)
    (Analysis.RationalArgmin.eq_le (recode_equal b))
  exact .andI (rationalLE_congr (.eqRefl _) e.eqSymm lower)
    (rationalLE_congr e.eqSymm (.eqRefl _) upper)

theorem member_at (N F q j : PTm n) (h : Γ ⊢[PRAAx] facetsMember N F q)
    (hj : Γ ⊢[PRAAx] lt j (length F)) :
    Γ ⊢[PRAAx] rowMember N (fstT (entry F j)) (sndT (entry F j)) q := by
  have rule : Γ ⊢[PRAAx] lt j (length F) ⟶ rowMember N (fstT (entry F j)) (sndT (entry F j)) q := by
    simpa only [Fm.subst_imp,subst_lt,subst_length,subst_rowMember,subst_fstT,subst_sndT,
      subst_entry,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE j
  exact .impE rule hj

theorem facets_opposite (N F q : PTm n) (h : Γ ⊢[PRAAx] facetsMember N F q) :
    Γ ⊢[PRAAx] facetsMember N F (oppositeVector N q) := by
  refine .allI (.impI ?_)
  have original : Γ.map Fm.shift ⊢[PRAAx] facetsMember (Syn.shift N) (Syn.shift F) (Syn.shift q) := by
    simpa only [Fm.shift,subst_facetsMember,Syn.shift] using h.shift
  have row := row_opposite _ _ _ _ (member_at _ _ _ (var 0) original.wk Prf.hyp0)
  simpa only [Syn.shift,subst_oppositeVector] using row

theorem facets_midpoint (N F q r : PTm n) (hq : Γ ⊢[PRAAx] facetsMember N F q)
    (hr : Γ ⊢[PRAAx] facetsMember N F r) : Γ ⊢[PRAAx] facetsMember N F (midpointVector N q r) := by
  refine .allI (.impI ?_)
  have oq : Γ.map Fm.shift ⊢[PRAAx] facetsMember (Syn.shift N) (Syn.shift F) (Syn.shift q) := by
    simpa only [Fm.shift,subst_facetsMember,Syn.shift] using hq.shift
  have or : Γ.map Fm.shift ⊢[PRAAx] facetsMember (Syn.shift N) (Syn.shift F) (Syn.shift r) := by
    simpa only [Fm.shift,subst_facetsMember,Syn.shift] using hr.shift
  have row := row_midpoint _ _ _ _ _ (member_at _ _ _ (var 0) oq.wk Prf.hyp0)
    (member_at _ _ _ (var 0) or.wk Prf.hyp0)
  simpa only [Syn.shift,subst_midpointVector] using row

theorem dot_affine_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((dot (var 0) (var 1) (oppositeVector (var 0) (var 2)) ≐ negative (dot (var 0) (var 1) (var 2))) ⋏
      (dot (var 0) (var 1) (midpointVector (var 0) (var 2) (var 3)) ≐
        midpoint (dot (var 0) (var 1) (var 2)) (dot (var 0) (var 1) (var 3)))) :=
  closeUniv 4 (.andI (dot_opposite _ _ _) (dot_midpoint _ _ _ _))

theorem slab_symmetry_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (facetsMember (var 0) (var 1) (var 2) ⟶
      (vectorGuard (var 0) (oppositeVector (var 0) (var 2)) ⋏
        facetsMember (var 0) (var 1) (oppositeVector (var 0) (var 2)))) :=
  closeUniv 3 (.impI (.andI (MinkowskiWellFormed.opposite_vector_guard _ _) (facets_opposite _ _ _ Prf.hyp0)))

theorem slab_midpoint_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (facetsMember (var 0) (var 1) (var 2) ⟶ facetsMember (var 0) (var 1) (var 3) ⟶
      (vectorGuard (var 0) (midpointVector (var 0) (var 2) (var 3)) ⋏
        facetsMember (var 0) (var 1) (midpointVector (var 0) (var 2) (var 3)))) :=
  closeUniv 4 (.impI (.impI (.andI (MinkowskiWellFormed.midpoint_vector_guard _ _ _)
    (facets_midpoint _ _ _ _ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiSlabLinearity
