import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.Reindexing.GaussianRationalSumSegments
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianPowers.GaussianRationalPowerExpansion
import IPRADerivations.Analysis.Geometry.GeometricBounds.GaussianGeometricSumBound

/-!
# The actual constant, dominant term and off-dominant decomposition

The actual ascending power list splits into four consecutive segments:
the constant, the positive degrees below k, degree k, and the degrees
above k. Bounded individual entry-code equalities identify the two middle
sum programs with the already constructed off-dominant lists. Gaussian
associativity and commutativity regroup the normalized sums.

The constant coefficient can be a raw noncanonical code. Only a contextual
unit law removes its normalized product with one, inside the actual sum;
no equality of a raw coefficient with its canonical recoding is asserted.
All polynomial codes, degrees, displacements and indices are internal.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalDominantDecomposition

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate qadd qmul)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone qadd_congr qmul_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalSumSegments (segment partialSum sum entriesEqual)
open LeanProofs.IPRA.Analysis.GaussianRationalPowerExpansion (terms)
open LeanProofs.IPRA.Analysis.GaussianOffDominantTerms (term lowerList upperList)
open LeanProofs.IPRA.Analysis.GaussianBalancedRadiusSyntax (coefficient)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem one_add_pred (k : PTm n) (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx] one+pred k ≐ k :=
  (by ipra_ring : Γ ⊢[PRAAx] one+pred k ≐ succ (pred k)).eqTrans
    (RationalIntegerNormalization.positive_form hk).eqSymm

theorem total_index (N k : PTm n) (hkN : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx]
    k+one+monus N k ≐ succ N :=
  (by ipra_ring : Γ ⊢[PRAAx] k+one+monus N k ≐ succ (k+monus N k)).eqTrans
    (congrSucc (eq_add_of_le hkN).eqSymm)

theorem lower_degree_bound (N k s : PTm n) (hk : Γ ⊢[PRAAx] le one k)
    (hkN : Γ ⊢[PRAAx] le k N) (hs : Γ ⊢[PRAAx] lt s (pred k)) : Γ ⊢[PRAAx] le (succ s) N :=
  le_trans hs (le_trans
    (le_congr (.eqRefl _) (RationalIntegerNormalization.positive_form hk).eqSymm (le_succ_self (pred k))) hkN)

theorem lower_entries (C N delta k : PTm n) (hk : Γ ⊢[PRAAx] le one k)
    (hkN : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx]
    entriesEqual (segment (terms C N delta) one (pred k)) (lowerList C N delta k) (pred k) := by
  simp only [entriesEqual,Syn.shift,GaussianRationalSumSegments.subst_segment,
    GaussianRationalPowerExpansion.subst_terms,GaussianOffDominantTerms.subst_lowerList,
    PTm.subst_pred,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]
  refine .allI (.impI ?_)
  have hk' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift k) := by
    simpa only [Fm.shift,subst_le,Syn.shift,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using hk.shift
  have hn' : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift k) (Syn.shift N) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using hkN.shift
  have degree := lower_degree_bound (Syn.shift N) (Syn.shift k) (var 0) hk'.wk hn'.wk Prf.hyp0
  exact (GaussianRationalSumSegments.segment_lookup _ one _ (var 0) Prf.hyp0).eqTrans
    ((entry_congr (.eqRefl _) (by ipra_ring)).eqTrans
      ((GaussianRationalPowerExpansion.terms_lookup (Syn.shift C) (Syn.shift N) (Syn.shift delta) (succ (var 0)) degree).eqTrans
        (GaussianOffDominantTerms.lower_lookup (Syn.shift C) (Syn.shift N) (Syn.shift delta) (Syn.shift k) (var 0) Prf.hyp0).eqSymm))

theorem upper_entries (C N delta k : PTm n) (hkN : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx]
    entriesEqual (segment (terms C N delta) (k+one) (monus N k)) (upperList C N delta k) (monus N k) := by
  simp only [entriesEqual,Syn.shift,GaussianRationalSumSegments.subst_segment,
    GaussianRationalPowerExpansion.subst_terms,GaussianOffDominantTerms.subst_upperList,
    PTm.subst_monus,PTm.subst_add,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]
  refine .allI (.impI ?_)
  have hn' : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift k) (Syn.shift N) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using hkN.shift
  have degree := GaussianOffDominantTerms.upper_degree_bound (Syn.shift N) (Syn.shift k) (var 0) hn'.wk Prf.hyp0
  exact (GaussianRationalSumSegments.segment_lookup _ (Syn.shift k+one) _ (var 0) Prf.hyp0).eqTrans
    ((entry_congr (.eqRefl _) (by ipra_ring)).eqTrans
      ((GaussianRationalPowerExpansion.terms_lookup (Syn.shift C) (Syn.shift N) (Syn.shift delta) (Syn.shift k+succ (var 0)) degree).eqTrans
        (GaussianOffDominantTerms.upper_lookup (Syn.shift C) (Syn.shift N) (Syn.shift delta) (Syn.shift k) (var 0) Prf.hyp0).eqSymm))

theorem lower_sum_binding (C N delta k : PTm n) (hk : Γ ⊢[PRAAx] le one k)
    (hkN : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx]
    sum (segment (terms C N delta) one (pred k)) ≐ sum (lowerList C N delta k) :=
  (GaussianRationalSumSegments.sum_segment _ _ _).eqTrans
    ((GaussianRationalSumSegments.prefix_entries_congr _ _ _ _ (lower_entries C N delta k hk hkN) (le_refl _)).eqTrans
      (GaussianRationalSumSegments.prefix_congr (.eqRefl _) (GaussianOffDominantTerms.lower_length C N delta k)).eqSymm)

theorem upper_sum_binding (C N delta k : PTm n) (hkN : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx]
    sum (segment (terms C N delta) (k+one) (monus N k)) ≐ sum (upperList C N delta k) :=
  (GaussianRationalSumSegments.sum_segment _ _ _).eqTrans
    ((GaussianRationalSumSegments.prefix_entries_congr _ _ _ _ (upper_entries C N delta k hkN) (le_refl _)).eqTrans
      (GaussianRationalSumSegments.prefix_congr (.eqRefl _) (GaussianOffDominantTerms.upper_length C N delta k)).eqSymm)

theorem first_term (C N delta : PTm n) : Γ ⊢[PRAAx] partialSum (terms C N delta) one ≐ term C N delta zero :=
  GaussianRationalSumSegments.prefix_singleton _ _ (GaussianOffDominantTerms.term_canonical C N delta zero)
    (GaussianRationalPowerExpansion.terms_lookup C N delta zero (zero_le N))

theorem dominant_singleton (C N delta k : PTm n) (hkN : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx]
    sum (segment (terms C N delta) k one) ≐ term C N delta k :=
  GaussianRationalSumSegments.singleton_sum _ _ _ (GaussianOffDominantTerms.term_canonical C N delta k)
    (GaussianRationalPowerExpansion.terms_lookup C N delta k hkN)

/-- The raw constant is removed from its product with one only inside
the normalized sum, rather than identified with its canonical recoding. -/
theorem constant_context (C N delta q : PTm n) : Γ ⊢[PRAAx]
    qadd (term C N delta zero) q ≐ qadd (coefficient C N zero) q :=
  (qadd_congr (qmul_congr (.eqRefl _) (GaussianRationalReciprocal.power_zero delta)) (.eqRefl _)).eqTrans
    (GaussianRationalSumAlgebra.contextual_unit _ _)

theorem power_sum_split (C N delta k : PTm n) (hk : Γ ⊢[PRAAx] le one k)
    (hkN : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx]
    sum (terms C N delta) ≐ qadd (qadd (coefficient C N zero) (term C N delta k))
      (GaussianGeometricSumBound.otherSum (lowerList C N delta k) (upperList C N delta k)) := by
  have lowerPrefix : Γ ⊢[PRAAx] partialSum (terms C N delta) k ≐
      qadd (term C N delta zero) (sum (lowerList C N delta k)) :=
    (GaussianRationalSumSegments.prefix_congr (.eqRefl _) (one_add_pred k hk).eqSymm).eqTrans
      ((GaussianRationalSumSegments.sum_split _ one (pred k)).eqTrans
        (qadd_congr (first_term C N delta) (lower_sum_binding C N delta k hk hkN)))
  have central : Γ ⊢[PRAAx] partialSum (terms C N delta) (k+one) ≐
      qadd (qadd (term C N delta zero) (sum (lowerList C N delta k))) (term C N delta k) :=
    (GaussianRationalSumSegments.sum_split _ k one).eqTrans
      (qadd_congr lowerPrefix (dominant_singleton C N delta k hkN))
  exact (GaussianRationalSumSegments.prefix_congr (.eqRefl _) (GaussianRationalPowerExpansion.terms_length C N delta)).eqTrans
    ((GaussianRationalSumSegments.prefix_congr (.eqRefl _) (total_index N k hkN).eqSymm).eqTrans
      ((GaussianRationalSumSegments.sum_split _ (k+one) (monus N k)).eqTrans
        ((qadd_congr central (upper_sum_binding C N delta k hkN)).eqTrans
          ((GaussianRationalSumAlgebra.shuffle_four _ _ _ _).eqTrans
            (qadd_congr (constant_context C N delta (term C N delta k)) (.eqRefl _))))))

/-- Full actual decomposition from the original list shape and the
internal selected-degree guards alone. No expansion or split law is an input. -/
theorem dominant_decomposition (C N delta k : PTm n)
    (hLen : Γ ⊢[PRAAx] length C ≐ succ N) (hk : Γ ⊢[PRAAx] le one k) (hkN : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx]
    evaluate C delta ≐ qadd (qadd (coefficient C N zero) (term C N delta k))
      (GaussianGeometricSumBound.otherSum (lowerList C N delta k) (upperList C N delta k)) :=
  (GaussianRationalPowerExpansion.power_expansion C N delta hLen).eqTrans (power_sum_split C N delta k hk hkN)

def output (C N delta k : PTm n) : PTm n := pairT (evaluate C delta) (pairT (coefficient C N zero)
  (pairT (term C N delta k) (GaussianGeometricSumBound.otherSum (lowerList C N delta k) (upperList C N delta k))))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (C N delta k : PTm n) : PTm n := app outputF ![C,N,delta,k]

ipra_subst output
ipra_subst run

theorem program_at (C N delta k : PTm n) : Γ ⊢[PRAAx] run C N delta k ≐ output C N delta k := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![C,N,delta,k]

theorem returned_evaluation (C N delta k : PTm n) : Γ ⊢[PRAAx] fstT (run C N delta k) ≐ evaluate C delta :=
  (program_at C N delta k).fstE
theorem returned_constant (C N delta k : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run C N delta k)) ≐ coefficient C N zero :=
  (program_at C N delta k).sndE.fstE
theorem returned_dominant (C N delta k : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run C N delta k))) ≐ term C N delta k :=
  (program_at C N delta k).sndE.sndE.fstE
theorem returned_other (C N delta k : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run C N delta k))) ≐
    GaussianGeometricSumBound.otherSum (lowerList C N delta k) (upperList C N delta k) :=
  (program_at C N delta k).sndE.sndE.sndE

theorem returned_decomposition (C N delta k : PTm n)
    (hLen : Γ ⊢[PRAAx] length C ≐ succ N) (hk : Γ ⊢[PRAAx] le one k) (hkN : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx]
    fstT (run C N delta k) ≐ qadd (qadd (fstT (sndT (run C N delta k)))
      (fstT (sndT (sndT (run C N delta k))))) (sndT (sndT (sndT (run C N delta k)))) :=
  (returned_evaluation C N delta k).eqTrans ((dominant_decomposition C N delta k hLen hk hkN).eqTrans
    (qadd_congr (qadd_congr (returned_constant C N delta k).eqSymm (returned_dominant C N delta k).eqSymm)
      (returned_other C N delta k).eqSymm))

theorem actual_dominant_decomposition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶ le one (var 3) ⟶ le (var 3) (var 1) ⟶
      evaluate (var 0) (var 2) ≐ qadd (qadd (coefficient (var 0) (var 1) zero) (term (var 0) (var 1) (var 2) (var 3)))
        (GaussianGeometricSumBound.otherSum (lowerList (var 0) (var 1) (var 2) (var 3)) (upperList (var 0) (var 1) (var 2) (var 3)))) :=
  closeUniv 4 (.impI (.impI (.impI (dominant_decomposition _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem actual_decomposition_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (program_at _ _ _ _)

theorem actual_decomposition_fields_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((fstT (run (var 0) (var 1) (var 2) (var 3)) ≐ evaluate (var 0) (var 2)) ⋏
      ((fstT (sndT (run (var 0) (var 1) (var 2) (var 3))) ≐ coefficient (var 0) (var 1) zero) ⋏
        ((fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3)))) ≐ term (var 0) (var 1) (var 2) (var 3)) ⋏
          sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3)))) ≐
            GaussianGeometricSumBound.otherSum (lowerList (var 0) (var 1) (var 2) (var 3)) (upperList (var 0) (var 1) (var 2) (var 3))))) :=
  closeUniv 4 (.andI (returned_evaluation _ _ _ _) (.andI (returned_constant _ _ _ _)
    (.andI (returned_dominant _ _ _ _) (returned_other _ _ _ _))))

theorem returned_dominant_decomposition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶ le one (var 3) ⟶ le (var 3) (var 1) ⟶
      fstT (run (var 0) (var 1) (var 2) (var 3)) ≐
        qadd (qadd (fstT (sndT (run (var 0) (var 1) (var 2) (var 3))))
          (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3))))))
          (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3)))))) :=
  closeUniv 4 (.impI (.impI (.impI (returned_decomposition _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianRationalDominantDecomposition
