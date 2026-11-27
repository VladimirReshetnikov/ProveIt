import IPRADerivations.Analysis.Exponential.Polynomials.GaussianFiniteExponentialWeightedNorm
import IPRADerivations.Analysis.Polynomials.Horner.Perturbation.GaussianRationalVariableHornerBudget
import IPRADerivations.Analysis.Polynomials.Coefficients.NamedCoefficients.GaussianCoefficientNameBounds

/-!
# Actual Euclidean unit-disk Horner prefixes from the original finite norm

The existing native size(C,1,k) budget is identified with the actual
coefficient L1 prefix at its genuine computed common denominator. Native
size monotonicity then transports an original total coefficient-norm bound
to every actual Horner prefix on the Euclidean unit disk. No L1 bound on
the query is inferred from its Euclidean radius. The source specialization
uses the SAME original logarithm/exponential composition and its dilation.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalUnitDiskHornerNorm

open_ipra
open GaussianRationalVariableHornerBudget (denominator denominator_positive coefficient size)
open GaussianRationalHorner (horner scalar_congr scalar_add_same qmul)
open GaussianRationalMetric (bounded)
open GaussianCoefficientL1 (prefixNorm coefficientNorm)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open RationalArithmetic (represents)
open RationalArgmin (rationalLE)
open RationalSupMetric (numeratorOf)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def representationLaw (C k : PTm n) : Fm PTm n := le k (length C) ⟶
  represents (prefixNorm C k) (ZT.ofNat (size C one k)) (denominator C)
ipra_subst representationLaw

theorem representation_zero (C : PTm n) : Γ ⊢[PRAAx]
    represents (prefixNorm C zero) (ZT.ofNat (size C one zero)) (denominator C) := by
  have code : Γ ⊢[PRAAx] fraction zero (denominator C) ≐ RationalIntegerNormalization.integerCode (ZT.natLit 0) := by
    apply RationalIntegerNormalization.normalize_integer _ _ _ (denominator_positive C)
    ipra_lc
  have hz := scalar_congr code (.eqRefl _) (.eqRefl _)
    (fraction_represents zero (denominator C) (denominator_positive (Γ := Γ) C))
  refine scalar_congr (GaussianCoefficientL1.prefix_zero C).eqSymm ?_ (.eqRefl _) hz
  apply ZT.derive
  simp only [ZT.toZ_ofNat]
  exact (natEq (GaussianRationalVariableHornerBudget.size_zero (Γ := Γ) C one)).symm

theorem representation_step (C k : PTm n) (hk : Γ ⊢[PRAAx] lt k (length C))
    (ih : Γ ⊢[PRAAx] represents (prefixNorm C k) (ZT.ofNat (size C one k)) (denominator C)) :
    Γ ⊢[PRAAx] represents (prefixNorm C (succ k)) (ZT.ofNat (size C one (succ k))) (denominator C) := by
  have term := GaussianRationalL1.qL1_represents (Γ := Γ) _ _ _ (denominator_positive C)
    (GaussianRationalVariableHornerBudget.coefficient_represents C k hk)
  have sum := scalar_add_same _ _ _ _ _ (denominator_positive C) ih term
  refine scalar_congr (GaussianCoefficientL1.prefix_succ C k).eqSymm ?_ (.eqRefl _) sum
  apply ZT.derive
  simp only [ZT.toZ_add,ZT.toZ_ofNat]
  rw [natEq (GaussianRationalVariableHornerBudget.size_succ (Γ := Γ) C one k)]
  simp only [GaussianRationalVariableHornerBudget.coefficient]
  ipra_simps
  ring

/-- Genuine guarded QF induction compares two existing actual programs;
no replacement norm or Horner recursion is introduced. -/
theorem prefix_represents (C k : PTm n) (hk : Γ ⊢[PRAAx] le k (length C)) : Γ ⊢[PRAAx]
    represents (prefixNorm C k) (ZT.ofNat (size C one k)) (denominator C) := by
  have all : Γ ⊢[PRAAx] .all (representationLaw (Syn.shift C) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,trivial⟩) [subst_representationLaw]
    · exact .impI (representation_zero C).wk
    · exact .impI (representation_step _ _ Prf.hyp0
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)))
  have rule : Γ ⊢[PRAAx] representationLaw C k := by
    simpa only [subst_representationLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k
  exact .impE rule hk

theorem size_index_congr (C : PTm n) {j k : PTm n} (h : Γ ⊢[PRAAx] j ≐ k) : Γ ⊢[PRAAx]
    size C one j ≐ size C one k :=
  congrFst (congrAp2 GaussianRationalVariableHornerBudget.stateF h (.eqRefl _))
theorem size_step_monotone (C k : PTm n) : Γ ⊢[PRAAx] le (size C one k) (size C one (succ k)) :=
  le_congr (.eqRefl _) ((GaussianRationalVariableHornerBudget.size_succ C one k).eqTrans
    (congrAdd (one_mul _) (.eqRefl _))).eqSymm (le_add_right _ _)

def sizeOrder (C k r : PTm n) : Fm PTm n := le k r ⟶ le (size C one k) (size C one r)
ipra_subst sizeOrder

theorem size_order_zero (C k : PTm n) : Γ ⊢[PRAAx] sizeOrder C k zero := by
  refine .impI ?_
  have h : (le k zero :: Γ) ⊢[PRAAx] k ≐ zero := le_antisymm Prf.hyp0 (zero_le k)
  exact le_congr (size_index_congr C h).eqSymm (.eqRefl _) (le_refl _)
theorem size_order_step (C k r : PTm n) (hk : Γ ⊢[PRAAx] le k (succ r))
    (ih : Γ ⊢[PRAAx] sizeOrder C k r) : Γ ⊢[PRAAx] le (size C one k) (size C one (succ r)) := by
  refine .orE (lt_or_eq_of_le hk) ?_ ?_
  · have range : (lt k (succ r) :: Γ) ⊢[PRAAx] le k r := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
    exact le_trans (.impE ih.wk range) (size_step_monotone C r)
  · exact le_congr (size_index_congr C Prf.hyp0).eqSymm (.eqRefl _) (le_refl _)

theorem size_monotone (C k r : PTm n) (hk : Γ ⊢[PRAAx] le k r) : Γ ⊢[PRAAx]
    le (size C one k) (size C one r) := by
  have all : Γ ⊢[PRAAx] .all (sizeOrder (Syn.shift C) (Syn.shift k) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,le_QF _ _⟩) [subst_sizeOrder]
    · exact size_order_zero C k
    · exact .impI (size_order_step _ _ _ Prf.hyp0 Prf.hyp1)
  have rule : Γ ⊢[PRAAx] sizeOrder C k r := by
    simpa only [subst_sizeOrder,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE r
  exact .impE rule hk

/-- Original total coefficient L1 norm controls every actual Horner prefix
on the ORIGINAL Euclidean unit disk, with arbitrary raw coefficients/query. -/
theorem unit_prefix_bound (C z k A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hC : Γ ⊢[PRAAx] rationalLE (coefficientNorm C) (fraction A B))
    (hz : Γ ⊢[PRAAx] bounded z one one) (hk : Γ ⊢[PRAAx] le k (length C)) :
    Γ ⊢[PRAAx] bounded (horner C z k) A B := by
  have total := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (prefix_represents C (length C) (le_refl _)) (fraction_represents A B hB) hC
  have prefixBound : Γ ⊢[PRAAx] le (size C one k*B) (A*denominator C) :=
    le_trans (le_congr (mul_comm _ _) (.eqRefl _)
      (LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl B) (size_monotone C k (length C) hk))) total
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (denominator_positive C) hB prefixBound
    (GaussianRationalVariableHornerBudget.size_prefix C one z k hz hk)

def sourceBuffer (d K : PTm n) : PTm n := GaussianRationalPolynomialDilation.dilated
  (GaussianFiniteLogarithmPolynomial.composition d K) (K*d) GaussianFiniteLogarithmWeightedNorm.point
def query (w : PTm n) : PTm n := qmul (GaussianDominantPairAlgebra.radiusPoint (num 9) (num 5)) w
ipra_subst sourceBuffer
ipra_subst query

theorem source_length (d K : PTm n) : Γ ⊢[PRAAx] length (sourceBuffer d K) ≐ succ (K*d) :=
  GaussianRationalPolynomialDilation.dilated_length _ _ _

theorem query_bound (w : PTm n) (hw : Γ ⊢[PRAAx] bounded w one two) : Γ ⊢[PRAAx]
    bounded (query w) (num 9) (num 10) := by
  have h5 : Γ ⊢[PRAAx] le one (num 5 : PTm n) := le_of_eq_add (d := num 4) (by ipra_ring)
  exact GaussianRationalReciprocal.bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ h5 (le_succ_self one)
      (GaussianDominantPairAlgebra.radius_bounded (num 9) (num 5) h5) hw)

theorem query_unit (w : PTm n) (hw : Γ ⊢[PRAAx] bounded w one two) : Γ ⊢[PRAAx] bounded (query w) one one :=
  GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (le_of_eq_add (d := num 9) (by ipra_ring)) (le_refl _)
    (le_of_eq_add (d := one) (by ipra_ring)) (query_bound w hw)

/-- The exact original half disk maps into radius9/10. The source379 norm
bound for the SAME dilation controls every actual high Horner prefix. -/
theorem source_prefix_bound (d K w k : PTm n) (hw : Γ ⊢[PRAAx] bounded w one two)
    (hk : Γ ⊢[PRAAx] le k (succ (K*d))) : Γ ⊢[PRAAx]
    bounded (horner (sourceBuffer d K) (query w) k) (num 11) one :=
  unit_prefix_bound (sourceBuffer d K) (query w) k (num 11) one (le_refl _)
    (GaussianFiniteExponentialWeightedNorm.composition_bound_eleven d K) (query_unit w hw)
    (le_congr (.eqRefl _) (source_length d K).eqSymm hk)

/-! Actual source PR4 data retains original composition, its weighted
buffer/query/prefix and the genuine existing size/common-denominator pair. -/
def output (d K w k : PTm n) : PTm n := pairT (GaussianFiniteLogarithmPolynomial.composition d K)
  (pairT (sourceBuffer d K) (pairT (query w) (pairT (horner (sourceBuffer d K) (query w) k)
    (pairT (size (sourceBuffer d K) one k) (denominator (sourceBuffer d K))))))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (d K w k : PTm n) : PTm n := PTm.app outputF ![d,K,w,k]
ipra_subst output
ipra_subst run

theorem program_at (d K w k : PTm n) : Γ ⊢[PRAAx] run d K w k ≐ output d K w k := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![d,K,w,k]
theorem returned_composition (d K w k : PTm n) : Γ ⊢[PRAAx] fstT (run d K w k) ≐ GaussianFiniteLogarithmPolynomial.composition d K :=
  (program_at _ _ _ _).fstE
theorem returned_tail (d K w k : PTm n) : Γ ⊢[PRAAx] sndT (run d K w k) ≐
    pairT (sourceBuffer d K) (pairT (query w) (pairT (horner (sourceBuffer d K) (query w) k)
      (pairT (size (sourceBuffer d K) one k) (denominator (sourceBuffer d K))))) :=
  (program_at _ _ _ _).sndE
theorem returned_buffer (d K w k : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run d K w k)) ≐ sourceBuffer d K :=
  (returned_tail _ _ _ _).fstE
theorem returned_rest (d K w k : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run d K w k)) ≐
    pairT (query w) (pairT (horner (sourceBuffer d K) (query w) k)
      (pairT (size (sourceBuffer d K) one k) (denominator (sourceBuffer d K)))) :=
  (returned_tail _ _ _ _).sndE
theorem returned_query (d K w k : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run d K w k))) ≐ query w :=
  (returned_rest _ _ _ _).fstE
theorem returned_prefix_pair (d K w k : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run d K w k))) ≐
    pairT (horner (sourceBuffer d K) (query w) k)
      (pairT (size (sourceBuffer d K) one k) (denominator (sourceBuffer d K))) :=
  (returned_rest _ _ _ _).sndE
theorem returned_prefix (d K w k : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run d K w k)))) ≐
    horner (sourceBuffer d K) (query w) k :=
  (returned_prefix_pair _ _ _ _).fstE
theorem returned_clear_pair (d K w k : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (run d K w k)))) ≐
    pairT (size (sourceBuffer d K) one k) (denominator (sourceBuffer d K)) :=
  (returned_prefix_pair _ _ _ _).sndE
theorem returned_size (d K w k : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (sndT (run d K w k))))) ≐
    size (sourceBuffer d K) one k :=
  (returned_clear_pair _ _ _ _).fstE
theorem returned_denominator (d K w k : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (sndT (run d K w k))))) ≐
    denominator (sourceBuffer d K) :=
  (returned_clear_pair _ _ _ _).sndE
theorem returned_bound (d K w k : PTm n) (hw : Γ ⊢[PRAAx] bounded w one two)
    (hk : Γ ⊢[PRAAx] le k (succ (K*d))) : Γ ⊢[PRAAx]
    bounded (fstT (sndT (sndT (sndT (run d K w k))))) (num 11) one :=
  GaussianRationalReciprocal.bound_congr (returned_prefix d K w k).eqSymm (.eqRefl _) (.eqRefl _)
    (source_prefix_bound d K w k hw hk)
theorem returned_clear_bound (d K w k : PTm n) (hw : Γ ⊢[PRAAx] bounded w one two)
    (hk : Γ ⊢[PRAAx] le k (succ (K*d))) : Γ ⊢[PRAAx]
    bounded (fstT (sndT (sndT (sndT (run d K w k)))))
      (fstT (sndT (sndT (sndT (sndT (run d K w k)))))) (sndT (sndT (sndT (sndT (sndT (run d K w k)))))) :=
  GaussianRationalReciprocal.bound_congr (returned_prefix d K w k).eqSymm (returned_size d K w k).eqSymm
    (returned_denominator d K w k).eqSymm
    (GaussianRationalVariableHornerBudget.size_prefix (sourceBuffer d K) one (query w) k (query_unit w hw)
      (le_congr (.eqRefl _) (source_length d K).eqSymm hk))

theorem actual_unit_size_prefix_representation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (var 1) (length (var 0)) ⟶ represents (prefixNorm (var 0) (var 1))
      (ZT.ofNat (size (var 0) one (var 1))) (denominator (var 0))) :=
  closeUniv 2 (.impI (prefix_represents _ _ Prf.hyp0))
theorem actual_unit_size_monotone_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 1) (var 2) ⟶ le (size (var 0) one (var 1)) (size (var 0) one (var 2))) :=
  closeUniv 3 (.impI (size_monotone _ _ _ Prf.hyp0))
theorem original_euclidean_unit_prefix_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 4) ⟶ rationalLE (coefficientNorm (var 0)) (fraction (var 3) (var 4)) ⟶
      bounded (var 1) one one ⟶ le (var 2) (length (var 0)) ⟶ bounded (horner (var 0) (var 1) (var 2)) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (unit_prefix_bound _ _ _ _ _
    Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))
theorem original_half_disk_rescaled_query_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (bounded (var 0) one two ⟶ bounded (query (var 0)) (num 9) (num 10)) := closeUniv 1 (.impI (query_bound _ Prf.hyp0))
theorem original_composition_prefix_eleven_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (bounded (var 2) one two ⟶ le (var 3) (succ (var 1*var 0)) ⟶
      bounded (horner (sourceBuffer (var 0) (var 1)) (query (var 2)) (var 3)) (num 11) one) :=
  closeUniv 4 (.impI (.impI (source_prefix_bound _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_unit_prefix_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (program_at _ _ _ _)
theorem returned_unit_prefix_eleven_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (bounded (var 2) one two ⟶ le (var 3) (succ (var 1*var 0)) ⟶
      bounded (fstT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3)))))) (num 11) one) :=
  closeUniv 4 (.impI (.impI (returned_bound _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem returned_unit_prefix_cleared_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (bounded (var 2) one two ⟶ le (var 3) (succ (var 1*var 0)) ⟶
      bounded (fstT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3))))))
        (fstT (sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3)))))))
        (sndT (sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3)))))))) :=
  closeUniv 4 (.impI (.impI (returned_clear_bound _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRationalUnitDiskHornerNorm
