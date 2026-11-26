import IPRADerivations.Analysis.Polynomials.GaussianRationalSyntheticDivision
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalL1Algebra
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianFactorBudget
import IPRADerivations.Analysis.RationalArithmetic.RationalAlgebra
import IPRADerivations.Core.CongruenceTactic
import IPRADerivations.Core.LinearCombination

/-!
# Bounds for actual Gaussian-rational synthetic division

The actual quotient coefficients are normalized rational Horner prefixes.
Their L1 bounds are derived from the original coefficient bounds and an
original L1 root bound, using the proved rational triangle/product laws.
Quantifier-free induction compares the actual rational values with the
natural majorants (A+1)(1+Z)^k; independently normalized denominators remain
inside those comparisons. No quotient bound or supplied recurrence is an
input contract. This is a coefficient-growth dependency of source (AF),
not the complete deflation/error theorem.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalSyntheticBounds

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (qL1 qL1_guard qL1_nonnegative)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (horner qadd qmul)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (quotient qone quotient_lookup quotient_successor)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE left)
open LeanProofs.IPRA.Analysis.RationalArithmetic (add multiply)
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.Analysis.RationalIntegerNormalization (normalize)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def natCode (a : PTm n) : PTm n := normalize (ZT.ofNat a) one
def majorant (A Z k : PTm n) : PTm n := (A+one)*pw (one+Z) k

@[simp] theorem subst_natCode {m : ℕ} (σ : Fin n → PTm m) (a : PTm n) :
    Syn.subst σ (natCode a) = natCode (Syn.subst σ a) := by
  simp only [natCode,RationalIntegerNormalization.subst_normalize,ZT.subst_ofNat,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]
@[simp] theorem subst_majorant {m : ℕ} (σ : Fin n → PTm m) (A Z k : PTm n) :
    Syn.subst σ (majorant A Z k) = majorant (Syn.subst σ A) (Syn.subst σ Z) (Syn.subst σ k) := by
  simp only [majorant,PTm.subst_add,PTm.subst_mul,subst_ap2,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]

theorem natCode_represents (a : PTm n) : Γ ⊢[PRAAx] RationalArithmetic.represents (natCode a) (ZT.ofNat a) one :=
  RationalIntegerNormalization.normalize_preserves_value _ _ (le_refl one)

theorem natCode_nonnegative (a : PTm n) : Γ ⊢[PRAAx] le (numeratorOf (natCode a)).neg (numeratorOf (natCode a)).pos :=
  GaussianRationalL1.nonnegative_of_representation _ _ one (le_refl _) (natCode_represents a)

theorem natCode_order (a b : PTm n) (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] rationalLE (natCode a) (natCode b) :=
  GaussianRationalMetric.comparison_of_cleared _ _ _ _ one one (le_refl _) (le_refl _)
    (natCode_represents a) (natCode_represents b) (le_congr (by ipra_ring) (by ipra_ring) h)

theorem natCode_add (a b : PTm n) : Γ ⊢[PRAAx] add (natCode a) (natCode b) ≐ natCode (a+b) := by
  have h := RationalRepresentations.represents_add (Γ := Γ) (natCode a) (natCode b) _ _ _ _
    (natCode_represents a) (natCode_represents b)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.add_guard _ _)
    (RationalNormalForm.normalize_well_formed _ _ (le_refl one)) h (natCode_represents (a+b))
    (RationalAlgebra.positive_product (le_refl one) (le_refl one)) (le_refl one)
  ipra_lc

theorem natCode_multiply (a b : PTm n) : Γ ⊢[PRAAx] multiply (natCode a) (natCode b) ≐ natCode (a*b) := by
  have h := RationalRepresentations.represents_multiply (Γ := Γ) (natCode a) (natCode b) _ _ _ _
    (natCode_represents a) (natCode_represents b)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.multiply_guard _ _)
    (RationalNormalForm.normalize_well_formed _ _ (le_refl one)) h (natCode_represents (a*b))
    (RationalAlgebra.positive_product (le_refl one) (le_refl one)) (le_refl one)
  ipra_lc

/-- Rational addition is monotone in both independently denominated inputs.
The two actual input comparison gaps give the exact cross-numerator gap. -/
theorem add_monotone (a b c d : PTm n) (hab : Γ ⊢[PRAAx] rationalLE a b)
    (hcd : Γ ⊢[PRAAx] rationalLE c d) : Γ ⊢[PRAAx] rationalLE (add a c) (add b d) := by
  apply RationalArithmetic.order_of_representations _ _ _ _ _ _
    (RationalArithmetic.add_value a c) (RationalArithmetic.add_value b d)
    (RationalArithmetic.product_denominator_positive a c) (RationalArithmetic.product_denominator_positive b d)
  apply zle_of_toZ (denominatorOf c*denominatorOf d*PTm.monus (left b a) (left a b)+
    denominatorOf a*denominatorOf b*PTm.monus (left d c) (left c d))
  have first := natEq (eq_add_of_le hab)
  have second := natEq (eq_add_of_le hcd)
  simp only [RationalArithmetic.addNumerator,RationalArithmetic.productDenominator,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat]
  simp only [ZT.toZ]
  unfold left at first second ⊢
  simp only [Q.mk_add,Q.mk_mul,map_add,map_mul] at first second
  ipra_simps
  linear_combination -𝔞(denominatorOf c)*𝔞(denominatorOf d)*first-
    𝔞(denominatorOf a)*𝔞(denominatorOf b)*second

theorem qL1_congr {q r : PTm n} (h : Γ ⊢[PRAAx] q ≐ r) : Γ ⊢[PRAAx] qL1 q ≐ qL1 r := by
  ipra_congr (qL1 (var 0) : PTm 1) with [h]

theorem qL1_qone : Γ ⊢[PRAAx] qL1 (qone : PTm n) ≐ natCode one := by
  have rep := GaussianRationalL1.qL1_represents (Γ := Γ) qone ComplexLogarithmRemainder.oneCode one (le_refl _)
    (GaussianRationalHorner.ofGaussian_represents _ _ (le_refl _))
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (qL1_guard _)
    (RationalNormalForm.normalize_well_formed _ _ (le_refl one)) rep (natCode_represents one)
    (le_refl _) (le_refl _)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  rw [natEq (GaussianL1.norm1_one (Γ := Γ) (n := n))]

/-- The source coefficient bounds concern the actual original rational
coefficients, rather than a supplied quotient or desired growth estimate. -/
def coefficientBounds (C A : PTm n) : Fm PTm n :=
  .all (lt (var 0) (length (Syn.shift C)) ⟶ rationalLE (qL1 (entry (Syn.shift C) (var 0))) (natCode (Syn.shift A)))

@[simp] theorem subst_coefficientBounds {m : ℕ} (σ : Fin n → PTm m) (C A : PTm n) :
    (coefficientBounds C A).subst σ = coefficientBounds (Syn.subst σ C) (Syn.subst σ A) := by
  simp only [coefficientBounds,Fm.subst_all,Fm.subst_imp,subst_lt,subst_length,RationalArgmin.subst_rationalLE,
    GaussianRationalL1.subst_qL1,subst_entry,subst_natCode,Syn.subst_var,Syn.up_zero,Syn.up_succ,Syn.subst_shift,Syn.shift_subst]

theorem coefficient_at (C A i : PTm n) (h : Γ ⊢[PRAAx] coefficientBounds C A)
    (hi : Γ ⊢[PRAAx] lt i (length C)) : Γ ⊢[PRAAx] rationalLE (qL1 (entry C i)) (natCode A) := by
  have inst : Γ ⊢[PRAAx] lt i (length C) ⟶ rationalLE (qL1 (entry C i)) (natCode A) := by
    simpa only [Fm.subst_imp,subst_lt,subst_length,RationalArgmin.subst_rationalLE,GaussianRationalL1.subst_qL1,
      subst_entry,subst_natCode,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE i
  exact .impE inst hi

/-- The successor bound follows from the actual quotient recurrence and
actual rational triangle/product estimates. No recurrence is a hypothesis. -/
theorem quotient_step (C z N A Z k : PTm n) (hk : Γ ⊢[PRAAx] lt (succ k) N)
    (hcoeff : Γ ⊢[PRAAx] rationalLE (qL1 (entry C (succ k))) (natCode A))
    (hz : Γ ⊢[PRAAx] rationalLE (qL1 z) (natCode Z))
    (ih : Γ ⊢[PRAAx] rationalLE (qL1 (entry (quotient C z N) k)) (natCode (majorant A Z k))) : Γ ⊢[PRAAx]
    rationalLE (qL1 (entry (quotient C z N) (succ k))) (natCode (majorant A Z (succ k))) := by
  let old := entry (quotient C z N) k
  have product := GaussianRationalL1Algebra.qL1_multiply (Γ := Γ) old z
  have first := RationalArithmetic.multiply_monotone (qL1 z) (qL1 old) (natCode (majorant A Z k))
    (qL1_nonnegative z) ih
  have first' : Γ ⊢[PRAAx] rationalLE (multiply (qL1 old) (qL1 z))
      (multiply (natCode (majorant A Z k)) (qL1 z)) := RationalArgmin.rationalLE_congr
    (RationalAlgebra.multiply_commutative _ _) (RationalAlgebra.multiply_commutative _ _) first
  have second := RationalArithmetic.multiply_monotone (natCode (majorant A Z k)) (qL1 z) (natCode Z)
    (natCode_nonnegative _) hz
  have multiplied := RationalArgmin.transitive product (RationalArgmin.transitive first' second)
  have triangle := GaussianRationalL1Algebra.qL1_add (Γ := Γ) (qmul old z) (entry C (succ k))
  have estimate := RationalArgmin.transitive triangle (add_monotone _ _ _ _ multiplied hcoeff)
  have actual := qL1_congr (quotient_successor C z N k hk)
  have code : Γ ⊢[PRAAx] add (multiply (natCode (majorant A Z k)) (natCode Z)) (natCode A) ≐
      natCode (majorant A Z k*Z+A) :=
    (RationalAlgebra.add_congr (natCode_multiply _ _) (.eqRefl _)).eqTrans (natCode_add _ _)
  have coarse : Γ ⊢[PRAAx] le (majorant A Z k*Z+A) (majorant A Z (succ k)) := by
    have hp := GaussianFactorBudget.power_positive (Γ := Γ) (one+Z) k (le_add_right one Z)
    have base : Γ ⊢[PRAAx] le A (majorant A Z k) := le_trans (le_add_right A one)
      (le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl (A+one)) hp))
    have eq := natEq (pw_succ (Γ := Γ) (one+Z) k)
    have gap := natEq (eq_add_of_le base)
    refine le_of_eq_add (d := PTm.monus (majorant A Z k) A) ?_
    apply deriveNat
    unfold majorant at gap ⊢
    ipra_simps
    rw [eq]
    linear_combination gap
  exact RationalArgmin.transitive
    (RationalArgmin.rationalLE_congr actual.eqSymm code estimate)
    (natCode_order _ _ coarse)

theorem natCode_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] natCode a ≐ natCode b := by
  ipra_congr (natCode (var 0) : PTm 1) with [h]

/-- Induction on the actual quotient indices uses only original coefficient
bounds, the original root bound and literal monicity of the input. -/
theorem quotient_prefix_bound (C z N A Z i : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hmonic : Γ ⊢[PRAAx] entry C zero ≐ qone)
    (hcoeff : Γ ⊢[PRAAx] coefficientBounds C A) (hz : Γ ⊢[PRAAx] rationalLE (qL1 z) (natCode Z))
    (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    rationalLE (qL1 (entry (quotient C z N) i)) (natCode (majorant A Z i)) := by
  have all : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift N) ⟶
      rationalLE (qL1 (entry (quotient (Syn.shift C) (Syn.shift z) (Syn.shift N)) (var 0)))
        (natCode (majorant (Syn.shift A) (Syn.shift Z) (var 0)))) := by
    refine PRA.qfInd _ ⟨lt_QF _ _,le_QF _ _⟩ ?_ ?_
    · simp only [Fm.subst_imp,subst_lt,RationalArgmin.subst_rationalLE,GaussianRationalL1.subst_qL1,
        subst_entry,GaussianRationalSyntheticDivision.subst_quotient,subst_natCode,subst_majorant,
        Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      refine .impI ?_
      have init : (lt zero N :: Γ) ⊢[PRAAx] entry (quotient C z N) zero ≐ qone :=
        Prf.andE₂ (GaussianRationalSyntheticDivision.quotient_monic C z N Prf.hyp0 hmonic.wk)
      have norm := (qL1_congr init).eqTrans qL1_qone
      have low : Γ ⊢[PRAAx] le one (majorant A Z zero) := by
        refine le_of_eq_add (d := A) ?_
        exact (congrMul (.eqRefl _) (pw_zero _)).eqTrans (by ipra_ring)
      exact RationalArgmin.rationalLE_congr norm.eqSymm (.eqRefl _) (natCode_order _ _ low).wk
    · simp only [Fm.subst_imp,subst_lt,RationalArgmin.subst_rationalLE,GaussianRationalL1.subst_qL1,
        subst_entry,GaussianRationalSyntheticDivision.subst_quotient,subst_natCode,subst_majorant,
        Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let IH := lt (var 0) (Syn.shift N) ⟶
        rationalLE (qL1 (entry (quotient (Syn.shift C) (Syn.shift z) (Syn.shift N)) (var 0)))
          (natCode (majorant (Syn.shift A) (Syn.shift Z) (var 0)))
      let Δ := lt (succ (var 0)) (Syn.shift N) :: IH :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] rationalLE
          (qL1 (entry (quotient (Syn.shift C) (Syn.shift z) (Syn.shift N)) (var 0)))
          (natCode (majorant (Syn.shift A) (Syn.shift Z) (var 0))) :=
        .impE Prf.hyp1 (lt_of_le_of_lt (le_succ_self _) Prf.hyp0)
      have coeff : Γ.map Fm.shift ⊢[PRAAx] coefficientBounds (Syn.shift C) (Syn.shift A) := by
        simpa only [Fm.shift,subst_coefficientBounds,Syn.shift] using hcoeff.shift
      have root : Γ.map Fm.shift ⊢[PRAAx] rationalLE (qL1 (Syn.shift z)) (natCode (Syn.shift Z)) := by
        simpa only [Fm.shift,RationalArgmin.subst_rationalLE,GaussianRationalL1.subst_qL1,subst_natCode,Syn.shift] using hz.shift
      have len : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
        simpa only [Fm.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hC.shift
      have valid : Δ ⊢[PRAAx] lt (succ (var 0)) (length (Syn.shift C)) :=
        lt_congr (.eqRefl _) len.wk.wk.eqSymm (lt_of_lt_of_le Prf.hyp0 (le_succ_self _))
      exact quotient_step _ _ _ _ _ _ Prf.hyp0 (coefficient_at _ _ _ coeff.wk.wk valid) root.wk.wk ih
  have inst : Γ ⊢[PRAAx] lt i N ⟶ rationalLE (qL1 (entry (quotient C z N) i)) (natCode (majorant A Z i)) := by
    simpa only [Fm.subst_imp,subst_lt,RationalArgmin.subst_rationalLE,GaussianRationalL1.subst_qL1,
      subst_entry,GaussianRationalSyntheticDivision.subst_quotient,subst_natCode,subst_majorant,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE i
  exact .impE inst hi

/-- A numerical horizon H can exceed the actual current degree N. This is
the global original degree retained in source (AF) during deflation. -/
theorem quotient_bound (C z N H A Z i : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hmonic : Γ ⊢[PRAAx] entry C zero ≐ qone)
    (hcoeff : Γ ⊢[PRAAx] coefficientBounds C A) (hz : Γ ⊢[PRAAx] rationalLE (qL1 z) (natCode Z))
    (hNH : Γ ⊢[PRAAx] le N H) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    rationalLE (qL1 (entry (quotient C z N) i)) (natCode (majorant A Z H)) := by
  have ih := quotient_prefix_bound C z N A Z i hC hmonic hcoeff hz hi
  have ik : Γ ⊢[PRAAx] le i H := le_trans (le_trans (le_succ_self _) hi) hNH
  have order := le_mul_mono (le_refl (A+one))
    (GaussianFactorBudget.power_monotone_length (one+Z) i H (le_add_right one Z) ik)
  exact RationalArgmin.transitive ih (natCode_order _ _ order)

theorem horner_bound (C z N H A Z i : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hmonic : Γ ⊢[PRAAx] entry C zero ≐ qone)
    (hcoeff : Γ ⊢[PRAAx] coefficientBounds C A) (hz : Γ ⊢[PRAAx] rationalLE (qL1 z) (natCode Z))
    (hNH : Γ ⊢[PRAAx] le N H) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    rationalLE (qL1 (horner C z (succ i))) (natCode (majorant A Z H)) :=
  RationalArgmin.rationalLE_congr (qL1_congr (quotient_lookup C z N i hi)) (.eqRefl _)
    (quotient_bound C z N H A Z i hC hmonic hcoeff hz hNH hi)

/-- At stage j the original Euclidean radius A_j+2 and original coefficient
L1 bounds yield the actual next precomputed A_(j+1). No quotient or Horner
bound is supplied, and the current degree can be smaller than H. -/
theorem stage_bound (C z N H A0 j i : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hmonic : Γ ⊢[PRAAx] entry C zero ≐ qone)
    (hcoeff : Γ ⊢[PRAAx] coefficientBounds C (GaussianFactorBudget.bound H A0 j))
    (hz : Γ ⊢[PRAAx] GaussianRationalMetric.bounded z (GaussianFactorBudget.bound H A0 j+two) one)
    (hNH : Γ ⊢[PRAAx] le N H) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    rationalLE (qL1 (entry (quotient C z N) i)) (natCode (GaussianFactorBudget.bound H A0 (succ j))) := by
  have root := GaussianRationalL1Algebra.qL1_of_bounded (Γ := Γ) z (GaussianFactorBudget.bound H A0 j+two) one (le_refl _) hz
  have estimate := quotient_bound C z N H (GaussianFactorBudget.bound H A0 j)
    (two*(GaussianFactorBudget.bound H A0 j+two)) i hC hmonic hcoeff root hNH hi
  have eq : Γ ⊢[PRAAx] majorant (GaussianFactorBudget.bound H A0 j)
      (two*(GaussianFactorBudget.bound H A0 j+two)) H ≐ GaussianFactorBudget.bound H A0 (succ j) := by
    have e : Γ ⊢[PRAAx] one+two*(GaussianFactorBudget.bound H A0 j+two) ≐ GaussianFactorBudget.factor H A0 j := by
      unfold GaussianFactorBudget.factor GaussianFactorBudget.five
      ipra_ring
    exact (congrMul (.eqRefl _) (congrAp2 powF (.eqRefl _) e)).eqTrans (GaussianFactorBudget.bound_succ H A0 j).eqSymm
  exact RationalArgmin.rationalLE_congr (.eqRefl _) (natCode_congr eq) estimate

/-- The full actual output coefficient list has the next-stage bound.
This packages every output index using its proved stored length. -/
theorem stage_coefficient_bounds (C z N H A0 j : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hmonic : Γ ⊢[PRAAx] entry C zero ≐ qone)
    (hcoeff : Γ ⊢[PRAAx] coefficientBounds C (GaussianFactorBudget.bound H A0 j))
    (hz : Γ ⊢[PRAAx] GaussianRationalMetric.bounded z (GaussianFactorBudget.bound H A0 j+two) one)
    (hNH : Γ ⊢[PRAAx] le N H) : Γ ⊢[PRAAx]
    coefficientBounds (quotient C z N) (GaussianFactorBudget.bound H A0 (succ j)) := by
  refine .allI (.impI ?_)
  have shape : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
    simpa only [Fm.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hC.shift
  have monic : Γ.map Fm.shift ⊢[PRAAx] entry (Syn.shift C) zero ≐ qone := by
    simpa only [Fm.shift,Fm.subst_eq,subst_entry,ConciseIPRA.PTm.subst_zero,
      GaussianRationalSyntheticDivision.subst_qone,Syn.shift] using hmonic.shift
  have coeff : Γ.map Fm.shift ⊢[PRAAx] coefficientBounds (Syn.shift C)
      (GaussianFactorBudget.bound (Syn.shift H) (Syn.shift A0) (Syn.shift j)) := by
    simpa only [Fm.shift,subst_coefficientBounds,GaussianFactorBudget.subst_bound,Syn.shift] using hcoeff.shift
  have root : Γ.map Fm.shift ⊢[PRAAx] GaussianRationalMetric.bounded (Syn.shift z)
      (GaussianFactorBudget.bound (Syn.shift H) (Syn.shift A0) (Syn.shift j)+two) one := by
    simpa only [Fm.shift,GaussianRationalMetric.subst_bounded,PTm.subst_add,GaussianFactorBudget.subst_bound,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hz.shift
  have degree : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift N) (Syn.shift H) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using hNH.shift
  have index : (lt (var 0) (length (Syn.shift (quotient C z N))) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (Syn.shift N) := by
    have stored : (lt (var 0) (length (Syn.shift (quotient C z N))) :: Γ.map Fm.shift) ⊢[PRAAx]
        lt (var 0) (length (quotient (Syn.shift C) (Syn.shift z) (Syn.shift N))) := by
      simpa only [Syn.shift,GaussianRationalSyntheticDivision.subst_quotient] using Prf.hyp0
    exact lt_congr (.eqRefl _) (GaussianRationalSyntheticDivision.quotient_length _ _ _) stored
  have value := stage_bound _ _ _ _ _ _ _ shape.wk monic.wk coeff.wk root.wk degree.wk index
  simpa only [Syn.shift,GaussianRationalSyntheticDivision.subst_quotient,GaussianFactorBudget.subst_bound,
    ConciseIPRA.PTm.subst_succ] using value

/-- The bound value is itself a fixed PR3 program, uniform in all numerical
coefficients, norm bounds and original-degree horizons. -/
def majorantF : PR 3 := PTm.toPR (natCode (majorant (var 0) (var 1) (var 2)))

theorem majorant_program (A Z H : PTm n) : Γ ⊢[PRAAx]
    ap3 majorantF A Z H ≐ natCode (majorant A Z H) := by
  simpa only [majorantF,ap3,subst_natCode,subst_majorant,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (natCode (majorant (var 0) (var 1) (var 2)) : PTm 3) ![A,Z,H]

theorem quotient_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (length (var 0) ≐ succ (var 2) ⟶ entry (var 0) zero ≐ qone ⟶
      coefficientBounds (var 0) (var 4) ⟶ rationalLE (qL1 (var 1)) (natCode (var 5)) ⟶
        le (var 2) (var 3) ⟶ lt (var 6) (var 2) ⟶
          rationalLE (qL1 (entry (quotient (var 0) (var 1) (var 2)) (var 6)))
            (natCode (majorant (var 4) (var 5) (var 3)))) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI (.impI
    (quotient_bound _ _ _ _ _ _ _ Prf.hyp1.wk.wk.wk.wk Prf.hyp1.wk.wk.wk
      Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))))

theorem horner_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (length (var 0) ≐ succ (var 2) ⟶ entry (var 0) zero ≐ qone ⟶
      coefficientBounds (var 0) (var 4) ⟶ rationalLE (qL1 (var 1)) (natCode (var 5)) ⟶
        le (var 2) (var 3) ⟶ lt (var 6) (var 2) ⟶
          rationalLE (qL1 (horner (var 0) (var 1) (succ (var 6))))
            (natCode (majorant (var 4) (var 5) (var 3)))) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI (.impI
    (horner_bound _ _ _ _ _ _ _ Prf.hyp1.wk.wk.wk.wk Prf.hyp1.wk.wk.wk
      Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))))

theorem stage_coefficient_bounds_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (length (var 0) ≐ succ (var 2) ⟶ entry (var 0) zero ≐ qone ⟶
      coefficientBounds (var 0) (GaussianFactorBudget.bound (var 3) (var 4) (var 5)) ⟶
        GaussianRationalMetric.bounded (var 1) (GaussianFactorBudget.bound (var 3) (var 4) (var 5)+two) one ⟶
          le (var 2) (var 3) ⟶ coefficientBounds (quotient (var 0) (var 1) (var 2))
            (GaussianFactorBudget.bound (var 3) (var 4) (succ (var 5)))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (.impI
    (stage_coefficient_bounds _ _ _ _ _ _ Prf.hyp1.wk.wk.wk Prf.hyp1.wk.wk
      Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))))

theorem majorant_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 majorantF (var 0) (var 1) (var 2) ≐ natCode (majorant (var 0) (var 1) (var 2))) :=
  closeUniv 3 (majorant_program _ _ _)

end LeanProofs.IPRA.Analysis.GaussianRationalSyntheticBounds
