import IPRADerivations.Algebra.QuadraticTowerSignEmbedding

/-!
# Actual numerical-tower difference and order-translation identities

Source `isoperimetric_ipra.tex`, the ordered-extension equality/congruence
and order laws. Genuine original rational arithmetic proves cancellation
and common-translation equality of the SAME constructed coefficient
differences. Actual sign-table queries inherit these identities at every
numerical depth. These are individual quotient/order identities, not a
general ordered-domain or zero-ideal closure theorem.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Algebra.QuadraticTowerDifferenceIdentities

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis
open RationalSupMetric (numeratorOf denominatorOf)
open QuadraticTowerCoefficients (width)
open QuadraticTowerCoefficientArithmetic (added negated)
open QuadraticTowerScalarArrays (zeroArray zeroScalar)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceEquality (sequence_equal)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def scalarDifference (a b : PTm n) : PTm n := RationalArithmetic.add a (RationalArithmetic.negative b)
def difference (h A B : PTm n) : PTm n := added h A (negated h B)
def signDifference (h B D A C : PTm n) : PTm n := QuadraticTowerSignTable.query h B D (difference h A C)
def equivalent (h B D A C : PTm n) : Fm PTm n := signDifference h B D A C ≐ zero
def less (h B D A C : PTm n) : Fm PTm n := signDifference h B D C A ≐ one
@[simp] theorem subst_scalarDifference {k : ℕ} (σ : Fin n → PTm k) (a b : PTm n) :
    Syn.subst σ (scalarDifference a b) = scalarDifference (Syn.subst σ a) (Syn.subst σ b) := by simp [scalarDifference]
@[simp] theorem subst_difference {k : ℕ} (σ : Fin n → PTm k) (h A B : PTm n) :
    Syn.subst σ (difference h A B) = difference (Syn.subst σ h) (Syn.subst σ A) (Syn.subst σ B) := by simp [difference]
@[simp] theorem subst_signDifference {k : ℕ} (σ : Fin n → PTm k) (h B D A C : PTm n) :
    Syn.subst σ (signDifference h B D A C) = signDifference (Syn.subst σ h) (Syn.subst σ B)
      (Syn.subst σ D) (Syn.subst σ A) (Syn.subst σ C) := by simp [signDifference]
@[simp] theorem subst_equivalent {k : ℕ} (σ : Fin n → PTm k) (h B D A C : PTm n) :
    (equivalent h B D A C).subst σ = equivalent (Syn.subst σ h) (Syn.subst σ B)
      (Syn.subst σ D) (Syn.subst σ A) (Syn.subst σ C) := by simp [equivalent]
@[simp] theorem subst_less {k : ℕ} (σ : Fin n → PTm k) (h B D A C : PTm n) :
    (less h B D A C).subst σ = less (Syn.subst σ h) (Syn.subst σ B)
      (Syn.subst σ D) (Syn.subst σ A) (Syn.subst σ C) := by simp [less]

theorem scalar_difference_congr {a b c d : PTm n} (ha : Γ ⊢[PRAAx] a ≐ c) (hb : Γ ⊢[PRAAx] b ≐ d) : Γ ⊢[PRAAx]
    scalarDifference a b ≐ scalarDifference c d := RationalAlgebra.add_congr ha (RationalAlgebra.negative_congr hb)

theorem scalar_cancel (a : PTm n) : Γ ⊢[PRAAx] scalarDifference a a ≐ zeroScalar := by
  have negRep := RationalRepresentations.represents_negative (Γ := Γ) a (numeratorOf a) (denominatorOf a)
    (RationalRepresentations.represents_self a)
  have total := RationalRepresentations.represents_add (Γ := Γ) a (RationalArithmetic.negative a)
    (numeratorOf a) (-numeratorOf a) (denominatorOf a) (denominatorOf a)
      (RationalRepresentations.represents_self a) negRep
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.add_guard _ _) QuadraticTowerScalarArrays.zero_canonical total
    (QuadraticRationalEmbedding.zero_scalar_represents one)
    (RationalAlgebra.positive_product (RationalArgmin.denominator_positive a) (RationalArgmin.denominator_positive a)) (le_refl one)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_neg,ZT.toZ_ofNat,Q.mk_one,Q.mk_zero,map_one,map_zero]
  ring

/-- Canonical original rational differences are literally invariant under
common addition, with all raw denominators retained in the proof. -/
theorem scalar_translation (a b c : PTm n) : Γ ⊢[PRAAx]
    scalarDifference (RationalArithmetic.add a c) (RationalArithmetic.add b c) ≐ scalarDifference a b := by
  let A := numeratorOf a
  let B := numeratorOf b
  let C := numeratorOf c
  let D := denominatorOf a
  let E := denominatorOf b
  let F := denominatorOf c
  have ac := RationalRepresentations.represents_add (Γ := Γ) a c A C D F
    (RationalRepresentations.represents_self a) (RationalRepresentations.represents_self c)
  have bc := RationalRepresentations.represents_add (Γ := Γ) b c B C E F
    (RationalRepresentations.represents_self b) (RationalRepresentations.represents_self c)
  have negbc := RationalRepresentations.represents_negative (Γ := Γ) _ _ _ bc
  have left := RationalRepresentations.represents_add (Γ := Γ) _ _ _ _ _ _ ac negbc
  have right := RationalRepresentations.represents_add (Γ := Γ) a (RationalArithmetic.negative b) A (-B) D E
    (RationalRepresentations.represents_self a)
      (RationalRepresentations.represents_negative b B E (RationalRepresentations.represents_self b))
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.add_guard _ _) (RationalArithmetic.add_guard _ _) left right
    (RationalAlgebra.positive_product
      (RationalAlgebra.positive_product (RationalArgmin.denominator_positive a) (RationalArgmin.denominator_positive c))
      (RationalAlgebra.positive_product (RationalArgmin.denominator_positive b) (RationalArgmin.denominator_positive c)))
    (RationalAlgebra.positive_product (RationalArgmin.denominator_positive a) (RationalArgmin.denominator_positive b))
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_neg,ZT.toZ_ofNat,Q.mk_mul,map_mul]
  ring

theorem difference_body_at (h A B i : PTm n) (hi : Γ ⊢[PRAAx] lt i (width h)) : Γ ⊢[PRAAx]
    inst2 QuadraticTowerCoefficientArithmetic.addBody i (pairT A (negated h B)) ≐ scalarDifference (entry A i) (entry B i) :=
  (QuadraticTowerCoefficientArithmetic.add_body_at _ _ _).eqTrans
    (RationalAlgebra.add_congr (.eqRefl _) (QuadraticTowerCoefficientArithmetic.negated_lookup _ _ _ hi))
theorem difference_lookup (h A B i : PTm n) (hi : Γ ⊢[PRAAx] lt i (width h)) : Γ ⊢[PRAAx]
    entry (difference h A B) i ≐ scalarDifference (entry A i) (entry B i) :=
  (QuadraticTowerCoefficientArithmetic.added_lookup _ _ _ _ hi).eqTrans
    (RationalAlgebra.add_congr (.eqRefl _) (QuadraticTowerCoefficientArithmetic.negated_lookup _ _ _ hi))

/-- Equality is between two actual sequence constructors, without any
arbitrary-list extensionality or input-canonicality premise. -/
theorem difference_self (h A : PTm n) : Γ ⊢[PRAAx] difference h A A ≐ zeroArray h := by
  apply sequence_equal QuadraticTowerCoefficientArithmetic.addBody QuadraticTowerScalarArrays.zeroBody (width h) (pairT A (negated h A)) zero
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (width (Syn.shift h)) :: Γ.map Fm.shift
  have value := (difference_body_at (Γ := Δ) (Syn.shift h) (Syn.shift A) (Syn.shift A) (var 0) Prf.hyp0).eqTrans (scalar_cancel _)
  simpa only [Δ,Syn.shift,subst_pairT,QuadraticTowerCoefficientArithmetic.subst_negated,QuadraticTowerCoefficients.subst_width,
    QuadraticTowerScalarArrays.zero_body_at] using value

theorem difference_translation (h A B C : PTm n) : Γ ⊢[PRAAx]
    difference h (added h A C) (added h B C) ≐ difference h A B := by
  apply sequence_equal QuadraticTowerCoefficientArithmetic.addBody QuadraticTowerCoefficientArithmetic.addBody (width h)
    (pairT (added h A C) (negated h (added h B C))) (pairT A (negated h B))
  refine .allI (.impI ?_)
  let h' := Syn.shift h
  let a := Syn.shift A
  let b := Syn.shift B
  let c := Syn.shift C
  let Δ := lt (var 0) (width h') :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (width h') := Prf.hyp0
  have value := (difference_body_at h' (added h' a c) (added h' b c) (var 0) hi).eqTrans
    ((scalar_difference_congr (QuadraticTowerCoefficientArithmetic.added_lookup _ _ _ _ hi)
      (QuadraticTowerCoefficientArithmetic.added_lookup _ _ _ _ hi)).eqTrans
        ((scalar_translation _ _ _).eqTrans (difference_body_at h' a b (var 0) hi).eqSymm))
  simpa only [Δ,h',a,b,c,Syn.shift,subst_pairT,QuadraticTowerCoefficientArithmetic.subst_added,
    QuadraticTowerCoefficientArithmetic.subst_negated,QuadraticTowerCoefficients.subst_width] using value

theorem sign_reflexive (h B D A : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] signDifference h B D A A ≐ zero :=
  (QuadraticTowerSignRecipe.read_operand_congr h B (QuadraticTowerSignTable.table h B D) _ _ (difference_self h A)).eqTrans
    (QuadraticTowerSignEmbedding.zero_query h B D hB)
theorem sign_translation (h B D A C E : PTm n) : Γ ⊢[PRAAx]
    signDifference h B D (added h A E) (added h C E) ≐ signDifference h B D A C :=
  QuadraticTowerSignRecipe.read_operand_congr h B (QuadraticTowerSignTable.table h B D) _ _ (difference_translation h A C E)
theorem equivalent_reflexive (h B D A : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] equivalent h B D A A :=
  sign_reflexive h B D A hB
theorem less_irreflexive (h B D A : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] neg (less h B D A A) :=
  .impI (succ_ne_zero' _ (Prf.hyp0.eqSymm.eqTrans (sign_reflexive h B D A hB.wk)))

/-- Actual sign-zero equality is translation invariant, even in redundant
extensions. This does not assert the remaining equivalence/ideal laws. -/
theorem equivalent_translation (h B D A C E : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (equivalent h B D (added h A E) (added h C E)) (equivalent h B D A C) :=
  .andI (.impI ((sign_translation h B D A C E).eqSymm.eqTrans Prf.hyp0))
    (.impI ((sign_translation h B D A C E).eqTrans Prf.hyp0))
theorem less_translation (h B D A C E : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (less h B D (added h A E) (added h C E)) (less h B D A C) :=
  .andI (.impI ((sign_translation h B D C A E).eqSymm.eqTrans Prf.hyp0))
    (.impI ((sign_translation h B D C A E).eqTrans Prf.hyp0))

theorem returned_sign_translation (h B D A C E : PTm n) : Γ ⊢[PRAAx]
    fstT (QuadraticTowerSignTable.run h B D (difference h (added h A E) (added h C E))) ≐
      fstT (QuadraticTowerSignTable.run h B D (difference h A C)) :=
  (QuadraticTowerSignTable.returned_tag _ _ _ _).eqTrans
    ((sign_translation h B D A C E).eqTrans (QuadraticTowerSignTable.returned_tag _ _ _ _).eqSymm)

def output (h B D A C E : PTm n) : PTm n := pairT (difference h A C)
  (pairT (difference h (added h A E) (added h C E))
    (pairT (signDifference h B D A C) (signDifference h B D (added h A E) (added h C E))))
def outputF : PR 6 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def run (h B D A C E : PTm n) : PTm n := PTm.app outputF ![h,B,D,A,C,E]
@[simp] theorem subst_output {k : ℕ} (σ : Fin n → PTm k) (h B D A C E : PTm n) :
    Syn.subst σ (output h B D A C E) = output (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D)
      (Syn.subst σ A) (Syn.subst σ C) (Syn.subst σ E) := by simp [output]
@[simp] theorem subst_run {k : ℕ} (σ : Fin n → PTm k) (h B D A C E : PTm n) :
    Syn.subst σ (run h B D A C E) = run (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D)
      (Syn.subst σ A) (Syn.subst σ C) (Syn.subst σ E) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
theorem program_at (h B D A C E : PTm n) : Γ ⊢[PRAAx] run h B D A C E ≐ output h B D A C E := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![h,B,D,A,C,E]
theorem returned_original (h B D A C E : PTm n) : Γ ⊢[PRAAx] fstT (run h B D A C E) ≐ difference h A C :=
  (congrFst (program_at h B D A C E)).eqTrans (fst_pair _ _)
theorem returned_tail (h B D A C E : PTm n) : Γ ⊢[PRAAx] sndT (run h B D A C E) ≐
    pairT (difference h (added h A E) (added h C E))
      (pairT (signDifference h B D A C) (signDifference h B D (added h A E) (added h C E))) :=
  (congrSnd (program_at h B D A C E)).eqTrans (snd_pair _ _)
theorem returned_translated (h B D A C E : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run h B D A C E)) ≐ difference h (added h A E) (added h C E) :=
  (congrFst (returned_tail h B D A C E)).eqTrans (fst_pair _ _)
theorem returned_signs (h B D A C E : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run h B D A C E)) ≐
    pairT (signDifference h B D A C) (signDifference h B D (added h A E) (added h C E)) :=
  (congrSnd (returned_tail h B D A C E)).eqTrans (snd_pair _ _)
theorem returned_arrays_equal (h B D A C E : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run h B D A C E)) ≐ fstT (run h B D A C E) :=
  (returned_translated h B D A C E).eqTrans ((difference_translation h A C E).eqTrans (returned_original h B D A C E).eqSymm)
theorem returned_signs_equal (h B D A C E : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run h B D A C E))) ≐ sndT (sndT (sndT (run h B D A C E))) :=
  ((congrFst (returned_signs h B D A C E)).eqTrans (fst_pair _ _)).eqTrans
    ((sign_translation h B D A C E).eqSymm.eqTrans ((congrSnd (returned_signs h B D A C E)).eqTrans (snd_pair _ _)).eqSymm)

theorem actual_tower_difference_self_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (difference (var 0) (var 1) (var 1) ≐ zeroArray (var 0)) := closeUniv 2 (difference_self _ _)
theorem actual_tower_difference_translation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (difference (var 0) (added (var 0) (var 1) (var 3)) (added (var 0) (var 2) (var 3)) ≐ difference (var 0) (var 1) (var 2)) :=
  closeUniv 4 (difference_translation _ _ _ _)
theorem actual_tower_sign_difference_reflexive_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ signDifference (var 0) (var 1) (var 2) (var 3) (var 3) ≐ zero) :=
  closeUniv 4 (.impI (sign_reflexive _ _ _ _ Prf.hyp0))
theorem actual_tower_sign_difference_translation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (signDifference (var 0) (var 1) (var 2) (added (var 0) (var 3) (var 5)) (added (var 0) (var 4) (var 5)) ≐
      signDifference (var 0) (var 1) (var 2) (var 3) (var 4)) := closeUniv 6 (sign_translation _ _ _ _ _ _)
theorem actual_tower_sign_equality_reflexive_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ equivalent (var 0) (var 1) (var 2) (var 3) (var 3)) :=
  closeUniv 4 (.impI (equivalent_reflexive _ _ _ _ Prf.hyp0))
theorem actual_tower_strict_order_irreflexive_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ neg (less (var 0) (var 1) (var 2) (var 3) (var 3))) :=
  closeUniv 4 (.impI (less_irreflexive _ _ _ _ Prf.hyp0))
theorem actual_tower_sign_equality_translation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (Fm.iff (equivalent (var 0) (var 1) (var 2) (added (var 0) (var 3) (var 5)) (added (var 0) (var 4) (var 5)))
      (equivalent (var 0) (var 1) (var 2) (var 3) (var 4))) := closeUniv 6 (equivalent_translation _ _ _ _ _ _)
theorem actual_tower_strict_order_translation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (Fm.iff (less (var 0) (var 1) (var 2) (added (var 0) (var 3) (var 5)) (added (var 0) (var 4) (var 5)))
      (less (var 0) (var 1) (var 2) (var 3) (var 4))) := closeUniv 6 (less_translation _ _ _ _ _ _)
theorem actual_tower_difference_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (program_at _ _ _ _ _ _)
theorem actual_tower_difference_returned_equalities_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) ≐ fstT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) ⋏
      fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))) ≐ sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))))) :=
  closeUniv 6 (.andI (returned_arrays_equal _ _ _ _ _ _) (returned_signs_equal _ _ _ _ _ _))

end LeanProofs.IPRA.Algebra.QuadraticTowerDifferenceIdentities
