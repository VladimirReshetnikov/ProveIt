import IPRADerivations.Algebra.QuadraticTowerCoefficients
import IPRADerivations.Algebra.QuadraticRationalRepresentationInvariance

/-!
# Original rational arithmetic on numerical tower coefficient arrays

Actual finite sequence programs add or negate the original rational
coefficients at width 2^h. Bounded coefficient value equality is proper
without canonical input guards. The extension-half laws below bind both
halves to the actual lower-depth constructors. Recursive tower products,
radicand validity and tower sign are separate obligations.
-/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

namespace LeanProofs.IPRA.Algebra.QuadraticTowerCoefficientArithmetic

open_ipra
open LeanProofs.IPRA.Analysis
open RationalArgmin (rationalEq rationalEq_congr)
open QuadraticTowerCoefficients (width width_succ flatten flatten_length flatten_succ)
open LeanProofs.IPRA.Foundations.MasterCertificate (sequence entry sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length append append_left append_right entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def addBody : PTm 2 := RationalArithmetic.add (entry (fstT (var 1)) (var 0)) (entry (sndT (var 1)) (var 0))
def negativeBody : PTm 2 := RationalArithmetic.negative (entry (var 1) (var 0))
def added (h A B : PTm n) : PTm n := sequence addBody (width h) (pairT A B)
def negated (h A : PTm n) : PTm n := sequence negativeBody (width h) A
def equalValues (h A B : PTm n) : Fm PTm n := .all (lt (var 0) (width (Syn.shift h)) ⟶
  rationalEq (entry (Syn.shift A) (var 0)) (entry (Syn.shift B) (var 0)))

ipra_subst added
ipra_subst negated
ipra_subst equalValues [Syn.subst_shift, Syn.shift_subst]
theorem added_congr {h h' A A' B B' : PTm n} (hh : Γ ⊢[PRAAx] h ≐ h')
    (hA : Γ ⊢[PRAAx] A ≐ A') (hB : Γ ⊢[PRAAx] B ≐ B') : Γ ⊢[PRAAx]
    added h A B ≐ added h' A' B' := by
  ipra_congr (added (var 0) (var 1) (var 2) : PTm 3) with [hh, hA, hB]
theorem negated_congr {h h' A A' : PTm n} (hh : Γ ⊢[PRAAx] h ≐ h')
    (hA : Γ ⊢[PRAAx] A ≐ A') : Γ ⊢[PRAAx] negated h A ≐ negated h' A' := by
  ipra_congr (negated (var 0) (var 1) : PTm 2) with [hh, hA]

theorem add_body_at (A B i : PTm n) : Γ ⊢[PRAAx] inst2 addBody i (pairT A B) ≐
    RationalArithmetic.add (entry A i) (entry B i) := by
  simp only [addBody,inst2,RationalArithmetic.subst_add,Foundations.MasterCertificate.subst_entry,
    subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact RationalAlgebra.add_congr (entry_congr (fst_pair _ _) (.eqRefl _)) (entry_congr (snd_pair _ _) (.eqRefl _))
theorem negative_body_at (A i : PTm n) : inst2 negativeBody i A = RationalArithmetic.negative (entry A i) := by
  simp [negativeBody,inst2]
theorem added_length (h A B : PTm n) : Γ ⊢[PRAAx] length (added h A B) ≐ width h := sequence_length _ _ _
theorem negated_length (h A : PTm n) : Γ ⊢[PRAAx] length (negated h A) ≐ width h := sequence_length _ _ _
theorem added_lookup (h A B i : PTm n) (hi : Γ ⊢[PRAAx] lt i (width h)) : Γ ⊢[PRAAx]
    entry (added h A B) i ≐ RationalArithmetic.add (entry A i) (entry B i) :=
  (sequence_decode addBody (x := pairT A B) hi).eqTrans (add_body_at _ _ _)
theorem negated_lookup (h A i : PTm n) (hi : Γ ⊢[PRAAx] lt i (width h)) : Γ ⊢[PRAAx]
    entry (negated h A) i ≐ RationalArithmetic.negative (entry A i) := by
  simpa only [negated,negative_body_at] using sequence_decode (Γ := Γ) negativeBody (x := A) hi
theorem added_canonical_at (h A B i : PTm n) (hi : Γ ⊢[PRAAx] lt i (width h)) : Γ ⊢[PRAAx]
    RationalNormalForm.wellFormed (entry (added h A B) i) :=
  RationalArithmetic.guard_congr (added_lookup _ _ _ _ hi) (RationalArithmetic.add_guard _ _)
theorem negated_canonical_at (h A i : PTm n) (hi : Γ ⊢[PRAAx] lt i (width h)) : Γ ⊢[PRAAx]
    RationalNormalForm.wellFormed (entry (negated h A) i) :=
  RationalArithmetic.guard_congr (negated_lookup _ _ _ hi) (RationalArithmetic.negative_guard _)

theorem values_at (h A B i : PTm n) (hv : Γ ⊢[PRAAx] equalValues h A B)
    (hi : Γ ⊢[PRAAx] lt i (width h)) : Γ ⊢[PRAAx] rationalEq (entry A i) (entry B i) := by
  have rule := hv.allE i
  simp only [Fm.subst_imp,subst_lt,QuadraticTowerCoefficients.subst_width,
    RationalArgmin.subst_rationalEq,Foundations.MasterCertificate.subst_entry,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] at rule
  exact .impE rule hi
theorem added_proper (h A A' B B' : PTm n) (hA : Γ ⊢[PRAAx] equalValues h A A')
    (hB : Γ ⊢[PRAAx] equalValues h B B') : Γ ⊢[PRAAx] equalValues h (added h A B) (added h A' B') := by
  have ha : Γ.map Fm.shift ⊢[PRAAx] equalValues (Syn.shift h) (Syn.shift A) (Syn.shift A') := by
    simpa only [Fm.shift,subst_equalValues,Syn.shift] using hA.shift
  have hb : Γ.map Fm.shift ⊢[PRAAx] equalValues (Syn.shift h) (Syn.shift B) (Syn.shift B') := by
    simpa only [Fm.shift,subst_equalValues,Syn.shift] using hB.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (width (Syn.shift h)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (width (Syn.shift h)) := Prf.hyp0
  have a := values_at (Syn.shift h) (Syn.shift A) (Syn.shift A') (var 0) ha.wk hi
  have b := values_at (Syn.shift h) (Syn.shift B) (Syn.shift B') (var 0) hb.wk hi
  have result := rationalEq_congr (added_lookup (Syn.shift h) (Syn.shift A) (Syn.shift B) (var 0) hi).eqSymm
    (added_lookup (Syn.shift h) (Syn.shift A') (Syn.shift B') (var 0) hi).eqSymm
    (QuadraticRationalRepresentationInvariance.scalar_add_congr _ _ _ _ a b)
  simpa only [Δ,Syn.shift,subst_added] using result
theorem negated_proper (h A B : PTm n) (hv : Γ ⊢[PRAAx] equalValues h A B) : Γ ⊢[PRAAx]
    equalValues h (negated h A) (negated h B) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] equalValues (Syn.shift h) (Syn.shift A) (Syn.shift B) := by
    simpa only [Fm.shift,subst_equalValues,Syn.shift] using hv.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (width (Syn.shift h)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (width (Syn.shift h)) := Prf.hyp0
  have a := values_at (Syn.shift h) (Syn.shift A) (Syn.shift B) (var 0) hs.wk hi
  have result := rationalEq_congr (negated_lookup (Syn.shift h) (Syn.shift A) (var 0) hi).eqSymm
    (negated_lookup (Syn.shift h) (Syn.shift B) (var 0) hi).eqSymm
    (QuadraticRationalRepresentationInvariance.scalar_negative_congr _ _ a)
  simpa only [Δ,Syn.shift,subst_negated] using result

theorem width_le_next (h : PTm n) : Γ ⊢[PRAAx] le (width h) (width (succ h)) :=
  le_congr (.eqRefl _) (width_succ h).eqSymm (le_add_right _ _)
theorem right_half_bound (h i : PTm n) (hi : Γ ⊢[PRAAx] lt i (width h)) : Γ ⊢[PRAAx]
    lt (width h+i) (width (succ h)) :=
  lt_congr (.eqRefl _) (width_succ h).eqSymm (Foundations.SequenceComposition.add_lt_left _ hi)
theorem added_join_left (h A B C D i : PTm n) (hA : Γ ⊢[PRAAx] length A ≐ width h)
    (hC : Γ ⊢[PRAAx] length C ≐ width h) (hi : Γ ⊢[PRAAx] lt i (width h)) : Γ ⊢[PRAAx]
    entry (added (succ h) (append A B) (append C D)) i ≐ entry (added h A C) i :=
  (added_lookup _ _ _ _ (lt_of_lt_of_le hi (width_le_next h))).eqTrans
    ((RationalAlgebra.add_congr
      (append_left (lt_congr (.eqRefl _) hA.eqSymm hi))
      (append_left (lt_congr (.eqRefl _) hC.eqSymm hi))).eqTrans (added_lookup _ _ _ _ hi).eqSymm)
theorem added_join_right (h A B C D i : PTm n) (hA : Γ ⊢[PRAAx] length A ≐ width h)
    (hB : Γ ⊢[PRAAx] length B ≐ width h) (hC : Γ ⊢[PRAAx] length C ≐ width h)
    (hD : Γ ⊢[PRAAx] length D ≐ width h) (hi : Γ ⊢[PRAAx] lt i (width h)) : Γ ⊢[PRAAx]
    entry (added (succ h) (append A B) (append C D)) (width h+i) ≐ entry (added h B D) i :=
  (added_lookup _ _ _ _ (right_half_bound h i hi)).eqTrans
    ((RationalAlgebra.add_congr
      ((entry_congr (.eqRefl _) (congrAdd hA.eqSymm (.eqRefl _))).eqTrans (append_right (lt_congr (.eqRefl _) hB.eqSymm hi)))
      ((entry_congr (.eqRefl _) (congrAdd hC.eqSymm (.eqRefl _))).eqTrans (append_right (lt_congr (.eqRefl _) hD.eqSymm hi)))).eqTrans
        (added_lookup _ _ _ _ hi).eqSymm)
theorem negated_join_left (h A B i : PTm n) (hA : Γ ⊢[PRAAx] length A ≐ width h)
    (hi : Γ ⊢[PRAAx] lt i (width h)) : Γ ⊢[PRAAx]
    entry (negated (succ h) (append A B)) i ≐ entry (negated h A) i :=
  (negated_lookup _ _ _ (lt_of_lt_of_le hi (width_le_next h))).eqTrans
    ((RationalAlgebra.negative_congr (append_left (lt_congr (.eqRefl _) hA.eqSymm hi))).eqTrans (negated_lookup _ _ _ hi).eqSymm)
theorem negated_join_right (h A B i : PTm n) (hA : Γ ⊢[PRAAx] length A ≐ width h)
    (hB : Γ ⊢[PRAAx] length B ≐ width h) (hi : Γ ⊢[PRAAx] lt i (width h)) : Γ ⊢[PRAAx]
    entry (negated (succ h) (append A B)) (width h+i) ≐ entry (negated h B) i :=
  (negated_lookup _ _ _ (right_half_bound h i hi)).eqTrans
    ((RationalAlgebra.negative_congr ((entry_congr (.eqRefl _) (congrAdd hA.eqSymm (.eqRefl _))).eqTrans
      (append_right (lt_congr (.eqRefl _) hB.eqSymm hi)))).eqTrans (negated_lookup _ _ _ hi).eqSymm)

theorem added_commutative_at (h A B i : PTm n) (hi : Γ ⊢[PRAAx] lt i (width h)) : Γ ⊢[PRAAx]
    entry (added h A B) i ≐ entry (added h B A) i :=
  (added_lookup _ _ _ _ hi).eqTrans ((RationalAlgebra.add_commutative _ _).eqTrans (added_lookup _ _ _ _ hi).eqSymm)
theorem added_associative_at (h A B C i : PTm n) (hi : Γ ⊢[PRAAx] lt i (width h)) : Γ ⊢[PRAAx]
    entry (added h (added h A B) C) i ≐ entry (added h A (added h B C)) i :=
  (added_lookup _ _ _ _ hi).eqTrans
    ((RationalAlgebra.add_congr (added_lookup _ _ _ _ hi) (.eqRefl _)).eqTrans
      ((RationalAlgebra.add_associative _ _ _).eqTrans
        ((RationalAlgebra.add_congr (.eqRefl _) (added_lookup _ _ _ _ hi).eqSymm).eqTrans (added_lookup _ _ _ _ hi).eqSymm)))
theorem negated_involution_at (h A i : PTm n) (hi : Γ ⊢[PRAAx] lt i (width h)) : Γ ⊢[PRAAx]
    entry (negated h (negated h A)) i ≐ RationalArithmetic.recode (entry A i) :=
  (negated_lookup _ _ _ hi).eqTrans
    ((RationalAlgebra.negative_congr (negated_lookup _ _ _ hi)).eqTrans (RationalAlgebra.negative_involution _))

def addNested (h x y : PTm n) : PTm n := added h (flatten h x) (flatten h y)
def negativeNested (h x : PTm n) : PTm n := negated h (flatten h x)
ipra_subst addNested
ipra_subst negativeNested
theorem add_nested_length (h x y : PTm n) : Γ ⊢[PRAAx] length (addNested h x y) ≐ width h := added_length _ _ _
theorem negative_nested_length (h x : PTm n) : Γ ⊢[PRAAx] length (negativeNested h x) ≐ width h := negated_length _ _
theorem base_index : Γ ⊢[PRAAx] lt (zero : PTm n) (width zero) :=
  lt_congr (.eqRefl _) QuadraticTowerCoefficients.width_zero.eqSymm (le_refl one)
theorem add_nested_zero (x y : PTm n) : Γ ⊢[PRAAx]
    entry (addNested zero x y) zero ≐ RationalArithmetic.add x y :=
  (added_lookup _ _ _ _ base_index).eqTrans
    (RationalAlgebra.add_congr (QuadraticTowerCoefficients.flatten_base_entry x) (QuadraticTowerCoefficients.flatten_base_entry y))
theorem negative_nested_zero (x : PTm n) : Γ ⊢[PRAAx]
    entry (negativeNested zero x) zero ≐ RationalArithmetic.negative x :=
  (negated_lookup _ _ _ base_index).eqTrans (RationalAlgebra.negative_congr (QuadraticTowerCoefficients.flatten_base_entry x))
theorem add_nested_left (h x y i : PTm n) (hi : Γ ⊢[PRAAx] lt i (width h)) : Γ ⊢[PRAAx]
    entry (addNested (succ h) x y) i ≐ entry (addNested h (fstT x) (fstT y)) i :=
  (entry_congr (added_congr (.eqRefl _) (flatten_succ h x) (flatten_succ h y)) (.eqRefl _)).eqTrans
    (added_join_left _ _ _ _ _ _ (flatten_length _ _) (flatten_length _ _) hi)
theorem add_nested_right (h x y i : PTm n) (hi : Γ ⊢[PRAAx] lt i (width h)) : Γ ⊢[PRAAx]
    entry (addNested (succ h) x y) (width h+i) ≐ entry (addNested h (sndT x) (sndT y)) i :=
  (entry_congr (added_congr (.eqRefl _) (flatten_succ h x) (flatten_succ h y)) (.eqRefl _)).eqTrans
    (added_join_right _ _ _ _ _ _ (flatten_length _ _) (flatten_length _ _) (flatten_length _ _) (flatten_length _ _) hi)
theorem negative_nested_left (h x i : PTm n) (hi : Γ ⊢[PRAAx] lt i (width h)) : Γ ⊢[PRAAx]
    entry (negativeNested (succ h) x) i ≐ entry (negativeNested h (fstT x)) i :=
  (entry_congr (negated_congr (.eqRefl _) (flatten_succ h x)) (.eqRefl _)).eqTrans
    (negated_join_left _ _ _ _ (flatten_length _ _) hi)
theorem negative_nested_right (h x i : PTm n) (hi : Γ ⊢[PRAAx] lt i (width h)) : Γ ⊢[PRAAx]
    entry (negativeNested (succ h) x) (width h+i) ≐ entry (negativeNested h (sndT x)) i :=
  (entry_congr (negated_congr (.eqRefl _) (flatten_succ h x)) (.eqRefl _)).eqTrans
    (negated_join_right _ _ _ _ (flatten_length _ _) (flatten_length _ _) hi)
theorem add_first_extension_first (x y : PTm n) : Γ ⊢[PRAAx]
    entry (addNested one x y) zero ≐ fstT (QuadraticRationalPairArithmetic.add x y) :=
  ((add_nested_left zero x y zero base_index).eqTrans (add_nested_zero _ _)).eqTrans (fst_pair _ _).eqSymm
theorem add_first_extension_second (x y : PTm n) : Γ ⊢[PRAAx]
    entry (addNested one x y) one ≐ sndT (QuadraticRationalPairArithmetic.add x y) :=
  ((entry_congr (.eqRefl _) ((add_zero _).eqTrans QuadraticTowerCoefficients.width_zero).eqSymm).eqTrans
    ((add_nested_right zero x y zero base_index).eqTrans (add_nested_zero _ _))).eqTrans (snd_pair _ _).eqSymm
theorem negative_first_extension_first (x : PTm n) : Γ ⊢[PRAAx]
    entry (negativeNested one x) zero ≐ fstT (QuadraticRationalPairArithmetic.negative x) :=
  ((negative_nested_left zero x zero base_index).eqTrans (negative_nested_zero _)).eqTrans (fst_pair _ _).eqSymm
theorem negative_first_extension_second (x : PTm n) : Γ ⊢[PRAAx]
    entry (negativeNested one x) one ≐ sndT (QuadraticRationalPairArithmetic.negative x) :=
  ((entry_congr (.eqRefl _) ((add_zero _).eqTrans QuadraticTowerCoefficients.width_zero).eqSymm).eqTrans
    ((negative_nested_right zero x zero base_index).eqTrans (negative_nested_zero _))).eqTrans (snd_pair _ _).eqSymm

def addF : PR 3 := PTm.toPR (added (var 0) (var 1) (var 2))
def negativeF : PR 2 := PTm.toPR (negated (var 0) (var 1))
def output (h x y : PTm n) : PTm n := pairT (addNested h x y) (pairT (negativeNested h x) (width h))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (h x y : PTm n) : PTm n := ap3 outputF h x y
ipra_subst output
ipra_subst run
theorem add_program_at (h A B : PTm n) : Γ ⊢[PRAAx] ap3 addF h A B ≐ added h A B := by
  simpa [addF,ap3] using toPR_eq (Γ := Γ) (added (var 0) (var 1) (var 2) : PTm 3) ![h,A,B]
theorem negative_program_at (h A : PTm n) : Γ ⊢[PRAAx] ap2 negativeF h A ≐ negated h A := by
  simpa [negativeF,ap2] using toPR_eq (Γ := Γ) (negated (var 0) (var 1) : PTm 2) ![h,A]
theorem program_at (h x y : PTm n) : Γ ⊢[PRAAx] run h x y ≐ output h x y := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![h,x,y]
theorem returned_add (h x y : PTm n) : Γ ⊢[PRAAx] fstT (run h x y) ≐ addNested h x y :=
  (program_at _ _ _).fstE
theorem returned_negative (h x y : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run h x y)) ≐ negativeNested h x :=
  (program_at _ _ _).sndE.fstE
theorem returned_width (h x y : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run h x y)) ≐ width h :=
  (program_at _ _ _).sndE.sndE
theorem returned_lengths (h x y : PTm n) : Γ ⊢[PRAAx]
    length (fstT (run h x y)) ≐ width h ⋏ length (fstT (sndT (run h x y))) ≐ width h :=
  .andI ((congrFst (returned_add _ _ _)).eqTrans (add_nested_length _ _ _))
    ((congrFst (returned_negative _ _ _)).eqTrans (negative_nested_length _ _))

theorem actual_tower_array_lengths_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (added (var 0) (var 1) (var 2)) ≐ width (var 0) ⋏ length (negated (var 0) (var 1)) ≐ width (var 0)) :=
  closeUniv 3 (.andI (added_length _ _ _) (negated_length _ _))
theorem actual_tower_array_add_lookup_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (width (var 0)) ⟶ entry (added (var 0) (var 1) (var 2)) (var 3) ≐
      RationalArithmetic.add (entry (var 1) (var 3)) (entry (var 2) (var 3))) :=
  closeUniv 4 (.impI (added_lookup _ _ _ _ Prf.hyp0))
theorem actual_tower_array_negative_lookup_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (width (var 0)) ⟶ entry (negated (var 0) (var 1)) (var 2) ≐
      RationalArithmetic.negative (entry (var 1) (var 2))) :=
  closeUniv 3 (.impI (negated_lookup _ _ _ Prf.hyp0))
theorem actual_tower_array_canonical_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (width (var 0)) ⟶
      RationalNormalForm.wellFormed (entry (added (var 0) (var 1) (var 2)) (var 3)) ⋏
      RationalNormalForm.wellFormed (entry (negated (var 0) (var 1)) (var 3))) :=
  closeUniv 4 (.impI (.andI (added_canonical_at _ _ _ _ Prf.hyp0) (negated_canonical_at _ _ _ Prf.hyp0)))
theorem actual_tower_add_raw_properness_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (equalValues (var 0) (var 1) (var 2) ⟶ equalValues (var 0) (var 3) (var 4) ⟶
      equalValues (var 0) (added (var 0) (var 1) (var 3)) (added (var 0) (var 2) (var 4))) :=
  closeUniv 5 (.impI (.impI (added_proper _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_tower_negative_raw_properness_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (equalValues (var 0) (var 1) (var 2) ⟶
      equalValues (var 0) (negated (var 0) (var 1)) (negated (var 0) (var 2))) :=
  closeUniv 3 (.impI (negated_proper _ _ _ Prf.hyp0))
theorem actual_nested_tower_add_halves_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (width (var 0)) ⟶
      entry (addNested (succ (var 0)) (var 1) (var 2)) (var 3) ≐
        entry (addNested (var 0) (fstT (var 1)) (fstT (var 2))) (var 3) ⋏
      entry (addNested (succ (var 0)) (var 1) (var 2)) (width (var 0)+var 3) ≐
        entry (addNested (var 0) (sndT (var 1)) (sndT (var 2))) (var 3)) :=
  closeUniv 4 (.impI (.andI (add_nested_left _ _ _ _ Prf.hyp0) (add_nested_right _ _ _ _ Prf.hyp0)))
theorem actual_nested_tower_negative_halves_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (width (var 0)) ⟶
      entry (negativeNested (succ (var 0)) (var 1)) (var 2) ≐
        entry (negativeNested (var 0) (fstT (var 1))) (var 2) ⋏
      entry (negativeNested (succ (var 0)) (var 1)) (width (var 0)+var 2) ≐
        entry (negativeNested (var 0) (sndT (var 1))) (var 2)) :=
  closeUniv 3 (.impI (.andI (negative_nested_left _ _ _ Prf.hyp0) (negative_nested_right _ _ _ Prf.hyp0)))
theorem actual_tower_arithmetic_ground_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (entry (addNested zero (var 0) (var 1)) zero ≐ RationalArithmetic.add (var 0) (var 1) ⋏
      entry (negativeNested zero (var 0)) zero ≐ RationalArithmetic.negative (var 0)) :=
  closeUniv 2 (.andI (add_nested_zero _ _) (negative_nested_zero _))
theorem actual_first_extension_add_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (entry (addNested one (var 0) (var 1)) zero ≐ fstT (QuadraticRationalPairArithmetic.add (var 0) (var 1)) ⋏
      entry (addNested one (var 0) (var 1)) one ≐ sndT (QuadraticRationalPairArithmetic.add (var 0) (var 1))) :=
  closeUniv 2 (.andI (add_first_extension_first _ _) (add_first_extension_second _ _))
theorem actual_first_extension_negative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (entry (negativeNested one (var 0)) zero ≐ fstT (QuadraticRationalPairArithmetic.negative (var 0)) ⋏
      entry (negativeNested one (var 0)) one ≐ sndT (QuadraticRationalPairArithmetic.negative (var 0))) :=
  closeUniv 1 (.andI (negative_first_extension_first _) (negative_first_extension_second _))
theorem actual_tower_add_commutative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (width (var 0)) ⟶ entry (added (var 0) (var 1) (var 2)) (var 3) ≐
      entry (added (var 0) (var 2) (var 1)) (var 3)) :=
  closeUniv 4 (.impI (added_commutative_at _ _ _ _ Prf.hyp0))
theorem actual_tower_add_associative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (var 4) (width (var 0)) ⟶ entry (added (var 0) (added (var 0) (var 1) (var 2)) (var 3)) (var 4) ≐
      entry (added (var 0) (var 1) (added (var 0) (var 2) (var 3))) (var 4)) :=
  closeUniv 5 (.impI (added_associative_at _ _ _ _ _ Prf.hyp0))
theorem actual_tower_negative_involution_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (width (var 0)) ⟶ entry (negated (var 0) (negated (var 0) (var 1))) (var 2) ≐
      RationalArithmetic.recode (entry (var 1) (var 2))) :=
  closeUniv 3 (.impI (negated_involution_at _ _ _ Prf.hyp0))
theorem actual_tower_add_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 addF (var 0) (var 1) (var 2) ≐ added (var 0) (var 1) (var 2)) := closeUniv 3 (add_program_at _ _ _)
theorem actual_tower_negative_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (ap2 negativeF (var 0) (var 1) ≐ negated (var 0) (var 1)) := closeUniv 2 (negative_program_at _ _)
theorem actual_tower_arithmetic_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)
theorem actual_returned_tower_arithmetic_lengths_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (fstT (run (var 0) (var 1) (var 2))) ≐ width (var 0) ⋏
      length (fstT (sndT (run (var 0) (var 1) (var 2)))) ≐ width (var 0)) := closeUniv 3 (returned_lengths _ _ _)

end LeanProofs.IPRA.Algebra.QuadraticTowerCoefficientArithmetic
