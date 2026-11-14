import PA194SourceRho8Preservation
import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.EquationalTheory
/-! Model-uniform PA proofs of the numerical equality-substitution source
axiom families head3 and head4. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000
namespace PA194SourceEqualityPreservation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
open PA194CanonicalDualForall PA194DualRecursion PA194DualQuantRecursion PA194DualAtomCode
  PA194TagDecoder PA194ChildCodes PA194SourceOutputWF PA194SourcePolarity PA194SourceRho8Preservation PA194TemplateInternal
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def memSource (a b : M) : M := 4*cantor a b+1
noncomputable def eqSource (a b : M) : M := 4*cantor a b+3

noncomputable def bitFormula (a b : M) : Bootstrapping.Formula M ℒₒᵣ :=
  (⌜(Rew.emb ▹ bitDef.val : ArithmeticSemiformula Nat 2)⌝ : Bootstrapping.Semiformula M ℒₒᵣ 2).subst
    ![Bootstrapping.Semiterm.fvar b, Bootstrapping.Semiterm.fvar a]

lemma membership_code (a b : M) : translated (memSource a b) = (bitFormula a b).val := by
  have hm := modelDualMembership fixedTag
    PA194TermWellFormedUnconditional.canonicalFirst PA194TermWellFormedUnconditional.canonicalSecond
    fixedFirst fixedSecond PA194CanonicalDualForall.canonical (Classical.choose_spec PRA_has_tagCode).2
    (Classical.choose_spec PRA_has_firstChildCode).2 (Classical.choose_spec PRA_has_secondChildCode).2 a b
  change F fixedTranslation (fun _ => memSource a b) = F dualBitCode ![b,a] at hm
  unfold translated
  rw [hm, modelDualBitInternal, pi₁_pair]
  change _ = (Bootstrapping.Semiformula.subst (substEnv b a 0) _).val
  rfl

lemma equality_code (a b : M) : translated (eqSource a b) =
    ((Bootstrapping.Semiterm.fvar a : Bootstrapping.Term M ℒₒᵣ) ≐ Bootstrapping.Semiterm.fvar b).val := by
  have hm := modelDualEquality fixedTag
    PA194TermWellFormedUnconditional.canonicalFirst PA194TermWellFormedUnconditional.canonicalSecond
    fixedFirst fixedSecond PA194CanonicalDualForall.canonical (Classical.choose_spec PRA_has_tagCode).2
    (Classical.choose_spec PRA_has_firstChildCode).2 (Classical.choose_spec PRA_has_secondChildCode).2 a b
  change F fixedTranslation (fun _ => eqSource a b) = F dualEqCode ![a,b] at hm
  unfold translated
  rw [hm, modelDualEqInternal, pi₁_pair]
  have heq : Encodable.encode (Language.Eq.eq : (ℒₒᵣ : Language).Rel 2) = 0 := by decide
  simp [Arithmetic.qqEQ, Arithmetic.eqIndex, heq]

lemma memSource_nonzero (a b : M) : memSource a b ≠ 0 := by
  have hpos : (0 : M) < 1 := by norm_num
  have hle : (1 : M) ≤ memSource a b := by unfold memSource; exact le_add_self
  exact ne_of_gt (lt_of_lt_of_le hpos hle)

lemma eqSource_nonzero (a b : M) : eqSource a b ≠ 0 := by
  have hpos : (0 : M) < 3 := by norm_num
  have hle : (3 : M) ≤ eqSource a b := by unfold eqSource; exact le_add_self
  exact ne_of_gt (lt_of_lt_of_le hpos hle)

lemma bit_replace_second (h d a : M) :
    (𝗣𝗔 : ArithmeticTheory).internalize M ⊢
      (bitFormula h d) 🡒 ((Bootstrapping.Semiterm.fvar h : Bootstrapping.Term M ℒₒᵣ) ≐ Bootstrapping.Semiterm.fvar a) 🡒 bitFormula a d := by
  classical
  let T := (𝗣𝗔 : ArithmeticTheory)
  let B : Bootstrapping.Semiformula M ℒₒᵣ 2 := ⌜(Rew.emb ▹ bitDef.val : ArithmeticSemiformula Nat 2)⌝
  let P : Bootstrapping.Semiformula M ℒₒᵣ 1 := B.subst ![Bootstrapping.Semiterm.fvar d, Bootstrapping.Semiterm.bvar 0]
  have hrep := Bootstrapping.Arithmetic.replace T P (Bootstrapping.Semiterm.fvar h) (Bootstrapping.Semiterm.fvar a)
  have hrep' : T.internalize M ⊢
      ((Bootstrapping.Semiterm.fvar h : Bootstrapping.Term M ℒₒᵣ) ≐ Bootstrapping.Semiterm.fvar a) 🡒 bitFormula h d 🡒 bitFormula a d := by
    simpa [P,B,bitFormula, Bootstrapping.Semiformula.substs_substs, Matrix.vecHead, Matrix.vecTail] using hrep
  exact C!_swap hrep'

lemma head3 (h d a : M) : Provable (𝗣𝗔 : ArithmeticTheory)
    (translated (impSource (memSource h d) (impSource (eqSource h a) (memSource a d)))) := by
  have hinner : impSource (eqSource h a) (memSource a d) ≠ 0 := imp_nonzero_left _ _ (eqSource_nonzero h a)
  have houter : impSource (memSource h d) (impSource (eqSource h a) (memSource a d)) ≠ 0 := imp_nonzero_left _ _ (memSource_nonzero h d)
  rw [imp_code _ _ houter, imp_code _ _ hinner, membership_code, membership_code, equality_code]
  change Provable (𝗣𝗔 : ArithmeticTheory) (((bitFormula h d) 🡒
    ((Bootstrapping.Semiterm.fvar h : Bootstrapping.Term M ℒₒᵣ) ≐ Bootstrapping.Semiterm.fvar a) 🡒 bitFormula a d).val)
  exact (tprovable_iff_provable).mp (bit_replace_second h d a)

lemma bit_replace_first (h d a : M) :
    (𝗣𝗔 : ArithmeticTheory).internalize M ⊢
      ((Bootstrapping.Semiterm.fvar h : Bootstrapping.Term M ℒₒᵣ) ≐ Bootstrapping.Semiterm.fvar d) 🡒 bitFormula a h 🡒 bitFormula a d := by
  let T := (𝗣𝗔 : ArithmeticTheory)
  let B : Bootstrapping.Semiformula M ℒₒᵣ 2 := ⌜(Rew.emb ▹ bitDef.val : ArithmeticSemiformula Nat 2)⌝
  let P : Bootstrapping.Semiformula M ℒₒᵣ 1 := B.subst ![Bootstrapping.Semiterm.bvar 0, Bootstrapping.Semiterm.fvar a]
  have hrep := Bootstrapping.Arithmetic.replace T P (Bootstrapping.Semiterm.fvar h) (Bootstrapping.Semiterm.fvar d)
  simpa [P,B,bitFormula, Bootstrapping.Semiformula.substs_substs, Matrix.vecHead, Matrix.vecTail] using hrep

lemma head4 (h d a : M) : Provable (𝗣𝗔 : ArithmeticTheory)
    (translated (impSource (eqSource h d) (impSource (memSource a h) (memSource a d)))) := by
  have hinner : impSource (memSource a h) (memSource a d) ≠ 0 := imp_nonzero_left _ _ (memSource_nonzero a h)
  have houter : impSource (eqSource h d) (impSource (memSource a h) (memSource a d)) ≠ 0 := imp_nonzero_left _ _ (eqSource_nonzero h d)
  rw [imp_code _ _ houter, imp_code _ _ hinner, membership_code, membership_code, equality_code]
  change Provable (𝗣𝗔 : ArithmeticTheory) ((((Bootstrapping.Semiterm.fvar h : Bootstrapping.Term M ℒₒᵣ) ≐
    Bootstrapping.Semiterm.fvar d) 🡒 bitFormula a h 🡒 bitFormula a d).val)
  exact (tprovable_iff_provable).mp (bit_replace_first h d a)

#print axioms head4
#print axioms bit_replace_first
#print axioms head3
#print axioms bit_replace_second
#print axioms membership_code
#print axioms equality_code
end models
end PA194SourceEqualityPreservation
