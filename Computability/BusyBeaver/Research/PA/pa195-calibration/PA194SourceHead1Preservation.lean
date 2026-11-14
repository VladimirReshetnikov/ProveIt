import PA194SourceHead1Logic
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace PA194SourceHead1Preservation
open PA194SourceHead1Logic
open PA194SourceHead1Syntax
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
open PA194GenericRenameBase PA194GenericRenameAxiom PA194GenericRenameRules PA194RenameShiftCompatibility PA194ReplacementOpening
open PA194SourceOutputWF PA194SourceRho8Preservation PA194SourceEqualityPreservation PA194SourceHead6Preservation PA194SourceHead5Preservation
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


lemma head1_typed (label h : M) :
    let P : Bootstrapping.Formula M ℒₒᵣ := ⟨translated h, (fixed_all_wf h).1⟩
    let D : Bootstrapping.Formula M ℒₒᵣ := ⟨translated 1, (fixed_all_wf 1).1⟩
    let R : Bootstrapping.Formula M ℒₒᵣ := ⟨translated (allSource label h), (fixed_all_wf _).1⟩
    let R1 : Bootstrapping.Semiformula M ℒₒᵣ 1 := ⟨PA194InternalFormulaClose.close label 0 R.val, by
      simpa using PA194InternalFormulaClose.close_wellformed label 0 R.val R.isSemiformula⟩
    let D1 : Bootstrapping.Semiformula M ℒₒᵣ 1 := ⟨PA194InternalFormulaClose.close label 0 D.val, by
      simpa using PA194InternalFormulaClose.close_wellformed label 0 D.val D.isSemiformula⟩
    (𝗣𝗔 : ArithmeticTheory).internalize M ⊢ ((∀⁰ (R1 🡒 D1)) 🡒 D) 🡒 P := by
  classical
  dsimp only
  let T := (𝗣𝗔 : ArithmeticTheory).internalize M
  let P : Bootstrapping.Formula M ℒₒᵣ := ⟨translated h, (fixed_all_wf h).1⟩
  let D : Bootstrapping.Formula M ℒₒᵣ := ⟨translated 1, (fixed_all_wf 1).1⟩
  let R : Bootstrapping.Formula M ℒₒᵣ := ⟨translated (allSource label h), (fixed_all_wf _).1⟩
  let Q : Bootstrapping.Semiformula M ℒₒᵣ 1 := ⟨PA194InternalFormulaClose.close label 0 P.val, by simpa using PA194InternalFormulaClose.close_wellformed label 0 P.val P.isSemiformula⟩
  let R1 : Bootstrapping.Semiformula M ℒₒᵣ 1 := ⟨PA194InternalFormulaClose.close label 0 R.val, by simpa using PA194InternalFormulaClose.close_wellformed label 0 R.val R.isSemiformula⟩
  let D1 : Bootstrapping.Semiformula M ℒₒᵣ 1 := ⟨PA194InternalFormulaClose.close label 0 D.val, by simpa using PA194InternalFormulaClose.close_wellformed label 0 D.val D.isSemiformula⟩
  change T ⊢ ((∀⁰ (R1 🡒 D1)) 🡒 D) 🡒 P
  have hR : R1.val = R.val := by
    change PA194InternalFormulaClose.close label 0 (translated (allSource label h)) = translated (allSource label h)
    rw [universal_code label h]
    rw [PA194InternalFormulaClose.close_all label 0 _ (PA194InternalFormulaClose.close_wellformed label 0 P.val P.isSemiformula).isUFormula]
    rw [close_formula_twice label 0 P.val P.isSemiformula]
  have hRP : T ⊢ R 🡒 P := by
    apply Nonempty.intro
    apply FiniteContext.deduct'
    have hu : [R] ⊢[T]! ∀⁰ Q := by
      have hx : R = ∀⁰ Q := by
        apply Bootstrapping.Semiformula.ext
        exact universal_code label h
      rw [← hx]
      exact FiniteContext.byAxm (by simp)
    have ho : Q.subst ![Bootstrapping.Semiterm.fvar label] = P := by
      apply Bootstrapping.Semiformula.ext
      change substs1 ℒₒᵣ (^&label) (PA194InternalFormulaClose.close label 0 (translated h)) = translated h
      exact reopen_identity label (translated h) P.isSemiformula
    rw [← ho]
    exact TProof.specializeWithCtx hu (Bootstrapping.Semiterm.fvar label)
  have hD : T ⊢ ∼D := by
    have he : D = bitFormula 0 0 := by
      apply Bootstrapping.Semiformula.ext
      exact one_code
    rw [he]
    simpa [bitFormula] using (PA194InternalBitDiagonal.internal_PA_proves_bit_diag_neg (0 : M))
  exact head1_logic R P D R1 D1 hR hRP hD

noncomputable def exSource (label p : M) : M := impSource (allSource label (impSource p 1)) 1

lemma exSource_nonzero (label p : M) : exSource label p ≠ 0 :=
  imp_nonzero_left _ _ (allSource_nonzero _ _)

lemma head1 (label h : M) : Provable (𝗣𝗔 : ArithmeticTheory)
    (translated (impSource (exSource label (allSource label h)) h)) := by
  have houter := imp_nonzero_left (exSource label (allSource label h)) h (exSource_nonzero _ _)
  have hex := imp_nonzero_left (allSource label (impSource (allSource label h) 1)) 1 (allSource_nonzero _ _)
  have hi := imp_nonzero_left (allSource label h) 1 (allSource_nonzero _ _)
  rw [imp_code _ _ houter]
  unfold exSource
  rw [imp_code _ _ hex, universal_code, imp_code _ _ hi]
  have hr : IsFormula ℒₒᵣ (translated (allSource label h)) := (fixed_all_wf _).1
  have hd : IsFormula ℒₒᵣ (translated (1 : M)) := (fixed_all_wf _).1
  rw [close_imp label (translated (allSource label h)) (translated 1) hr hd]
  exact (tprovable_iff_provable).mp (head1_typed label h)

#print axioms head1
#print axioms head1_typed
end models
end PA194SourceHead1Preservation
