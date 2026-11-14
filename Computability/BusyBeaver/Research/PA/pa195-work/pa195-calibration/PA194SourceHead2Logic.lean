import PA194SourceHead1Preservation
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace PA194SourceHead2Logic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
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

lemma exchange_forall (Q : Bootstrapping.Semiformula M ℒₒᵣ 2) :
    (𝗣𝗔 : ArithmeticTheory).internalize M ⊢ (∀⁰ ∀⁰ Q) 🡒
      ∀⁰ ∀⁰ (Q.subst ![Bootstrapping.Semiterm.bvar 1, Bootstrapping.Semiterm.bvar 0]) := by
  classical
  let T := (𝗣𝗔 : ArithmeticTheory).internalize M
  apply Nonempty.intro
  apply FiniteContext.deduct'
  apply TProof.generalize
  simp only [Bootstrapping.Semiformula.free, Bootstrapping.Semiformula.shift_all, Bootstrapping.Semiformula.substs_all]
  apply TProof.generalize
  have hu : [(∀⁰ ∀⁰ Q).shift.shift] ⊢[T]! ∀⁰ ∀⁰ Q.shift.shift := by
    simpa using (FiniteContext.byAxm (by simp) : [(∀⁰ ∀⁰ Q).shift.shift] ⊢[T]! (∀⁰ ∀⁰ Q).shift.shift)
  have hs1 := TProof.specializeWithCtx hu (Bootstrapping.Semiterm.fvar 0)
  simp only [Bootstrapping.Semiformula.substs_all] at hs1
  have hs := TProof.specializeWithCtx hs1 (Bootstrapping.Semiterm.fvar 1)
  simpa [Bootstrapping.Semiformula.free, Bootstrapping.Semiformula.substs_substs, Bootstrapping.Semiformula.shift_substs, SemitermVec.q, Matrix.vecHead, Matrix.vecTail] using hs
#print axioms exchange_forall
end models
end PA194SourceHead2Logic
