import PA194SourceHead1Syntax
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace PA194SourceHead1Logic
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

lemma head1_logic (R P D : Bootstrapping.Formula M ℒₒᵣ)
    (R1 D1 : Bootstrapping.Semiformula M ℒₒᵣ 1) (hR : R1.val = R.val)
    (hRP : (𝗣𝗔 : ArithmeticTheory).internalize M ⊢ R 🡒 P)
    (hD : (𝗣𝗔 : ArithmeticTheory).internalize M ⊢ ∼D) :
    (𝗣𝗔 : ArithmeticTheory).internalize M ⊢ ((∀⁰ (R1 🡒 D1)) 🡒 D) 🡒 P := by
  classical
  let T := (𝗣𝗔 : ArithmeticTheory).internalize M
  let K := ∀⁰ (R1 🡒 D1)
  have hfree : (R1 🡒 D1).free = R.shift 🡒 D1.free := by
    have hr := unbound_free R R1 hR
    simpa [Bootstrapping.Semiformula.free] using congrArg (fun x => x 🡒 D1.free) hr
  have hnk : T ⊢! ∼P 🡒 K := by
    apply FiniteContext.deduct'
    apply TProof.generalize
    rw [hfree]
    apply FiniteContext.deduct
    have hr : [R.shift, (∼P).shift] ⊢[T]! R.shift := FiniteContext.byAxm (by simp)
    have hn : [R.shift, (∼P).shift] ⊢[T]! ∼P.shift := by
      simpa using (FiniteContext.byAxm (by simp) : [R.shift, (∼P).shift] ⊢[T]! (∼P).shift)
    have hrp : [R.shift, (∼P).shift] ⊢[T]! R.shift 🡒 P.shift := by
      have hh : T ⊢! R.shift 🡒 P.shift := by
        simpa only [Bootstrapping.Semiformula.shift_imp] using TProof.shift hRP.some
      exact FiniteContext.of hh
    have hex : T ⊢! ∼P.shift 🡒 P.shift 🡒 D1.free := CNC
    have hex' : [R.shift, (∼P).shift] ⊢[T]! ∼P.shift 🡒 P.shift 🡒 D1.free := FiniteContext.of hex
    have hp' : [R.shift, (∼P).shift] ⊢[T]! P.shift := hrp ⨀ hr
    have hf' : [R.shift, (∼P).shift] ⊢[T]! P.shift 🡒 D1.free := hex' ⨀ hn
    exact hf' ⨀ hp'
  have hkn : T ⊢! (K 🡒 D) 🡒 ∼K := by
    apply FiniteContext.deduct'
    have hk : [K 🡒 D] ⊢[T]! K 🡒 D := FiniteContext.byAxm (by simp)
    have hd : [K 🡒 D] ⊢[T]! ∼D := FiniteContext.of hD.some
    exact contra hk ⨀ hd
  exact ⟨C_of_CNN (C_trans hnk (CN_of_CN_right hkn))⟩

#print axioms head1_logic
end models
end PA194SourceHead1Logic
