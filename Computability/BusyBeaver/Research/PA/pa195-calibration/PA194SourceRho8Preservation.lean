import PA194SourceMPPreservation
/-! Internal PA proves every numerical rho8 axiom translation, including
nonstandard instances and the zero-implication alias. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194SourceRho8Preservation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.Entailment
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
open PA194CanonicalDualForall PA194DualRecursion PA194DualQuantRecursion PA194DualAtomCode
  PA194TagDecoder PA194ChildCodes PA194SourceOutputWF PA194SourcePolarity
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

noncomputable def impSource (a b : M) : M := 4*cantor a b
noncomputable def translated (x : M) : M := π₁ (F fixedTranslation (fun _ => x))

lemma translated_zero : translated (0 : M) = ^⊤ := by
  unfold translated fixedTranslation translation dualQuantTranslation
  rw [modelDualZero]
  simp [qqVerum]

lemma zero_provable : Provable (𝗣𝗔 : ArithmeticTheory) (translated (0 : M)) := by
  rw [translated_zero]
  apply Derivable.toProvable
  exact Derivable.verum (by simp) (by simp)

lemma imp_conseq (a b : M) (hb : Provable (𝗣𝗔 : ArithmeticTheory) (translated b)) :
    Provable (𝗣𝗔 : ArithmeticTheory) (translated (impSource a b)) := by
  by_cases hz : impSource a b = 0
  · obtain ⟨rfl,rfl⟩ := PA194SourceMPPreservation.implication_zero a b hz
    simpa [hz] using hb
  · have hnz : 4*cantor a b ≠ 0 := hz
    rw [show translated (impSource a b) = imp ℒₒᵣ (translated a) (translated b) from
      PA194SourceMPPreservation.implication_code a b hnz]
    let φ : Bootstrapping.Formula M ℒₒᵣ := ⟨translated a, (fixed_all_wf a).1⟩
    let ψ : Bootstrapping.Formula M ℒₒᵣ := ⟨translated b, (fixed_all_wf b).1⟩
    have hψ : (𝗣𝗔 : ArithmeticTheory).internalize M ⊢ ψ := (tprovable_iff_provable).mpr hb
    have hp : (𝗣𝗔 : ArithmeticTheory).internalize M ⊢ φ 🡒 ψ := ⟨C_of_conseq hψ.some⟩
    exact (tprovable_iff_provable).mp hp

noncomputable def rho8_tautology (A B C U : Bootstrapping.Formula M ℒₒᵣ) :
    (𝗣𝗔 : ArithmeticTheory).internalize M ⊢! ((C 🡒 U) 🡒 A) 🡒 (A 🡒 C) 🡒 B 🡒 C := by
  classical
  let T := (𝗣𝗔 : ArithmeticTheory).internalize M
  let X := C 🡒 U
  have comp : T ⊢! (X 🡒 A) 🡒 (A 🡒 C) 🡒 X 🡒 C := by
    apply FiniteContext.deduct'
    apply FiniteContext.deduct
    have hXA : [A 🡒 C, X 🡒 A] ⊢[T]! X 🡒 A := FiniteContext.byAxm (by simp)
    have hAC : [A 🡒 C, X 🡒 A] ⊢[T]! A 🡒 C := FiniteContext.byAxm (by simp)
    exact C_trans hXA hAC
  have finish : T ⊢! (X 🡒 C) 🡒 B 🡒 C := C_trans peirce implyK
  have lift1 : T ⊢! ((A 🡒 C) 🡒 X 🡒 C) 🡒 (A 🡒 C) 🡒 B 🡒 C := implyS ⨀ C_of_conseq finish
  have lift2 : T ⊢! ((X 🡒 A) 🡒 (A 🡒 C) 🡒 X 🡒 C) 🡒 (X 🡒 A) 🡒 (A 🡒 C) 🡒 B 🡒 C := implyS ⨀ C_of_conseq lift1
  exact lift2 ⨀ comp

#print axioms rho8_tautology
lemma imp_nonzero_left (a b : M) (ha : a ≠ 0) : impSource a b ≠ 0 := by
  intro h
  exact ha (PA194SourceMPPreservation.implication_zero a b h).1

lemma imp_nonzero_right (a b : M) (hb : b ≠ 0) : impSource a b ≠ 0 := by
  intro h
  exact hb (PA194SourceMPPreservation.implication_zero a b h).2

lemma imp_code (a b : M) (hnz : impSource a b ≠ 0) :
    translated (impSource a b) = imp ℒₒᵣ (translated a) (translated b) :=
  PA194SourceMPPreservation.implication_code a b hnz

lemma rho8_nonzero (a b c u : M) (hc : c ≠ 0) : Provable (𝗣𝗔 : ArithmeticTheory)
    (translated (impSource (impSource (impSource c u) a) (impSource (impSource a c) (impSource b c)))) := by
  have hcu : impSource c u ≠ 0 := imp_nonzero_left c u hc
  have hac : impSource a c ≠ 0 := imp_nonzero_right a c hc
  have hbc : impSource b c ≠ 0 := imp_nonzero_right b c hc
  have hleft : impSource (impSource c u) a ≠ 0 := imp_nonzero_left _ _ hcu
  have hright : impSource (impSource a c) (impSource b c) ≠ 0 := imp_nonzero_left _ _ hac
  have houter : impSource (impSource (impSource c u) a) (impSource (impSource a c) (impSource b c)) ≠ 0 := imp_nonzero_left _ _ hleft
  rw [imp_code _ _ houter, imp_code _ _ hleft, imp_code _ _ hcu,
    imp_code _ _ hright, imp_code _ _ hac, imp_code _ _ hbc]
  let A : Bootstrapping.Formula M ℒₒᵣ := ⟨translated a, (fixed_all_wf a).1⟩
  let B : Bootstrapping.Formula M ℒₒᵣ := ⟨translated b, (fixed_all_wf b).1⟩
  let C : Bootstrapping.Formula M ℒₒᵣ := ⟨translated c, (fixed_all_wf c).1⟩
  let U : Bootstrapping.Formula M ℒₒᵣ := ⟨translated u, (fixed_all_wf u).1⟩
  change Provable (𝗣𝗔 : ArithmeticTheory) ((((C 🡒 U) 🡒 A) 🡒 (A 🡒 C) 🡒 B 🡒 C).val)
  exact (tprovable_iff_provable).mp ⟨rho8_tautology A B C U⟩

#print axioms rho8_nonzero
lemma rho8_zero (a b u : M) : Provable (𝗣𝗔 : ArithmeticTheory)
    (translated (impSource (impSource (impSource 0 u) a) (impSource (impSource a 0) (impSource b 0)))) := by
  have hb := imp_conseq b 0 (zero_provable (M := M))
  have hc := imp_conseq (impSource a 0) (impSource b 0) hb
  exact imp_conseq (impSource (impSource 0 u) a) (impSource (impSource a 0) (impSource b 0)) hc

lemma rho8 (a b c u : M) : Provable (𝗣𝗔 : ArithmeticTheory)
    (translated (impSource (impSource (impSource c u) a) (impSource (impSource a c) (impSource b c)))) := by
  by_cases hc : c = 0
  · subst c
    exact rho8_zero a b u
  · exact rho8_nonzero a b c u hc

#print axioms rho8
#print axioms rho8_zero
#print axioms imp_conseq
#print axioms zero_provable
end models
end PA194SourceRho8Preservation
