import PA194Site31SentenceClock
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
namespace PA194Site31SentenceRun
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194StateOne PA194UnaryRuns PA194BinaryDouble PA194FiniteControls PA194RegisterFile PA194RegisterPermutation PA194StartupSentence PA194Site31Sentence PA194Site31SentenceVectors PA194Site31SentenceClock
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem valAfter (e : Fin 13 → M) (x : T) :
    Semiterm.val e Empty.elim (afterT x) =
      PA194Site31AfterRun.runAfter (e 10) (e 11) (args e) (Semiterm.val e Empty.elim x) := by
  let v : Fin 11 → M := ![e 2,e 8,e 1,e 4,e 3,e 7,e 0,e 5,e 6,e 12,F PA194OneSpareReturn.repeatOutput ![e 11,(0 : M)]]
  have hv := physicalArgsEval e
  change physicalArgs (args e) = v at hv
  have hE : (fun i : Fin 5 => v ⟨i.val+6,by omega⟩) =
      ![e 0,e 5,e 6,e 12,F PA194OneSpareReturn.repeatOutput ![e 11,(0 : M)]] := by
    funext i
    fin_cases i <;> rfl
  have h4 : (fun i : Fin 4 => v ⟨i.succ.val+6,by omega⟩) =
      ![e 5,e 6,e 12,F PA194OneSpareReturn.repeatOutput ![e 11,(0 : M)]] := by
    funext i
    fin_cases i <;> rfl
  dsimp only [PA194Site31AfterRun.runAfter]
  rw [hv,hE,h4]
  have hEP := valEP e
  have htail4 := valFour e
  have he0 : Semiterm.val e Empty.elim (E 0) = e 0 := rfl
  simp only [afterT,coreFor,run,front,cc3,cc6,PA194StartupSentence.valApp2,Semiterm.val_func,Function.comp_def,hEP,htail4,he0]
  simp [rc,plus1,twice,A,k,count,c,PA194StartupSentence.valApp2,PA194StartupSentence.valState,
    PA194StartupSentence.valOne,Semiterm.val_bvar,Semiterm.val_func,Function.comp_def,v,he0,htail4]
  rfl
#print axioms valAfter
end models
end PA194Site31SentenceRun
