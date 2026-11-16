import PA194Site31SentenceDefs
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace PA194Site31SentenceVectors
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode PA194StartupSentence PA194Site31Sentence PA194OneSpareReturn
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local notation "F" => Structure.func (L := language)
theorem valSuffix (e : Fin 13 → M) :
    Semiterm.val e Empty.elim (app2 repeatOutput count (c 0)) = F repeatOutput ![e 11,(0 : M)] := by
  rw [PA194StartupSentence.valApp2]
  simp only [count,Semiterm.val_bvar,c,valState]
  rfl

theorem valFive (e : Fin 13 → M) :
    (fun i : Fin 5 => Semiterm.val e Empty.elim (E i)) =
      ![e 0,e 5,e 6,e 12,F repeatOutput ![e 11,(0 : M)]] := by
  funext i
  fin_cases i <;> first | rfl | exact valSuffix e

theorem valFour (e : Fin 13 → M) :
    (fun i : Fin 4 => Semiterm.val e Empty.elim ((![E 1,E 2,E 3,E 4] : Fin 4 → T) i)) =
      ![e 5,e 6,e 12,F repeatOutput ![e 11,(0 : M)]] := by
  funext i
  fin_cases i <;> first | rfl | exact valSuffix e

theorem valEP (e : Fin 13 → M) :
    (fun i : Fin 7 => Semiterm.val e Empty.elim (EP i)) =
      ![e 2,e 8,e 1,e 4,e 3,e 7,F (PA194MarkedFile.markedFile 3)
        ![e 0,e 5,e 6,e 12,F repeatOutput ![e 11,(0 : M)]]] := by
  funext i
  fin_cases i <;> first
    | rfl
    | (change Semiterm.val e Empty.elim marked = _
       rw [marked,Semiterm.val_func]
       change F (PA194MarkedFile.markedFile 3) (fun i => Semiterm.val e Empty.elim (E i)) = _
       rw [valFive]
       rfl)

theorem valRev (e : Fin 13 → M) :
    (fun i : Fin 6 => Semiterm.val e Empty.elim ((![V 4,V 3,V 2,V 1,V 0,base] : Fin 6 → T) i)) =
      ![e 3,e 4,e 1,e 8,e 2,Semiterm.val e Empty.elim base] := by
  funext i
  fin_cases i <;> rfl
#print axioms valSuffix
#print axioms valFive
#print axioms valFour
#print axioms valEP
#print axioms valRev
end models
end PA194Site31SentenceVectors
