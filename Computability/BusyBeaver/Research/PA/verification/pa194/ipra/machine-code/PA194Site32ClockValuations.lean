import PA194Site32ClockTerms
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace PA194Site32PositiveClockCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode PRATermCompilation
open TableDispatch PA194StateOne PA194ZeroRuns PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194StartupSentence
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen

theorem hv (e : Fin 12 → M) (i : Fin 11) : Semiterm.val e Empty.elim (v i) = physicalArgs (fun j : Fin 11 => e j.succ) i := by
  fin_cases i <;> rfl

theorem hv6 (e : Fin 12 → M) (a b c d f g : T) :
    (fun i : Fin 6 => Semiterm.val e Empty.elim (![a,b,c,d,f,g] i)) =
    ![Semiterm.val e Empty.elim a,Semiterm.val e Empty.elim b,Semiterm.val e Empty.elim c,
      Semiterm.val e Empty.elim d,Semiterm.val e Empty.elim f,Semiterm.val e Empty.elim g] := by
  funext i; fin_cases i <;> rfl

theorem hv9 (e : Fin 12 → M) (a b c d f g h i j : T) :
    (fun x : Fin 9 => Semiterm.val e Empty.elim (![a,b,c,d,f,g,h,i,j] x)) =
    ![Semiterm.val e Empty.elim a,Semiterm.val e Empty.elim b,Semiterm.val e Empty.elim c,
      Semiterm.val e Empty.elim d,Semiterm.val e Empty.elim f,Semiterm.val e Empty.elim g,
      Semiterm.val e Empty.elim h,Semiterm.val e Empty.elim i,Semiterm.val e Empty.elim j] := by
  funext x; fin_cases x <;> rfl

theorem hv2 (e : Fin 12 → M) (a b : T) : (fun i : Fin 2 => Semiterm.val e Empty.elim (![a,b] i)) =
    ![Semiterm.val e Empty.elim a,Semiterm.val e Empty.elim b] := by
  funext i; fin_cases i <;> rfl

noncomputable def modelSeed : M :=
  let a0 := (1 : M)+1+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2
  let a4 := a3+a3+1
  let a5 := a4+a4+1
  let a6 := a5+a5+1
  (a6+a6)+(a6+a6)

noncomputable def modelBase (e : Fin 12 → M) : M :=
  let v := physicalArgs (fun i : Fin 11 => e i.succ)
  let l0 := F ones ![e 0,modelSeed]
  let l1 := l0+l0+1
  let l2 := l1+l1+1
  let l3 := l2+l2
  let l4 := F ones ![v 0+1,l3]
  let l5 := l4+l4
  let b0 := F ones ![v 1,l5]
  (b0+b0+1)+(b0+b0+1)

noncomputable def modelQ (e : Fin 12 → M) : M :=
  F ones ![physicalArgs (fun i : Fin 11 => e i.succ) 8,
    F (fileCode 1) ![physicalArgs (fun i : Fin 11 => e i.succ) 9,
      physicalArgs (fun i : Fin 11 => e i.succ) 10]]

theorem hleft (e : Fin 12 → M) : Semiterm.val e Empty.elim leftSeed = modelSeed := by
  dsimp only [modelSeed]
  simp only [leftSeed,twice,succT,A,oneT,valApp2,valOne]
  rfl

theorem hbase (e : Fin 12 → M) : Semiterm.val e Empty.elim baseTerm = modelBase e := by
  dsimp only [modelBase]
  simp only [baseTerm,twice,succT,A,oneT,valApp2,hv e,hleft e,k,Semiterm.val_bvar,valOne]
  rfl

theorem hq (e : Fin 12 → M) : Semiterm.val e Empty.elim qTerm = modelQ e := by
  dsimp only [modelQ]
  simp only [qTerm,valApp2,Semiterm.val_func,Function.comp_def,hv2 e,hv e]

theorem valRev (e : Fin 12 → M) :
    (fun i : Fin 6 => Semiterm.val e Empty.elim (revTerm i)) =
      ![physicalArgs (fun j : Fin 11 => e j.succ) 6,
        physicalArgs (fun j : Fin 11 => e j.succ) 5,
        physicalArgs (fun j : Fin 11 => e j.succ) 4,
        physicalArgs (fun j : Fin 11 => e j.succ) 3,
        physicalArgs (fun j : Fin 11 => e j.succ) 2,modelBase e] := by
  funext i
  fin_cases i <;> first | exact hv e _ | exact hbase e

theorem valVec (e : Fin 12 → M) :
    (fun i : Fin 9 => Semiterm.val e Empty.elim (vecTerm i)) =
      ![physicalArgs (fun j : Fin 11 => e j.succ) 0,
        physicalArgs (fun j : Fin 11 => e j.succ) 1,
        physicalArgs (fun j : Fin 11 => e j.succ) 2,
        physicalArgs (fun j : Fin 11 => e j.succ) 3,
        physicalArgs (fun j : Fin 11 => e j.succ) 4,
        physicalArgs (fun j : Fin 11 => e j.succ) 5,
        physicalArgs (fun j : Fin 11 => e j.succ) 6,
        physicalArgs (fun j : Fin 11 => e j.succ) 7,
        (modelQ e+modelQ e)+(modelQ e+modelQ e)] := by
  funext i
  fin_cases i <;> simp [vecTerm,twice,A,valApp2,hv e,hq e] <;> rfl

theorem valCr (e : Fin 12 → M) :
    Semiterm.val e Empty.elim crTerm =
      (modelNumeral M 2+((physicalArgs (fun j : Fin 11 => e j.succ) 7+1)+1))+
        F (PA194CarryFile.costCode 5) ![physicalArgs (fun j : Fin 11 => e j.succ) 6,
          physicalArgs (fun j : Fin 11 => e j.succ) 5,physicalArgs (fun j : Fin 11 => e j.succ) 4,
          physicalArgs (fun j : Fin 11 => e j.succ) 3,physicalArgs (fun j : Fin 11 => e j.succ) 2,modelBase e] := by
  simp only [crTerm,A,succT,oneT,num,valApp2,valOne,valState,hv e 7,Semiterm.val_func,Function.comp_def,valRev e]
  rfl

theorem valCarry (e : Fin 12 → M) :
    Semiterm.val e Empty.elim carryTerm =
      ((e 0+1)+F (PA194CarryFile.costCode 8) ![physicalArgs (fun j : Fin 11 => e j.succ) 0,
        physicalArgs (fun j : Fin 11 => e j.succ) 1,physicalArgs (fun j : Fin 11 => e j.succ) 2,
        physicalArgs (fun j : Fin 11 => e j.succ) 3,physicalArgs (fun j : Fin 11 => e j.succ) 4,
        physicalArgs (fun j : Fin 11 => e j.succ) 5,physicalArgs (fun j : Fin 11 => e j.succ) 6,
        physicalArgs (fun j : Fin 11 => e j.succ) 7,(modelQ e+modelQ e)+(modelQ e+modelQ e)])+modelNumeral M 2 := by
  simp only [carryTerm,A,succT,oneT,num,k,valApp2,valOne,valState,Semiterm.val_bvar,
    Semiterm.val_func,Function.comp_def,valVec e]
  rfl

#print axioms hbase
#print axioms hq
end models
end PA194Site32PositiveClockCode
