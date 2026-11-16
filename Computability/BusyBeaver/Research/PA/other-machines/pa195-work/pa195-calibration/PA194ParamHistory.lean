import PA194StackHistory
import DiophantineConsistency.PRAOpenInduction
import DiophantineConsistency.PRAAddition
import DiophantineConsistency.PRASubAddition

/-! Parameter-preserving reverse histories for generic term closing. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194ParamHistory
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
  PRAModelIOpenPairing PRAExhaustion PRAHerbrandSelection
open PA194StackCode PA194StackHistory PRAOpenInduction PRAAddition PRASubAddition

/-- Update inputs are stage, history, closing label and binder depth. -/
def historyStep (next : Code 4) : Code 4 :=
  bin addCode (bin pairCode next (.proj 1)) (.comp oneCode (.nil 4))
def historyCode (next : Code 4) : Code 3 := .prec (.zero 2) (historyStep next)
def translationCode (next : Code 4) : Code 3 :=
  .comp next (.cons (.proj 0) (.cons (historyCode next)
    (.cons (.proj 1) (.cons (.proj 2) (.nil 3)))))

def reverseBody (next : Code 4) (head tail : Code 1) : Semiformula language Nat 1 :=
  .rel Language.ORing.Rel.eq
    ![.func (lookupCode (stackComponent head) (stackComponent tail))
       ![.bvar 0, .func (historyCode next)
          ![.func Code.succ ![.func addCode ![.fvar 0,.bvar 0]],.fvar 1,.fvar 2]],
      .func next ![.fvar 0,.func (historyCode next) ![.fvar 0,.fvar 1,.fvar 2],.fvar 1,.fvar 2]]
theorem reverseBody_open (next : Code 4) (head tail : Code 1) : (reverseBody next head tail).Open := by
  simp [reverseBody,Semiformula.Open]

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

theorem modelBase (next : Code 4) (label depth : M) :
    F (historyCode next) ![0,label,depth] = 0 := by
  have h := PRAAddOne.modelBase (M := M) (.zero 2) (historyStep next) ![label,depth]
  change F (historyCode next) ![0,label,depth] = F (.zero 2) ![label,depth] at h
  rw [PRAMultiplication.modelZero] at h
  exact h

theorem modelStep (next : Code 4) (n label depth : M) :
    F (historyCode next) ![n+1,label,depth] =
      pair (F next ![n,F (historyCode next) ![n,label,depth],label,depth])
        (F (historyCode next) ![n,label,depth]) + 1 := by
  have h := PRAAddOne.modelStep (M := M) (.zero 2) (historyStep next) ![n,label,depth]
  change F (historyCode next) ![F Code.succ (fun _ => n),label,depth] =
    F (historyStep next) ![n,F (historyCode next) ![n,label,depth],label,depth] at h
  change F (historyCode next) ![F addCode ![n,F oneCode Fin.elim0],label,depth] = _
  rw [modelAddOne,h,historyStep,modelBin,modelBin,modelPairCode,modelProjection]
  have hc : F (.comp oneCode (.nil 4)) ![n,F (historyCode next) ![n,label,depth],label,depth] = (1 : M) := by
    rw [modelComposition]
    congr 1
    exact Subsingleton.elim _ _
  rw [hc]
  rfl

theorem modelTranslation (next : Code 4) (n label depth : M) :
    F (translationCode next) ![n,label,depth] =
      F next ![n,F (historyCode next) ![n,label,depth],label,depth] := by
  rw [translationCode,modelComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact modelProjection 0 _
  · refine Fin.cases rfl (fun k => ?_) j
    refine Fin.cases ?_ (fun l => ?_) k
    · exact modelProjection 1 _
    · exact Fin.cases (modelProjection 2 _) (fun m => Fin.elim0 m) l

theorem modelNewest (next : Code 4) (head tail : Code 1)
    (hhead : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) head)
    (n label depth : M) :
    F (lookupCode (stackComponent head) (stackComponent tail))
      ![0,F (historyCode next) ![n+1,label,depth]] =
      F (translationCode next) ![n,label,depth] := by
  rw [modelStep,modelLookupZero head tail hhead,modelTranslation]

theorem modelEarlier (next : Code 4) (head tail : Code 1)
    (htail : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) tail)
    (n i label depth : M) :
    F (lookupCode (stackComponent head) (stackComponent tail))
      ![i+1,F (historyCode next) ![n+1,label,depth]] =
    F (lookupCode (stackComponent head) (stackComponent tail))
      ![i,F (historyCode next) ![n,label,depth]] := by
  rw [modelStep,modelLookupConsSucc head tail htail]

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem reverseBody_eval (next : Code 4) (head tail : Code 1) (k : M) (e : Nat → M) :
    (reverseBody next head tail).Eval ![k] e ↔
      F (lookupCode (stackComponent head) (stackComponent tail))
        ![k,F (historyCode next) ![F Code.succ (fun _ => F addCode ![e 0,k]),e 1,e 2]] =
      F next ![e 0,F (historyCode next) ![e 0,e 1,e 2],e 1,e 2] := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![k] (reverseBody next head tail) ↔ _
  simp only [reverseBody,Semiformula.EvalAux,eqRel,Matrix.cons_val_zero,Matrix.cons_val_one]
  have h0 : (fun j => Semiterm.val ![k] e
      (![(.bvar 0 : Semiterm language Nat 1),.func (historyCode next)
        ![.func Code.succ ![.func addCode ![.fvar 0,.bvar 0]],.fvar 1,.fvar 2]] j)) =
      ![k,F (historyCode next) ![F Code.succ (fun _ => F addCode ![e 0,k]),e 1,e 2]] := by
    funext j
    refine Fin.cases rfl (fun l => ?_) j
    refine Fin.cases ?_ (fun m => Fin.elim0 m) l
    change F (historyCode next) _ = _
    congr 1
    funext m
    refine Fin.cases ?_ (fun n => ?_) m
    · change F Code.succ _ = _
      congr 1
      funext n
      refine Fin.cases ?_ (fun o => Fin.elim0 o) n
      change F addCode _ = _
      congr 1
      funext o
      refine Fin.cases rfl (fun p => ?_) o
      exact Fin.cases rfl (fun q => Fin.elim0 q) p
    · refine Fin.cases rfl (fun p => ?_) n
      exact Fin.cases rfl (fun q => Fin.elim0 q) p
  have h1 : (fun j => Semiterm.val ![k] e
      (![(.fvar 0 : Semiterm language Nat 1),.func (historyCode next) ![.fvar 0,.fvar 1,.fvar 2],.fvar 1,.fvar 2] j)) =
      ![e 0,F (historyCode next) ![e 0,e 1,e 2],e 1,e 2] := by
    funext j
    refine Fin.cases rfl (fun l => ?_) j
    refine Fin.cases ?_ (fun m => ?_) l
    · change F (historyCode next) _ = _
      congr 1
      funext m
      refine Fin.cases rfl (fun n => ?_) m
      refine Fin.cases rfl (fun p => ?_) n
      exact Fin.cases rfl (fun q => Fin.elim0 q) p
    · refine Fin.cases rfl (fun n => ?_) m
      exact Fin.cases rfl (fun p => Fin.elim0 p) n
  simp only [Semiterm.val_func,Function.comp_def]
  rw [h0,h1]

/-- Stage and reverse index may be nonstandard, while the closing label and
binder depth are carried unchanged through the full primitive recursion. -/
theorem modelHistoryReverse (next : Code 4) (head tail : Code 1)
    (hhead : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) head)
    (htail : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) tail)
    (j k label depth : M) :
    F (lookupCode (stackComponent head) (stackComponent tail))
      ![k,F (historyCode next) ![j+k+1,label,depth]] =
      F (translationCode next) ![j,label,depth] := by
  let e : Nat → M := fun i => if i = 0 then j else if i = 1 then label else depth
  have e0 : e 0 = j := by simp [e]
  have e1 : e 1 = label := by simp [e]
  have e2 : e 2 = depth := by simp [e]
  have main : (reverseBody next head tail).Eval ![k] e := by
    apply modelOpenInduction (M := M) (reverseBody next head tail)
      (reverseBody_open next head tail) e
    · apply (reverseBody_eval next head tail (0 : M) e).mpr
      rw [e0,e1,e2]
      change F (lookupCode (stackComponent head) (stackComponent tail))
        ![F (Code.zero 0) Fin.elim0,F (historyCode next) ![F Code.succ
          (fun _ => F addCode ![j,F (Code.zero 0) Fin.elim0]),label,depth]] =
          F next ![j,F (historyCode next) ![j,label,depth],label,depth]
      rw [modelAddZero, ← modelAddOne]
      rw [← modelTranslation]
      exact modelNewest next head tail hhead j label depth
    · intro i hi
      apply (reverseBody_eval next head tail (F Code.succ (fun _ => i)) e).mpr
      have ih := (reverseBody_eval next head tail i e).mp hi
      rw [e0,e1,e2] at ih ⊢
      change F (lookupCode (stackComponent head) (stackComponent tail))
        ![i,F (historyCode next) ![F Code.succ (fun _ => F addCode ![j,i]),label,depth]] =
          F next ![j,F (historyCode next) ![j,label,depth],label,depth] at ih
      change F (lookupCode (stackComponent head) (stackComponent tail))
        ![F Code.succ (fun _ => i),F (historyCode next) ![F Code.succ
          (fun _ => F addCode ![j,F Code.succ (fun _ => i)]),label,depth]] =
          F next ![j,F (historyCode next) ![j,label,depth],label,depth]
      rw [modelAddSucc, ← modelAddOne, ← modelAddOne, ← modelAddOne]
      change F (lookupCode (stackComponent head) (stackComponent tail))
        ![i+1,F (historyCode next) ![(j+i+1)+1,label,depth]] =
          F next ![j,F (historyCode next) ![j,label,depth],label,depth]
      rw [modelEarlier next head tail htail]
      rw [← modelAddOne] at ih
      change F (lookupCode (stackComponent head) (stackComponent tail))
        ![i,F (historyCode next) ![j+i+1,label,depth]] =
          F next ![j,F (historyCode next) ![j,label,depth],label,depth] at ih
      exact ih
  have h := (reverseBody_eval next head tail k e).mp main
  rw [e0,e1,e2,← modelAddOne,← modelTranslation] at h
  exact h

/-- The explicit distance reads any strictly earlier model stage. -/
theorem modelLookupEarlier (next : Code 4) (head tail : Code 1)
    (hhead : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) head)
    (htail : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) tail)
    (j n label depth : M) (h : j < n) :
    F (lookupCode (stackComponent head) (stackComponent tail))
      ![F distanceCode ![n,j],F (historyCode next) ![n,label,depth]] =
      F (translationCode next) ![j,label,depth] := by
  obtain ⟨k,hk⟩ := le_iff_exists_add.mp (lt_iff_succ_le.mp h)
  have hn : n = j+k+1 := by rw [hk]; ac_rfl
  have hconst : F (.comp oneCode (.nil 2)) ![n,j] = (1 : M) := by
    rw [modelComposition]
    congr 1
    exact Subsingleton.elim _ _
  have hdist : F distanceCode ![n,j] = k := by
    rw [distanceCode, modelBin, modelBin, modelProjection, modelProjection, hconst]
    change F subCode ![n,j+1] = k
    rw [hk]
    exact modelSubAdd (j+1) k
  rw [hdist,hn]
  exact modelHistoryReverse next head tail hhead htail j k label depth

#print axioms modelHistoryReverse
#print axioms modelLookupEarlier

#print axioms reverseBody_eval

#print axioms modelBase
#print axioms modelStep
#print axioms modelTranslation
#print axioms modelNewest
#print axioms modelEarlier
end models
end PA194ParamHistory
