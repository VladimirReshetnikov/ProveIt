import PA194OneSpareIterate
import PA194ReturnFileMeaning
import PA194ReturnCell
import PA194RegisterFile
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 12000000
namespace PA194OneSpareReturn
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion PRABooleanOps PRAIsZero PRAOpenInduction
open BinaryTapeCodes PackedDecoderModel PA194FiniteControls PA194BinaryDouble PA194StateOne PA194GenericRightScan PA194UnaryRuns PA194OneSpareIterate PA194ReturnCell PA194RegisterFile PA194Stepper TableDispatch

def outputBlock : Code 1 := bin block (unary (constantCode 1) (.zero 1)) (.proj 0)
def outputBody : Code 3 := unary outputBlock (.proj 1)
def repeatOutput : Code 2 := .prec (.proj 0) outputBody

def ix : Semiterm language Nat 1 := .bvar 0
def total : Semiterm language Nat 1 := .fvar 0
def left : Semiterm language Nat 1 := .fvar 1
def right : Semiterm language Nat 1 := .fvar 2
def state7 : Semiterm language Nat 1 := PA194GenericRightScan.state 7
def app1 (f : Code 1) (a : Semiterm language Nat 1) : Semiterm language Nat 1 := .func f ![a]
def app2 (f : Code 2) (a b : Semiterm language Nat 1) : Semiterm language Nat 1 := .func f ![a,b]
def plus1 (a : Semiterm language Nat 1) : Semiterm language Nat 1 := app2 addCode a (.func oneCode Fin.elim0)
def twice (a : Semiterm language Nat 1) : Semiterm language Nat 1 := app2 addCode a a
def pack (l r : Semiterm language Nat 1) : Semiterm language Nat 1 := app2 pairCode state7 (app2 pairCode l r)
def time : Semiterm language Nat 1 := app2 addCode (app2 addCode ix ix) ix
def start : Semiterm language Nat 1 := pack (app1 halfCode (app2 repeatBlock total left)) (plus1 (twice right))
def finish : Semiterm language Nat 1 := pack (app1 halfCode (app2 repeatBlock (app2 subCode total ix) left)) (plus1 (twice (app2 repeatOutput ix right)))
def body : Semiformula language Nat 1 := .or
  (.rel Language.ORing.Rel.lt ![total,ix])
  (.rel Language.ORing.Rel.eq ![app2 stepper time start,finish])
theorem body_open : body.Open := by simp [body,Semiformula.Open,Semiformula.qr]
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelOutputBlock (x : M) : F outputBlock (fun _ => x) = F block ![(1 : M),x] := by
  simp only [outputBlock,modelBin,modelUnary,modelProjection,modelConstant,modelNumeralOne]

theorem modelOutputZero (x : M) : F repeatOutput ![(0 : M),x] = x := by
  have h := modelBase (M := M) (Code.proj (0 : Fin 1)) outputBody (fun _ => x)
  rw [modelProjection] at h
  have hs : Fin.cases (F (Code.zero 0) Fin.elim0) (fun _ : Fin 1 => x) = ![(0 : M),x] := by
    funext i; refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [hs] at h
  exact h

theorem modelOutputSucc (n x : M) : F repeatOutput ![F Code.succ (fun _ => n),x] =
    F outputBlock (fun _ => F repeatOutput ![n,x]) := by
  have h := modelStep (M := M) (Code.proj (0 : Fin 1)) outputBody ![n,x]
  have hs : Fin.cases (F Code.succ (fun _ => ![n,x] 0)) (fun i => ![n,x] i.succ) =
      ![F Code.succ (fun _ => n),x] := by
    funext i; refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [hs] at h
  have hv : (fun i : Fin 1 => ![n,x] i.succ) = (fun _ => x) := by
    funext j; exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [hv] at h
  simp only [Matrix.cons_val_zero] at h
  change F repeatOutput ![F Code.succ (fun _ => n),x] = F outputBody
    (Fin.cases n (Fin.cases (F repeatOutput ![n,x]) (fun _ => x))) at h
  rw [h,outputBody,modelUnary,modelProjection]
  rfl

theorem modelRepeatOdd (n l : M) (hl : F parityCode (fun _ => l) = (1 : M)) :
    F parityCode (fun _ => F repeatBlock ![n,l]) = (1 : M) := by
  have he := PRAExhaustion.modelZeroOrSuccPred n
  change n = (0 : M) ∨ F Code.succ (fun _ => F predCode (fun _ => n)) = n at he
  rcases he with hn | hn
  · subst n; rw [modelRepeatZero]; exact hl
  · let u := F predCode (fun _ => n)
    have hn' : n = F Code.succ (fun _ => u) := hn.symm
    rw [hn',modelRepeatSucc,modelOneBlock]
    have h2 : modelNumeral M 2 = F Code.succ (fun _ => (1 : M)) := by
      change F Code.succ (fun _ => modelNumeral M 1) = _
      rw [modelNumeralOne]
    rw [h2,modelOnesSucc,(modelOdd _).1]

theorem returnOne (l t : M) (hl : F parityCode (fun _ => l) = (1 : M)) :
    F stepper ![modelNumeral M 3,F pairCode ![modelNumeral M 7,
      F pairCode ![F halfCode (fun _ => F oneBlock (fun _ => l)),t+t+1]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => l),
      F outputBlock (fun _ => t)+F outputBlock (fun _ => t)+1]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := modelReturnCell (M := M) (1 : M) l t
  dsimp only at h
  rw [hl] at h
  have hhalf : F halfCode (fun _ => F oneBlock (fun _ => l)) = F ones ![(1 : M),l+l] := by
    rw [modelOneBlock]
    have h2 : modelNumeral M 2 = F Code.succ (fun _ => (1 : M)) := by
      change F Code.succ (fun _ => modelNumeral M 1) = _
      rw [modelNumeralOne]
    rw [h2,modelOnesSucc,(modelOdd _).2]
  have hout : F outputBlock (fun _ => t) =
      F ones ![(1 : M),(1 : M)+t+t]+F ones ![(1 : M),(1 : M)+t+t] := by
    rw [modelOutputBlock,←PA194ReturnFileMeaning.modelReturnBlock]
    congr 1 <;> simp only [add_assoc,add_comm,add_left_comm]
  have hclock : modelNumeral M 3 = ((1 : M)+1)+1 := by rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  rw [hhalf,hout,hclock]
  simpa only [add_assoc,add_comm,add_left_comm] using h

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem valApp1 (x : M) (e : Nat → M) (f : Code 1) (a : Semiterm language Nat 1) :
    Semiterm.val ![x] e (app1 f a) = F f (fun _ => Semiterm.val ![x] e a) := by
  simp only [app1,Semiterm.val_func]
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem valApp2 (x : M) (e : Nat → M) (f : Code 2) (a b : Semiterm language Nat 1) :
    Semiterm.val ![x] e (app2 f a b) = F f ![Semiterm.val ![x] e a,Semiterm.val ![x] e b] := by
  simp only [app2,Semiterm.val_func]
  congr 1
  exact val_pair ![x] e a b

theorem body_eval (x : M) (e : Nat → M) : body.Eval ![x] e ↔
    e 0 < x ∨
    F stepper ![(x+x)+x,F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => F repeatBlock ![e 0,e 1]),e 2+e 2+1]]] =
      F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => F repeatBlock ![F subCode ![e 0,x],e 1]),
        F repeatOutput ![x,e 2]+F repeatOutput ![x,e 2]+1]] := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![x] body ↔ _
  simp only [body,Semiformula.EvalAux,eqRel]
  have hv (a b : Semiterm language Nat 1) :
      (fun i => Semiterm.val ![x] e (![a,b] i)) = ![Semiterm.val ![x] e a,Semiterm.val ![x] e b] := by
    exact val_pair ![x] e a b
  rw [hv]
  simp [ix,total,left,right,time,start,finish,pack,state7,plus1,twice,valApp1,valApp2,PA194GenericRightScan.valState,
    Semiterm.val_bvar,Semiterm.val_fvar,Matrix.cons_val_zero,Matrix.cons_val_one]
  have hv0 : (Semiterm.val ![x] e ∘ (Fin.elim0 : Fin 0 → Semiterm language Nat 1)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [hv0]
  rfl

theorem modelPartialReturn (n i l t : M) (hl : F parityCode (fun _ => l) = (1 : M)) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
    i ≤ n →
    F stepper ![(i+i)+i,F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => F repeatBlock ![n,l]),t+t+1]]] =
      F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => F repeatBlock ![F subCode ![n,i],l]),
        F repeatOutput ![i,t]+F repeatOutput ![i,t]+1]] := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let e : Nat → M := fun j => if j=0 then n else if j=1 then l else t
  have h0 : e 0 = n := by simp [e]
  have h1 : e 1 = l := by simp [e]
  have h2 : e 2 = t := by simp [e]
  have main : body.Eval ![i] e := by
    apply modelOpenInduction (M := M) body body_open e
    · apply (body_eval (0 : M) e).mpr
      right
      rw [h0,h1,h2]
      have hz := modelStepperZero (F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => F repeatBlock ![n,l]),t+t+1]])
      change F stepper ![(0 : M),_] = _ at hz
      simp only [zero_add]
      have hsub : F subCode ![n,(0 : M)] = n := PRASubtraction.modelSubZero n
      rw [hz,modelOutputZero,hsub]
    · intro u hu
      apply (body_eval (F Code.succ (fun _ => u)) e).mpr
      rw [h0,h1,h2]
      have hs : F Code.succ (fun _ => u) = u+1 := (modelAddOne u).symm
      rw [hs]
      by_cases hbound : n < u+1
      · exact Or.inl hbound
      · right
        have hle : u+1 ≤ n := le_of_not_gt hbound
        have hu_lt : u < n := lt_of_lt_of_le (lt_add_one u) hle
        have hu' := (body_eval u e).mp hu
        rw [h0,h1,h2] at hu'
        have prev := hu'.resolve_left (not_lt_of_ge (le_of_lt hu_lt))
        have subeq : F subCode ![n,u] = F subCode ![n,u+1] + 1 := by
          rw [modelSubAsTsub,modelSubAsTsub]
          have hn : (u+1) + (n-(u+1)) = n := add_tsub_cancel_of_le hle
          calc
            n-u = ((u+1)+(n-(u+1)))-u := congrArg (fun z => z-u) hn.symm
            _ = (n-(u+1))+1 := by simp [add_assoc,add_comm]
        let a := F repeatBlock ![F subCode ![n,u+1],l]
        let b := F repeatOutput ![u,t]
        have hleft : F repeatBlock ![F subCode ![n,u],l] = F oneBlock (fun _ => a) := by
          rw [subeq]
          rw [show F subCode ![n,u+1]+1 = F Code.succ (fun _ => F subCode ![n,u+1]) from modelAddOne _]
          rw [modelRepeatSucc]
        have hright : F repeatOutput ![u+1,t] = F outputBlock (fun _ => b) := by
          rw [show u+1 = F Code.succ (fun _ => u) from modelAddOne _]
          rw [modelOutputSucc]
        have ha : F parityCode (fun _ => a) = (1 : M) := modelRepeatOdd _ l hl
        have hclock : ((u+1)+(u+1))+(u+1) = ((u+u)+u)+modelNumeral M 3 := by
          rw [show modelNumeral M 3 = (1 : M)+((1 : M)+1) by rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]]
          simp only [add_assoc,add_comm,add_left_comm]
        rw [hclock]
        change F stepper ![F addCode ![(u+u)+u,modelNumeral M 3],_] = _
        rw [PA194StepperCompose.modelStepperCompose,prev,hleft,returnOne _ _ ha,hright]
  have h := (body_eval i e).mp main
  rw [h0,h1,h2] at h
  intro hle
  exact h.resolve_left (not_lt_of_ge hle)

theorem modelFullReturn (n l t : M) (hl : F parityCode (fun _ => l) = (1 : M)) :
    F stepper ![(n+n)+n,F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => F repeatBlock ![n,l]),t+t+1]]] =
      F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => l),F repeatOutput ![n,t]+F repeatOutput ![n,t]+1]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := modelPartialReturn n n l t hl le_rfl
  have hsub : F subCode ![n,n] = (0 : M) := by rw [modelSubAsTsub]; simp
  rw [hsub,modelRepeatZero] at h
  exact h
#print axioms modelOutputBlock
#print axioms modelOutputZero
#print axioms modelOutputSucc
#print axioms modelRepeatOdd
#print axioms returnOne
#print axioms modelPartialReturn
#print axioms modelFullReturn
end models
end PA194OneSpareReturn
