import PA194GenericRightScan
import PA194Site28CarryCell
import DiophantineConsistency.PRAOpenInduction
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 12000000
namespace PA194OneSpareIterate
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion PRABooleanOps PRAIsZero PRAOpenInduction
open PackedDecoderModel PA194FiniteControls PA194BinaryDouble PA194StateOne PA194GenericRightScan PA194UnaryRuns PA194Site28CarryCell PA194Stepper TableDispatch

def oneBlock : Code 1 := bin ones (unary (constantCode 2) (.zero 1)) (bin addCode (.proj 0) (.proj 0))
def repeatBody : Code 3 := unary oneBlock (.proj 1)
def repeatBlock : Code 2 := .prec (.proj 0) repeatBody

def ix : Semiterm language Nat 1 := .bvar 0
def total : Semiterm language Nat 1 := .fvar 0
def left : Semiterm language Nat 1 := .fvar 1
def right : Semiterm language Nat 1 := .fvar 2
def state3 : Semiterm language Nat 1 := PA194GenericRightScan.state 3
def app2 (f : Code 2) (a b : Semiterm language Nat 1) : Semiterm language Nat 1 := .func f ![a,b]
def pack (l r : Semiterm language Nat 1) : Semiterm language Nat 1 := app2 pairCode state3 (app2 pairCode l r)
def time : Semiterm language Nat 1 := app2 addCode (app2 addCode ix ix) ix
def start : Semiterm language Nat 1 := pack left (app2 repeatBlock total right)
def finish : Semiterm language Nat 1 := pack (app2 repeatBlock ix left) (app2 repeatBlock (app2 subCode total ix) right)
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
theorem modelOneBlock (x : M) : F oneBlock (fun _ => x) = F ones ![modelNumeral M 2,x+x] := by
  simp only [oneBlock,modelBin,modelUnary,modelProjection,modelConstant]
  rfl

theorem modelRepeatZero (x : M) : F repeatBlock ![(0 : M),x] = x := by
  have h := modelBase (M := M) (Code.proj (0 : Fin 1)) repeatBody (fun _ => x)
  rw [modelProjection] at h
  have hs : Fin.cases (F (Code.zero 0) Fin.elim0) (fun _ : Fin 1 => x) = ![(0 : M),x] := by
    funext i; refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [hs] at h
  exact h

theorem modelRepeatSucc (n x : M) : F repeatBlock ![F Code.succ (fun _ => n),x] =
    F oneBlock (fun _ => F repeatBlock ![n,x]) := by
  have h := modelStep (M := M) (Code.proj (0 : Fin 1)) repeatBody ![n,x]
  have hs : Fin.cases (F Code.succ (fun _ => ![n,x] 0)) (fun i => ![n,x] i.succ) =
      ![F Code.succ (fun _ => n),x] := by
    funext i; refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [hs] at h
  have hv : (fun i : Fin 1 => ![n,x] i.succ) = (fun _ => x) := by
    funext j; exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [hv] at h
  simp only [Matrix.cons_val_zero] at h
  change F repeatBlock ![F Code.succ (fun _ => n),x] = F repeatBody
    (Fin.cases n (Fin.cases (F repeatBlock ![n,x]) (fun _ => x))) at h
  rw [h,repeatBody,modelUnary,modelProjection]
  rfl

theorem carryOne (l r : M) :
    F stepper ![modelNumeral M 3,F pairCode ![modelNumeral M 3,F pairCode ![l,F oneBlock (fun _ => r)]]] =
    F pairCode ![modelNumeral M 3,F pairCode ![F oneBlock (fun _ => l),r]] := by
  have h := PA194Site28CarryCell.carryCell (M := M) (1 : M) l r
  rw [modelOneBlock,modelOneBlock]
  have h2 : modelNumeral M 2 = (1 : M)+1 := by rw [←modelNumeralOne,←modelNumeralAdd]
  have h3 : modelNumeral M 3 = (1 : M)+((1 : M)+1) := by rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  rw [h2]
  rw [←h3] at h
  exact h

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem valApp2 (x : M) (e : Nat → M) (f : Code 2) (a b : Semiterm language Nat 1) :
    Semiterm.val ![x] e (app2 f a b) = F f ![Semiterm.val ![x] e a,Semiterm.val ![x] e b] := by
  simp only [app2,Semiterm.val_func]
  congr 1
  exact val_pair ![x] e a b

theorem body_eval (x : M) (e : Nat → M) : body.Eval ![x] e ↔
    e 0 < x ∨
    F stepper ![(x+x)+x,F pairCode ![modelNumeral M 3,F pairCode ![e 1,F repeatBlock ![e 0,e 2]]]] =
      F pairCode ![modelNumeral M 3,F pairCode ![F repeatBlock ![x,e 1],F repeatBlock ![F subCode ![e 0,x],e 2]]] := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![x] body ↔ _
  simp only [body,Semiformula.EvalAux,eqRel]
  have hv (a b : Semiterm language Nat 1) :
      (fun i => Semiterm.val ![x] e (![a,b] i)) = ![Semiterm.val ![x] e a,Semiterm.val ![x] e b] := by
    exact val_pair ![x] e a b
  rw [hv]
  simp [ix,total,left,right,time,start,finish,pack,state3,valApp2,PA194GenericRightScan.valState,
    Semiterm.val_bvar,Semiterm.val_fvar,Matrix.cons_val_zero,Matrix.cons_val_one]
  rfl

theorem modelPartialCarry (n i l r : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
    i ≤ n →
    F stepper ![(i+i)+i,F pairCode ![modelNumeral M 3,F pairCode ![l,F repeatBlock ![n,r]]]] =
      F pairCode ![modelNumeral M 3,F pairCode ![F repeatBlock ![i,l],F repeatBlock ![F subCode ![n,i],r]]] := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let e : Nat → M := fun j => if j=0 then n else if j=1 then l else r
  have h0 : e 0 = n := by simp [e]
  have h1 : e 1 = l := by simp [e]
  have h2 : e 2 = r := by simp [e]
  have main : body.Eval ![i] e := by
    apply modelOpenInduction (M := M) body body_open e
    · apply (body_eval (0 : M) e).mpr
      right
      rw [h0,h1,h2]
      have hz := modelStepperZero (F pairCode ![modelNumeral M 3,F pairCode ![l,F repeatBlock ![n,r]]])
      change F stepper ![(0 : M),_] = _ at hz
      simp only [zero_add]
      have hsub : F subCode ![n,(0 : M)] = n := PRASubtraction.modelSubZero n
      rw [hz,modelRepeatZero,hsub]
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
        have hright : F repeatBlock ![F subCode ![n,u],r] =
            F oneBlock (fun _ => F repeatBlock ![F subCode ![n,u+1],r]) := by
          rw [subeq]
          rw [show F subCode ![n,u+1]+1 = F Code.succ (fun _ => F subCode ![n,u+1]) from modelAddOne _]
          rw [modelRepeatSucc]
        have hleft : F repeatBlock ![u+1,l] = F oneBlock (fun _ => F repeatBlock ![u,l]) := by
          rw [show u+1 = F Code.succ (fun _ => u) from modelAddOne _]
          rw [modelRepeatSucc]
        have hclock : ((u+1)+(u+1))+(u+1) = ((u+u)+u)+modelNumeral M 3 := by
          rw [show modelNumeral M 3 = (1 : M)+((1 : M)+1) by rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]]
          simp only [add_assoc,add_comm,add_left_comm]
        rw [hclock]
        change F stepper ![F addCode ![(u+u)+u,modelNumeral M 3],_] = _
        rw [PA194StepperCompose.modelStepperCompose,prev,hright,carryOne,hleft]
  have h := (body_eval i e).mp main
  rw [h0,h1,h2] at h
  intro hle
  exact h.resolve_left (not_lt_of_ge hle)

theorem modelFullCarry (n l r : M) :
    F stepper ![(n+n)+n,F pairCode ![modelNumeral M 3,F pairCode ![l,F repeatBlock ![n,r]]]] =
      F pairCode ![modelNumeral M 3,F pairCode ![F repeatBlock ![n,l],r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := modelPartialCarry n n l r le_rfl
  have hsub : F subCode ![n,n] = (0 : M) := by rw [modelSubAsTsub]; simp
  rw [hsub,modelRepeatZero] at h
  exact h
#print axioms modelOneBlock
#print axioms modelRepeatZero
#print axioms modelRepeatSucc
#print axioms carryOne
#print axioms modelPartialCarry
#print axioms modelFullCarry
end models
end PA194OneSpareIterate
