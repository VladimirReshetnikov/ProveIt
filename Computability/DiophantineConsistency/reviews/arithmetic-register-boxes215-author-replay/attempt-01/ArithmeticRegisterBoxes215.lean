import DiophantineConsistency.ArithmeticMachineTape215
import BusyBeaver.ZFC.ArithmeticTapePrefix254

/-! Arithmetic execution of the literal215 register engine. Register values,
scan lengths, spare counts and clocks are internal IΣ1-model elements.
No old252 execution theorem or caller-supplied box semantics is used. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.ArithmeticRegisterBoxes215
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticTapePrefix254 ArithmeticMachineTape215
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def digit (b : Bool) : V := if b then 1 else 0
noncomputable def prefix (b : Bool) (n z : V) : V :=
  if b then onesPrefix n z else Exp.exp n*z
def prefixDef (b : Bool) : 𝚺₁.Semisentence 3 :=
  if b then .mkSigma “out n z. !onesPrefixDef out n z”
  else .mkSigma “out n z. ∃ e, !expDef e n ∧ out=e*z”
instance prefix_defined (b : Bool) : 𝚺₁-Function₂[V] (prefix b) via prefixDef b :=
  .mk fun e => by cases b <;> simp [prefixDef,prefix,onesPrefix_defined.iff]
private instance prefix_delta (b : Bool) : 𝚫₁-Function₂[V] (prefix b) :=
  (prefix_defined b).graph_delta.to_definable
private instance run_delta : 𝚫₁-Function₂[V] runFrom := runFrom_defined_delta.to_definable
private instance frame_delta (q : Nat) : 𝚫₁-Function₂[V] (frameSparse q) := by
  unfold frameSparse; definability

@[simp] theorem prefix_zero (b : Bool) (z : V) : prefix b 0 z=z := by
  cases b <;> simp [prefix]
theorem prefix_succ (b : Bool) (n z : V) :
    prefix b (n+1) z=2*prefix b n z+digit b := by
  cases b
  · simp only [prefix,digit,Bool.false_eq_true,if_false,exp_succ]
    ring
  · exact onesPrefix_succ n z
theorem prefix_push (b : Bool) (n z : V) :
    prefix b n (2*z+digit b)=prefix b (n+1) z := by
  cases b
  · simp only [prefix,digit,Bool.false_eq_true,if_false,exp_succ]
    ring
  · exact onesPrefix_push n z
theorem prefix_add (b : Bool) (n m z : V) :
    prefix b (n+m) z=prefix b n (prefix b m z) := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih =>
    rw [show n+1+m=(n+m)+1 by ring,prefix_succ,prefix_succ,ih]

lemma digit_mod (b : Bool) (x : V) : (2*x+digit b)%2=digit (V:=V) b := by
  cases b
  · simp [digit,mul_comm]
  · simpa only [digit,if_true,mul_comm] using mod_mul_add_of_lt x 2 (by simp : (1:V)<2)
lemma digit_div (b : Bool) (x : V) : (2*x+digit b)/2=x := by
  cases b
  · simp [digit]
  · simpa only [digit,if_true] using div_mul_add' x 2 (by simp : (1:V)<2)
lemma digit_cast (b : Bool) : (b.toNat:V)=digit b := by cases b <;> rfl

noncomputable def leftFrame (q : Nat) (L R : V) : V :=
  frameSparse q (L/2) (L%2+2*R)
private instance leftFrame_delta (q : Nat) : 𝚫₁-Function₂[V] (leftFrame q) := by
  unfold leftFrame; definability
theorem leftFrame_bit (q : Nat) (b : Bool) (L R : V) :
    leftFrame q (2*L+digit b) R=frameSparse q L (2*R+digit b) := by
  simp only [leftFrame,digit_div,digit_mod]
  congr 1
  ring
theorem step_right {q q' : Nat} {b w : Bool}
    (h : KTableCore.tm215 q b=some (w,true,q')) (L R : V) :
    ArithmeticMachineStep215.stepValue (frameSparse q L (2*R+digit b))=
      frameSparse q' (2*L+digit w) R := by
  have hr : (2*R+digit b)%2=(b.toNat:V) := by rw [digit_cast,digit_mod]
  simpa only [if_true,digit_cast,digit_div] using sparse_step h L (2*R+digit b) hr
theorem step_left {q q' : Nat} {b w : Bool}
    (h : KTableCore.tm215 q b=some (w,false,q')) (L R : V) :
    ArithmeticMachineStep215.stepValue (frameSparse q L (2*R+digit b))=
      leftFrame q' L (2*R+digit w) := by
  have hr : (2*R+digit b)%2=(b.toNat:V) := by rw [digit_cast,digit_mod]
  simpa only [Bool.false_eq_true,if_false,digit_cast,digit_div,leftFrame,add_comm] using
    sparse_step h L (2*R+digit b) hr
theorem step_left_facing {q q' : Nat} {b w : Bool}
    (h : KTableCore.tm215 q b=some (w,false,q')) (L R : V) :
    ArithmeticMachineStep215.stepValue (leftFrame q (2*L+digit b) R)=
      leftFrame q' L (2*R+digit w) := by
  rw [leftFrame_bit]
  exact step_left h L R

theorem run_first (t x : V) :
    runFrom (t+1) x=runFrom t (ArithmeticMachineStep215.stepValue x) := by
  rw [add_comm,runFrom_add,show runFrom (1:V) x=ArithmeticMachineStep215.stepValue x by
    simpa using runFrom_succ (0:V) x]
theorem run_one (x : V) : runFrom (1:V) x=ArithmeticMachineStep215.stepValue x := by
  simpa using runFrom_succ (0:V) x

def Reach (x y : V) : Prop := ∃ t : V, runFrom t x=y
theorem Reach.refl (x : V) : Reach x x := ⟨0,runFrom_zero x⟩
theorem Reach.trans {x y z : V} (h : Reach x y) (g : Reach y z) : Reach x z := by
  obtain ⟨t,ht⟩ := h
  obtain ⟨u,hu⟩ := g
  exact ⟨t+u,by rw [runFrom_add,ht,hu]⟩
theorem Reach.of_step {x y : V} (h : ArithmeticMachineStep215.stepValue x=y) : Reach x y :=
  ⟨1,(run_one x).trans h⟩
theorem Reach.of_eq {x y : V} (h : x=y) : Reach x y := ⟨0,(runFrom_zero x).trans h⟩
theorem stR {q q' : Nat} {b w : Bool} {L R X : V}
    (h : KTableCore.tm215 q b=some (w,true,q'))
    (g : Reach (frameSparse q' (2*L+digit w) R) X) :
    Reach (frameSparse q L (2*R+digit b)) X :=
  (Reach.of_step (step_right h L R)).trans g
theorem stL {q q' : Nat} {b w : Bool} {L R X : V}
    (h : KTableCore.tm215 q b=some (w,false,q'))
    (g : Reach (leftFrame q' L (2*R+digit w)) X) :
    Reach (frameSparse q L (2*R+digit b)) X :=
  (Reach.of_step (step_left h L R)).trans g
theorem stLL {q q' : Nat} {b w : Bool} {L R X : V}
    (h : KTableCore.tm215 q b=some (w,false,q'))
    (g : Reach (leftFrame q' L (2*R+digit w)) X) :
    Reach (leftFrame q (2*L+digit b) R) X :=
  (Reach.of_step (step_left_facing h L R)).trans g

/-- Exact clocks make the uniform invariant Pi1, available in IΣ1. -/
theorem scan_right (q : Nat) (b w : Bool)
    (h : KTableCore.tm215 q b=some (w,true,q)) (n L R : V) :
    runFrom n (frameSparse q L (prefix b n R))=frameSparse q (prefix w n L) R := by
  have all : ∀ n : V, ∀ L R : V,
      runFrom n (frameSparse q L (prefix b n R))=frameSparse q (prefix w n L) R := by
    intro n
    induction n using ISigma1.pi1_succ_induction
    · definability
    case zero => intro L R; simp
    case succ n ih =>
      intro L R
      rw [run_first,prefix_succ,step_right h,ih,prefix_push]
  exact all n L R
theorem scan_left (q : Nat) (b w : Bool)
    (h : KTableCore.tm215 q b=some (w,false,q)) (n L R : V) :
    runFrom n (leftFrame q (prefix b n L) R)=leftFrame q L (prefix w n R) := by
  have all : ∀ n : V, ∀ L R : V,
      runFrom n (leftFrame q (prefix b n L) R)=leftFrame q L (prefix w n R) := by
    intro n
    induction n using ISigma1.pi1_succ_induction
    · definability
    case zero => intro L R; simp
    case succ n ih =>
      intro L R
      rw [run_first,prefix_succ,step_left_facing h,ih,prefix_push]
  exact all n L R

def repeatZeroDef : 𝚺₁.Semisentence 3 := .mkSigma “out d z. out=z”
def repeatSuccDef : 𝚺₁.Semisentence 5 := .mkSigma “out prev n d z. out=d+8*prev”
def repeatBlueprint : PR.Blueprint 2 where
  zero := repeatZeroDef
  succ := repeatSuccDef
noncomputable def repeatConstruction : PR.Construction V repeatBlueprint where
  zero p := p 1
  succ p _ previous := p 0+8*previous
  zero_defined := .mk fun e => by simp [repeatBlueprint,repeatZeroDef]
  succ_defined := .mk fun e => by simp [repeatBlueprint,repeatSuccDef]
noncomputable def repeat3 (d n z : V) : V := repeatConstruction.result ![d,z] n
def repeat3Def : 𝚺₁.Semisentence 4 := repeatBlueprint.resultDef
instance repeat3_defined : 𝚺₁-Function₃[V] (fun n d z => repeat3 d n z) via repeat3Def :=
  .mk fun e => by
    have he : (fun i : Fin 2 => e i.succ.succ)=![e 2,e 3] := by
      funext i; fin_cases i <;> rfl
    have h := (repeatConstruction (V:=V)).result_defined.df e
    change repeatBlueprint.resultDef.val.Evalb e ↔
      e 0=repeatConstruction.result (fun i : Fin 2 => e i.succ.succ) (e 1) at h
    rw [he] at h
    exact h
private instance repeat3_delta : 𝚫₁-Function₃[V] (fun d n z => repeat3 d n z) := by
  haveI := repeat3_defined.graph_delta.to_definable
  definability
@[simp] theorem repeat3_zero (d z : V) : repeat3 d 0 z=z := by simp [repeat3,repeatConstruction]
theorem repeat3_succ (d n z : V) : repeat3 d (n+1) z=d+8*repeat3 d n z := by
  simp [repeat3,repeatConstruction,PR.Construction.result_succ]
theorem repeat3_push (d n z : V) : repeat3 d n (d+8*z)=repeat3 d (n+1) z := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp [repeat3_succ]
  case succ n ih => rw [repeat3_succ,ih,repeat3_succ d (n+1)]

noncomputable def block (v z : V) : V := 2*prefix true (v+1) z
noncomputable def reverseBlock (v z : V) : V := prefix true (v+1) (2*z)
noncomputable def carryBlock (v z : V) : V := 1+4*prefix true v z
noncomputable def reverseCarryBlock (v z : V) : V := prefix true v (2+4*z)
noncomputable def file : List V → V → V
  | [], z => z
  | v::vs, z => block v (file vs z)
noncomputable def reverseFile : List V → V → V
  | [], z => z
  | v::vs, z => reverseFile vs (reverseBlock v z)
noncomputable def reverseCarry : List V → V → V
  | [], z => z
  | v::vs, z => reverseCarry vs (reverseCarryBlock v z)

end DiophantineConsistency.ArithmeticRegisterBoxes215
