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
noncomputable def bitPrefix (b : Bool) (n z : V) : V :=
  if b then onesPrefix n z else Exp.exp n*z
def bitPrefixDef (b : Bool) : 𝚺₁.Semisentence 3 :=
  if b then .mkSigma “out n z. !onesPrefixDef out n z”
  else .mkSigma “out n z. ∃ e, !expDef e n ∧ out=e*z”
instance bitPrefix_defined (b : Bool) : 𝚺₁-Function₂[V] (bitPrefix b) via bitPrefixDef b :=
  .mk fun e => by cases b <;> simp [bitPrefixDef,bitPrefix,onesPrefix_defined.iff]
private instance bitPrefix_delta (b : Bool) : 𝚫₁-Function₂[V] (bitPrefix b) :=
  (bitPrefix_defined b).graph_delta.to_definable
private instance run_delta : 𝚫₁-Function₂[V] runFrom := runFrom_defined_delta.to_definable
noncomputable def frame (q L R : V) : V := cantor q (cantor L R)
def frameDef : 𝚺₁.Semisentence 4 := .mkSigma
  “out q L R. ∃ t, !ArithmeticCantor.pairDef t L R ∧ !ArithmeticCantor.pairDef out q t”
instance frame_defined : 𝚺₁-Function₃[V] frame via frameDef :=
  .mk fun e => by simp [frameDef,frame]
private instance frame_delta : 𝚫₁-Function₃[V] frame := frame_defined.graph_delta.to_definable
private instance sparse_frame_delta (q : Nat) : 𝚫₁-Function₂[V] (frameSparse q) := by
  change 𝚫₁-Function₂[V] (fun L R => frame (sparseCode q:V) L R)
  definability

@[simp] theorem bitPrefix_zero (b : Bool) (z : V) : bitPrefix b 0 z=z := by
  cases b <;> simp [bitPrefix]
theorem bitPrefix_succ (b : Bool) (n z : V) :
    bitPrefix b (n+1) z=2*bitPrefix b n z+digit b := by
  cases b
  · simp only [bitPrefix,digit,Bool.false_eq_true,if_false,exp_succ]
    ring
  · exact onesPrefix_succ n z
theorem bitPrefix_push (b : Bool) (n z : V) :
    bitPrefix b n (2*z+digit b)=bitPrefix b (n+1) z := by
  cases b
  · simp only [bitPrefix,digit,Bool.false_eq_true,if_false,exp_succ]
    ring
  · exact onesPrefix_push n z
theorem bitPrefix_add (b : Bool) (n m z : V) :
    bitPrefix b (n+m) z=bitPrefix b n (bitPrefix b m z) := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih =>
    rw [show n+1+m=(n+m)+1 by ring,bitPrefix_succ,bitPrefix_succ,ih]

lemma digit_mod (b : Bool) (x : V) : (2*x+digit b)%2=digit (V:=V) b := by
  cases b
  · simp [digit,mul_comm]
  · simpa only [digit,if_true,mul_comm] using mod_mul_add_of_lt x 2 (by simp : (1:V)<2)
lemma digit_div (b : Bool) (x : V) : (2*x+digit b)/2=x := by
  cases b
  · simp [digit]
  · simpa only [digit,if_true] using div_mul_add' x 2 (by simp : (1:V)<2)
lemma digit_cast (b : Bool) : (b.toNat:V)=digit b := by cases b <;> simp [digit]

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
    runFrom n (frameSparse q L (bitPrefix b n R))=frameSparse q (bitPrefix w n L) R := by
  induction n using ISigma1.pi1_succ_induction generalizing L R with
  | hP => definability
  | zero => simp
  | succ n ih => rw [run_first,bitPrefix_succ,step_right h,ih,bitPrefix_push]
theorem scan_left (q : Nat) (b w : Bool)
    (h : KTableCore.tm215 q b=some (w,false,q)) (n L R : V) :
    runFrom n (leftFrame q (bitPrefix b n L) R)=leftFrame q L (bitPrefix w n R) := by
  induction n using ISigma1.pi1_succ_induction generalizing L R with
  | hP => definability
  | zero => simp
  | succ n ih => rw [run_first,bitPrefix_succ,step_left_facing h,ih,bitPrefix_push]

def repeatZeroDef : 𝚺₁.Semisentence 3 := .mkSigma “out d z. out=z”
def repeatSuccDef : 𝚺₁.Semisentence 5 := .mkSigma “out prev n d z. out=d+8*prev”
def repeatBlueprint : PR.Blueprint 2 where
  zero := repeatZeroDef
  succ := repeatSuccDef
noncomputable def repeatConstruction : PR.Construction V repeatBlueprint where
  zero p := p 1
  succ p _ previous := p 0+8*previous
  zero_defined := .mk fun e => by simp [repeatBlueprint,repeatZeroDef]
  succ_defined := .mk fun e => by simp [repeatBlueprint,repeatSuccDef,numeral_eq_natCast]
noncomputable def repeat3 (d n z : V) : V := repeatConstruction.result ![d,z] n
noncomputable def repeatValue (n d z : V) : V := repeat3 d n z
def repeat3Def : 𝚺₁.Semisentence 4 := repeatBlueprint.resultDef
instance repeat3_defined : 𝚺₁-Function₃[V] repeatValue via repeat3Def :=
  .mk fun e => by
    have he : (fun i : Fin 2 => e i.succ.succ)=![e 2,e 3] := by
      funext i
      refine Fin.cases rfl (fun j => ?_) i
      have hj : j=0 := Subsingleton.elim _ _
      subst j
      rfl
    have h := (repeatConstruction (V:=V)).result_defined.df e
    change repeatBlueprint.resultDef.val.Evalb e ↔
      e 0=repeatConstruction.result (fun i : Fin 2 => e i.succ.succ) (e 1) at h
    rw [he] at h
    exact h
private instance repeatValue_delta : 𝚫₁-Function₃[V] repeatValue :=
  (repeat3_defined (V:=V)).graph_delta.to_definable
private instance repeat3_delta : 𝚫₁-Function₃[V] repeat3 := by
  change 𝚫₁-Function₃[V] (fun d n z => repeatValue n d z)
  definability
@[simp] theorem repeat3_zero (d z : V) : repeat3 d 0 z=z := by simp [repeat3,repeatConstruction]
theorem repeat3_succ (d n z : V) : repeat3 d (n+1) z=d+8*repeat3 d n z := by
  simp [repeat3,repeatConstruction,PR.Construction.result_succ]
theorem repeat3_push (d n z : V) : repeat3 d n (d+8*z)=repeat3 d (n+1) z := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using (repeat3_succ d (0:V) z).symm
  case succ n ih => rw [repeat3_succ,ih,repeat3_succ d (n+1)]

noncomputable def block (v z : V) : V := 2*bitPrefix true (v+1) z
noncomputable def reverseBlock (v z : V) : V := bitPrefix true (v+1) (2*z)
noncomputable def carryBlock (v z : V) : V := 1+4*bitPrefix true v z
noncomputable def reverseCarryBlock (v z : V) : V := bitPrefix true v (2+4*z)
noncomputable def file : List V → V → V
  | [], z => z
  | v::vs, z => block v (file vs z)
noncomputable def reverseFile : List V → V → V
  | [], z => z
  | v::vs, z => reverseFile vs (reverseBlock v z)
noncomputable def reverseCarry : List V → V → V
  | [], z => z
  | v::vs, z => reverseCarry vs (reverseCarryBlock v z)



omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
@[simp] theorem digit_false : digit (V:=V) false=0 := rfl
omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
@[simp] theorem digit_true : digit (V:=V) true=1 := rfl
@[simp] lemma bitPrefix_one (b : Bool) (z : V) : bitPrefix b 1 z=2*z+digit b := by
  simpa using bitPrefix_succ b (0:V) z
lemma ones_succ (n z : V) : bitPrefix true (n+1) z=2*bitPrefix true n z+1 := by
  simpa using bitPrefix_succ true n z
lemma ones_push (n z : V) : bitPrefix true n (2*z+1)=bitPrefix true (n+1) z := by
  simpa using bitPrefix_push true n z
local notation "step" => ArithmeticMachineStep215.stepValue
lemma right_zero {q q' : Nat} {w : Bool}
    (h : KTableCore.tm215 q false=some (w,true,q')) (L R : V) :
    step (frameSparse q L (2*R))=frameSparse q' (2*L+digit w) R := by
  simpa using step_right h L R
lemma right_one {q q' : Nat} {w : Bool}
    (h : KTableCore.tm215 q true=some (w,true,q')) (L R : V) :
    step (frameSparse q L (2*R+1))=frameSparse q' (2*L+digit w) R := by
  simpa using step_right h L R
lemma left_zero {q q' : Nat} {w : Bool}
    (h : KTableCore.tm215 q false=some (w,false,q')) (L R : V) :
    step (frameSparse q L (2*R))=leftFrame q' L (2*R+digit w) := by
  simpa using step_left h L R
lemma left_one {q q' : Nat} {w : Bool}
    (h : KTableCore.tm215 q true=some (w,false,q')) (L R : V) :
    step (frameSparse q L (2*R+1))=leftFrame q' L (2*R+digit w) := by
  simpa using step_left h L R
lemma facing_zero {q q' : Nat} {w : Bool}
    (h : KTableCore.tm215 q false=some (w,false,q')) (L R : V) :
    step (leftFrame q (2*L) R)=leftFrame q' L (2*R+digit w) := by
  simpa using step_left_facing h L R
lemma facing_one {q q' : Nat} {w : Bool}
    (h : KTableCore.tm215 q true=some (w,false,q')) (L R : V) :
    step (leftFrame q (2*L+1) R)=leftFrame q' L (2*R+digit w) := by
  simpa using step_left_facing h L R
lemma run_two_prefix (t x : V) : runFrom (t+2) x=runFrom t (step (step x)) := by
  rw [show t+2=(t+1)+1 by ring,run_first,run_first]
lemma forward_block {qa qb : Nat}
    (h0 : KTableCore.tm215 qa false=some (false,true,qb))
    (h1 : KTableCore.tm215 qb true=some (true,true,qa))
    (hs : KTableCore.tm215 qa true=some (true,true,qa)) (v L R : V) :
    runFrom (v+2) (frameSparse qa L (block v R))=
      frameSparse qa (reverseBlock v L) R := by
  rw [run_two_prefix,block,ones_succ,right_zero h0,right_one h1]
  simp only [digit_false,digit_true,add_zero]
  rw [scan_right qa true true hs]
  exact congrArg (fun x => frameSparse qa x R) (ones_push v (2*L))
lemma carry_block (v L R : V) :
    runFrom (v+2) (frameSparse 0 L (block v R))=
      frameSparse 0 (reverseCarryBlock v L) R := by
  rw [run_two_prefix,block,ones_succ,
    right_zero (show KTableCore.tm215 0 false=some (true,true,94) from rfl),
    right_one (show KTableCore.tm215 94 true=some (false,true,0) from rfl)]
  simp only [digit_false,digit_true,add_zero]
  rw [scan_right 0 true true (by rfl)]
  apply congrArg (fun z => frameSparse 0 (bitPrefix true v z) R)
  ring
lemma return_block {entry ones exit : Nat}
    (h1 : KTableCore.tm215 entry true=some (true,false,ones))
    (hs : KTableCore.tm215 ones true=some (true,false,ones))
    (h0 : KTableCore.tm215 ones false=some (false,false,exit)) (v L R : V) :
    runFrom (v+2) (leftFrame entry (reverseBlock v L) R)=leftFrame exit L (block v R) := by
  rw [show v+2=(v+1)+1 by ring,run_first,reverseBlock,ones_succ,facing_one h1]
  simp only [digit_true]
  rw [runFrom_succ,scan_left ones true true hs,facing_zero h0]
  simp only [digit_false,add_zero]
  rw [ones_push]
  rfl
lemma rollback_block (v L R : V) :
    runFrom (v+2) (leftFrame 97 (reverseCarryBlock v L) R)=leftFrame 97 L (block v R) := by
  rw [show v+2=v+(1+1) by ring,runFrom_add,reverseCarryBlock,scan_left 97 true true (by rfl)]
  rw [show (2:V)+4*L=2*(2*L+1) by ring]
  rw [run_first,run_one,
    facing_zero (show KTableCore.tm215 97 false=some (true,false,113) from rfl),
    facing_one (show KTableCore.tm215 113 true=some (false,false,97) from rfl)]
  simp only [digit_true,digit_false,add_zero]
  rw [←ones_succ]
  rfl

lemma forward_file {qa qb : Nat}
    (h0 : KTableCore.tm215 qa false=some (false,true,qb))
    (h1 : KTableCore.tm215 qb true=some (true,true,qa))
    (hs : KTableCore.tm215 qa true=some (true,true,qa)) (vs : List V) (L R : V) :
    Reach (frameSparse qa L (file vs R)) (frameSparse qa (reverseFile vs L) R) := by
  induction vs generalizing L with
  | nil => exact Reach.refl _
  | cons v vs ih => exact (show Reach _ _ from ⟨v+2,forward_block h0 h1 hs v L (file vs R)⟩).trans (ih _)
lemma carry_file (vs : List V) (L R : V) :
    Reach (frameSparse 0 L (file vs R)) (frameSparse 0 (reverseCarry vs L) R) := by
  induction vs generalizing L with
  | nil => exact Reach.refl _
  | cons v vs ih => exact (show Reach _ _ from ⟨v+2,carry_block v L (file vs R)⟩).trans (ih _)
lemma return_file {ones exit : Nat}
    (h1 : KTableCore.tm215 exit true=some (true,false,ones))
    (hs : KTableCore.tm215 ones true=some (true,false,ones))
    (h0 : KTableCore.tm215 ones false=some (false,false,exit)) (vs : List V) (L R : V) :
    Reach (leftFrame exit (reverseFile vs L) R) (leftFrame exit L (file vs R)) := by
  induction vs generalizing L R with
  | nil => exact Reach.refl _
  | cons v vs ih => exact (ih _ _).trans ⟨v+2,return_block h1 hs h0 v L (file vs R)⟩
lemma return_nonempty {entry ones exit : Nat}
    (he : KTableCore.tm215 entry true=some (true,false,ones))
    (h1 : KTableCore.tm215 exit true=some (true,false,ones))
    (hs : KTableCore.tm215 ones true=some (true,false,ones))
    (h0 : KTableCore.tm215 ones false=some (false,false,exit))
    (vs : List V) (hn : vs≠[]) (L R : V) :
    Reach (leftFrame entry (reverseFile vs L) R) (leftFrame exit L (file vs R)) := by
  induction vs generalizing L R with
  | nil => exact (hn rfl).elim
  | cons v vs ih =>
    cases vs with
    | nil => exact ⟨v+2,return_block he hs h0 v L R⟩
    | cons w ws => exact (ih (by simp) _ _).trans ⟨v+2,return_block h1 hs h0 v L (file (w::ws) R)⟩
lemma rollback_file (vs : List V) (L R : V) :
    Reach (leftFrame 97 (reverseCarry vs L) R) (leftFrame 97 L (file vs R)) := by
  induction vs generalizing L R with
  | nil => exact Reach.refl _
  | cons v vs ih => exact (ih _ _).trans ⟨v+2,rollback_block v L (file vs R)⟩
lemma carry_reverse_block (v L : V) :
    2*reverseCarryBlock v L+1=reverseBlock v (2*L+1) := by
  change 2*bitPrefix true v (2+4*L)+1=bitPrefix true (v+1) (2*(2*L+1))
  rw [ones_succ]
  apply congrArg (fun z => 2*bitPrefix true v z+1)
  ring
lemma carry_reverse_file (vs : List V) (L : V) :
    2*reverseCarry vs L+1=reverseFile vs (2*L+1) := by
  induction vs generalizing L with
  | nil => rfl
  | cons v vs ih => simpa only [reverseCarry,reverseFile,carry_reverse_block] using ih (reverseCarryBlock v L)

lemma carry_spares (n L R : V) :
    runFrom (3*n) (frameSparse 0 L (repeat3 6 n R))=
      frameSparse 0 (repeat3 5 n L) R := by
  induction n using ISigma1.pi1_succ_induction generalizing L R with
  | hP => definability
  | zero => simp
  | succ n ih =>
    have hb : block (1:V) (repeat3 6 n R)=6+8*repeat3 6 n R := by
      simp only [block,ones_succ,bitPrefix_one,digit_true]; ring
    have hc : reverseCarryBlock (1:V) L=5+8*L := by
      simp only [reverseCarryBlock,bitPrefix_one,digit_true]; ring
    rw [show 3*(n+1)=(1+2)+3*n by ring,repeat3_succ,←hb,runFrom_add,carry_block,hc,ih,repeat3_push]
lemma return_spares (n L R : V) :
    runFrom (3*n) (leftFrame 40 (repeat3 3 n L) R)=
      leftFrame 40 L (repeat3 6 n R) := by
  induction n using ISigma1.pi1_succ_induction generalizing L R with
  | hP => definability
  | zero => simp
  | succ n ih =>
    have hb : reverseBlock (1:V) (repeat3 3 n L)=3+8*repeat3 3 n L := by
      simp only [reverseBlock,ones_succ,bitPrefix_one,digit_true]; ring
    have hc : block (1:V) R=6+8*R := by
      simp only [block,ones_succ,bitPrefix_one,digit_true]; ring
    rw [show 3*(n+1)=(1+2)+3*n by ring,repeat3_succ,←hb,runFrom_add,
      return_block (ones:=54) (by rfl) (by rfl) (by rfl),hc,ih,repeat3_push]
lemma carry_reverse_spares (n L : V) : 2*repeat3 5 n L+1=repeat3 3 n (2*L+1) := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih => rw [repeat3_succ,repeat3_succ,←ih]; ring



noncomputable def markedBlock (v R : V) : V := 2*(2*bitPrefix true v R)
lemma markedBlock_eq (v R : V) : markedBlock v R=4*bitPrefix true v R := by unfold markedBlock; ring
lemma mark_local (v L R : V) :
    runFrom 3 (frameSparse 51 L (block v R))=leftFrame 1 L (markedBlock v R) := by
  rw [show (3:V)=(1+1)+1 by ring,run_first,run_first,run_one,block,ones_succ,
    right_zero (show KTableCore.tm215 51 false=some (false,true,16) from rfl)]
  simp only [digit_false,add_zero]
  rw [left_one (show KTableCore.tm215 16 true=some (false,false,1) from rfl)]
  simp only [digit_false,add_zero]
  rw [facing_zero (show KTableCore.tm215 1 false=some (false,false,1) from rfl)]
  simp only [digit_false,add_zero]
  rfl
lemma decrement_positive_local (v L R : V) :
    runFrom 4 (frameSparse 0 L (markedBlock (v+1) R))=
      leftFrame 40 (2*L+1) (block v R) := by
  rw [show (4:V)=((1+1)+1)+1 by ring,run_first,run_first,run_first,run_one,
    markedBlock,ones_succ,
    right_zero (show KTableCore.tm215 0 false=some (true,true,94) from rfl)]
  simp only [digit_true]
  rw [right_zero (show KTableCore.tm215 94 false=some (false,true,66) from rfl)]
  simp only [digit_false,add_zero]
  rw [left_one (show KTableCore.tm215 66 true=some (true,false,54) from rfl)]
  simp only [digit_true]
  rw [facing_zero (show KTableCore.tm215 54 false=some (false,false,40) from rfl)]
  simp only [digit_false,add_zero]
  rw [←ones_succ]
  rfl
lemma decrement_zero_local (w L R : V) :
    runFrom 7 (frameSparse 0 L (markedBlock 0 (block w R)))=
      leftFrame 97 L (block 0 (block w R)) := by
  rw [show (7:V)=(((((1+1)+1)+1)+1)+1)+1 by ring]
  repeat rw [run_first]
  rw [run_one,markedBlock,bitPrefix_zero,block,ones_succ,
    right_zero (show KTableCore.tm215 0 false=some (true,true,94) from rfl)]
  simp only [digit_true]
  rw [right_zero (show KTableCore.tm215 94 false=some (false,true,66) from rfl)]
  simp only [digit_false,add_zero]
  rw [right_zero (show KTableCore.tm215 66 false=some (true,true,198) from rfl)]
  simp only [digit_true]
  rw [left_one (show KTableCore.tm215 198 true=some (true,false,113) from rfl)]
  simp only [digit_true]
  rw [facing_one (show KTableCore.tm215 113 true=some (false,false,97) from rfl)]
  simp only [digit_false,add_zero]
  rw [facing_zero (show KTableCore.tm215 97 false=some (true,false,113) from rfl)]
  simp only [digit_true]
  rw [facing_one (show KTableCore.tm215 113 true=some (false,false,97) from rfl)]
  simp only [digit_false,add_zero,block,zero_add,bitPrefix_one,digit_true]
lemma right_blank {q q' : Nat} {w : Bool}
    (h : KTableCore.tm215 q false=some (w,true,q')) (L : V) :
    step (frameSparse q L 0)=frameSparse q' (2*L+digit w) 0 := by
  simpa using right_zero h L (0:V)
lemma left_blank {q q' : Nat} {w : Bool}
    (h : KTableCore.tm215 q false=some (w,false,q')) (L : V) :
    step (frameSparse q L 0)=leftFrame q' L (digit w) := by
  simpa using left_zero h L (0:V)
lemma increment_tail (L : V) :
    runFrom 6 (frameSparse 0 L 0)=leftFrame 40 (2*L+1) 6 := by
  rw [show (6:V)=((((1+1)+1)+1)+1)+1 by ring]
  repeat rw [run_first]
  rw [run_one,right_blank (show KTableCore.tm215 0 false=some (true,true,94) from rfl)]
  simp only [digit_true]
  rw [right_blank (show KTableCore.tm215 94 false=some (false,true,66) from rfl)]
  simp only [digit_false,add_zero]
  rw [right_blank (show KTableCore.tm215 66 false=some (true,true,198) from rfl)]
  simp only [digit_true]
  rw [left_blank (show KTableCore.tm215 198 false=some (true,false,40) from rfl)]
  simp only [digit_true]
  rw [facing_one (show KTableCore.tm215 40 true=some (true,false,54) from rfl)]
  simp only [digit_true]
  rw [facing_zero (show KTableCore.tm215 54 false=some (false,false,40) from rfl)]
  simp only [digit_false,add_zero]
  congr 1
  ring
lemma increment_middle (v L R : V) :
    runFrom (v+2) (frameSparse 64 L (markedBlock v R))=
      frameSparse 0 (bitPrefix true v (2*(2*L)+1)) R := by
  rw [run_two_prefix,markedBlock,
    right_zero (show KTableCore.tm215 64 false=some (false,true,74) from rfl)]
  simp only [digit_false,add_zero]
  rw [right_zero (show KTableCore.tm215 74 false=some (true,true,0) from rfl)]
  simp only [digit_true]
  exact scan_right 0 true true (by rfl) _ _ _
lemma increment_middle_reverse (v L : V) :
    2*bitPrefix true v (2*(2*L)+1)+1=reverseBlock (v+1) L := by
  rw [ones_push,reverseBlock]
  exact (ones_succ (v+1) (2*L)).symm

/-- Actual marker-entry order for all nine physical registers. -/
def skipState (r : Nat) : Nat := [51,36,25,48,32,33,22,55,60].getD r 0
def markExit (r : Nat) : Nat := if r=0 then 1 else 3
lemma skip_self (r : Nat) (hr : r<9) :
    KTableCore.tm215 (skipState r) true=some (true,true,skipState r) := by
  have h : ∀ r : Fin 9, KTableCore.tm215 (skipState r) true=some (true,true,skipState r) := by decide
  exact h ⟨r,hr⟩
lemma skip_next (r : Nat) (hr : r<8) :
    KTableCore.tm215 (skipState (r+1)) false=some (false,true,skipState r) := by
  have h : ∀ r : Fin 8, KTableCore.tm215 (skipState (r+1)) false=some (false,true,skipState r) := by decide
  exact h ⟨r,hr⟩
lemma skip_file (pre : List V) (m : Nat) (h : pre.length+m<9) (L R : V) :
    Reach (frameSparse (skipState (pre.length+m)) L (file pre R))
      (frameSparse (skipState m) (reverseFile pre L) R) := by
  induction pre generalizing L with
  | nil => simpa only [List.length_nil,Nat.zero_add,file,reverseFile] using Reach.refl (frameSparse (skipState m) L R)
  | cons v pre ih =>
    have hn : pre.length+m<8 := by simp only [List.length_cons] at h; omega
    change Reach (frameSparse (skipState (pre.length+1+m)) L (block v (file pre R))) _
    rw [show pre.length+1+m=(pre.length+m)+1 by omega,block]
    refine (Reach.of_step (by simpa using right_zero (skip_next _ hn) L (bitPrefix true (v+1) (file pre R)))).trans ?_
    refine (show Reach _ _ from ⟨v+1,scan_right _ true true (skip_self _ (by omega)) _ _ _⟩).trans ?_
    exact ih (by omega) _
lemma mark_split (pre rest : List V) (v L tail : V) (hr : pre.length<9) :
    Reach (frameSparse (skipState pre.length) L (file pre (block v (file rest tail))))
      (leftFrame (markExit pre.length) L (file pre (markedBlock v (file rest tail)))) := by
  refine (show Reach _ _ from by simpa using skip_file pre 0 (by simpa using hr) L (block v (file rest tail))).trans ?_
  refine (show Reach _ _ from ⟨3,mark_local v (reverseFile pre L) (file rest tail)⟩).trans ?_
  cases pre with
  | nil => exact Reach.refl _
  | cons w ws =>
    exact return_nonempty (ones:=2) (exit:=3) (by rfl) (by rfl) (by rfl) (by rfl) _ (by simp) _ _
lemma decrement_positive_split (pre rest : List V) (v L tail : V) :
    Reach (frameSparse 0 L (file pre (markedBlock (v+1) (file rest tail))))
      (leftFrame 40 (2*L+1) (file pre (block v (file rest tail)))) := by
  refine (carry_file pre L _).trans ?_
  refine (show Reach _ _ from ⟨4,decrement_positive_local v (reverseCarry pre L) (file rest tail)⟩).trans ?_
  rw [carry_reverse_file]
  exact return_file (ones:=54) (by rfl) (by rfl) (by rfl) _ _ _
lemma decrement_zero_split (pre : List V) (w L R : V) :
    Reach (frameSparse 0 L (file pre (markedBlock 0 (block w R))))
      (leftFrame 97 L (file pre (block 0 (block w R)))) := by
  refine (carry_file pre L _).trans ?_
  exact (show Reach _ _ from ⟨7,decrement_zero_local w (reverseCarry pre L) R⟩).trans (rollback_file pre L _)
lemma increment_split (pre rest : List V) (v L k : V) :
    Reach (frameSparse 64 L (file pre (markedBlock v (file rest (repeat3 6 k 0)))))
      (leftFrame 40 L (file pre (block (v+1) (file rest (repeat3 6 (k+1) 0))))) := by
  refine (forward_file (qa:=64) (qb:=74) (by rfl) (by rfl) (by rfl) pre L _).trans ?_
  refine (show Reach _ _ from ⟨v+2,increment_middle v (reverseFile pre L) _⟩).trans ?_
  refine (carry_file rest _ _).trans ?_
  refine (show Reach _ _ from ⟨3*k,carry_spares k _ 0⟩).trans ?_
  refine (show Reach _ _ from ⟨6,increment_tail _⟩).trans ?_
  rw [carry_reverse_spares,carry_reverse_file,increment_middle_reverse]
  refine (show Reach _ _ from ⟨3*k,return_spares k _ 6⟩).trans ?_
  have hr : repeat3 6 k (6:V)=repeat3 6 (k+1) 0 := by
    simpa using repeat3_push (6:V) k 0
  rw [hr]
  refine (return_file (ones:=54) (by rfl) (by rfl) (by rfl) rest _ _).trans ?_
  refine (show Reach _ _ from ⟨(v+1)+2,return_block (ones:=54) (by rfl) (by rfl) (by rfl) (v+1) _ _⟩).trans ?_
  exact return_file (ones:=54) (by rfl) (by rfl) (by rfl) pre L _



/-- A positive execution clock, distinct from the zero-length scan convention. -/
def ReachPos (x y : V) : Prop := ∃ t : V, 0<t ∧ runFrom t x=y
lemma Reach.positive {q q' : Nat} {L R L' R' : V}
    (h : Reach (frameSparse q L R) (leftFrame q' L' R'))
    (hne : sparseCode q≠sparseCode q') :
    ReachPos (frameSparse q L R) (leftFrame q' L' R') := by
  obtain ⟨t,ht⟩ := h
  refine ⟨t,pos_iff_ne_zero.mpr ?_,ht⟩
  intro hz
  subst t
  have he := congrArg first ht
  have hc : (sparseCode q:V)=(sparseCode q':V) := by
    simpa only [runFrom_zero,leftFrame,frameSparse,first_cantor] using he
  exact hne (nat_cast_inj.mp hc)

noncomputable def plain (values : Fin 9 → V) (k : V) : V :=
  file (List.ofFn values) (repeat3 6 k 0)
noncomputable def before (values : Fin 9 → V) (r : Fin 9) : List V :=
  (List.ofFn values).take r.val
noncomputable def after (values : Fin 9 → V) (r : Fin 9) : List V :=
  (List.ofFn values).drop (r.val+1)
noncomputable def marked (values : Fin 9 → V) (r : Fin 9) (k : V) : V :=
  file (before values r) (markedBlock (values r) (file (after values r) (repeat3 6 k 0)))
omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma before_length (values : Fin 9 → V) (r : Fin 9) : (before values r).length=r.val := by
  simp [before]
lemma file_append (vs ws : List V) (R : V) : file (vs++ws) R=file vs (file ws R) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [List.cons_append,file,ih]
omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma values_split (values : Fin 9 → V) (r : Fin 9) :
    List.ofFn values=before values r++values r::after values r := by
  have h : r.val<(List.ofFn values).length := by simp
  calc
    List.ofFn values=(List.ofFn values).take r.val++(List.ofFn values).drop r.val := (List.take_append_drop _ _).symm
    _=before values r++values r::after values r := by rw [List.drop_eq_getElem_cons h]; simp only [before,after,List.getElem_ofFn]
lemma plain_split (values : Fin 9 → V) (r : Fin 9) (k : V) :
    plain values k=file (before values r) (block (values r) (file (after values r) (repeat3 6 k 0))) := by
  unfold plain
  rw [values_split values r,file_append]
  rfl
omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma values_update (values : Fin 9 → V) (r : Fin 9) (w : V) :
    List.ofFn (Function.update values r w)=(List.ofFn values).set r.val w := by
  apply List.ext_getElem (by simp)
  intro j hj hj'
  simp only [List.getElem_ofFn,List.getElem_set]
  by_cases h : r.val=j
  · subst j; simp
  · simp [Function.update,Fin.ext_iff,h,Ne.symm h]
lemma plain_update (values : Fin 9 → V) (r : Fin 9) (w k : V) :
    plain (Function.update values r w) k=
      file (before values r) (block w (file (after values r) (repeat3 6 k 0))) := by
  unfold plain
  rw [values_update,List.set_eq_take_append_cons_drop,if_pos (by simp),file_append]
  rfl
lemma following_block (rest : List V) (k : V) (hk : 0<k) :
    ∃ w R : V, file rest (repeat3 6 k 0)=block w R := by
  cases rest with
  | cons w ws => exact ⟨w,file ws (repeat3 6 k 0),rfl⟩
  | nil =>
    have he : k-1+1=k := tsub_add_cancel_of_le (pos_iff_one_le.mp hk)
    refine ⟨1,repeat3 6 (k-1) 0,?_⟩
    change repeat3 6 k 0=block 1 (repeat3 6 (k-1) 0)
    conv_lhs => rw [←he,repeat3_succ]
    simp only [block,ones_succ,bitPrefix_one,digit_true]
    ring

/-- Every physical marker entry, with zero register values and arbitrary left tape allowed. -/
theorem box_mark (values : Fin 9 → V) (r : Fin 9) (L k : V) :
    ReachPos (frameSparse (skipState r) L (plain values k))
      (leftFrame (markExit r) L (marked values r k)) := by
  apply Reach.positive
  · rw [plain_split values r,marked]
    have h := mark_split (before values r) (after values r) (values r) L (repeat3 6 k 0)
      (by rw [before_length]; exact r.isLt)
    simpa only [before_length] using h
  · have h : ∀ r : Fin 9, sparseCode (skipState r)≠sparseCode (markExit r) := by decide
    exact h r
/-- The actual215 increment appends a spare block holding one. -/
theorem box_inc (values : Fin 9 → V) (r : Fin 9) (L k : V) :
    ReachPos (frameSparse 64 L (marked values r k))
      (leftFrame 40 L (plain (Function.update values r (values r+1)) (k+1))) := by
  apply Reach.positive
  · rw [plain_update,marked]
    exact increment_split _ _ _ _ _
  · decide
/-- A spare is needed for zero DEC at the last physical register. -/
theorem box_dec0 (values : Fin 9 → V) (r : Fin 9) (L k : V)
    (hk : 0<k) (hv : values r=0) :
    ReachPos (frameSparse 0 L (marked values r k)) (leftFrame 97 L (plain values k)) := by
  apply Reach.positive
  · rw [plain_split values r,marked,hv]
    obtain ⟨w,R,hR⟩ := following_block (after values r) k hk
    rw [hR]
    exact decrement_zero_split _ _ _ _
  · decide
/-- Positive DEC preserves the spare count and retains the extra left-hand one. -/
theorem box_decp (values : Fin 9 → V) (r : Fin 9) (L k : V)
    (hv : 0<values r) :
    ReachPos (frameSparse 0 L (marked values r k))
      (leftFrame 40 (2*L+1) (plain (Function.update values r (values r-1)) k)) := by
  apply Reach.positive
  · rw [plain_update,marked]
    have he : values r-1+1=values r := tsub_add_cancel_of_le (pos_iff_one_le.mp hv)
    have h := decrement_positive_split (before values r) (after values r) (values r-1) L (repeat3 6 k 0)
    simpa only [he] using h
  · decide


/-- Complete finite engine-row audit: the44 shared rows and215's bypass.
The execution proofs above also use these actual rows directly. -/
def engineRows : List ((Nat×Bool)×(Bool×Bool×Nat)) := [
  ((0,false),(true,true,94)),
  ((0,true),(true,true,0)),
  ((1,false),(false,false,1)),
  ((1,true),(true,false,2)),
  ((2,false),(false,false,3)),
  ((2,true),(true,false,2)),
  ((3,false),(false,false,5)),
  ((3,true),(true,false,2)),
  ((16,false),(true,false,1)),
  ((16,true),(false,false,1)),
  ((22,false),(false,true,33)),
  ((22,true),(true,true,22)),
  ((25,false),(false,true,36)),
  ((25,true),(true,true,25)),
  ((32,false),(false,true,48)),
  ((32,true),(true,true,32)),
  ((33,false),(false,true,32)),
  ((33,true),(true,true,33)),
  ((36,false),(false,true,51)),
  ((36,true),(true,true,36)),
  ((40,false),(false,false,4)),
  ((40,true),(true,false,54)),
  ((48,false),(false,true,25)),
  ((48,true),(true,true,48)),
  ((51,false),(false,true,16)),
  ((51,true),(true,true,51)),
  ((54,false),(false,false,40)),
  ((54,true),(true,false,54)),
  ((55,false),(false,true,22)),
  ((55,true),(true,true,55)),
  ((60,false),(false,true,55)),
  ((60,true),(true,true,60)),
  ((64,false),(false,true,74)),
  ((64,true),(true,true,64)),
  ((66,false),(true,true,198)),
  ((66,true),(true,false,54)),
  ((74,false),(true,true,0)),
  ((74,true),(true,true,64)),
  ((94,false),(false,true,66)),
  ((94,true),(false,true,0)),
  ((97,false),(true,false,113)),
  ((97,true),(true,false,97)),
  ((113,true),(false,false,97)),
  ((198,true),(true,false,113)),
  ((198,false),(true,false,40))]
theorem engine_rows_length : engineRows.length=45 := rfl
theorem engine_rows_checked : ∀ row ∈ engineRows,
    KTableCore.tm215 row.1.1 row.1.2=some row.2 := by decide
theorem engine_rows_coverage : engineRows.map Prod.fst=
    ([0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198].flatMap
      fun q => (if q=113 ∨ q=198 then [] else [(q,false)])++[(q,true)])++[(198,false)] := by decide

end DiophantineConsistency.ArithmeticRegisterBoxes215

