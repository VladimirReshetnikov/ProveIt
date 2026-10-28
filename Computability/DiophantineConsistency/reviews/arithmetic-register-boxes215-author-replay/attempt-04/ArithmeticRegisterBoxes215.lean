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
  have all : ∀ n : V, ∀ L R : V,
      runFrom n (frameSparse q L (bitPrefix b n R))=frameSparse q (bitPrefix w n L) R := by
    intro n
    induction n using ISigma1.pi1_succ_induction
    · definability
    case zero => intro L R; simp
    case succ n ih =>
      intro L R
      rw [run_first,bitPrefix_succ,step_right h,ih,bitPrefix_push]
  exact all n L R
theorem scan_left (q : Nat) (b w : Bool)
    (h : KTableCore.tm215 q b=some (w,false,q)) (n L R : V) :
    runFrom n (leftFrame q (bitPrefix b n L) R)=leftFrame q L (bitPrefix w n R) := by
  have all : ∀ n : V, ∀ L R : V,
      runFrom n (leftFrame q (bitPrefix b n L) R)=leftFrame q L (bitPrefix w n R) := by
    intro n
    induction n using ISigma1.pi1_succ_induction
    · definability
    case zero => intro L R; simp
    case succ n ih =>
      intro L R
      rw [run_first,bitPrefix_succ,step_left_facing h,ih,bitPrefix_push]
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



@[simp] theorem digit_false : digit (V:=V) false=0 := rfl
@[simp] theorem digit_true : digit (V:=V) true=1 := rfl
local notation "step" => ArithmeticMachineStep215.stepValue
lemma right_zero {q q' : Nat} {w : Bool}
    (h : KTableCore.tm215 q false=some(w,true,q')) (L R : V) :
    step (frameSparse q L (2*R))=frameSparse q' (2*L+digit w) R := by
  simpa using step_right h L R
lemma right_one {q q' : Nat} {w : Bool}
    (h : KTableCore.tm215 q true=some(w,true,q')) (L R : V) :
    step (frameSparse q L (2*R+1))=frameSparse q' (2*L+digit w) R := by
  simpa using step_right h L R
lemma left_zero {q q' : Nat} {w : Bool}
    (h : KTableCore.tm215 q false=some(w,false,q')) (L R : V) :
    step (frameSparse q L (2*R))=leftFrame q' L (2*R+digit w) := by
  simpa using step_left h L R
lemma left_one {q q' : Nat} {w : Bool}
    (h : KTableCore.tm215 q true=some(w,false,q')) (L R : V) :
    step (frameSparse q L (2*R+1))=leftFrame q' L (2*R+digit w) := by
  simpa using step_left h L R
lemma facing_zero {q q' : Nat} {w : Bool}
    (h : KTableCore.tm215 q false=some(w,false,q')) (L R : V) :
    step (leftFrame q (2*L) R)=leftFrame q' L (2*R+digit w) := by
  simpa using step_left_facing h L R
lemma facing_one {q q' : Nat} {w : Bool}
    (h : KTableCore.tm215 q true=some(w,false,q')) (L R : V) :
    step (leftFrame q (2*L+1) R)=leftFrame q' L (2*R+digit w) := by
  simpa using step_left_facing h L R
lemma run_two_prefix (t x : V) : runFrom (t+2) x=runFrom t (step (step x)) := by
  rw [show t+2=(t+1)+1 by ring,run_first,run_first]
lemma forward_block {qa qb : Nat}
    (h0 : KTableCore.tm215 qa false=some(false,true,qb))
    (h1 : KTableCore.tm215 qb true=some(true,true,qa))
    (hs : KTableCore.tm215 qa true=some(true,true,qa)) (v L R : V) :
    runFrom (v+2) (frameSparse qa L (block v R))=
      frameSparse qa (reverseBlock v L) R := by
  rw [run_two_prefix,block,bitPrefix_succ,right_zero h0,right_one h1]
  simp only [digit_false,digit_true,add_zero]
  rw [scan_right qa true true hs]
  exact congrArg (fun x => frameSparse qa x R) (bitPrefix_push true v (2*L))
lemma carry_block (v L R : V) :
    runFrom (v+2) (frameSparse 0 L (block v R))=
      frameSparse 0 (reverseCarryBlock v L) R := by
  rw [run_two_prefix,block,bitPrefix_succ,
    right_zero (show KTableCore.tm215 0 false=some(true,true,94) from rfl),
    right_one (show KTableCore.tm215 94 true=some(false,true,0) from rfl)]
  simp only [digit_false,digit_true,add_zero]
  rw [scan_right 0 true true (by rfl)]
  congr 2
  ring
lemma return_block {entry ones exit : Nat}
    (h1 : KTableCore.tm215 entry true=some(true,false,ones))
    (hs : KTableCore.tm215 ones true=some(true,false,ones))
    (h0 : KTableCore.tm215 ones false=some(false,false,exit)) (v L R : V) :
    runFrom (v+2) (leftFrame entry (reverseBlock v L) R)=leftFrame exit L (block v R) := by
  rw [show v+2=(v+1)+1 by ring,run_first,reverseBlock,bitPrefix_succ,facing_one h1]
  simp only [digit_true]
  rw [runFrom_succ,scan_left ones true true hs,facing_zero h0]
  simp only [digit_false,add_zero]
  rw [bitPrefix_push]
  rfl
lemma rollback_block (v L R : V) :
    runFrom (v+2) (leftFrame 97 (reverseCarryBlock v L) R)=leftFrame 97 L (block v R) := by
  rw [show v+2=v+(1+1) by ring,runFrom_add,reverseCarryBlock,scan_left 97 true true (by rfl)]
  rw [show (2:V)+4*L=2*(2*L+1) by ring]
  rw [run_two_prefix,runFrom_zero,
    facing_zero (show KTableCore.tm215 97 false=some(true,false,113) from rfl),
    facing_one (show KTableCore.tm215 113 true=some(false,false,97) from rfl)]
  simp only [digit_true,digit_false,add_zero]
  rw [←bitPrefix_succ]
  rfl

lemma forward_file {qa qb : Nat}
    (h0 : KTableCore.tm215 qa false=some(false,true,qb))
    (h1 : KTableCore.tm215 qb true=some(true,true,qa))
    (hs : KTableCore.tm215 qa true=some(true,true,qa)) (vs : List V) (L R : V) :
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
    (h1 : KTableCore.tm215 exit true=some(true,false,ones))
    (hs : KTableCore.tm215 ones true=some(true,false,ones))
    (h0 : KTableCore.tm215 ones false=some(false,false,exit)) (vs : List V) (L R : V) :
    Reach (leftFrame exit (reverseFile vs L) R) (leftFrame exit L (file vs R)) := by
  induction vs generalizing L R with
  | nil => exact Reach.refl _
  | cons v vs ih => exact (ih _ _).trans ⟨v+2,return_block h1 hs h0 v L (file vs R)⟩
lemma return_nonempty {entry ones exit : Nat}
    (he : KTableCore.tm215 entry true=some(true,false,ones))
    (h1 : KTableCore.tm215 exit true=some(true,false,ones))
    (hs : KTableCore.tm215 ones true=some(true,false,ones))
    (h0 : KTableCore.tm215 ones false=some(false,false,exit))
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
  rw [bitPrefix_succ]
  congr 2
  ring
lemma carry_reverse_file (vs : List V) (L : V) :
    2*reverseCarry vs L+1=reverseFile vs (2*L+1) := by
  induction vs generalizing L with
  | nil => rfl
  | cons v vs ih => simpa only [reverseCarry,reverseFile,carry_reverse_block] using ih (reverseCarryBlock v L)

lemma carry_spares (n L R : V) :
    runFrom (3*n) (frameSparse 0 L (repeat3 6 n R))=
      frameSparse 0 (repeat3 5 n L) R := by
  have all : ∀ n : V, ∀ L R : V,
      runFrom (3*n) (frameSparse 0 L (repeat3 6 n R))=frameSparse 0 (repeat3 5 n L) R := by
    intro n
    induction n using ISigma1.pi1_succ_induction
    · definability
    case zero => intro L R; simp
    case succ n ih =>
      intro L R
      have hb : block (1:V) (repeat3 6 n R)=6+8*repeat3 6 n R := by
        simp only [block,bitPrefix_succ,bitPrefix_zero,digit_true]; ring
      have hc : reverseCarryBlock (1:V) L=5+8*L := by
        simp only [reverseCarryBlock,bitPrefix_succ,bitPrefix_zero,digit_true]; ring
      rw [show 3*(n+1)=(1+2)+3*n by ring,repeat3_succ,←hb,runFrom_add,carry_block,hc,ih,repeat3_push]
  exact all n L R
lemma return_spares (n L R : V) :
    runFrom (3*n) (leftFrame 40 (repeat3 3 n L) R)=
      leftFrame 40 L (repeat3 6 n R) := by
  have all : ∀ n : V, ∀ L R : V,
      runFrom (3*n) (leftFrame 40 (repeat3 3 n L) R)=leftFrame 40 L (repeat3 6 n R) := by
    intro n
    induction n using ISigma1.pi1_succ_induction
    · definability
    case zero => intro L R; simp
    case succ n ih =>
      intro L R
      have hb : reverseBlock (1:V) (repeat3 3 n L)=3+8*repeat3 3 n L := by
        simp only [reverseBlock,bitPrefix_succ,bitPrefix_zero,digit_true]; ring
      have hc : block (1:V) R=6+8*R := by
        simp only [block,bitPrefix_succ,bitPrefix_zero,digit_true]; ring
      rw [show 3*(n+1)=(1+2)+3*n by ring,repeat3_succ,←hb,runFrom_add,
        return_block (ones:=54) (by rfl) (by rfl) (by rfl),hc,ih,repeat3_push]
  exact all n L R
lemma carry_reverse_spares (n L : V) : 2*repeat3 5 n L+1=repeat3 3 n (2*L+1) := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih => rw [repeat3_succ,repeat3_succ,←ih]; ring

end DiophantineConsistency.ArithmeticRegisterBoxes215
