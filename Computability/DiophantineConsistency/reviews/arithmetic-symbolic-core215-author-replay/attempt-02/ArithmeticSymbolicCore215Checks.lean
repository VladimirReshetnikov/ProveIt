import DiophantineConsistency.ArithmeticSymbolicCore215

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticSymbolicCore215Checks
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticSymbolicCore215 ArithmeticRegisterBoxes215 ArithmeticMachineTape215
open KRuntimeCore (SConf BoxSt Branch Seg)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (v : Fin 9 → V) (k L : V) (hk : 0<k) {q q' : Nat} {br : Branch}
    {x x' : BoxSt} {e : Bool} (h : KRuntimeCore.oracle q br x=some (q',x',e))
    (hv : BranchValid br v) :
    ReachPos (frameSparse q L (boxValue v k x))
      (leftFrame q' (if e then 2*L+1 else L) (boxValue v k x')) := oracle_actual v k L hk h hv
example (gap : V) (v : Fin 9 → V) (k : V) (hk : 0<k) {br : Branch}
    (hv : BranchValid br v) {s t : SConf} {m : Bool}
    (h : KRuntimeCore.sstep KTableCore.tm215 br s=some (t,m)) :
    StepOk gap v k s t m := sstep_actual gap v k hk hv h
example (gap : V) (v : Fin 9 → V) (k : V) (hk : 0<k) {br : Branch}
    (hv : BranchValid br v) {fuel : Nat} {s t : SConf} {target : SConf → Bool}
    (h : KRuntimeCore.exec KTableCore.tm215 br target fuel s false=some t) :
    target t=true ∧ ReachPos (interpret gap v k s) (interpret gap v k t) := exec_actual gap v k hk hv h
example (gap : V) (v : Fin 9 → V) (k : V) {s t : SConf}
    (h : KRuntimeCore.sMatches s t=true) : interpret gap v k s=interpret gap v k t := matches_actual gap v k h
example (v : Fin 9 → V) (k : V) : boxValue v k (.mark 9)=plain v k := by
  simp [boxValue,boxTail,plainTail]
example (v : Fin 9 → V) (k : V) (b : Bool) (xs : List Seg) :
    flatValue 0 v k (.run b 3 0::xs) 0=flatValue 0 v k xs 0 := by
  simp [flatValue,segValue]
example (v : Fin 9 → V) (k L : V) :
    leftFrame 84 (2*L+digit true) (boxValue v k (.plain .none))=
      frameSparse 84 L (2*plain v k+1) := by rw [leftFrame_bit]; rfl
example (v : Fin 9 → Nat) (k : Nat) :
    plain v k=ArithmeticMachinePerm252.bitsCode (KRuntimeCore.sepsR (List.ofFn v++List.replicate k 1)) := plain_nat v k
example (v : Fin 9 → Nat) (k : Nat) :
    marked v 8 k=ArithmeticMachinePerm252.bitsCode (KRuntimeCore.sepsM 8 (List.ofFn v++List.replicate k 1)) := marked_nat v 8 k
example (v : Fin 9 → Nat) (r : Fin 9) (k : Nat) :
    boxValue v k (.plain (.inc r))=ArithmeticMachinePerm252.bitsCode
      (KRuntimeCore.boxList (.plain (.inc r)) (List.ofFn v++List.replicate k 1)) := increment_nat v r k
example (v : Fin 9 → Nat) (r : Fin 9) (k : Nat) :
    boxValue v k (.plain (.dec r))=ArithmeticMachinePerm252.bitsCode
      (KRuntimeCore.boxList (.plain (.dec r)) (List.ofFn v++List.replicate k 1)) := decrement_nat v r k
#print axioms boxTail_even
#print axioms oracle_actual
#print axioms peelLeft_actual
#print axioms peelRight_actual
#print axioms sstep_actual
#print axioms execWith_actual
#print axioms exec_actual
#print axioms flatTok_push
#print axioms flatTok_norm
#print axioms flatTok_normL
#print axioms matches_actual
#print axioms plain_nat
#print axioms marked_nat
#print axioms increment_nat
#print axioms decrement_nat
end DiophantineConsistency.ArithmeticSymbolicCore215Checks
