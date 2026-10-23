import DiophantineConsistency.AnnotatedCodeArithmetic
import DiophantineConsistency.ArithmeticNonzero
import DiophantineConsistency.PairingRepresentation

/-! # Direct polynomial graphs for elementary annotated-code operations

These graph data represent the exact scalar operations independently of their
primitive-recursive implementations. They do not represent the full parser,
reference loop, or sealed-ZFC checker.
-/

namespace DiophantineConsistency.AnnotatedCodeGraphs

open AnnotatedCodeArithmetic AnnotatedProofCode

set_option maxRecDepth 12000
set_option maxHeartbeats 600000

abbrev G (f : Nat → Nat) := GraphRep (fun v : Fin 1 → Nat => f (v 0))

/-- For natural input and output, `(n²+out²)(out+1-n)²=0` is exactly
`out=pred n`, including the zero input. No extra witness is required. -/
def predecessor : G Nat.pred := by
  let n : Expr (Option (Fin 1)) := .var (some 0)
  let out : Expr (Option (Fin 1)) := .var none
  let d := out+1-n
  refine (Rep.equality ((n*n+out*out)*(d*d)) 0).ofIff ?_
  intro v
  change ((v (some 0):ℤ)*(v (some 0):ℤ)+(v none:ℤ)*(v none:ℤ))*
    (((v none:ℤ)+1-(v (some 0):ℤ))*((v none:ℤ)+1-(v (some 0):ℤ)))=0 ↔
      v none=(v (some 0)).pred
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hs | hd
    · have hn : (v (some 0):ℤ)=0 := by nlinarith [sq_nonneg (v (some 0):ℤ),sq_nonneg (v none:ℤ)]
      have ho : (v none:ℤ)=0 := by nlinarith [sq_nonneg (v (some 0):ℤ),sq_nonneg (v none:ℤ)]
      have hnn : v (some 0)=0 := by exact_mod_cast hn
      have hoo : v none=0 := by exact_mod_cast ho
      simp [hnn,hoo]
    · have hd : (v none:ℤ)+1-(v (some 0):ℤ)=0 :=
        (mul_eq_zero.mp hd).elim id id
      have hh : v none+1=v (some 0) := by omega
      rw [←hh,Nat.pred_succ]
  · intro h
    cases hn : v (some 0) with
    | zero => simp only [hn,Nat.pred_zero] at h; simp [h]
    | succ n => simp only [hn,Nat.pred_succ] at h; simp [h]

def treeLeft : G AnnotatedCodeArithmetic.treeLeft :=
  GraphRep.composeDirect GraphRep.unpairLeftCoordinate (fun _ => predecessor)

def treeRight : G AnnotatedCodeArithmetic.treeRight :=
  GraphRep.composeDirect GraphRep.unpairRightCoordinate (fun _ => predecessor)

def treeLeftChild : G AnnotatedCodeArithmetic.treeLeftChild :=
  GraphRep.composeDirect predecessor (fun _ => treeLeft)

def treeKind : G AnnotatedCodeArithmetic.treeKind :=
  GraphRep.ifEqDirect (GraphRep.coordinate 0) (GraphRep.constant 0) (GraphRep.constant 0)
    (GraphRep.ifEqDirect treeLeft (GraphRep.constant 0) (GraphRep.constant 1) (GraphRep.constant 2))

def listHead : G AnnotatedCodeArithmetic.listHead :=
  GraphRep.ifEqDirect (GraphRep.coordinate 0) (GraphRep.constant 0) (GraphRep.constant 0)
    (treeLeft.add (GraphRep.constant 1))

def listTail : G AnnotatedCodeArithmetic.listTail :=
  GraphRep.ifEqDirect (GraphRep.coordinate 0) (GraphRep.constant 0) (GraphRep.constant 0) treeRight

private theorem zero_pair (n : Nat) : Nat.pair 0 n=n*n := by
  cases n with
  | zero => rfl
  | succ n => simp [Nat.pair]

/-- The numeric atom constructor has the direct equation `out=n*n+1`.
It needs no additional natural witnesses. -/
def atomConstructor : G (fun n => Tree.quote (.atom n)) :=
  (Rep.equality (.var none)
    ((Expr.var (some (0 : Fin 1))) * .var (some 0) + .constant 1)).ofIff (fun v => by
      change (v none:ℤ)=(v (some 0):ℤ)*(v (some 0):ℤ)+1 ↔
        v none=Nat.pair 0 (v (some 0))+1
      rw [zero_pair]
      rw [←Int.natCast_mul]
      omega)

/-- A direct graph for `(a,b) ↦ pair(a+1,b)+1`. -/
def forkConstructor : GraphRep (fun v : Fin 2 → Nat => Nat.pair (v 0+1) (v 1)+1) := by
  let arguments : ∀ i : Fin 2, GraphRep
      (![fun v : Fin 2 → Nat => v 0+1,fun v : Fin 2 → Nat => v 1] i) :=
    Fin.cases ((GraphRep.coordinate 0).add (GraphRep.constant 1))
      (Fin.cases (GraphRep.coordinate 1) (fun i => Fin.elim0 i))
  exact (GraphRep.composeDirect GraphRep.pairCoordinates arguments).add (GraphRep.constant 1)

/-- Counts include every natural witness introduced by the supplied graph
constructors, including direct composition's input values. -/
theorem predecessor_witnessCount : predecessor.witnessCount=0 := rfl
theorem treeLeft_witnessCount : treeLeft.witnessCount=4 := by decide
theorem treeRight_witnessCount : treeRight.witnessCount=4 := by decide
theorem treeLeftChild_witnessCount : treeLeftChild.witnessCount=5 := by decide
theorem treeKind_witnessCount : treeKind.witnessCount=14 := by decide
theorem listHead_witnessCount : listHead.witnessCount=11 := by decide
theorem listTail_witnessCount : listTail.witnessCount=9 := by decide
theorem atomConstructor_witnessCount : atomConstructor.witnessCount=0 := rfl
theorem forkConstructor_witnessCount : forkConstructor.witnessCount=8 := by decide

end DiophantineConsistency.AnnotatedCodeGraphs
