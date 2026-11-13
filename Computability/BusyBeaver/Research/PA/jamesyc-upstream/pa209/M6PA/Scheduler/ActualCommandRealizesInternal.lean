module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualCommandHeadsInternal
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.ActualCommandStepGraph
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal ActualHeadGraphs ActualCommandWordGraph ActualCommandLiteralInternal
open M6.Source M6.Source.CommandAtomEncoding M6.Source.ActualCommandMacros
open InternalTrace.HFSAppend
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Clean-state semantic invariant for a single encoded word. Early halting is
allowed; a normal result preserves the entire source-Cantor tail. -/
def Realizes (word a : V) : Prop := ∀ t w,
  wordValue word (stateCode t w 0 0)=0 ∨
  wordValue word (stateCode t w 0 0)=stateCode a w 0 0

 theorem realizes_gen (word a u : V) (ha : Realizes word a) :
    Realizes (append word (genWord u)) (ActualArithmeticGraph.eval universalExpr u a 0 0) := by
  intro t w
  rw [word_append]
  rcases ha t w with he | he
  · left; rw [he,word_halted]
  · right; rw [he,GEN_value]

 theorem realizes_mp (major minor a b : V)
    (hmajor : Realizes major (ActualArithmeticGraph.eval implicationExpr a b 0 0))
    (hminor : Realizes minor a) :
    Realizes (append major (append (literalValue (atoms PUSH))
      (append minor (append (literalValue (atoms PUSH)) (mpWord b))))) b := by
  intro t w
  simp only [word_append]
  rcases hmajor t w with he | he
  · left; simp only [he,word_halted]
  · rw [he,PUSH_value]
    rcases hminor 0 (pairValue (ActualArithmeticGraph.eval implicationExpr a b 0 0) w) with hm | hm
    · left; simp only [hm,word_halted]
    · rw [hm,PUSH_value,MP_value]
      by_cases h : a=1
      · left; simp only [h,ite_true]
      · right; simp only [h,ite_false]

theorem realizes_head1 (a b c : V) :
    Realizes (selectedHeadWord 1 a b c) (ActualArithmeticGraph.eval rho1Expr a b c 0) := by
  intro t w
  exact Or.inr (selectedHead1_value a b c t w)
theorem realizes_head2 (a b c : V) :
    Realizes (selectedHeadWord 2 a b c) (ActualArithmeticGraph.eval rho2Expr a b c 0) := by
  intro t w
  exact Or.inr (selectedHead2_value a b c t w)
theorem realizes_head3 (a b c : V) :
    Realizes (selectedHeadWord 3 a b c) (ActualArithmeticGraph.eval rho3Expr a b c 0) := by
  intro t w
  exact Or.inr (selectedHead3_value a b c t w)
theorem realizes_head4 (a b c : V) :
    Realizes (selectedHeadWord 4 a b c) (ActualArithmeticGraph.eval rho4Expr a b c 0) := by
  intro t w
  exact Or.inr (selectedHead4_value a b c t w)
theorem realizes_head5 (a b c : V) :
    Realizes (selectedHeadWord 5 a b c) (ActualArithmeticGraph.eval rho5Expr a b c 0) := by
  intro t w
  exact Or.inr (selectedHead5_value a b c t w)
theorem realizes_head6 (a b c : V) :
    Realizes (selectedHeadWord 6 a b c) (ActualArithmeticGraph.eval rho6Expr a b c 0) := by
  intro t w
  exact Or.inr (selectedHead6_value a b c t w)
theorem realizes_head7 (a b c : V) :
    Realizes (selectedHeadWord 7 a b c) (ActualArithmeticGraph.eval rho7Expr a b c 0) := by
  intro t w
  exact Or.inr (selectedHead7_value a b c t w)
theorem realizes_head8 (a b c u : V) (hu : u≤a) :
    Realizes (headEightWord a b c u) (ActualArithmeticGraph.eval rho8Expr a b c u) := by
  intro t w
  exact Or.inr (headEight_value a b c u t w hu)
theorem realizes_gate (a b c : V) : Realizes (gateCodeWord a b c) (gateValue a b c 0) := by
  intro t w
  exact Or.inr (gateWord_value a b c t w)

#print axioms realizes_head8
#print axioms realizes_gate
#print axioms realizes_gen
#print axioms realizes_mp
end M6.PA.ActualCommandStepGraph

