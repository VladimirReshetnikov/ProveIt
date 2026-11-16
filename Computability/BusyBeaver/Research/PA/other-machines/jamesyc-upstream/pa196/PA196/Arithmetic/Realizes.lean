module
public import PA196.Arithmetic.WordSelectors
@[expose] public section
namespace PA196.Arithmetic.CommandStep
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open M6.PA M6.PA.SourceCantorInternal HeadGraphs CommandWord LiteralWords VectorAppend Commands
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
  · right; rw [he,gen_value]

 theorem realizes_mp (major minor a b : V)
    (hmajor : Realizes major (ActualArithmeticGraph.eval implicationExpr a b 0 0))
    (hminor : Realizes minor a) :
    Realizes (append major (append (literalValue (atoms Commands.push))
      (append minor (append (literalValue (atoms Commands.push)) (mpWord b))))) b := by
  intro t w
  simp only [word_append]
  rcases hmajor t w with he | he
  · left; simp only [he,word_halted]
  · rw [he,push_value]
    rcases hminor 0 (pairValue (ActualArithmeticGraph.eval implicationExpr a b 0 0) w) with hm | hm
    · left; simp only [hm,word_halted]
    · rw [hm,push_value,mpWord_value]
      by_cases h : a=1
      · left; simp only [h,ite_true]
      · right; simp only [h,ite_false]

theorem realizes_head1 (a b : V) :
    Realizes (selectedHeadWord 6 a b 0) (ActualArithmeticGraph.eval head1Expr a b 0 0) := by
  intro t w
  exact Or.inr (selectedHead6_value a b 0 t w)
theorem realizes_head2 (a b c : V) :
    Realizes (selectedHeadWord 5 a c b) (ActualArithmeticGraph.eval head2Expr a b c 0) := by
  intro t w
  exact Or.inr (selectedHead5_value a c b t w)
theorem realizes_head3 (a b c : V) :
    Realizes (selectedHeadWord 4 a c b) (ActualArithmeticGraph.eval head3Expr a b c 0) := by
  intro t w
  exact Or.inr (selectedHead4_value a c b t w)
theorem realizes_head4 (a b c : V) :
    Realizes (selectedHeadWord 3 a c b) (ActualArithmeticGraph.eval head4Expr a b c 0) := by
  intro t w
  exact Or.inr (selectedHead3_value a c b t w)
theorem realizes_head5 (a b : V) :
    Realizes (selectedHeadWord 2 a b 0) (ActualArithmeticGraph.eval head5Expr a b 0 0) := by
  intro t w
  exact Or.inr (selectedHead2_value a b 0 t w)
theorem realizes_head6 (a b c : V) :
    Realizes (selectedHeadWord 1 a c b) (ActualArithmeticGraph.eval head6Expr a b c 0) := by
  intro t w
  exact Or.inr (selectedHead1_value a c b t w)
theorem realizes_rho8 (a b c u : V) (hu : u ≤ a) :
    Realizes (rho8Word a b c u) (ActualArithmeticGraph.eval rho8Expr a b c u) := by
  intro t w
  exact Or.inr (rho8Word_value a b c u t w hu)

theorem realizes_gate (a b c : V) : Realizes (gateWord a b c) (gateValue a b c 0) := by
  intro t w
  exact Or.inr (gateWord_value a b c t w)

#print axioms realizes_rho8
#print axioms realizes_gate
#print axioms realizes_gen
#print axioms realizes_mp
end PA196.Arithmetic.CommandStep
