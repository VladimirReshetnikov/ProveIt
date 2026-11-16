module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualCommandAXInternal
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.ActualCommandStepGraph
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal ActualHeadGraphs
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The generated logical heads are zero or at least two. -/
def Sparse (x : V) : Prop := x=0 ∨ 2≤x

theorem sparse_four_mul (p : V) : Sparse (4*p) := by
  by_cases hp : p=0
  · simp [Sparse,hp]
  · have hone : (1 : V)≤p := one_le_of_zero_lt p (pos_iff_ne_zero.mpr hp)
    have hfour : (4 : V)≤4*p := by
      simpa using mul_le_mul_of_nonneg_left hone (show (0 : V)≤4 by simp)
    have h24 : (2 : V)≤4 := calc
      (2 : V) ≤ 2+1 := le_add_of_nonneg_right (by simp)
      _ ≤ (2+1)+1 := le_add_of_nonneg_right (by simp)
      _ = 4 := by rw [two_add_one_eq_three,three_add_one_eq_four]
    exact Or.inr (le_trans h24 hfour)

theorem sparse_ne_one {x : V} (hx : Sparse x) : x≠1 := by
  rcases hx with rfl|hx
  · simp
  · exact ne_of_gt (lt_of_lt_of_le (show (1 : V)<2 by simp) hx)

theorem sparse_add_ne_one {x y : V} (hx : Sparse x) (hy : Sparse y) : x+y≠1 := by
  rcases hx with rfl|hx
  · simpa using sparse_ne_one hy
  · exact ne_of_gt (lt_of_lt_of_le (show (1 : V)<2 by simp) (le_trans hx (by simp)))

theorem implication_sparse (a b : V) :
    Sparse (ActualArithmeticGraph.eval implicationExpr a b 0 0) := by
  simpa [implicationExpr,im,ActualArithmeticGraph.eval] using sparse_four_mul (pairValue a b)

theorem universal_ge_two (a b : V) :
    2≤ActualArithmeticGraph.eval universalExpr a b 0 0 := by
  simp [universalExpr,al,im,ActualArithmeticGraph.eval]

theorem universal_add_ne_one (a b t : V) :
    ActualArithmeticGraph.eval universalExpr a b 0 0+t≠1 := by
  exact ne_of_gt (lt_of_lt_of_le (show (1 : V)<2 by simp)
    (le_trans (universal_ge_two a b) (by simp)))

theorem schemaHeads_sparse (a b c d h : V) :
    ∀ z ∈ schemaHeads a b c d h, Sparse z := by
  intro z hz
  simp only [schemaHeads,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first
    | exact Or.inr (universal_ge_two d h)
    | (simp only [rho1Expr,rho2Expr,rho3Expr,rho4Expr,rho5Expr,rho6Expr,
        rho7Expr,rho8Expr,ex,neg,im,ActualArithmeticGraph.eval,Nat.cast_ofNat]
       exact sparse_four_mul _)

theorem gate_sparse (a b c d : V) : Sparse (gateValue a b c d) := by
  unfold gateValue
  split
  · exact Or.inl rfl
  · split
    · exact Or.inl rfl
    · simp only [bundleExpr,neg,im,ActualArithmeticGraph.eval,Nat.cast_ofNat]
      exact sparse_four_mul _

#print axioms schemaHeads_sparse
#print axioms gate_sparse

#print axioms sparse_four_mul
#print axioms sparse_add_ne_one
#print axioms universal_add_ne_one
end M6.PA.ActualCommandStepGraph
