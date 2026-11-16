module
public import M6PA.Theory
public import M6PA.Calibration.ActualCertificateNeighborhoodBinders
@[expose] public section

/-! Genuine numeric neighborhood existential witness from actual R1/R7. -/
namespace M6.PA.ActualCertificateEquivalence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCertificateConstructors ActualCertificateConstructors.Dominated
open ActualCheckerBlueprint ActualHeadGraphs
universe u
variable {V : Type u} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]


noncomputable def primitiveToSpecialNeighborhood (a b : V) :
    Certificate (wim (weq a b) (neighborhoodEquality a b (wel a b))) := by
  let k := wel a b
  let h : Context [weq a b] (weq a b) := .assumption (by simp)
  let hs := Context.mp h (.closed (primitiveSymmetry a b))
  let l := Context.andIntro
    (.mp h (.closed (memLeftRewrite k a b)))
    (.mp hs (.closed (memLeftRewrite k b a)))
  let r := Context.andIntro
    (.mp h (.closed (memRightRewrite k a b)))
    (.mp hs (.closed (memRightRewrite k b a)))
  have hv : ∀ f, f ∈ [weq a b] → Certificate (wim f (wal k f)) := by
    intro f hf
    have hf' : f = weq a b := List.mem_singleton.mp hf
    subst f
    exact actualSpecialVacuity a b
  exact (Context.andIntro (l.generalize k hv) (r.generalize k hv)).deduction.empty


theorem wel_left_lt (a b : V) : a < wel a b := by
  have h : SourceCantorInternal.pairValue a b ≤ wim a b := by
    change SourceCantorInternal.pairValue a b ≤ 4 * SourceCantorInternal.pairValue a b
    exact Arithmetic.le_mul_of_pos_left (by norm_num)
  exact lt_of_le_of_lt (le_trans (SourceCantorInternal.pairValue_bounds a b).1 h) (lt_add_one _)

theorem wel_right_lt (a b : V) : b < wel a b := by
  have h : SourceCantorInternal.pairValue a b ≤ wim a b := by
    change SourceCantorInternal.pairValue a b ≤ 4 * SourceCantorInternal.pairValue a b
    exact Arithmetic.le_mul_of_pos_left (by norm_num)
  exact lt_of_le_of_lt (le_trans (SourceCantorInternal.pairValue_bounds a b).2 h) (lt_add_one _)

noncomputable def primitiveToNeighborhood (a b z : V) (hza : z ≠ a) (hzb : z ≠ b) :
    Certificate (wim (weq a b)
      (ActualArithmeticGraph.eval RelationalSource.Numeric.neighborhoodExpr a b z 0)) := by
  rw [neighborhood_expr_eq]
  exact implicationCompose (primitiveToSpecialNeighborhood a b)
    (neighborhoodBinderChangeCore a b (wel a b) z
      (ne_of_gt (wel_left_lt a b)) (ne_of_gt (wel_right_lt a b)) hza hzb)

noncomputable def neighborhoodWitness (x c z : V) (hzx : z ≠ x) (hzc : z ≠ c) :
    Certificate (wex x (ActualArithmeticGraph.eval RelationalSource.Numeric.neighborhoodExpr x c z 0)) :=
  (r1 x c).mp (existentialMonotonicity x (primitiveToNeighborhood x c z hzx hzc))

#print axioms primitiveToSpecialNeighborhood
#print axioms wel_left_lt
#print axioms wel_right_lt
#print axioms primitiveToNeighborhood
#print axioms neighborhoodWitness
end M6.PA.ActualCertificateEquivalence

