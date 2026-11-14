import PA194PAeqTermSubstVecGrowth

/-! Uniform PAeq-substitution output growth for atomic formulas. This
is the base case for a full structural substitution bound, not such a bound. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA194PAeqSubstAtomicGrowth
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAWitnessCodeGrowth PA194PAeqTermSubstVecGrowth
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def atomic (p : V) : Prop :=
  (∃ k r v, p = ^rel k r v) ∨ (∃ k r v, p = ^nrel k r v) ∨ p = ^⊤ ∨ p = ^⊥

theorem relation_uniform (tag k r w v : V) (htag : tag ≤ 1) :
    let p := ⟪tag,k,r,v⟫ + 1
    ⟪tag,k,r,termSubstVec PA194PAeq.language k w v⟫ + 1 ≤ tau (w + 3*p + 8) (22*p + 26) := by
  let p : V := ⟪tag,k,r,v⟫ + 1
  have hk : k ≤ p := by
    exact le_trans (le_pair_left k ⟪r,v⟫) (le_trans (le_pair_right tag ⟪k,r,v⟫) le_self_add)
  have hr : r ≤ p := by
    exact le_trans (le_pair_left r v) (le_trans (le_pair_right k ⟪r,v⟫)
      (le_trans (le_pair_right tag ⟪k,r,v⟫) le_self_add))
  have hv : v ≤ p := by
    exact le_trans (le_pair_right r v) (le_trans (le_pair_right k ⟪r,v⟫)
      (le_trans (le_pair_right tag ⟪k,r,v⟫) le_self_add))
  apply le_trans (relation_le tag k r w v htag)
  apply tau_mono
  · calc
      w + v + k + r + 8 ≤ w + p + p + p + 8 :=
        add_le_add (add_le_add (add_le_add (add_le_add le_rfl hv) hk) hr) le_rfl
      _ = w + 3*p + 8 := by ring
  · calc
      20*v + 2*k + 26 ≤ 20*p + 2*p + 26 :=
        add_le_add (add_le_add (mul_le_mul' le_rfl hv) (mul_le_mul' le_rfl hk)) le_rfl
      _ = 22*p + 26 := by ring

theorem subst_atomic_le (w p : V) (hp : IsUFormula PA194PAeq.language p) (ha : atomic p) :
    subst PA194PAeq.language w p ≤ tau (w + 3*p + 8) (22*p + 26) := by
  have hthree (x : V) : x ≤ 3*x := by
    calc
      x ≤ x + (x + x) := le_self_add
      _ = 3*x := by ring
  rcases ha with ⟨k,r,v,rfl⟩ | ⟨k,r,v,rfl⟩ | rfl | rfl
  · obtain ⟨hr,hv⟩ := IsUFormula.rel.mp hp
    rw [substs_rel hr hv]
    simpa [qqRel] using relation_uniform (0 : V) k r w v (by simp)
  · obtain ⟨hr,hv⟩ := IsUFormula.nrel.mp hp
    rw [substs_nrel hr hv]
    simpa [qqNRel] using relation_uniform (1 : V) k r w v (by simp)
  · rw [substs_verum]
    exact le_trans (le_trans (hthree _) (le_trans le_add_self le_self_add)) (le_tau _ _)
  · rw [substs_falsum]
    exact le_trans (le_trans (hthree _) (le_trans le_add_self le_self_add)) (le_tau _ _)

/-- An atomic graph result has the same bound, with well-formedness supplied
by the actual substitution fixpoint graph. -/
theorem graph_atomic_le (w p y : V)
    (hg : (Substs.construction (V := V) PA194PAeq.language).Graph PA194PAeq.language w p y) (ha : atomic p) :
    y ≤ tau (w + 3*p + 8) (22*p + 26) := by
  have hp : IsUFormula PA194PAeq.language p := (UformulaRec1.Construction.Graph.case_iff.mp hg).1
  have hy : subst PA194PAeq.language w p = y := (Substs.construction PA194PAeq.language).result_eq_of_graph hg
  rw [←hy]
  exact subst_atomic_le w p hp ha

/-- An atomic graph output is bounded by one qVec-majorant step once B
covers its parameter and formula code. -/
theorem graph_atomic_step (w p y B : V)
    (hg : (Substs.construction (V := V) PA194PAeq.language).Graph PA194PAeq.language w p y)
    (ha : atomic p) (hB : w + 3*p + 1 ≤ B) :
    y ≤ tau (B+8) (22*B+22) := by
  have hthree : p ≤ 3*p := by
    calc p ≤ p+(p+p) := le_self_add
      _ = 3*p := by ring
  have hp : p+1 ≤ B :=
    le_trans (add_le_add (le_trans hthree le_add_self) le_rfl) hB
  have hw : w+3*p ≤ B := le_trans le_self_add hB
  apply le_trans (graph_atomic_le w p y hg ha)
  apply tau_mono (add_le_add hw le_rfl)
  calc
    22*p+26 ≤ 22*(p+1)+22 := by
      rw [show 22*(p+1)+22 = (22*p+26)+18 by ring]
      exact le_self_add
    _ ≤ 22*B+22 := add_le_add (mul_le_mul' le_rfl hp) le_rfl

#print axioms graph_atomic_step
#print axioms graph_atomic_le
#print axioms relation_uniform
#print axioms subst_atomic_le
end PA194PAeqSubstAtomicGrowth
