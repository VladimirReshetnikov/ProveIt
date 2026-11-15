import PA194PAeqLessCongrTyped
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeq.LessShift
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PA194PAeq.AddOne

theorem shiftLess (a b : Tm) : (less a b).shift = less (Rew.shift a) (Rew.shift b) := by
  have hshift (t : Tm) : (Rew.shift.q) (Rew.bShift t) = Rew.bShift (Rew.shift t) := by exact Rew.q_comp_bShift_app Rew.shift t
  simp only [Rew.shift,Rew.map,Rew.q,emptyFn,Matrix.vecCons_empty_eq_singleton] at hshift
  change Semiformula.rewAux Rew.shift (less a b) = _
  simp [less,Semiformula.rewAux,Rew.shift,Rew.map,Rew.func,Rew.q,eq,add,succ,emptyFn,hshift]
  rfl
#print axioms shiftLess
end PA194PAeq.LessShift
