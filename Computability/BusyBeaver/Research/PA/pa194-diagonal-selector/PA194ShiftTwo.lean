import PA194Words
set_option autoImplicit false
namespace PA194ShiftTwo
open M6.Source.Cantor PA196.Commands PA194Words

theorem shift_two (g a b w d : Nat) (hg : g ≠ 1) (ha : a ≠ 1) :
    PA194Words.run [.shift,.shift] ⟨g,pair a (pair b w),d,0⟩ =
      some ⟨a,w,d,b⟩ := by
  simp [PA194Words.run,PA194Words.step,PA194CommandTransfer.step,decode_pair,hg,ha]

#print axioms shift_two
end PA194ShiftTwo
