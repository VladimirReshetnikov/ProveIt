module
public import M6.Source.Unpair
@[expose] public section
namespace M6.Source.Unpair

/-- The same literal decoder can add its head into a nonzero destination.
This is the exact behavior needed by MP's field reader, not a clean-zero alias. -/
theorem unpair_add (n h : Nat) (f : Registers) :
    Steps exactSites
      (loopCost n (0,0) + (3*(Cantor.decode n).2+1) + (3*(Cantor.decode n).1+1))
      (configAt 3933 ⟨n,h,0,0,f⟩)
      (exitAt ⟨(Cantor.decode n).2,h+(Cantor.decode n).1,0,0,f⟩) := by
  have body := loop n (0,0) h f
  have yclean := restore_y_w (Cantor.decode n).2 0 h (Cantor.decode n).1 f
  have xclean := restore_x_h (Cantor.decode n).1 (Cantor.decode n).2 h 0 f
  simp only [Cantor.pair, Cantor.triangle, Nat.add_zero] at body
  simp only [Nat.zero_add] at yclean
  exact steps_trans (steps_trans body yclean) xclean

#print axioms unpair_add
end M6.Source.Unpair

