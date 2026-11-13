module
public import M6.Source.AXPairDrains
@[expose] public section
namespace M6.Source.AXPair
variable {sites : Array Site} {offset : Nat} (hbound : Bound sites offset)
include hbound
/-- The diagonal walk terminates by decreasing X, accumulating its triangular
number. Its inner transfer loops preserve the complete unrelated register frame. -/
theorem pair_loop (s w y : Nat) (f : Registers) :
    ∃ n, Steps sites n (configAt offset 35 ⟨0,w,s,y,f⟩)
      (configAt offset 41 ⟨0,w,0,y+Cantor.triangle s,f⟩) := by
  induction s generalizing y with
  | zero =>
    refine ⟨1,?_⟩
    apply Steps.cons
    rw [step_35 hbound]
    simp only [↓reduceIte,Cantor.triangle,Nat.add_zero]
    exact Steps.refl _
  | succ s ih =>
    obtain ⟨n,hn⟩ := ih (y+1+s)
    have a : Steps sites 2 (configAt offset 35 ⟨0,w,s+1,y,f⟩)
        (configAt offset 37 ⟨0,w,s,y+1,f⟩) := by
      apply Steps.cons
      rw [step_35 hbound]
      simp only [Nat.add_sub_cancel,Nat.succ_ne_zero,↓reduceIte]
      apply Steps.cons
      rw [step_36 hbound]
      exact Steps.refl _
    have b : Steps sites (3*s+1) (configAt offset 37 ⟨0,w,s,y+1,f⟩)
        (configAt offset 40 ⟨s,w,0,y+1,f⟩) := by
      simpa only [Nat.zero_add] using drain_x hbound 0 w s (y+1) f
    have c : Steps sites 1 (configAt offset 40 ⟨s,w,0,y+1,f⟩)
        (configAt offset 31 ⟨s,w,0,y+1,f⟩) := by
      apply Steps.cons
      rw [step_40 hbound]
      exact Steps.refl _
    have d : Steps sites (4*s+1) (configAt offset 31 ⟨s,w,0,y+1,f⟩)
        (configAt offset 35 ⟨0,w,s,y+1+s,f⟩) := by
      simpa only [Nat.zero_add] using drain_t_xy hbound s w 0 (y+1) f
    refine ⟨2+(3*s+1)+1+(4*s+1)+n,?_⟩
    simpa only [Cantor.triangle,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      (((a.append b).append c).append d).append hn

/-- Ten-row arithmetic core, without assuming surrounding push instructions. -/
theorem pair (t w x : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps sites n (configAt offset 31 ⟨t,w,x,0,f⟩)
      (configAt offset 41 ⟨0,w,0,Cantor.pair x t,f⟩) := by
  have a : Steps sites (4*t+1) (configAt offset 31 ⟨t,w,x,0,f⟩)
      (configAt offset 35 ⟨0,w,x+t,t,f⟩) := by
    simpa only [Nat.zero_add] using drain_t_xy hbound t w x 0 f
  obtain ⟨n,hn⟩ := pair_loop hbound (x+t) w t f
  refine ⟨4*t+1+n,by omega,?_⟩
  simpa only [Cantor.pair,Nat.add_comm] using a.append hn
#print axioms pair
end M6.Source.AXPair

