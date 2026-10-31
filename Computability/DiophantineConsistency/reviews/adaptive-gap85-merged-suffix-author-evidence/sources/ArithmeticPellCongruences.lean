import DiophantineConsistency.ArithmeticPellClassification

/-! Actual internal residue witnesses and index order for the represented
Pell recurrence. These are arithmetic model theorems; the simultaneous
carrier witness construction and final PA/HA equation theorem remain open. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticPellCongruences
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellClassification
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Stronger than a residue assertion: both nonnegative quotients exist
at arbitrary internal time, including time0. -/
theorem residue_quotients (time b m : V) (hm : m∣b+1) :
    ∃ r s : V, xcoord time b=1+m*r ∧ ycoord time b=time+m*s := by
  obtain ⟨w,hw⟩ := hm
  have hbase : b+2=1+m*w := by
    calc
      b+2=(b+1)+1 := by ring
      _=1+m*w := by rw [hw]; ring
  have hd : delta b=m*w*(b+3) := by rw [delta,hw]
  induction time using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact ⟨0,0,by simp,by simp⟩
  case succ time ih =>
    obtain ⟨r,s,hx,hy⟩ := ih
    refine ⟨r+w*xcoord time b+w*(b+3)*ycoord time b,
      r+s+w*ycoord time b,?_,?_⟩
    all_goals
      simp only [x_succ,y_succ,hbase,hd,hx,hy]
      ring

theorem residue_divisibility (time b m : V) (hm : m∣b+1) :
    m∣xcoord time b-1 ∧ m∣ycoord time b-time := by
  obtain ⟨r,s,hx,hy⟩ := residue_quotients time b m hm
  exact ⟨⟨r,by rw [hx]; simp⟩,⟨s,by rw [hy]; simp⟩⟩

theorem residue_mod (time b m : V) (hm : m∣b+1) (hp : 0<m) :
    xcoord time b%m=1%m ∧ ycoord time b%m=time%m := by
  obtain ⟨r,s,hx,hy⟩ := residue_quotients time b m hm
  rw [hx,hy]
  exact ⟨mod_add_mul' 1 r hp,mod_add_mul' time s hp⟩

/-- The actual first-carrier scale gives a full quotient, not just a
standard-natural congruence. The caller's index identity is explicit. -/
theorem first_transport (time b Q R k : V) (hb : b+1=2*Q)
    (hk : k=2*ycoord time b) (hR : R+1=2*time) :
    ∃ s : V, k=R+1+(4*Q)*s := by
  have hm : 2*Q∣b+1 := ⟨1,by simpa only [mul_one] using hb⟩
  obtain ⟨_,s,_,hy⟩ := residue_quotients time b (2*Q) hm
  refine ⟨s,?_⟩
  rw [hk,hy,hR]
  ring

theorem first_difference_four (time b Q R k : V) (hb : b+1=2*Q)
    (hk : k=2*ycoord time b) (hR : R+1=2*time) :
    4*Q∣k-R-1 := by
  obtain ⟨s,hs⟩ := first_transport time b Q R k hb hk hR
  refine ⟨s,?_⟩
  rw [←tsub_add_eq_tsub_tsub,hs]
  simp

/-- Arbitrary internal norm solutions receive the same actual quotients. -/
theorem solution_residues (b x y m : V) (hn : x*x=1+delta b*y*y) (hm : m∣b+1) :
    ∃ time r s : V, time≤y ∧ xcoord time b=x ∧ ycoord time b=y ∧
      x=1+m*r ∧ y=time+m*s := by
  obtain ⟨time,ht,hx,hy⟩ := solution_index b x y hn
  obtain ⟨r,s,hr,hs⟩ := residue_quotients time b m hm
  exact ⟨time,r,s,ht,hx,hy,by rwa [←hx],by rwa [←hy]⟩

theorem y_add_ge (left right b : V) : ycoord left b+right≤ycoord (left+right) b :=
  ArithmeticPellRecurrence.ordinate_add_ge left right b

theorem y_strictMono (b : V) : StrictMono (fun time : V => ycoord time b) :=
  ArithmeticPellRecurrence.ordinate_strictMono b

theorem index_unique (b left right : V) (h : ycoord left b=ycoord right b) : left=right :=
  (y_strictMono b).injective h

end DiophantineConsistency.ArithmeticPellCongruences
