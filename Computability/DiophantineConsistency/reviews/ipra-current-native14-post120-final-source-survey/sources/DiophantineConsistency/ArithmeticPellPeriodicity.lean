import DiophantineConsistency.ArithmeticPellCongruences

/-! Internal reflection and period witnesses for the represented Pell sequence.
Every index and quotient is an element of the arithmetic model. The period
is the actual first-coordinate modulus, not a standard-natural surrogate.
Full carrier index recovery and simultaneous witnesses remain separate. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticPellPeriodicity
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellClassification ArithmeticPellCongruences
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem double_x (time b : V) :
    xcoord (2*time) b=1+2*delta b*ycoord time b*ycoord time b := by
  rw [two_mul,(addition time time b).1,norm time b]
  ring

theorem double_x_add_one (time b : V) :
    xcoord (2*time) b+1=2*xcoord time b*xcoord time b := by
  rw [double_x,show 2*xcoord time b*xcoord time b=2*(xcoord time b*xcoord time b) by ring,
    norm time b]
  ring

theorem double_y (time b : V) :
    ycoord (2*time) b=2*xcoord time b*ycoord time b := by
  rw [two_mul,(addition time time b).2]
  ring

/-- Reflection in additive form avoids any unproved subtraction identity. -/
theorem reflection_add (left right b : V) :
    ycoord (left+2*right) b=
      ycoord left b+2*xcoord (left+right) b*ycoord right b := by
  calc
    ycoord (left+2*right) b=
        xcoord (left+right) b*ycoord right b+ycoord (left+right) b*xcoord right b := by
      rw [show left+2*right=(left+right)+right by ring,(addition (left+right) right b).2]
    _=ycoord left b*(xcoord right b*xcoord right b)+
        2*xcoord left b*xcoord right b*ycoord right b+
        delta b*ycoord left b*ycoord right b*ycoord right b := by
      rw [(addition left right b).1,(addition left right b).2]
      ring
    _=ycoord left b+2*xcoord (left+right) b*ycoord right b := by
      rw [norm right b,(addition left right b).1]
      ring

theorem reflection (n m b : V) (hm : m≤n) :
    ycoord (n+m) b=ycoord (n-m) b+2*xcoord n b*ycoord m b := by
  simpa only [two_mul, ← add_assoc, tsub_add_cancel_of_le hm] using
    reflection_add (n-m) m b

/-- Explicit nonnegative quotients for the whole state at index4n. -/
theorem four_quotients (n b : V) :
    ∃ r s : V, xcoord (4*n) b=1+xcoord n b*r ∧
      ycoord (4*n) b=xcoord n b*s := by
  refine ⟨8*delta b*xcoord n b*ycoord n b*ycoord n b,
    4*xcoord (2*n) b*ycoord n b,?_,?_⟩
  · rw [show 4*n=2*(2*n) by ring,double_x,double_y]
    ring
  · rw [show 4*n=2*(2*n) by ring,double_y,double_y]
    ring

/-- A genuine Sigma1 induction supplies quotients at arbitrarily many
internal periods. This proves more than equality of sampled remainders. -/
theorem period_quotients (blocks n start b : V) :
    ∃ r s : V,
      xcoord (4*n*blocks+start) b=xcoord start b+xcoord n b*r ∧
      ycoord (4*n*blocks+start) b=ycoord start b+xcoord n b*s := by
  obtain ⟨rx,ry,hx4,hy4⟩ := four_quotients n b
  induction blocks using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact ⟨0,0,by simp,by simp⟩
  case succ blocks ih =>
    obtain ⟨r,s,hx,hy⟩ := ih
    refine ⟨r+rx*xcoord (4*n*blocks+start) b+delta b*ry*ycoord (4*n*blocks+start) b,
      s+rx*ycoord (4*n*blocks+start) b+ry*xcoord (4*n*blocks+start) b,?_,?_⟩
    all_goals
      simp only [show 4*n*(blocks+1)+start=4*n+(4*n*blocks+start) by ring,
        (addition (4*n) (4*n*blocks+start) b).1,
        (addition (4*n) (4*n*blocks+start) b).2, hx4, hy4, hx, hy]
      ring

theorem period_mod (blocks n start b : V) :
    xcoord (4*n*blocks+start) b%xcoord n b=xcoord start b%xcoord n b ∧
    ycoord (4*n*blocks+start) b%xcoord n b=ycoord start b%xcoord n b := by
  obtain ⟨r,s,hx,hy⟩ := period_quotients blocks n start b
  have hp : 0<xcoord n b := lt_of_lt_of_le (by simp : (0:V)<1) (one_le_x n b)
  rw [hx,hy]
  exact ⟨mod_add_mul' _ r hp,mod_add_mul' _ s hp⟩

theorem y_lt_x (time b : V) : ycoord time b<xcoord time b :=
  ArithmeticPellRecurrence.ordinate_lt_abscissa b time

/-- In the first n-window, equal actual residues identify the internal index. -/
theorem index_eq_of_mod (i j n b : V) (hi : i≤n) (hj : j≤n)
    (h : ycoord i b%xcoord n b=ycoord j b%xcoord n b) : i=j := by
  have hi' : ycoord i b<xcoord n b :=
    lt_of_le_of_lt ((y_strictMono b).monotone hi) (y_lt_x n b)
  have hj' : ycoord j b<xcoord n b :=
    lt_of_le_of_lt ((y_strictMono b).monotone hj) (y_lt_x n b)
  rw [mod_eq_self_of_lt hi',mod_eq_self_of_lt hj'] at h
  exact index_unique b i j h

end DiophantineConsistency.ArithmeticPellPeriodicity
