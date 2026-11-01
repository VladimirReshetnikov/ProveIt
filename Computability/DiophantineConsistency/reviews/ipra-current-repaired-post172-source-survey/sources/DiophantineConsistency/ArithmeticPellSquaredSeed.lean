import DiophantineConsistency.ArithmeticPellPeriodicity

/-! A direct strong Pell seed at index R*ycoord(R,a), in arbitrary IΣ1
models. Two-step quotient induction replaces arbitrary-modulus pigeonhole
for the displayed fourteen-variable carrier. Other converse witnesses remain. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticPellSquaredSeed
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellPeriodicity
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] xcoord ycoord

/-- Nonnegative quotient witnesses for every internal even block count. -/
theorem doubled_quotients (n R a : V) :
    ∃ r s : V,
      xcoord (2*n*R) a=1+ycoord R a*ycoord R a*r ∧
      ycoord (2*n*R) a=2*n*xcoord R a*ycoord R a+ycoord R a*ycoord R a*s := by
  let c:=ycoord R a
  let d:=xcoord R a
  change ∃ r s : V, xcoord (2*n*R) a=1+c*c*r ∧
    ycoord (2*n*R) a=2*n*d*c+c*c*s
  have hx2 : xcoord (2*R) a=1+2*delta a*c*c := double_x R a
  have hy2 : ycoord (2*R) a=2*d*c := double_y R a
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact ⟨0,0,by simp,by simp⟩
  case succ n ih =>
    obtain ⟨r,s,hx,hy⟩ := ih
    refine ⟨r+2*delta a+2*delta a*c*c*r+4*n*delta a*d*d+2*delta a*s*d*c,
      2*d*c*r+s+4*n*delta a*d*c+2*delta a*c*c*s,?_,?_⟩
    · rw [show 2*(n+1)*R=2*n*R+2*R by ring,
        (addition (2*n*R) (2*R) a).1,hx2,hy2,hx,hy]
      ring
    · rw [show 2*(n+1)*R=2*n*R+2*R by ring,
        (addition (2*n*R) (2*R) a).2,hx2,hy2,hx,hy]
      ring

/-- The odd block retains the full linear term and a natural quotient. -/
theorem odd_quotient (n R a : V) :
    ∃ s : V, ycoord ((2*n+1)*R) a=
      (2*n+1)*ycoord R a+ycoord R a*ycoord R a*s := by
  let c:=ycoord R a
  let d:=xcoord R a
  obtain ⟨r,s,hx,hy⟩ := doubled_quotients n R a
  change xcoord (2*n*R) a=1+c*c*r at hx
  change ycoord (2*n*R) a=2*n*d*c+c*c*s at hy
  have hn : d*d=1+delta a*c*c := norm R a
  refine ⟨c*r+2*n*delta a*c+s*d,?_⟩
  change ycoord ((2*n+1)*R) a=(2*n+1)*c+c*c*(c*r+2*n*delta a*c+s*d)
  rw [show (2*n+1)*R=2*n*R+R by ring,(addition (2*n*R) R a).2,hx,hy]
  change (1+c*c*r)*c+(2*n*d*c+c*c*s)*d=_
  calc
    (1+c*c*r)*c+(2*n*d*c+c*c*s)*d=
        c+2*n*c*(d*d)+c*c*(c*r+s*d) := by ring
    _=(2*n+1)*c+c*c*(c*r+2*n*delta a*c+s*d) := by rw [hn]; ring

/-- The original ordinate squared divides an explicitly indexed ordinate,
including rank zero. No search, period or divisibility premise is supplied. -/
theorem squared_ordinate (R a : V) :
    ∃ i : V, ycoord (R*ycoord R a) a=i*ycoord R a*ycoord R a := by
  let c:=ycoord R a
  let d:=xcoord R a
  change ∃ i : V, ycoord (R*c) a=i*c*c
  obtain ⟨n,h|h⟩ := even_or_odd c
  · obtain ⟨r,s,_,hy⟩ := doubled_quotients n R a
    change ycoord (2*n*R) a=2*n*d*c+c*c*s at hy
    refine ⟨d+s,?_⟩
    rw [show R*c=2*n*R by rw [h]; ring,hy,←h]
    ring
  · obtain ⟨s,hy⟩ := odd_quotient n R a
    change ycoord ((2*n+1)*R) a=(2*n+1)*c+c*c*s at hy
    refine ⟨1+s,?_⟩
    rw [show R*c=(2*n+1)*R by rw [h]; ring,hy,←h]
    ring

/-- The exact positive strong norm at the concrete index R*ycoord(R,a).
All private coordinates and both represented coordinate bindings are derived. -/
theorem strong_seed (R a : V) (hR : 0<R) :
    ∃ f i : V, 0<f ∧ 0<i ∧
      f=xcoord (R*ycoord R a) a ∧
      ycoord (R*ycoord R a) a=i*ycoord R a*ycoord R a ∧
      f*f=1+delta a*(i*ycoord R a*ycoord R a)*(i*ycoord R a*ycoord R a) := by
  let c:=ycoord R a
  have hc : 0<c := lt_of_lt_of_le hR (time_le_y R a)
  have ht : 0<R*c := mul_pos hR hc
  have hy : 0<ycoord (R*c) a := lt_of_lt_of_le ht (time_le_y (R*c) a)
  obtain ⟨i,hi⟩ := squared_ordinate R a
  change ycoord (R*c) a=i*c*c at hi
  have hi0 : 0<i := by
    apply pos_of_mul_pos_left (b := c*c) _ (by simp)
    rw [←mul_assoc, ←hi]
    exact hy
  have hf : 0<xcoord (R*c) a := lt_of_lt_of_le (by simp : (0:V)<1) (one_le_x (R*c) a)
  refine ⟨xcoord (R*c) a,i,hf,hi0,rfl,hi,?_⟩
  simpa only [hi] using norm (R*c) a

end DiophantineConsistency.ArithmeticPellSquaredSeed
