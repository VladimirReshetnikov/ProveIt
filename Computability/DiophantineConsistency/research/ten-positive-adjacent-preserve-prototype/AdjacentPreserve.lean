import ProductRoot
import DiophantineConsistency.ArithmeticAdaptiveFirstDivisibility2011

/-! Reduced-denominator preservation under the adjacent Pell step. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositiveAdjacentPreserve
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticGcdNormalization
open DiophantineConsistency.ArithmeticSignedPairs
open DiophantineConsistency.ArithmeticAdaptiveFirstDivisibility2011
open TenPositiveProductRoot
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Adding denominator multiples to the two sides of a signed numerator
preserves coprimality with the denominator, also after taking magnitude. -/
theorem reduced_signed_shift (r m x y : V) (hm : 0<m) (hu : Bez r m 1) :
    Bez (magnitude (r+m*x,m*y)) m 1 := by
  apply bez_of_common_divisors
  intro d hdmag hdm
  by_cases hd0 : d=0
  · subst d
    have : m=0 := by simpa using hdm
    exact False.elim ((ne_of_gt hm) this)
  have hdp : 0<d := pos_iff_ne_zero.mpr hd0
  have hM : m%d=0 := mod_eq_zero_iff_dvd.mpr hdm
  have hP : (r+m*x)%d=r%d := by
    rw [mod_add hdp,mod_mul hdp,hM,zero_mul,zero_mod,add_zero,
      mod_eq_self_of_lt (mod_lt r hdp)]
  have hN : (m*y)%d=0 := by
    rw [mod_mul hdp,hM,zero_mul,zero_mod]
  have hmod := magnitude_mod (r+m*x,m*y) d hdp hdmag
  change (r+m*x)%d=(m*y)%d at hmod
  rw [hP,hN] at hmod
  have hdr : d∣r := mod_eq_zero_iff_dvd.mp hmod
  exact bez_divisor hu hdr hdm

/-- The signed numerator of the adjacent Pell transform remains reduced.
B is Q−1, so 2Q−1=1+2B; m∣B follows from m²∣B. -/
theorem adjacent_step_reduced (B r m v : V) (hm : 0<m)
    (hu : Bez r m 1) (hB : m∣B) :
    Bez (magnitude ((1+2*B)*r,2*(1+B)*m*v)) m 1 := by
  obtain ⟨t,ht⟩ := hB
  have hp : (1+2*B)*r=r+m*(2*t*r) := by rw [ht]; ring
  have hn : 2*(1+B)*m*v=m*(2*(1+B)*v) := by ring
  rw [hp,hn]
  exact reduced_signed_shift r m (2*t*r) (2*(1+B)*v) hm hu


/-- The square-divisibility conclusion from the denominator step supplies
the divisibility required by reducedness preservation. -/
theorem adjacent_step_reduced_square (B r m v : V) (hm : 0<m)
    (hu : Bez r m 1) (hB : m*m∣B) :
    Bez (magnitude ((1+2*B)*r,2*(1+B)*m*v)) m 1 := by
  obtain ⟨t,ht⟩ := hB
  have hB' : m∣B := ⟨m*t,by rw [ht]; ring⟩
  exact adjacent_step_reduced B r m v hm hu hB'


/-- When m² divides B, the signed first-coordinate numerator has an
integral magnitude divisible by m; the quotient is displayed explicitly. -/
theorem adjacent_first_coordinate (B m v r t : V) (hB : B=(m*m)*t) :
    magnitude ((1+2*B)*(m*v),2*B*r) =
      m*magnitude ((1+2*B)*v,2*m*t*r) := by
  rw [hB]
  dsimp [magnitude]
  rw [mul_add,mul_tsub,mul_tsub]
  congr 1 <;> congr 1 <;> ring

/-- The adjacent transform preserves the cross-multiplied norm over every
commutative ring. Positivity, descent and denominator arguments are separate. -/
theorem adjacent_norm_identity {R : Type*} [CommRing R] (B X r m : R)
    (h : (1+B)*(X*X)=m*m+B*(r*r)) :
    let Xnew := (1+2*B)*X-2*B*r
    let rnew := (1+2*B)*r-2*(1+B)*X
    (1+B)*(Xnew*Xnew)=m*m+B*(rnew*rnew) := by
  dsimp
  simp only [←mul_assoc]
  calc
    (1+B)*((1+2*B)*X-2*B*r)*((1+2*B)*X-2*B*r) =
        ((1+B)*(X*X)-B*(r*r))+B*((1+2*B)*r-2*(1+B)*X)*((1+2*B)*r-2*(1+B)*X) := by ring
    _=(m*m+B*(r*r)-B*(r*r))+B*((1+2*B)*r-2*(1+B)*X)*((1+2*B)*r-2*(1+B)*X) := by rw [h]
    _=m*m+B*((1+2*B)*r-2*(1+B)*X)*((1+2*B)*r-2*(1+B)*X) := by ring

#print axioms TenPositiveAdjacentPreserve.reduced_signed_shift
#print axioms TenPositiveAdjacentPreserve.adjacent_step_reduced
#print axioms TenPositiveAdjacentPreserve.adjacent_step_reduced_square
#print axioms TenPositiveAdjacentPreserve.adjacent_first_coordinate
#print axioms TenPositiveAdjacentPreserve.adjacent_norm_identity
end TenPositiveAdjacentPreserve
