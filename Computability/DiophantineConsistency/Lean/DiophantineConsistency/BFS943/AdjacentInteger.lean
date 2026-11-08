import DiophantineConsistency.BFS943.AdjacentComplete

/-! Construct the reduced fraction and discharge its denominator. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositiveAdjacentInteger
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticGcdNormalization
open TenPositiveAdjacentComplete
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Adjacent-Pell scaled norm supplies its integral quotient; no reducedness
or scale-divides-numerator premise is supplied by the caller. -/
theorem quotient_of_scaled_norm (B M v z : V) (hB : 0<B) (hM : 0<M) (hv : 0<v)
    (h : (1+B)*((M*v)*(M*v))=M*M+B*(z*z)) :
    ∃ y : V, z=M*y ∧ (1+B)*(v*v)=1+B*(y*y) := by
  obtain ⟨g,hg⟩ := gcd_certificate_exists z M
  obtain ⟨r,hr⟩ := hg.1
  obtain ⟨m,hm⟩ := hg.2.1
  have hgpos : 0<g := pos_of_mul_pos_left (by rw [←hm]; exact hM) (by simp)
  have hmpos : 0<m := pos_of_mul_pos_right (by rw [←hm]; exact hM) (by simp)
  obtain ⟨u,v0,w,t,he⟩ := hg.2.2
  have hu : Bez r m 1 := by
    refine ⟨u,v0,w,t,?_⟩
    apply mul_left_cancel₀ (ne_of_gt hgpos)
    calc
      g*(1+r*u+m*v0)=g+z*u+M*v0 := by rw [hr,hm]; ring
      _=z*w+M*t := he
      _=g*(r*w+m*t) := by rw [hr,hm]; ring
  have hn : (1+B)*((m*v)*(m*v))=m*m+B*(r*r) := by
    apply mul_left_cancel₀ (ne_of_gt (mul_pos hgpos hgpos))
    calc
      (g*g)*((1+B)*((m*v)*(m*v)))=(1+B)*((M*v)*(M*v)) := by rw [hm]; ring
      _=M*M+B*(z*z) := h
      _=(g*g)*(m*m+B*(r*r)) := by rw [hm,hr]; ring
  have hm1 : m=1 := denominator_one B m v r hB hmpos hv hu hn
  have hM_eq : M=g := by simpa [hm1] using hm
  have hz : z=M*r := by rw [hr,hM_eq]
  have hnorm : (1+B)*(v*v)=1+B*(r*r) := by simpa [hm1] using hn
  exact ⟨r,hz,hnorm⟩

#print axioms TenPositiveAdjacentInteger.quotient_of_scaled_norm
end TenPositiveAdjacentInteger
