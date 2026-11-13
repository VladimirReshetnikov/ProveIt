import DiophantineConsistency.ArithmeticGcdNormalization

/-! Square divisibility in every IΣ₁ model, by the internal Bézout gcd. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticSquareDivisibility
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticGcdNormalization
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- No prime factorization or standardness premise; z may be zero. -/
theorem dvd_of_square_dvd (m z : V) (hm : 0<m) (h : m*m ∣ z*z) : m∣z := by
  obtain ⟨g,hg⟩ := gcd_certificate_exists z m
  obtain ⟨b,hz⟩ := hg.1
  obtain ⟨a,hmul⟩ := hg.2.1
  have hgpos : 0<g := pos_of_mul_pos_left (by rw [←hmul]; exact hm) (by simp)
  obtain ⟨u,v,w,t,he⟩ := hg.2.2
  have hunit : Bez b a 1 := by
    refine ⟨u,v,w,t,?_⟩
    apply mul_left_cancel₀ (ne_of_gt hgpos)
    calc
      g*(1+b*u+a*v)=g+z*u+m*v := by rw [hz,hmul]; ring
      _=z*w+m*t := he
      _=g*(b*w+a*t) := by rw [hz,hmul]; ring
  obtain ⟨c,hc⟩ := h
  have hs : b*b=a*a*c := by
    apply mul_left_cancel₀ (ne_of_gt (mul_pos hgpos hgpos))
    calc
      (g*g)*(b*b)=z*z := by rw [hz]; ring
      _=(m*m)*c := hc
      _=(g*g)*(a*a*c) := by rw [hmul]; ring
  have hab : a∣b*b := ⟨a*c,by rw [hs]; ring⟩
  have hab' : a∣b := unit_certificate_cancel hunit hab
  have ha1 : a∣(1:V) := bez_divisor hunit hab' (dvd_refl a)
  have hap : 0<a := pos_of_mul_pos_right (by rw [←hmul]; exact hm) (by simp)
  have ha : a=1 := le_antisymm (le_of_dvd (by simp) ha1) (pos_iff_one_le.mp hap)
  refine ⟨b,?_⟩
  rw [hz,hmul,ha]
  simp

end DiophantineConsistency.ArithmeticSquareDivisibility
