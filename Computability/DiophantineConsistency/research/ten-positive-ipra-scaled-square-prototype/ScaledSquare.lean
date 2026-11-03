import DiophantineConsistency.ModelProductPell

/-! Normalization for the rational-square step in the ten-positive
product-square proof. Abstract model arithmetic only. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositiveScaledSquare
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticGcdNormalization
open DiophantineConsistency.ModelProductPell
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A coprime ratio that is a square after multiplying by positive squares
has square numerator and denominator, in every IΣ₁ model. -/
theorem scaled_square_of_coprime (a b z m : V)
    (ha : 0<a) (hm : 0<m) (hu : Bez a b 1)
    (h : a*(z*z)=(m*m)*b) :
    ∃ x y : V, a=x*x ∧ b=y*y := by
  obtain ⟨g,hg⟩ := gcd_certificate_exists z m
  obtain ⟨z',hz⟩ := hg.1
  obtain ⟨m',hm'⟩ := hg.2.1
  have hgpos : 0<g := pos_of_mul_pos_left (by rw [←hm']; exact hm) (by simp)
  have hmpos : 0<m' := pos_of_mul_pos_right (by rw [←hm']; exact hm) (by simp)
  obtain ⟨u,v,w,t,he⟩ := hg.2.2
  have hunit : Bez z' m' 1 := by
    refine ⟨u,v,w,t,?_⟩
    apply mul_left_cancel₀ (ne_of_gt hgpos)
    calc
      g*(1+z'*u+m'*v)=g+z*u+m*v := by rw [hz,hm']; ring
      _=z*w+m*t := he
      _=g*(z'*w+m'*t) := by rw [hz,hm']; ring
  have heq : a*(z'*z')=(m'*m')*b := by
    apply mul_left_cancel₀ (ne_of_gt (mul_pos hgpos hgpos))
    calc
      (g*g)*(a*(z'*z'))=a*(z*z) := by rw [hz]; ring
      _=(m*m)*b := h
      _=(g*g)*((m'*m')*b) := by rw [hm']; ring
  have hmdiv : m'∣a*(z'*z') := ⟨m'*b, by rw [heq]; ring⟩
  have hmdiv1 : m'∣z'*(a*z') := by simpa only [mul_comm,mul_left_comm,mul_assoc] using hmdiv
  have hmdiv2 : m'∣a*z' := unit_certificate_cancel hunit hmdiv1
  have hmdiv3 : m'∣z'*a := by simpa only [mul_comm] using hmdiv2
  obtain ⟨d,hd⟩ := unit_certificate_cancel hunit hmdiv3
  have heq' : d*(z'*z')=m'*b := by
    apply mul_left_cancel₀ (ne_of_gt hmpos)
    calc
      m'*(d*(z'*z'))=a*(z'*z') := by rw [hd]; ring
      _=(m'*m')*b := heq
      _=m'*(m'*b) := by ring
  have hdivd : m'∣d*(z'*z') := ⟨b,heq'⟩
  have hdivd1 : m'∣z'*(d*z') := by simpa only [mul_comm,mul_left_comm,mul_assoc] using hdivd
  have hdivd2 : m'∣d*z' := unit_certificate_cancel hunit hdivd1
  have hdivd3 : m'∣z'*d := by simpa only [mul_comm] using hdivd2
  obtain ⟨s,hs⟩ := unit_certificate_cancel hunit hdivd3
  have hasa : a=(m'*m')*s := by rw [hd,hs]; ring
  have hbs : b=s*(z'*z') := by
    apply mul_left_cancel₀ (ne_of_gt hmpos)
    calc
      m'*b=d*(z'*z') := heq'.symm
      _=m'*(s*(z'*z')) := by rw [hs]; ring
  have hsA : s∣a := ⟨m'*m',by rw [hasa]; ring⟩
  have hsB : s∣b := ⟨z'*z',by rw [hbs]⟩
  have hsone : s∣(1:V) := bez_divisor hu hsA hsB
  have hspos : 0<s := pos_of_mul_pos_right (by rw [←hasa]; exact ha) (by simp)
  have hs1 : s=1 := le_antisymm (le_of_dvd (by simp : (0:V)<1) hsone) (pos_iff_one_le.mp hspos)
  refine ⟨m',z',?_,?_⟩
  · simpa [hs1] using hasa
  · simpa [hs1] using hbs


/-- A unit certificate remains valid when its second argument is replaced
by one of its divisors. -/
theorem restrict_right_certificate {a b c : V} (hd : c∣b) (hu : Bez a b 1) :
    Bez a c 1 := by
  obtain ⟨t,ht⟩ := hd
  obtain ⟨u,v,w,z,he⟩ := hu
  refine ⟨u,t*v,w,t*z,?_⟩
  rw [ht] at he
  simpa only [mul_assoc] using he

/-- If G is coprime to delta*Dy, the actual cross-multiplied product
relation forces G to be a square. No divisibility of z by m is assumed. -/
theorem scaled_product_factor_square (delta z m G Dy : V)
    (hm : 0<m) (hu : Bez G (delta*Dy) 1)
    (h : delta*(z*z)=(m*m)*(G*Dy)) : ∃ g : V, G=g*g := by
  obtain ⟨d,hd⟩ := gcd_certificate_exists z m
  obtain ⟨z',hz⟩ := hd.1
  obtain ⟨m',hm'⟩ := hd.2.1
  have hdpos : 0<d := pos_of_mul_pos_left (by rw [←hm']; exact hm) (by simp)
  have hmpos : 0<m' := pos_of_mul_pos_right (by rw [←hm']; exact hm) (by simp)
  obtain ⟨u,v,w,t,he⟩ := hd.2.2
  have hunit : Bez z' m' 1 := by
    refine ⟨u,v,w,t,?_⟩
    apply mul_left_cancel₀ (ne_of_gt hdpos)
    calc
      d*(1+z'*u+m'*v)=d+z*u+m*v := by rw [hz,hm']; ring
      _=z*w+m*t := he
      _=d*(z'*w+m'*t) := by rw [hz,hm']; ring
  have heq : delta*(z'*z')=(m'*m')*(G*Dy) := by
    apply mul_left_cancel₀ (ne_of_gt (mul_pos hdpos hdpos))
    calc
      (d*d)*(delta*(z'*z'))=delta*(z*z) := by rw [hz]; ring
      _=(m*m)*(G*Dy) := h
      _=(d*d)*((m'*m')*(G*Dy)) := by rw [hm']; ring
  have hdiv : m'∣z'*(delta*z') := ⟨m'*(G*Dy),by
    calc
      z'*(delta*z')=delta*(z'*z') := by ring
      _=(m'*m')*(G*Dy) := heq
      _=m'*(m'*(G*Dy)) := by ring⟩
  have hdelta1 : m'∣delta*z' := unit_certificate_cancel hunit hdiv
  have hdelta2 : m'∣z'*delta := by simpa only [mul_comm] using hdelta1
  obtain ⟨e,he⟩ := unit_certificate_cancel hunit hdelta2
  have heq' : e*(z'*z')=m'*(G*Dy) := by
    apply mul_left_cancel₀ (ne_of_gt hmpos)
    calc
      m'*(e*(z'*z'))=delta*(z'*z') := by rw [he]; ring
      _=(m'*m')*(G*Dy) := heq
      _=m'*(m'*(G*Dy)) := by ring
  have hediv : m'∣z'*(e*z') := ⟨G*Dy,by
    calc
      z'*(e*z')=e*(z'*z') := by ring
      _=m'*(G*Dy) := heq'⟩
  have hediv' : m'∣e*z' := unit_certificate_cancel hunit hediv
  have hediv'' : m'∣z'*e := by simpa only [mul_comm] using hediv'
  obtain ⟨f,hf⟩ := unit_certificate_cancel hunit hediv''
  have hdelta : delta=(m'*m')*f := by rw [he,hf]; ring
  have hfinal : f*(z'*z')=G*Dy := by
    apply mul_left_cancel₀ (ne_of_gt hmpos)
    calc
      m'*(f*(z'*z'))=e*(z'*z') := by rw [hf]; ring
      _=m'*(G*Dy) := heq'
  have hfactor : f*Dy∣delta*Dy := ⟨m'*m',by rw [hdelta]; ring⟩
  have hbez : Bez G (f*Dy) 1 := restrict_right_certificate hfactor hu
  apply pp_square_of_coprime G (f*Dy) (f*z') hbez
  calc
    G*(f*Dy)=f*(G*Dy) := by ring
    _=f*(f*(z'*z')) := by rw [hfinal]
    _=(f*z')*(f*z') := by ring

#print axioms TenPositiveScaledSquare.scaled_square_of_coprime
#print axioms TenPositiveScaledSquare.scaled_product_factor_square
end TenPositiveScaledSquare
