import DiophantineConsistency.ReducedNormInduction
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace ReducedNormNormalization
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticGcdNormalization
open ReducedNormInduction
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem denominator_divides {r v y d : V} (hr : 0<r) (hd : 0<d)
    (hn : (r+1)*(v*d)*(v*d)=r*(y*y)+d*d) : d∣y := by
  obtain ⟨g,hg⟩ := gcd_certificate_exists y d
  obtain ⟨a,ha⟩ := hg.1
  obtain ⟨b,hb⟩ := hg.2.1
  have hg0 : 0<g := pos_of_mul_pos_left (by rw [←hb]; exact hd) (by simp)
  have hb0 : 0<b := pos_of_mul_pos_right (by rw [←hb]; exact hd) (by simp)
  obtain ⟨u,vv,w,z,he⟩ := hg.2.2
  have hunit : Bez a b 1 := by
    refine ⟨u,vv,w,z,?_⟩
    apply mul_left_cancel₀ (ne_of_gt hg0)
    calc
      g*(1+a*u+b*vv)=g+y*u+d*vv := by rw [ha,hb]; ring
      _=y*w+d*z := he
      _=g*(a*w+b*z) := by rw [ha,hb]; ring
  have hred : (r+1)*(v*b)*(v*b)=r*(a*a)+b*b := by
    apply mul_left_cancel₀ (ne_of_gt (mul_pos hg0 hg0))
    calc
      (g*g)*((r+1)*(v*b)*(v*b))=(r+1)*(v*d)*(v*d) := by rw [hb]; ring
      _=r*(y*y)+d*d := hn
      _=(g*g)*(r*(a*a)+b*b) := by rw [ha,hb]; ring
  have hone : b=1 := reduced_denominator_one hr hb0 hunit hred
  subst b
  have hdg : d=g := by simpa using hb
  rw [hdg,ha]
  exact ⟨a,rfl⟩
end ReducedNormNormalization
#print axioms ReducedNormNormalization.denominator_divides
