import DiophantineConsistency.Compact44.P64Early

/-! Unchecked draft: cancel the free carrier modulo its positive scale. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMainCarrierCancel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency P64Early P72Mu
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem cancel (q X Y y0 g c h : V)
    (hq3 : 3≤q) (hy0 : 0<y0) (hY : Y=q*(q*q)*y0)
    (hcar : (Y*Y)*g=(Y*Y)*(X+(X*Y+Y)*c)+(4*(X*Y+Y)+3)*h) :
    ∃ e mu : V, 0<e ∧ Y*Y=e*mu ∧ e∣9 ∧ 0<mu ∧
      q*(q*(q*q))≤mu ∧ mu∣h := by
  let U : V := Y*Y
  let H : V := 4*(X*Y+Y)+3
  let b : V := X+(X*Y+Y)*c
  have hq0 : 0<q := lt_of_lt_of_le (by norm_num) hq3
  have hY0 : 0<Y := by rw [hY]; exact mul_pos (mul_pos hq0 (mul_pos hq0 hq0)) hy0
  have hU0 : 0<U := mul_pos hY0 hY0
  change U*g=U*b+H*h at hcar
  have hmod : (H*h)%U=(H*0)%U := by
    have e1 : U*g=0+U*g := by simp
    have e2 : U*b+H*h=H*h+U*b := by ring
    have hh := congrArg (fun z : V => z%U) hcar
    rw [e1,e2,mod_add_mul' _ _ hU0,mod_add_mul' _ _ hU0] at hh
    simpa using hh.symm
  obtain ⟨e,mu,he0,hUmu,heH,hmu0,hmodmu⟩ := gcd_cancel U H h 0 hU0 hmod
  have heY : e∣Y*Y := ⟨mu,by simpa only [U] using hUmu⟩
  have heH' : e∣3+4*(X*Y+Y) := by
    have heq : H=3+4*(X*Y+Y) := by dsimp [H]; ring
    rw [←heq]
    exact heH
  have he9 : e∣9 := gcd_dvd_nine X Y e heY heH'
  have hele : e≤9 := Arithmetic.le_of_dvd (by norm_num) he9
  have hU9 : U≤9*mu := by rw [hUmu]; exact mul_le_mul_of_nonneg_right hele (Arithmetic.zero_le _)
  have hq6 : 9*(q*(q*(q*q)))≤U := by
    have hqq : 9≤q*q := by
      calc
        (9:V)=3*3 := by norm_num
        _≤q*q := mul_le_mul hq3 hq3 (by norm_num) (Arithmetic.zero_le _)
    have hY3 : q*(q*q)≤Y := by
      rw [hY]
      exact le_mul_of_one_le_right (Arithmetic.zero_le _) (pos_iff_one_le.mp hy0)
    calc
      9*(q*(q*(q*q)))≤(q*q)*(q*(q*(q*q))) := mul_le_mul_of_nonneg_right hqq (Arithmetic.zero_le _)
      _=(q*(q*q))*(q*(q*q)) := by ring
      _≤Y*Y := mul_le_mul hY3 hY3 (Arithmetic.zero_le _) (Arithmetic.zero_le _)
      _=U := rfl
  have hmu : q*(q*(q*q))≤mu :=
    le_of_mul_le_mul_left (le_trans hq6 hU9) (by norm_num : (0:V)<9)
  have hdiv : mu∣h := by
    apply mod_eq_zero_iff_dvd.mp
    simpa using hmodmu
  exact ⟨e,mu,he0,hUmu,he9,hmu0,hmu,hdiv⟩

#print axioms cancel
end FreeMainCarrierCancel
