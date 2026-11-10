import DiophantineConsistency.BFS943.ScaledWitnessFromUnscaled
import DiophantineConsistency.BFS943.ScaledOffsetGeneric
import DiophantineConsistency.BFS943.ScaledKappaGeneric
import DiophantineConsistency.ArithmeticPellCongruences

/-! Fresh scaled first/main pair and both natural carrier quotients. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace TenPositiveScaledReverseStart
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticPellRecurrence ArithmeticPellHalfIndex ArithmeticPellCongruences
open TenPositiveScaledWitnessFromUnscaled TenPositiveScaledOffsetGeneric TenPositiveScaledKappaGeneric
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem scaled_start (X Y mu r eta zeta : V)
    (hX : 1≤X) (hY : 1≤Y) (hmu : 1≤mu) (hr : 0<r)
    (hXeq : X=Exp.exp (2*r+1)) (h72 : 72*r<X+1)
    (heta : 0<eta) (hzeta : 0<zeta)
    (hck : ycoord (2*r+1) (Y*(X+1))=
      2*ycoord (r+1) (2*(X*Y*Y-1)+1)*Y+eta)
    (hk : 2*ycoord (r+1) (2*(X*Y*Y-1)+1)=eta+zeta) :
    let P:=X*(mu*Y)*(mu*Y)
    let B:=2*(P-1)+1
    let a:=(mu*Y)*(X+1)-1
    let K:=2*ycoord (r+1) B
    let C:=ycoord (2*r+1) a
    ∃ eta' zeta' rho kappa tau : V, 0<eta' ∧ 0<zeta' ∧ 0<kappa ∧ 0<tau ∧
      C=K*Y+eta' ∧ K=eta'+zeta' ∧ K=(2*r+1)+1+(mu*mu)*rho ∧
      X<C ∧ X*(3*C-2*X)+2=(4*a+3)*kappa ∧
      tau*tau=1+P*(P+1)*K*K := by
  let S:=mu*Y
  let P:=X*S*S
  let B:=2*(P-1)+1
  let a:=S*(X+1)-1
  let K:=2*ycoord (r+1) B
  let C:=ycoord (2*r+1) a
  have hXpos : 0<X := lt_of_lt_of_le (by simp) hX
  have hYpos : 0<Y := lt_of_lt_of_le (by simp) hY
  have hmupos : 0<mu := lt_of_lt_of_le (by simp) hmu
  have hS : 1≤S := one_le_mul hmu hY
  have hSpos : 0<S := lt_of_lt_of_le (by simp) hS
  have hSY : Y≤S := le_mul_of_one_le_left (by simp) hmu
  obtain ⟨eta',zeta',heta',hzeta',hC,hK⟩ :=
    scaled_witnesses X Y S r eta zeta hX hY hSY hr hXeq h72 heta hzeta hck hk
  change C=K*Y+eta' at hC
  change K=eta'+zeta' at hK
  obtain ⟨rho,hoff⟩ := scaled_offset X Y mu r hXpos hYpos hmupos
  have hP : 0<P := mul_pos (mul_pos hXpos hSpos) hSpos
  have hP1 : P-1+1=P := tsub_add_cancel_of_le (pos_iff_one_le.mp hP)
  have hn2 : 2≤r+1 := by
    have hh := _root_.add_le_add (pos_iff_one_le.mp hr) (le_refl (1:V))
    simpa only [show (2:V)=1+1 by ring] using hh
  have hKbound : 8*P+4≤K := by
    calc
      8*P+4=2*ycoord 2 B := by
        rw [y_two]
        dsimp [B]
        have he : 2*(P-1)+1+2=2*(P-1+1)+1 := by ring
        rw [he,hP1]
        ring
      _≤2*ycoord (r+1) B := mul_le_mul_of_nonneg_left ((y_strictMono B).monotone hn2) (by simp)
      _=K := rfl
  have hXP : X≤P := by
    calc
      X≤X*S := le_mul_of_one_le_right (by simp) hS
      _≤X*S*S := le_mul_of_one_le_right (by simp) hS
  have hPK : P<K := lt_of_le_of_lt (le_mul_of_one_le_left (by simp) (by norm_num : (1:V)≤8))
    (lt_of_lt_of_le (by simp : 8*P<8*P+4) hKbound)
  have hCgt : X<C := calc
    X≤P := hXP
    _<K := hPK
    _≤K*Y := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hY (by simp : (0:V)≤K)
    _<C := by rw [hC]; exact lt_add_of_pos_right _ heta'
  obtain ⟨kappa,hkappa,hkap⟩ := positive_kappa a (2*r+1) X hXeq hCgt
  let tau:=xcoord (r+1) B
  have htau : 0<tau := lt_of_lt_of_le (by simp : (0:V)<1) (one_le_x (r+1) B)
  have hdelta : ArithmeticPellRecurrence.delta B=4*P*(P+1) := by
    dsimp [B,ArithmeticPellRecurrence.delta]
    calc
      (2*(P-1)+1+1)*(2*(P-1)+1+3)=4*(P-1+1)*(P-1+1+1) := by ring
      _=4*P*(P+1) := by rw [hP1]
  have hnorm : tau*tau=1+P*(P+1)*K*K := by
    have hh := norm (r+1) B
    rw [hdelta] at hh
    dsimp [tau,K]
    calc
      xcoord (r+1) B*xcoord (r+1) B=1+4*P*(P+1)*ycoord (r+1) B*ycoord (r+1) B := hh
      _=1+P*(P+1)*(2*ycoord (r+1) B)*(2*ycoord (r+1) B) := by ring
  exact ⟨eta',zeta',rho,kappa,tau,heta',hzeta',hkappa,htau,hC,hK,hoff,hCgt,hkap,hnorm⟩

#print axioms TenPositiveScaledReverseStart.scaled_start
end TenPositiveScaledReverseStart
