import ScaledStrongSeedAbove
import GeneralAuxiliarySeed

/-! Scaled strong and auxiliary Pell witnesses with a shared large index. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace TenPositiveScaledAuxiliarySeed
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticPellRecurrence TenPositiveScaledStrongSeedAbove TenPositiveGeneralAuxiliarySeed
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem scaled_auxiliary (a R tau L : V) (hphase : R%4=3) (htau : 0<tau) :
    let c:=ycoord R a
    let D:=ArithmeticPellRecurrence.delta a
    ∃ m i f T u y : V, L<m ∧ L<f ∧ 0<i ∧ 0<T ∧ 0<u ∧ 0<y ∧
      let U:=i*c*c
      let A:=D*U*U*tau*tau
      let F:=1+2*A
      let I:=D*(U*(2*tau*f))
      f*f=1+A ∧ xcoord (2*m) a=F ∧ ycoord (2*m) a=U*(2*tau*f) ∧
      F*F*c*T=u+c+F*F*R ∧ I*I*u*u+y*y=1+I*I*y*y := by
  let c:=ycoord R a
  let D:=ArithmeticPellRecurrence.delta a
  have hR : 0<R := (ArithmeticPellAuxiliarySeed.phase_indices R hphase).1
  have hc : 0<c := lt_of_lt_of_le hR (time_le_y R a)
  have hD : 0<D := by dsimp [D,ArithmeticPellRecurrence.delta]; exact mul_pos (by simp) (by simp)
  obtain ⟨m,i,f,hm,hi,hf,hym,hfx,hfnorm,hdoublex,hdoubley⟩ :=
    strong_seed_above a c tau L hc htau
  let U:=i*c*c
  let A:=D*U*U*tau*tau
  let F:=1+2*A
  let I:=D*(U*(2*tau*f))
  have hmpos : 0<m := lt_of_le_of_lt (by simp) hm
  have hfl : L<f := by
    have hy : m≤ycoord m a := time_le_y m a
    have hxy : ycoord m a<xcoord m a := ordinate_lt_abscissa a m
    rw [←hfx] at hxy
    exact lt_trans hm (lt_of_le_of_lt hy hxy)
  have hU : 0<U := mul_pos (mul_pos hi hc) hc
  have hA : 0<A := mul_pos (mul_pos (mul_pos (mul_pos hD hU) hU) htau) htau
  have hF : 0<F := add_pos (by simp) (mul_pos (by simp) hA)
  have hf1 : 1≤f := pos_iff_one_le.mp hf
  have hc1 : 1≤c := pos_iff_one_le.mp hc
  have hi1 : 1≤i := pos_iff_one_le.mp hi
  have ht1 : 1≤tau := pos_iff_one_le.mp htau
  have hD1 : 1≤D := pos_iff_one_le.mp hD
  have hU1 : 1≤U := pos_iff_one_le.mp hU
  have hI2 : 2≤I := by
    have hprod : 1≤D*U*tau*f := one_le_mul (one_le_mul (one_le_mul hD1 hU1) ht1) hf1
    calc
      (2:V)=2*1 := by ring
      _≤2*(D*U*tau*f) := mul_le_mul_of_nonneg_left hprod (by simp)
      _=I := by dsimp [I]; ring
  have hfn : f*f=1+A := hfnorm
  have hFn : F*F=1+D*(U*(2*tau*f))*(U*(2*tau*f)) := by
    calc
      F*F=1+4*A*(1+A) := by dsimp [F]; ring
      _=1+4*A*(f*f) := by rw [hfn]
      _=1+D*(U*(2*tau*f))*(U*(2*tau*f)) := by dsimp [A]; ring
  have hnorm : I*I+D=D*F*F := by
    calc
      I*I+D=D*(1+D*(U*(2*tau*f))*(U*(2*tau*f))) := by dsimp [I]; ring
      _=D*(F*F) := by rw [hFn]
      _=D*F*F := by ring
  have hIc : c∣I := ⟨D*i*c*(2*tau*f),by dsimp [I,U]; ring⟩
  have hfc : F*F=1+c*(D*i*i*c*c*c*(2*tau*f)*(2*tau*f)) := by
    rw [hFn]
    dsimp [U]
    ring
  obtain ⟨T,u,y,hT,hu,hy,_hycoord,_hux,hlit,haux⟩ :=
    auxiliary_of_strong a c R F I (D*i*i*c*c*c*(2*tau*f)*(2*tau*f))
      hphase hc rfl hI2 hF hnorm hIc hfc
  have hx : xcoord (2*m) a=F := by
    rw [hdoublex]
    dsimp [F,A,U,D]
    ring
  exact ⟨m,i,f,T,u,y,hm,hfl,hi,hT,hu,hy,hfn,hx,hdoubley,hlit,haux⟩

#print axioms TenPositiveScaledAuxiliarySeed.scaled_auxiliary
end TenPositiveScaledAuxiliarySeed
