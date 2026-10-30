import DiophantineConsistency.ArithmeticAdaptiveExactIndices2011

/-! Main correction divisibility and the adaptive q | 3X projection. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptivePowerProjection2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptiveFirstDivisibility2011
open ArithmeticAdaptiveTransport2011 ArithmeticAdaptiveMainOrientation2011
open ArithmeticAdaptiveExactIndices2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def Projection (p : Fin 4 → ℕ) (v : Fin 13 → V) : Prop :=
  let q : V := 1+v 0*(p 0:V)
  q∣3*v 6 ∧ q≤3*v 6

theorem projection_of_facts (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hq : 1<1+v 0*(p 0:V)) (hv : ∀j,0<v j)
    (hgap : v 1+v 2<1+v 0*(p 0:V))
    (hY : ∃ s:V, v 7=(1+v 0*(p 0:V))^3*s)
    (he : ExactIndices p v) : Projection p v := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let X : V := v 6
  let Y : V := v 7
  let U : V := Y*(q*q)
  let E : V := X*Y
  let Q : V := E*Y
  let k : V := v 9+v 10
  let c : V := v 9+Y*k
  let a : V := E+Y
  let H : V := 3+4*a
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  let R' : V := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)
  have hq0 : 0<q := lt_trans (by simp : (0:V)<1) hq
  have hF : v 1≤q := le_trans (by simp : v 1≤v 1+v 2) (le_of_lt hgap)
  have hbq : q-1=b := by dsimp [q]; rw [add_comm]; simp
  have hRank : R=R' := by dsimp [R,R']; rw [hbq]; simp only [pow_two]; ring
  obtain ⟨s,hs⟩ := hY
  obtain ⟨first,main,n,m,t,_,_,_,_,_,_,hk,_,horient,_,_,_,_⟩ := he
  change k=R+1+4*Q*t at hk
  let W : V := 4*X*q*s*t
  have hscale : 4*Q*t=U*W := by dsimp [Q,E,U,W,Y]; rw [hs]; ring
  have hrep := main_root_rep p v (le_of_lt hq) hF
  have hroot := equivalent_trans (equivalent_symm hrep) horient
  change (U*(X+a*c)+H*(U*v 12+E*q+R'+1))+0=H*k+U*main at hroot
  simp only [add_zero] at hroot
  rw [←hRank,hk,hscale] at hroot
  have hcancel : U*(main+H*W)=U*(X+a*c+H*v 12)+H*(E*q) := by
    apply add_right_cancel (b:=H*(R+1))
    calc
      U*(main+H*W)+H*(R+1)=H*(R+1+U*W)+U*main := by ring
      _=U*(X+a*c)+H*(U*v 12+E*q+R+1) := hroot.symm
      _=(U*(X+a*c+H*v 12)+H*(E*q))+H*(R+1) := by ring
  have hqY : 0<q*Y := mul_pos hq0 (hv 7)
  have hqeq : q*(main+H*W)=q*(X+a*c+H*v 12)+H*X := by
    apply mul_left_cancel₀ (ne_of_gt hqY)
    calc
      (q*Y)*(q*(main+H*W))=U*(main+H*W) := by dsimp [U]; ring
      _=U*(X+a*c+H*v 12)+H*(E*q) := hcancel
      _=(q*Y)*(q*(X+a*c+H*v 12)+H*X) := by dsimp [U,E]; ring
  let d : V := 4*(q*q)*s*(X+1)
  have hH : H=3+q*d := by dsimp [H,a,E,d,Y]; rw [hs]; ring
  have hqeq' : q*(main+H*W)=3*X+q*(X+a*c+H*v 12+d*X) := calc
    _=q*(X+a*c+H*v 12)+H*X := hqeq
    _=3*X+q*(X+a*c+H*v 12+d*X) := by rw [hH]; ring
  have hdiv : q∣3*X := by
    apply mod_eq_zero_iff_dvd.mp
    have hm := congrArg (fun z : V => z%q) hqeq'
    rw [show q*(main+H*W)=0+q*(main+H*W) by ring,
      mod_add_mul' _ _ hq0,mod_add_mul' _ _ hq0,zero_mod] at hm
    exact hm.symm
  exact ⟨hdiv,Arithmetic.le_of_dvd (mul_pos (by simp) (hv 6)) hdiv⟩

theorem expressionAt_projection (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : InternalZero (expressionAt (fun j => (p j:ℤ))) v) : Projection p v := by
  have hp := scaled_parameters_positive p v hb hv
  have hgap := tsub_pos_iff_lt.mp (expressionAt_transport_positive p v hb hv hz).2
  obtain ⟨s,_,hs⟩ := expressionAt_Y_quotient p v hb hv hz
  have hs' : v 7=(1+v 0*(p 0:V))^3*s := by
    simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using hs
  exact projection_of_facts p v hp.1 hv hgap ⟨s,hs'⟩ (expressionAt_exact_indices p v hb hl hh hv hz)

theorem current_projection (v : Fin 13 → V) (hv : ∀j,0<v j)
    (hz : InternalZero expression v) : Projection currentPorts v := by
  have hp := current_parameters_positive v hv
  have hgap := tsub_pos_iff_lt.mp (current_transport_positive v hv hz).2
  obtain ⟨s,_,hs⟩ := current_Y_quotient v hv hz
  have hs' : v 7=(1+v 0*(CurrentMasks2011.beta:V))^3*s := by
    simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using hs
  have hy : ∃s:V, v 7=(1+v 0*(currentPorts 0:V))^3*s := by
    refine ⟨s,?_⟩
    simpa only [currentPorts,Matrix.cons_val_zero] using hs'
  apply projection_of_facts currentPorts v
  · simpa only [currentPorts,Matrix.cons_val_zero] using hp.1
  · exact hv
  · simpa only [currentPorts,Matrix.cons_val_zero] using hgap
  · exact hy
  · exact current_exact_indices v hv hz

theorem current_natural_projection (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    Projection currentPorts (fun j => v j+1) :=
  current_projection _ (fun j => lt_of_le_of_lt (Arithmetic.zero_le (v j)) (lt_add_one _))
    ((internalZero_positiveShift expression v).mp hz)
end DiophantineConsistency.ArithmeticAdaptivePowerProjection2011
