import Trace74Mask

/-! UNCHECKED DRAFT. Conditional same-output gauge for the actual 74 circuit. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74ConditionalGauge
open DiophantineConsistency TenPositiveTrace75
variable {R : Type*} [CommRing R]

theorem same_output_of_transport_equations (p : Fin 4 → R) (v u : Fin 10 → R)
    (hJ : u 0=v 0) (hi : u 3=v 3) (hw : u 5=v 5) (hs : u 6=v 6)
    (heta : u 8=v 8) (hzeta : u 9=v 9)
    (hT : (regs p (Trace74Mask.oldVal p v)).c*(u 4-v 4)=
      (regs p (Trace74Mask.oldVal p u)).rank-(regs p (Trace74Mask.oldVal p v)).rank)
    (hN : let rv := regs p (Trace74Mask.oldVal p v)
      let ru := regs p (Trace74Mask.oldVal p u)
      rv.h*rv.D*(u 7-v 7)=(rv.h*rv.D*(rv.V*rv.V)+rv.D)*(ru.B-rv.B)-rv.h*(ru.rank-rv.rank)) :
    Trace74Mask.value74 p u=Trace74Mask.value74 p v := by
  let ov := Trace74Mask.oldVal p v
  let ou := Trace74Mask.oldVal p u
  let rv := regs p ov
  let ru := regs p ou
  have h0 : ou 0=ov 0 := by simpa [ou,ov,Trace74Mask.oldVal] using hJ
  have h3 : ou 3=ov 3 := by simpa [ou,ov,Trace74Mask.oldVal] using hi
  have h5 : ou 5=ov 5 := by simpa [ou,ov,Trace74Mask.oldVal] using hw
  have h6 : ou 6=ov 6 := by simpa [ou,ov,Trace74Mask.oldVal] using hs
  have h8 : ou 8=ov 8 := by simpa [ou,ov,Trace74Mask.oldVal] using heta
  have h9 : ou 9=ov 9 := by simpa [ou,ov,Trace74Mask.oldVal] using hzeta
  have h4u : ou 4=u 4 := by simp [ou,Trace74Mask.oldVal]
  have h4v : ov 4=v 4 := by simp [ov,Trace74Mask.oldVal]
  have h7u : ou 7=u 7 := by simp [ou,Trace74Mask.oldVal]
  have h7v : ov 7=v 7 := by simp [ov,Trace74Mask.oldVal]
  have hh : ru.h=rv.h := by simp only [ru,rv,h_def,h0]
  have hq : ru.q=rv.q := by simp only [ru,rv,q_def,hh]
  have hX : ru.X=rv.X := by simp only [ru,rv,X_def,h5,hq]
  have hY : ru.Y=rv.Y := by simp only [ru,rv,Y_def,h6,hq]
  have hk : ru.k=rv.k := by simp only [ru,rv,k_def,h8,h9]
  have hc : ru.c=rv.c := by simp only [ru,rv,c_def,hk,hY,h8]
  have hA : ru.Am1=rv.Am1 := by simp only [ru,rv,Am1_def,hX,hY]
  have hH : ru.H=rv.H := by simp only [ru,rv,H_def,hA]
  have hD : ru.D=rv.D := by simp only [ru,rv,D_def,hX,hY]
  have hDelta : ru.Delta=rv.Delta := by simp only [ru,rv,Delta_def,hA]
  have hE : ru.E=rv.E := by simp only [ru,rv,E_def,hX,hY,hk]
  have hU : ru.U=rv.U := by simp only [ru,rv,U_def,h3,hc]
  have ha : ru.a=rv.a := by simp only [ru,rv,a_def,hDelta,hU,hE]
  have hF0 : ru.F0=rv.F0 := by simp only [ru,rv,F0_def,ha]
  have hf : ru.f=rv.f := by simp only [ru,rv,f_def,ha,hF0]
  have hQ : ru.Q=rv.Q := by simp only [ru,rv,Q_def,hDelta,ha,hF0]
  have hK : ru.K=rv.K := by simp only [ru,rv,K_def,hX,hc]
  have hM : ru.M=rv.M := by simp only [ru,rv,M_def,hh,hX,hY,hH]
  have hGn : ru.Gn=rv.Gn := by simp only [ru,rv,Gn_def,hE,hF0]
  have hV : ru.V=rv.V := by
    rw [V_def,V_def,b_def,b_def,hf,hc,h4u,h4v]
    change rv.c*(u 4-v 4)=ru.rank-rv.rank at hT
    linear_combination rv.f*hT
  have he : ru.e=rv.e-(ru.rank-rv.rank) := by rw [e_def,e_def,hk]; ring
  have hZu : ru.Z=ru.h*ru.D*(ru.H*(u 7-ru.V*ru.V*ru.B)+ru.K)-
      ru.H*(ru.D*ru.B+ru.h*ru.e) := by rw [Z_def,D_def,h7u]
  have hZv : rv.Z=rv.h*rv.D*(rv.H*(v 7-rv.V*rv.V*rv.B)+rv.K)-
      rv.H*(rv.D*rv.B+rv.h*rv.e) := by rw [Z_def,D_def,h7v]
  have hZ : ru.Z=rv.Z := by
    rw [hZu,hZv,hh,hD,hH,hK,hV,he]
    change rv.h*rv.D*(u 7-v 7)=(rv.h*rv.D*(rv.V*rv.V)+rv.D)*(ru.B-rv.B)-rv.h*(ru.rank-rv.rank) at hN
    linear_combination rv.H*hN
  rw [Trace74Mask.coordinate_identity,Trace74Mask.coordinate_identity,value75_def,value75_def]
  change ru.Q*(ru.Z*ru.Z-ru.M*ru.M*ru.Gn*(ru.V*ru.V))+(ru.M*ru.M*ru.Gn-ru.Z*ru.Z)=_
  rw [hQ,hZ,hM,hGn,hV]

#print axioms Trace74ConditionalGauge.same_output_of_transport_equations
end Trace74ConditionalGauge
