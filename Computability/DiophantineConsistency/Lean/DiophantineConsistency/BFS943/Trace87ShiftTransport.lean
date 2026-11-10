import DiophantineConsistency.BFS943.Trace87Transport

/-! # Carrier data of the 87/214 analysis at a shifted carrier

The 87 soundness chain after `B ≥ 0` reads the carrier
`Z = h D [H (n - L B) + K] - H [D B + h eclear]` only modulo `D` and modulo
`H`. Shifting it by any multiple `M ws` of `M = h D H` changes neither
reduction. `ShiftZero p v ws` is the hypothesis of the shifted analysis: the
norm value vanishes at the carrier `Z - M ws`, and `B ≥ 0` (proved separately
for each shift, e.g. `Centred87Sign` for the centred circuits). With
`ws = 0` this is the 87 situation; with `ws = g V` it is a centred circuit
`n ↦ n - V (b B + g)` (package 179).

`graph_zero_data` is `Trace87Transport.graph_zero_data` at the shifted
carrier: `Z - M ws = M z` with `z = ±τ f y`, the mask, and at the first index
`eclear = 6 u`, `q⁷ ∣ u`, `q⁴ ∣ 2n - R - 1`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace87ShiftTransport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace87 TenPositiveTrace76
open Trace87Factors Trace87Residue Trace87NormRoots Trace87NormKpos
open Trace87NormRank (rankNat rank_eval_of_mask)
open ArithmeticPellRecurrence (ycoord)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A zero of the 87 norm polynomial at the shifted carrier `Z - M ws`, together
with the transport sign `B ≥ 0`. -/
def ShiftZero (p : Fin 4 → ℕ) (v : Fin 10 → V) (ws : DiffRing V) : Prop :=
  normValue (regs (ports p) (fun j => ι (v j)))
      ((regs (ports p) (fun j => ι (v j))).Z-(regs (ports p) (fun j => ι (v j))).M*ws) = 0 ∧
    0≤(regs (ports p) (fun j => ι (v j))).B

set_option maxHeartbeats 4000000 in
theorem graph_zero_data (p : Fin 4 → ℕ) (v : Fin 10 → V) {ws : DiffRing V}
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j) (hz : ShiftZero p v ws) :
    ∃ (z : DiffRing V) (tau f y : V), 0<tau ∧ 0<f ∧ 0<y ∧
      1+delta p v*U p v*U p v*E p v=f*f ∧
      (z=ι (tau*f*y) ∨ z=-ι (tau*f*y)) ∧
      (regs (ports p) (fun j => ι (v j))).Z-(regs (ports p) (fun j => ι (v j))).M*ws=
        (regs (ports p) (fun j => ι (v j))).M*z ∧
      0≤(regs (ports p) (fun j => ι (v j))).B ∧
      v 1+v 2<q p v ∧
      ∃ (n : V) (u w : DiffRing V), 0<n ∧ 2*ycoord n (2*(firstParam p v-1)+1)=k v ∧
        ecl (ports p) (fun j => ι (v j))=6*u ∧
        (ι (q p v):DiffRing V)^7 ∣ u ∧
        3*u=3*(ι (2*n)-ι (rankNat p v+1)-(ι (q p v))^4*ι (v 6))+
          ι (firstParam p v)*ι (firstParam p v)*w ∧
        (ι (q p v):DiffRing V)^4 ∣ ι (2*n)-ι (rankNat p v+1) := by
  let rr := regs (ports p) (fun j => ι (v j))
  let Z : DiffRing V := rr.Z-rr.M*ws
  have hZdef : Z=rr.Z-rr.M*ws := rfl
  have hzn : normValue rr Z = 0 := hz.1
  have hB : 0≤rr.B := hz.2
  obtain ⟨tau,f,Z0,y,ht,hf,hy,hf2,hZsq,hZeq,_hbound,_hL,_hsign⟩ :=
    Trace87Transport.graph_bv_bound p v Z hb hv hzn
  let mz : DiffRing V := ι (M p v)*ι (tau*f*y)
  have hsq : Z*Z=mz*mz := by
    calc
      Z*Z=ι (Z0*Z0) := hZsq
      _=mz*mz := by rw [hZeq]; dsimp [mz]; simp only [map_mul]; ring
  have hfactor : (Z-mz)*(Z+mz)=0 := by rw [show (Z-mz)*(Z+mz)=Z*Z-mz*mz by ring,hsq]; ring
  have hcarrier : ∃ z : DiffRing V, Z=ι (M p v)*z ∧ (z=ι (tau*f*y) ∨ z=-ι (tau*f*y)) := by
    rcases mul_eq_zero.mp hfactor with h|h
    · exact ⟨ι (tau*f*y),sub_eq_zero.mp h,Or.inl rfl⟩
    · refine ⟨-ι (tau*f*y),?_,Or.inr rfl⟩
      have heq : Z= -mz := eq_neg_of_add_eq_zero_left h
      dsimp [mz] at heq
      simpa only [mul_neg] using heq
  obtain ⟨z,hZ,hzpm⟩ := hcarrier
  have hZ' : Z=rr.M*z := by
    rw [M_eval p v hb hv]
    exact hZ
  have hb0 : 0<b p v := mul_pos hb (hv 0)
  have hq : 0<q p v := add_pos hb0 (by simp)
  have hY : 0<Y p v := mul_pos hq (hv 6)
  have hX : 0<X p v := mul_pos hq (hv 5)
  have hqr : rr.q=ι (q p v) := by
    dsimp [rr]
    simp only [q_def,h_def,ports,q,b,map_mul,map_add,map_one,map_natCast]
  let qq : DiffRing V := ι (q p v)
  have hD7 : rr.D=6*qq^7 := by
    change rr.D=6*ι (q p v)^7
    rw [D_def,hqr]; ring
  have eeval : rr.e=ι (k v)-rr.rank-1 := by
    dsimp [rr]
    rw [e_def,k_def]
    simp only [k,map_add]
  let N : DiffRing V := rr.e-rr.q*rr.q*(rr.q*rr.q)*ι (v 6)
  have hkr0 : rr.k=ι (k v) := by
    dsimp [rr]
    rw [k_def]
    simp only [k,map_add]
  have hPr : rr.X*rr.Y*rr.Y=ι (firstParam p v) := by
    dsimp [rr]
    simp only [X_def,Y_def,q_def,h_def,ports,firstParam,X,Y,q,b,map_mul,map_add,map_one,map_natCast]
    ring
  have heclN : ecl (ports p) (fun j => ι (v j))=6*N-rr.X*rr.Y*rr.Y*rr.k*(rr.k*rr.k-4) :=
    ecl_def _ _
  have hZ'' : Z=rr.h*rr.D*rr.H*z := by rw [hZ',M_def]
  have hMdef : rr.M=rr.h*rr.D*rr.H := M_def _ _
  have hshape : rr.Z=rr.h*rr.D*(rr.H*(ι (v 7)-(rr.b*rr.V)*rr.B)+rr.K)-
      rr.H*(rr.D*rr.B+rr.h*ecl (ports p) (fun j => ι (v j))) := Z_def (ports p) (fun j => ι (v j))
  -- the mask, with transport base `w`
  have hwpos : (0:DiffRing V)<ι (v 5) := by
    rw [←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hv 5
  have hcoef : 0<(ports p) 1+ι (v 5) := add_pos_of_nonneg_of_pos (by simp [ports]) hwpos
  have hBeq : rr.B=((ports p) 1+ι (v 5))*rr.C-ι (v 1) := by
    dsimp [rr]
    rw [B_def]
  have hfpos : (0:DiffRing V)<ι (v 1) := by rw [←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hv 1
  have hprod : 0<((ports p) 1+ι (v 5))*rr.C := by rw [hBeq] at hB; linarith
  have hC' : 0<rr.C := pos_of_mul_pos_right hprod (le_of_lt hcoef)
  have hCeq : rr.C=ι (q p v)-ι (v 1)-ι (v 2) := by
    dsimp [rr]
    simp only [C_def,q_def,h_def,ports,q,b,map_mul,map_add,map_one,map_natCast]
  have hqbound : (ι (v 1+v 2):DiffRing V)<ι (q p v) := by
    rw [hCeq] at hC'; simp only [map_add]; linarith
  have hmask : v 1+v 2<q p v := ι_lt_ι.mp hqbound
  have hrank : rr.rank=ι (rankNat p v) := rank_eval_of_mask p v hq hmask
  -- the first index and the inverse-Lucas split
  obtain ⟨_tau,_f,n,_I,_ht,_hf,hn0,_hnK,_hE,_hf2,_hnx,hny,_⟩ :=
    Trace87NormFold.first_and_doubled p v Z hb hv hzn
  let P : V := firstParam p v
  let B : V := 2*(P-1)+1
  change 2*ycoord n B=k v at hny
  have hP : 0<P := mul_pos hX (mul_pos hY hY)
  have hB1 : B+1=2*P := by
    have hP1 : P-1+1=P := tsub_add_cancel_of_le (pos_iff_one_le.mp hP)
    calc B+1=2*(P-1+1) := by dsimp [B]; ring
      _=2*P := by rw [hP1]
  let Δ : DiffRing V := -ι (rankNat p v+1)-qq^4*ι (v 6)
  obtain ⟨u,w,hu6,hu3⟩ := InverseLucasCubic.pell_cubic_split B P n Δ hB1
  have hkr : rr.k=2*ι (ycoord n B) := by
    rw [hkr0,←hny]; simp only [map_mul,map_ofNat]
  have hN : N=2*ι (ycoord n B)+Δ := by
    change rr.e-rr.q*rr.q*(rr.q*rr.q)*ι (v 6)=_
    rw [eeval,hrank,hqr,←hny]
    dsimp only [Δ,qq]
    simp only [map_mul,map_ofNat,map_add,map_one]
    ring
  have hEcl : ecl (ports p) (fun j => ι (v j))=6*u := by
    rw [heclN,hN,hkr,hPr]
    exact hu6
  -- `6 q⁷ ∣ h H (6 u)`, hence `q⁷ ∣ u`: the shift `M ws` is a multiple of `D`
  have hDdiv : rr.D∣(rr.h*rr.H)*ecl (ports p) (fun j => ι (v j)) := by
    refine ⟨rr.h*(rr.H*(ι (v 7)-(rr.b*rr.V)*rr.B)+rr.K)-rr.H*rr.B-rr.h*rr.H*z-rr.h*rr.H*ws,?_⟩
    linear_combination hshape+hZdef-hZ''-ws*hMdef
  have hu7 : qq^7∣(rr.h*rr.H)*u := by
    obtain ⟨c0,hc0⟩ := hDdiv
    refine ⟨c0,?_⟩
    apply mul_left_cancel₀ (show (6:DiffRing V)≠0 from ne_of_gt (by norm_num))
    linear_combination hc0-(rr.h*rr.H)*hEcl+c0*hD7
  have hrq : qq∣rr.h*rr.H-1 := by
    refine ⟨4*(qq-1)*ι (v 6)*(rr.X+1)-1,?_⟩
    dsimp [qq,rr]
    simp only [H_def,Am1_def,X_def,Y_def,q_def,h_def,ports,q,b,map_mul,map_add,map_one,map_natCast]
    ring
  have hu7' : qq^7∣u := Trace87Transport.cancel_one_mod_seventh qq (rr.h*rr.H) u hrq hu7
  -- `q⁶ ∣ v²` and `q⁴ ∣ 2n - R - 1`
  have hPq : (ι P:DiffRing V)*ι P=qq^6*(ι (v 5*v 6*v 6))^2 := by
    dsimp only [P,qq]
    simp only [firstParam,X,Y,map_mul]
    ring
  let x : DiffRing V := ι (2*n)-ι (rankNat p v+1)-qq^4*ι (v 6)
  have h2n : (ι (2*n):DiffRing V)=2*ι n := by simp only [map_mul,map_ofNat]
  have h3x : 3*x=3*u-ι P*ι P*w := by
    dsimp only [x]
    linear_combination -hu3+3*h2n
  have h6 : qq^6∣3*x := by
    rw [h3x,hPq]
    apply dvd_sub
    · exact dvd_mul_of_dvd_right (dvd_trans (pow_dvd_pow qq (by norm_num : 6≤7)) hu7') 3
    · exact ⟨(ι (v 5*v 6*v 6))^2*w,by ring⟩
  have h5 : qq^5∣x := InverseLucasCubic.cancel_three (q p v) x 5 h6
  have h4 : qq^4∣ι (2*n)-ι (rankNat p v+1) := by
    have hx4 : qq^4∣x := dvd_trans (pow_dvd_pow qq (by norm_num : 4≤5)) h5
    have hs := dvd_add hx4 (dvd_mul_right (qq^4) (ι (v 6)))
    dsimp only [x] at hs
    simpa only [sub_add_cancel] using hs
  have hu3' : 3*u=3*(ι (2*n)-ι (rankNat p v+1)-(ι (q p v))^4*ι (v 6))+
      ι (firstParam p v)*ι (firstParam p v)*w := by
    dsimp only [x,qq] at h3x
    linear_combination -h3x
  exact ⟨z,tau,f,y,ht,hf,hy,hf2,hzpm,hZ',hB,hmask,n,u,w,hn0,hny,hEcl,hu7',hu3',h4⟩

#print axioms Trace87ShiftTransport.graph_zero_data
end Trace87ShiftTransport
