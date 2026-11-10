import DiophantineConsistency.BFS943.Scaled87Regs
import DiophantineConsistency.BFS943.Trace87Residue
import DiophantineConsistency.BFS943.Trace111Estimate

/-! # The ten-positive 111-operation, degree-198 `product2` equation

Package 194 (`194-guarded-resultants-early-projection/positive`), mode
`product2`: the circuit `product2_radix67.json` (111 operations, exact degree
198, weight `L = bV`, root scale `r = 2`). In the 87 registers (`Y = q s` is
package 194's `Ybar`, `Am1 = A - 1`, `X Y² k = ell`) its centre is

  `Ω₂ = U {2A [E V - θ (E² + S²)] + S [4 θ E - (b - c)]}`,
  `S = (k Ybar) [ell + k - (k Ybar) (Ybar + 1)]`,  `θ = U² b`

(rows `cy`, `Yp1`, `cyYp1`, `sinner`, `S`, `U2`, `theta`, `thetaE`,
`fourthetaE`, `bmc`, `Rc`, `E2`, `S2`, `Sc`, `EV`, `thetaSc`, `Vdiff`,
`twoA = Am1 + Ap1`, `Apart`, `SRc`, `whole_inner`, `Omega`), its carrier is
`TenPositiveScaled87.regsW p v Ω₂` (gate `(n - b V B) - Ω₂`, rows `raw_center`,
`center`; `Z = Z₈₇ - M Ω₂`), and its output is the root-scale-two norm (rows
`scaledG`, `RG`, …, `N`).

`Trace111Omega`: at positive inputs `S = k² Ybar ((X - 2) Ybar² + Ybar (Ybar - 1) + 1)`
lies in `[0, E]` (`X ≥ 2`), and `Trace111Estimate` gives `Ω₂ ≤ 3 A U E |V| <
5 g |V|` (`omega_shift`, the size hypothesis of `Scaled87Sign.shift_zero`) and
`Ω₂ ≥ 0` once `V > 0` (`omega_nonneg`). -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.TenPositiveTrace111

section Generic
variable {R : Type*} [Add R] [Sub R] [Mul R] [OfNat R 1] [OfNat R 2] [OfNat R 3] [OfNat R 4]
  [OfNat R 6]

/-- The first-product centre `Ω₂`. -/
def omega (p : Fin 4 → R) (v : Fin 10 → R) : R :=
  let r := TenPositiveTrace87.regs p v
  let S := r.q * (r.k * v 6) * (r.X * r.Y * r.Y * r.k + r.k - r.q * (r.k * v 6) * (r.Y + 1))
  let theta := r.U * r.U * r.b
  r.U * ((r.Am1 + (r.Am1 + 2)) * (r.E * r.V - theta * (r.E * r.E + S * S)) +
    S * (4 * (theta * r.E) - (r.b - r.c)))

/-- The value of the 111-operation circuit (its output row `N`). -/
def value111 (p : Fin 4 → R) (v : Fin 10 → R) : R :=
  let r := TenPositiveScaled87.regsW p v (omega p v)
  r.Q * (r.Z * r.Z - r.M * r.M * (4 * r.Gn) * (r.V * r.V)) +
    (r.M * r.M * (4 * r.Gn) - r.Z * r.Z)

theorem value111_scaled (p : Fin 4 → R) (v : Fin 10 → R) :
    value111 p v = TenPositiveScaled87.scaledNorm (TenPositiveTrace87.regs p v)
      (TenPositiveScaled87.regsW p v (omega p v)).Z := rfl

end Generic

variable {R : Type*} [CommRing R]

theorem value111_eq (p : Fin 4 → R) (v : Fin 10 → R) :
    value111 p v = TenPositiveScaled87.scaledNorm (TenPositiveTrace87.regs p v)
      ((TenPositiveTrace87.regs p v).Z - (TenPositiveTrace87.regs p v).M * omega p v) := by
  rw [value111_scaled, TenPositiveScaled87.regsW_Z_shift]

/-- Only the carrier reads `n`. -/
theorem value111_update (p : Fin 4 → R) (v : Fin 10 → R) (x : R) :
    value111 p (Function.update v 7 x) = TenPositiveScaled87.scaledNorm (TenPositiveTrace87.regs p v)
      ((TenPositiveTrace87.regs p (Function.update v 7 x)).Z -
        (TenPositiveTrace87.regs p v).M * omega p v) := by
  set v' := Function.update v 7 x with hv'
  have hQ : (TenPositiveTrace87.regs p v').Q = (TenPositiveTrace87.regs p v).Q := rfl
  have hM : (TenPositiveTrace87.regs p v').M = (TenPositiveTrace87.regs p v).M := rfl
  have hG : (TenPositiveTrace87.regs p v').Gn = (TenPositiveTrace87.regs p v).Gn := rfl
  have hV : (TenPositiveTrace87.regs p v').V = (TenPositiveTrace87.regs p v).V := rfl
  have hc : omega p v' = omega p v := rfl
  rw [value111_eq]
  simp only [TenPositiveScaled87.scaledNorm]
  rw [hQ, hM, hG, hV, hc]

end DiophantineConsistency.TenPositiveTrace111

namespace Trace111Omega
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace87 Trace87Factors Trace87Residue
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

set_option maxHeartbeats 2000000 in
/-- `Ω₂` in the scalar form of `Trace111Estimate`, with all its hypotheses. -/
theorem omega_data (p : Fin 4 → ℕ) (v : Fin 10 → V) (hb : 0<(p 0:V)) (hv : ∀j,0<v j) :
    ∃ x u e S c : DiffRing V,
      TenPositiveTrace111.omega (ports p) (fun j => ι (v j))=
        Trace111Estimate.omegaOf x u e S c (regs (ports p) (fun j => ι (v j))).b
          (regs (ports p) (fun j => ι (v j))).V ∧
      2≤x ∧ 1≤u ∧ 1≤e ∧ 0<c ∧ c≤u ∧ 0≤S ∧ S≤e ∧
      (regs (ports p) (fun j => ι (v j))).V=
        (1+2*((x*x-1)*(u*u*e)))*(regs (ports p) (fun j => ι (v j))).b-c ∧
      x=ι (A p v)+1 ∧ u=ι (U p v) ∧ e=ι (E p v) := by
  set rr := regs (ports p) (fun j => ι (v j)) with hrr
  have hb0 : 0<b p v := mul_pos hb (hv 0)
  have hq : 0<q p v := add_pos hb0 (by simp)
  have hy : 0<Y p v := mul_pos hq (hv 6)
  have hx : 0<X p v := mul_pos hq (hv 5)
  have hA : 0<A p v := add_pos (mul_pos hx hy) hy
  have hb1 : 1≤b p v := pos_iff_one_le.mp hb0
  have hq2 : 2≤q p v := by
    simpa only [q,show (2:V)=1+1 by ring,add_comm] using _root_.add_le_add_right hb1 (1:V)
  have hX2 : 2≤X p v := le_trans hq2 (by
    change q p v≤q p v*v 5
    exact le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp (hv 5)))
  obtain ⟨_,hU,hE,_⟩ := factors_positive p v hb hv
  have hC : 0<c p v := add_pos (mul_pos (add_pos (hv 8) (hv 9)) (hv 6)) (hv 8)
  have hCU : c p v≤U p v := by
    calc
      c p v≤c p v*c p v := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hC) (by simp : (0:V)≤c p v)
      _≤v 3*(c p v*c p v) := le_mul_of_one_le_left (by simp) (pos_iff_one_le.mp (hv 3))
  have pos1 : ∀ w : V, 0<w → (1:DiffRing V)≤ι w := fun w hw => by
    rw [←map_one (ι : V →+* DiffRing V),ι_le_ι]; exact pos_iff_one_le.mp hw
  have hqr : rr.q=ι (q p v) := by
    dsimp [rr]; simp only [q_def,h_def,ports,q,b,map_mul,map_add,map_one,map_natCast]
  have hYr : rr.Y=ι (Y p v) := by
    dsimp [rr]; simp only [Y_def,q_def,h_def,ports,Y,q,b,map_mul,map_add,map_one,map_natCast]
  have hXr : rr.X=ι (X p v) := by
    dsimp [rr]; simp only [X_def,q_def,h_def,ports,X,q,b,map_mul,map_add,map_one,map_natCast]
  have hkr : rr.k=ι (k v) := by
    dsimp [rr]; rw [k_def]; simp only [k,map_add]
  have hAr : rr.Am1=ι (A p v) := by
    dsimp [rr]
    simp only [Am1_def,X_def,Y_def,q_def,h_def,ports,A,X,Y,q,b,map_mul,map_add,map_one,map_natCast]
  have hUr : rr.U=ι (U p v) := U_eval p v
  have hEr : rr.E=ι (E p v) := E_eval p v
  have hcr : rr.c=ι (c p v) := c_eval p v
  have hs : (ι (v 6):DiffRing V)*ι (q p v)=ι (Y p v) := by
    simp only [Y,map_mul]; ring
  have hVF : rr.V=(1+2*((ι (A p v)*(ι (A p v)+2))*(ι (U p v)*ι (U p v)*ι (E p v))))*rr.b-
      ι (c p v) := by
    dsimp [rr]
    rw [V_def,f_eq,a_eq,delta_eval,U_eval,E_eval,c_eval]
    simp only [delta,pow_two,map_mul,map_add,map_ofNat]
    ring
  have heE : (ι (E p v):DiffRing V)=1+ι (X p v)*ι (Y p v)^2*(ι (X p v)*ι (Y p v)^2+1)*ι (k v)^2 := by
    simp only [E,map_add,map_mul,map_one]; ring
  set a0 : DiffRing V := ι (A p v)
  set XX : DiffRing V := ι (X p v)
  set YY : DiffRing V := ι (Y p v)
  set kk : DiffRing V := ι (k v)
  set u : DiffRing V := ι (U p v)
  set e : DiffRing V := ι (E p v)
  set cc : DiffRing V := ι (c p v)
  have ha1 : 1≤a0 := pos1 _ hA
  have hX2R : 2≤XX := by
    have h := ι_le_ι.mpr hX2
    simpa only [map_ofNat] using h
  have hY1 : 1≤YY := pos1 _ hy
  have hk0 : 0≤kk := ι_nonneg _
  let S : DiffRing V := kk*kk*(YY*((XX-2)*YY*YY+YY*(YY-1)+1))
  refine ⟨a0+1,u,e,S,cc,?_,by linarith,pos1 _ hU,pos1 _ hE,?_,ι_le_ι.mpr hCU,?_,?_,?_,rfl,rfl,rfl⟩
  · change rr.U*((rr.Am1+(rr.Am1+2))*(rr.E*rr.V-rr.U*rr.U*rr.b*(rr.E*rr.E+
        (rr.q*(rr.k*ι (v 6))*(rr.X*rr.Y*rr.Y*rr.k+rr.k-rr.q*(rr.k*ι (v 6))*(rr.Y+1)))*
        (rr.q*(rr.k*ι (v 6))*(rr.X*rr.Y*rr.Y*rr.k+rr.k-rr.q*(rr.k*ι (v 6))*(rr.Y+1)))))+
      (rr.q*(rr.k*ι (v 6))*(rr.X*rr.Y*rr.Y*rr.k+rr.k-rr.q*(rr.k*ι (v 6))*(rr.Y+1)))*
        (4*(rr.U*rr.U*rr.b*rr.E)-(rr.b-rr.c)))=_
    have hs' : ι (q p v)*(kk*ι (v 6))=kk*YY := by rw [←hs]; ring
    rw [hAr,hUr,hEr,hqr,hXr,hYr,hkr,hcr,hs']
    unfold Trace111Estimate.omegaOf
    dsimp only [S]
    ring
  · rw [←map_zero (ι : V →+* DiffRing V)]; exact ι_lt_ι.mpr hC
  · have hY0 : 0≤YY := by linarith
    have h1 : 0≤(XX-2)*YY*YY := mul_nonneg (mul_nonneg (by linarith) hY0) hY0
    have h2 : 0≤YY*(YY-1) := mul_nonneg hY0 (by linarith)
    exact mul_nonneg (mul_nonneg hk0 hk0) (mul_nonneg hY0 (by linarith))
  · have hY0 : 0≤YY := by linarith
    have hX0 : 0≤XX := by linarith
    have hXY : 0≤XX*YY-1 := by
      have := one_le_mul_of_one_le_of_one_le (show (1:DiffRing V)≤XX by linarith) hY1; linarith
    have hid : e-S=1+kk*kk*(XX*YY^3*(XX*YY-1)+XX*YY^2+YY^3+YY*(YY-1)) := by
      rw [heE]; dsimp only [S]; ring
    have h0 : 0≤kk*kk*(XX*YY^3*(XX*YY-1)+XX*YY^2+YY^3+YY*(YY-1)) := by
      apply mul_nonneg (mul_nonneg hk0 hk0)
      have t1 := mul_nonneg (mul_nonneg hX0 (pow_nonneg hY0 3)) hXY
      have t2 := mul_nonneg hX0 (pow_nonneg hY0 2)
      have t3 := pow_nonneg hY0 3
      have t4 := mul_nonneg hY0 (show (0:DiffRing V)≤YY-1 by linarith)
      linarith
    linarith
  · rw [show rr.V=_ from hVF]
    ring

/-- The size hypothesis of `Scaled87Sign.shift_zero` for the shift `Ω₂`. -/
theorem omega_shift (p : Fin 4 → ℕ) (v : Fin 10 → V) (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (tau f V0 : V) (hE : E p v=tau*tau) (hf : 1+delta p v*U p v*U p v*E p v=f*f)
    (hV : (regs (ports p) (fun j => ι (v j))).V*(regs (ports p) (fun j => ι (v j))).V=ι (V0*V0)) :
    TenPositiveTrace111.omega (ports p) (fun j => ι (v j))≤5*ι (tau*f)*ι V0 := by
  obtain ⟨x,u,e,S,c,hom,hx,hu,he,hc,hcu,hS0,hSe,hVF,hxA,hu',he'⟩ := omega_data p v hb hv
  have hdisc : ∀ y : DiffRing V, 0<y → 1≤y := fun y hy =>
    one_le_of_pos (fun z hz => pos_iff_one_le.mp hz) hy
  have hV0 : (regs (ports p) (fun j => ι (v j))).V*(regs (ports p) (fun j => ι (v j))).V=
      ι V0*ι V0 := by rw [hV,map_mul]
  have hup := Trace111Estimate.omega_upper x u e S c _ _ (ι V0) hx hu he hc hcu hS0 hSe hVF hV0
    (ι_nonneg V0) hdisc
  have hG : ι (tau*f)*ι (tau*f)=e*(1+(x*x-1)*(u*u)*e) := by
    have h1 := congrArg (ι : V →+* DiffRing V) hf
    have h2 := congrArg (ι : V →+* DiffRing V) hE
    simp only [delta,map_add,map_mul,map_one,map_ofNat] at h1 h2
    rw [he',hu',hxA]
    have h3 : ι (tau*f)*ι (tau*f)=(ι tau*ι tau)*(ι f*ι f) := by simp only [map_mul]; ring
    rw [h3,←h1,←h2]
    ring
  have h35 := Trace111Estimate.three_lt_five x u e (ι (tau*f)) hx hu he (ι_nonneg _) hG
  have h2 : 3*(x*u*e)*ι V0≤5*ι (tau*f)*ι V0 :=
    mul_le_mul_of_nonneg_right (le_of_lt h35) (ι_nonneg _)
  rw [hom]
  exact le_trans hup h2

/-- `Ω₂ ≥ 0` once `V > 0`. -/
theorem omega_nonneg (p : Fin 4 → ℕ) (v : Fin 10 → V) (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hVpos : 0<(regs (ports p) (fun j => ι (v j))).V) :
    0≤TenPositiveTrace111.omega (ports p) (fun j => ι (v j)) := by
  obtain ⟨x,u,e,S,c,hom,hx,hu,he,hc,hcu,hS0,hSe,hVF,_,_,_⟩ := omega_data p v hb hv
  have hdisc : ∀ y : DiffRing V, 0<y → 1≤y := fun y hy =>
    one_le_of_pos (fun z hz => pos_iff_one_le.mp hz) hy
  set bb := (regs (ports p) (fun j => ι (v j))).b
  set F : DiffRing V := 1+2*((x*x-1)*(u*u*e))
  have hF : 0<F := by
    have hxx : 0≤x*x-1 := by nlinarith
    have : 0≤(x*x-1)*(u*u*e) := mul_nonneg hxx (mul_nonneg (mul_nonneg (by linarith)
      (by linarith)) (by linarith))
    dsimp only [F]; linarith
  have hbpos : 0<bb := by
    have h1 : 0<F*bb := by rw [hVF] at hVpos; linarith
    exact pos_of_mul_pos_right h1 (le_of_lt hF)
  rw [hom]
  exact Trace111Estimate.omega_nonneg x u e S c bb _ hx hu he hc hcu hS0 hSe hVF (hdisc _ hbpos)

#print axioms Trace111Omega.omega_data
#print axioms Trace111Omega.omega_shift
#print axioms Trace111Omega.omega_nonneg
end Trace111Omega
