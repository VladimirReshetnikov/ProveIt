import DiophantineConsistency.BFS943.Scaled87Regs
import DiophantineConsistency.BFS943.Trace87Factors

/-! # The ten-positive 97-operation, degree-202 `quotient_t` equation

Package 194 (`194-guarded-resultants-early-projection/positive`), mode
`quotient_t`: the circuit `quotient_t_radix67.json` (97 operations, exact
degree 202, weight `L = bV`, root scale `r = 2`). In the 87 registers
(`Y = q s` is package 194's `Ybar`, `Am1 = A - 1`, `X Y² k = ell`) its centre is

  `C2 = 2 A U E - U Qt`,  `Qt = (k Ybar) [ell + k - (k Ybar) Ybar]`

(rows `cy`, `cyy`, `qt_inner`, `Qt`, `twoA = Am1 + Ap1`, `twice_upper`, `UQt`,
`center_root`), its carrier is the centred carrier
`TenPositiveCentred87.regsAt p v C2` (`Z = Z₈₇ - M (C2 V)`, rows `bB_center`,
`LBt`, `center`), and its output is the root-scale-two norm
`Q (Z² - M² (4 G) V²) + (M² (4 G) - Z²)` (rows `scaledG`, `RG`, …, `N`).

`Trace97Centre`: at positive inputs `Qt = k² Ybar ((X - 1) Ybar² + 1)` lies in
`[0, E]`, so `0 ≤ C2 ≤ 2 A U E` and `C2² < 9 E (1 + Δ U² E) = 9 G`
(package 194's (8)–(9)); `centre_shift` is the size hypothesis of
`Scaled87Sign.shift_zero` for the shift `C2 V`. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.TenPositiveTrace97

section Generic
variable {R : Type*} [Add R] [Sub R] [Mul R] [OfNat R 1] [OfNat R 2] [OfNat R 3] [OfNat R 4]
  [OfNat R 6]

/-- The quotient centre `C2 = (Am1 + (Am1 + 2)) (U E) - U Qt`. -/
def centre (p : Fin 4 → R) (v : Fin 10 → R) : R :=
  let r := TenPositiveTrace87.regs p v
  (r.Am1 + (r.Am1 + 2)) * (r.U * r.E) -
    r.U * (r.q * (r.k * v 6) * (r.X * r.Y * r.Y * r.k + r.k - r.q * (r.k * v 6) * r.Y))

/-- The value of the 97-operation circuit (its output row `N`). -/
def value97 (p : Fin 4 → R) (v : Fin 10 → R) : R :=
  let r := TenPositiveCentred87.regsAt p v (centre p v)
  r.Q * (r.Z * r.Z - r.M * r.M * (4 * r.Gn) * (r.V * r.V)) +
    (r.M * r.M * (4 * r.Gn) - r.Z * r.Z)

theorem value97_scaled (p : Fin 4 → R) (v : Fin 10 → R) :
    value97 p v = TenPositiveScaled87.scaledNorm (TenPositiveTrace87.regs p v)
      (TenPositiveCentred87.regsAt p v (centre p v)).Z := rfl

end Generic

variable {R : Type*} [CommRing R]

theorem value97_eq (p : Fin 4 → R) (v : Fin 10 → R) :
    value97 p v = TenPositiveScaled87.scaledNorm (TenPositiveTrace87.regs p v)
      ((TenPositiveTrace87.regs p v).Z -
        (TenPositiveTrace87.regs p v).M * (centre p v * (TenPositiveTrace87.regs p v).V)) := by
  rw [value97_scaled, TenPositiveCentred87.Z_shift]

/-- Only the carrier reads `n`. -/
theorem value97_update (p : Fin 4 → R) (v : Fin 10 → R) (x : R) :
    value97 p (Function.update v 7 x) = TenPositiveScaled87.scaledNorm (TenPositiveTrace87.regs p v)
      ((TenPositiveTrace87.regs p (Function.update v 7 x)).Z -
        (TenPositiveTrace87.regs p v).M * (centre p v * (TenPositiveTrace87.regs p v).V)) := by
  set v' := Function.update v 7 x with hv'
  have hQ : (TenPositiveTrace87.regs p v').Q = (TenPositiveTrace87.regs p v).Q := rfl
  have hM : (TenPositiveTrace87.regs p v').M = (TenPositiveTrace87.regs p v).M := rfl
  have hG : (TenPositiveTrace87.regs p v').Gn = (TenPositiveTrace87.regs p v).Gn := rfl
  have hV : (TenPositiveTrace87.regs p v').V = (TenPositiveTrace87.regs p v).V := rfl
  have hc : centre p v' = centre p v := rfl
  rw [value97_eq]
  simp only [TenPositiveScaled87.scaledNorm]
  rw [hQ, hM, hG, hV, hc]

end DiophantineConsistency.TenPositiveTrace97

namespace Trace97Centre
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace87 Trace87Factors
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

set_option maxHeartbeats 1000000 in
/-- `0 ≤ C2` and `C2² < 9 E (1 + Δ U² E)` at positive inputs. -/
theorem centre_bounds (p : Fin 4 → ℕ) (v : Fin 10 → V) (hb : 0<(p 0:V)) (hv : ∀j,0<v j) :
    0≤TenPositiveTrace97.centre (ports p) (fun j => ι (v j)) ∧
      TenPositiveTrace97.centre (ports p) (fun j => ι (v j))*
        TenPositiveTrace97.centre (ports p) (fun j => ι (v j))<
        9*(ι (E p v)*(1+ι (delta p v)*ι (U p v)*ι (U p v)*ι (E p v))) := by
  let rr := regs (ports p) (fun j => ι (v j))
  have hb0 : 0<b p v := mul_pos hb (hv 0)
  have hq : 0<q p v := add_pos hb0 (by simp)
  have hy : 0<Y p v := mul_pos hq (hv 6)
  have hx : 0<X p v := mul_pos hq (hv 5)
  have hA : 0<A p v := add_pos (mul_pos hx hy) hy
  obtain ⟨_,hU,hE,_⟩ := factors_positive p v hb hv
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
  have hDr : (ι (delta p v):DiffRing V)=ι (A p v)*(ι (A p v)+2) := by
    simp only [delta,map_mul,map_add,map_ofNat]
  have hs : (ι (v 6):DiffRing V)*ι (q p v)=ι (Y p v) := by
    simp only [Y,map_mul]; ring
  have heE : (ι (E p v):DiffRing V)=1+ι (X p v)*ι (Y p v)^2*(ι (X p v)*ι (Y p v)^2+1)*ι (k v)^2 := by
    simp only [E,map_add,map_mul,map_one]; ring
  set x : DiffRing V := ι (A p v)
  set XX : DiffRing V := ι (X p v)
  set YY : DiffRing V := ι (Y p v)
  set kk : DiffRing V := ι (k v)
  set u : DiffRing V := ι (U p v)
  set e : DiffRing V := ι (E p v)
  have hx1 : 1≤x := pos1 _ hA
  have hX1 : 1≤XX := pos1 _ hx
  have hY1 : 1≤YY := pos1 _ hy
  have hu1 : 1≤u := pos1 _ hU
  have he1 : 1≤e := pos1 _ hE
  have hk0 : 0≤kk := ι_nonneg _
  let Qt : DiffRing V := kk*kk*YY*((XX-1)*YY*YY+1)
  have hcentre : TenPositiveTrace97.centre (ports p) (fun j => ι (v j))=(2*x+2)*(u*e)-u*Qt := by
    change (rr.Am1+(rr.Am1+2))*(rr.U*rr.E)-
      rr.U*(rr.q*(rr.k*ι (v 6))*(rr.X*rr.Y*rr.Y*rr.k+rr.k-rr.q*(rr.k*ι (v 6))*rr.Y))=_
    rw [hAr,hUr,hEr,hqr,hXr,hYr,hkr]
    have hs' : ι (q p v)*(kk*ι (v 6))=kk*YY := by rw [←hs]; ring
    rw [hs']
    dsimp only [Qt]
    ring
  have hQt0 : 0≤Qt := by
    have h1 : 0≤(XX-1)*YY*YY+1 := by
      have := mul_nonneg (mul_nonneg (sub_nonneg.mpr hX1) (le_trans zero_le_one hY1))
        (le_trans zero_le_one hY1)
      linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg hk0 hk0) (le_trans zero_le_one hY1)) h1
  have hQtE : Qt≤e := by
    have hXY : 0≤XX*YY-1 := by
      have := one_le_mul_of_one_le_of_one_le hX1 hY1; linarith
    have hid : e-Qt=1+kk*kk*(XX*YY^3*(XX*YY-1)+YY^3+YY*(XX*YY-1)) := by
      rw [heE]; dsimp only [Qt]; ring
    have h0 : 0≤kk*kk*(XX*YY^3*(XX*YY-1)+YY^3+YY*(XX*YY-1)) := by
      have hY0 : 0≤YY := le_trans zero_le_one hY1
      have hX0 : 0≤XX := le_trans zero_le_one hX1
      apply mul_nonneg (mul_nonneg hk0 hk0)
      have t1 := mul_nonneg (mul_nonneg hX0 (pow_nonneg hY0 3)) hXY
      have t2 := pow_nonneg hY0 3
      have t3 := mul_nonneg hY0 hXY
      linarith
    linarith
  have hu0 : 0≤u := le_trans zero_le_one hu1
  have he0 : 0≤e := le_trans zero_le_one he1
  have hlow : (2*x+1)*(u*e)≤TenPositiveTrace97.centre (ports p) (fun j => ι (v j)) := by
    rw [hcentre]
    have := mul_le_mul_of_nonneg_left hQtE hu0
    linarith
  have hup : TenPositiveTrace97.centre (ports p) (fun j => ι (v j))≤(2*x+2)*(u*e) := by
    rw [hcentre]
    have := mul_nonneg hu0 hQt0
    linarith
  have hue : 0≤u*e := mul_nonneg hu0 he0
  have hc0 : 0≤TenPositiveTrace97.centre (ports p) (fun j => ι (v j)) :=
    le_trans (mul_nonneg (by linarith) hue) hlow
  refine ⟨hc0,?_⟩
  set C := TenPositiveTrace97.centre (ports p) (fun j => ι (v j))
  have hsq : C*C≤((2*x+2)*(u*e))*((2*x+2)*(u*e)) := mul_self_le_mul_self hc0 hup
  rw [hDr]
  have hgap : 9*(e*(1+x*(x+2)*u*u*e))-((2*x+2)*(u*e))*((2*x+2)*(u*e))=
      9*e+(u*e)*(u*e)*(5*x*x+10*x-4) := by ring
  have hpoly : 0<5*x*x+10*x-4 := by nlinarith
  have hpos : 0<9*e+(u*e)*(u*e)*(5*x*x+10*x-4) := by
    have := mul_nonneg (mul_self_nonneg (u*e)) (le_of_lt hpoly)
    linarith
  linarith

/-- The size hypothesis of `Scaled87Sign.shift_zero` for the shift `C2 V`. -/
theorem centre_shift (p : Fin 4 → ℕ) (v : Fin 10 → V) (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (tau f V0 : V) (hE : E p v=tau*tau) (hf : 1+delta p v*U p v*U p v*E p v=f*f)
    (hV : (regs (ports p) (fun j => ι (v j))).V*(regs (ports p) (fun j => ι (v j))).V=ι (V0*V0)) :
    TenPositiveTrace97.centre (ports p) (fun j => ι (v j))*(regs (ports p) (fun j => ι (v j))).V≤
      5*ι (tau*f)*ι V0 := by
  obtain ⟨hc0,hc9⟩ := centre_bounds p v hb hv
  set C := TenPositiveTrace97.centre (ports p) (fun j => ι (v j))
  set W := (regs (ports p) (fun j => ι (v j))).V
  have hG : 9*(ι (E p v)*(1+ι (delta p v)*ι (U p v)*ι (U p v)*ι (E p v)))=
      (3*ι (tau*f))*(3*ι (tau*f):DiffRing V) := by
    have h1 := congrArg (ι : V →+* DiffRing V) hf
    have h2 := congrArg (ι : V →+* DiffRing V) hE
    simp only [map_add,map_mul,map_one] at h1 h2
    rw [h1,h2]
    simp only [map_mul]
    ring
  rw [hG] at hc9
  have hlt : C<3*ι (tau*f) := lt_of_mul_self_lt_mul_self₀ (by
    have := ι_nonneg (tau*f); linarith) hc9
  have hVle : W≤ι V0 := by
    by_contra hlt'
    push_neg at hlt'
    have h0 : (0:DiffRing V)≤ι V0 := ι_nonneg V0
    have : ι V0*ι V0<W*W := mul_self_lt_mul_self h0 hlt'
    rw [hV,map_mul] at this
    exact lt_irrefl _ this
  have h1 : C*W≤C*ι V0 := mul_le_mul_of_nonneg_left hVle hc0
  have h2 : C*ι V0≤(3*ι (tau*f))*ι V0 := mul_le_mul_of_nonneg_right (le_of_lt hlt) (ι_nonneg _)
  have h3 : 0≤ι (tau*f)*(ι V0:DiffRing V) := mul_nonneg (ι_nonneg _) (ι_nonneg _)
  linarith

#print axioms Trace97Centre.centre_bounds
#print axioms Trace97Centre.centre_shift
end Trace97Centre
