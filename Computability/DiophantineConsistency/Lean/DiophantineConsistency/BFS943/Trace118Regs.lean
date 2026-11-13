import DiophantineConsistency.BFS943.Scaled87Regs
import DiophantineConsistency.BFS943.Trace87Residue
import DiophantineConsistency.BFS943.Trace118Estimate

/-! # The ten-positive 118-operation, degree-190 `whole190` equation

Package 193 (`193-transport-and-pell-reuse/positive`): the circuit
`whole190.json` (118 operations, exact degree 190, root scale 4). It keeps
the 87/214 free-inverse registers of package 172 (`Y = q s` is package 193's
`Ybar`, `Am1 = A - 1`, `X Y² k = ell`, `v = X Y²`) and changes the carrier and
the norm:

* the whole-product centre (package 178, `PROOF.md` §1)
  `Ω = U [2 S Rc + A (4 E V - θ Sc)]`, `θ = U² b`,
  `S = (k Ybar) [ell + k - (k Ybar) (Ybar + 1)]`, `e₂ = (k Ybar)²`,
  `Rc = θ (3 E + e₂) - (b - c)`, `Sc = 4 E² + 3 S² + e₂²`,
  is folded with the new transport weight `L = A U³ b²` into
  `OmegaFold = U [2 S Rc + A (4 E V - θ (Sc - b B))] = Ω + L B`
  (`omegaFold`, rows `new_*`; `omegaFold_eq`);
* the carrier is `Z = h D [H (n - OmegaFold) + K] - H [D B + h eclear]`
  (rows `center`, `Hn`, `lin`, `Zpart1`, `Zpart2`, `Znum`; `regs118`), so
  `Z = Z₈₇ - M (OmegaFold - b V B)` (`regs118_Z_shift`) and
  `Z = h D [H (n - L B) + K] - H [D B + h eclear] - M Ω` (`regs118_Z_split`);
* the norm has root scale four,
  `P = Q (Z² - 16 M² G V²) + (16 M² G - Z²)` (`norm16`, rows
  `new_scaledG`, `RG`, …, `N`); identically `norm16 r (4 Z') = 16 normValue r Z'`.

`Trace118Omega` reads `Ω` in the scalar form of `Trace118Estimate` at positive
inputs (`0 ≤ S ≤ E`, `0 ≤ e₂ ≤ E`) and evaluates the weight. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.TenPositiveTrace118
open DiophantineConsistency.TenPositiveTrace75 (Regs)

section Generic
variable {R : Type*} [Add R] [Sub R] [Mul R] [OfNat R 1] [OfNat R 2] [OfNat R 3] [OfNat R 4]
  [OfNat R 6] [OfNat R 16]

/-- The folded whole-product centre `OmegaFold = Ω + A U³ b² B`. -/
def omegaFold (p : Fin 4 → R) (v : Fin 10 → R) : R :=
  let r := TenPositiveTrace87.regs p v
  let kY := r.k * r.Y
  let S := kY * (r.X * r.Y * r.Y * r.k + r.k - kY * (r.Y + 1))
  let e2 := kY * kY
  let theta := r.U * r.U * r.b
  let Rc := theta * (3 * r.E + e2) - (r.b - r.c)
  let Sc := 4 * (r.E * r.E) + 3 * (S * S) + e2 * e2
  r.U * ((r.Am1 + 1) * (4 * (r.E * r.V) - theta * (Sc - r.b * r.B)) + 2 * (S * Rc))

/-- The 87 registers with the folded carrier `h D [H (n - OmegaFold) + K] - H [D B + h eclear]`. -/
def regs118 (p : Fin 4 → R) (v : Fin 10 → R) : Regs R :=
  let r := TenPositiveTrace87.regs p v
  { r with Z := r.h * r.D * (r.H * (v 7 - omegaFold p v) + r.K) -
                r.H * (r.D * r.B + r.h * TenPositiveTrace87.ecl p v) }

/-- The root-scale-four norm polynomial `Q (Z² - 16 M² G V²) + (16 M² G - Z²)`. -/
def norm16 (r : Regs R) (Z : R) : R :=
  r.Q * (Z * Z - r.M * r.M * (16 * r.Gn) * (r.V * r.V)) + (r.M * r.M * (16 * r.Gn) - Z * Z)

/-- The value of the 118-operation circuit (its output row `N`). -/
def value118 (p : Fin 4 → R) (v : Fin 10 → R) : R :=
  let r := regs118 p v
  r.Q * (r.Z * r.Z - r.M * r.M * (16 * r.Gn) * (r.V * r.V)) +
    (r.M * r.M * (16 * r.Gn) - r.Z * r.Z)

/-- The scalar centre `u (x (4 e V - u² b Sc) + 2 S (u² b (3 e + e₂) - (b - c)))`. -/
def omegaAt (x u e S e2 c b Vs : R) : R :=
  u*(x*(4*(e*Vs)-u*u*b*(4*(e*e)+3*(S*S)+e2*e2))+2*(S*(u*u*b*(3*e+e2)-(b-c))))

/-- The quotient remainder `S = (k Ybar) [ell + k - (k Ybar) (Ybar + 1)]`. -/
def Sq (p : Fin 4 → R) (v : Fin 10 → R) : R :=
  let r := TenPositiveTrace87.regs p v
  r.k * r.Y * (r.X * r.Y * r.Y * r.k + r.k - r.k * r.Y * (r.Y + 1))

/-- `e₂ = (k Ybar)²`. -/
def e2q (p : Fin 4 → R) (v : Fin 10 → R) : R :=
  let r := TenPositiveTrace87.regs p v
  r.k * r.Y * (r.k * r.Y)

/-- The unfolded whole-product centre `Ω`. -/
def omega (p : Fin 4 → R) (v : Fin 10 → R) : R :=
  let r := TenPositiveTrace87.regs p v
  omegaAt (r.Am1 + 1) r.U r.E (Sq p v) (e2q p v) r.c r.b r.V

/-- The transport weight `L = A U³ b²`. -/
def weight (p : Fin 4 → R) (v : Fin 10 → R) : R :=
  let r := TenPositiveTrace87.regs p v
  (r.Am1 + 1) * (r.U * r.U * r.U) * (r.b * r.b)

theorem value118_norm (p : Fin 4 → R) (v : Fin 10 → R) :
    value118 p v = norm16 (TenPositiveTrace87.regs p v) (regs118 p v).Z := rfl

theorem regs118_Z_def (p : Fin 4 → R) (v : Fin 10 → R) :
    (regs118 p v).Z = (TenPositiveTrace87.regs p v).h * (TenPositiveTrace87.regs p v).D *
      ((TenPositiveTrace87.regs p v).H * (v 7 - omegaFold p v) + (TenPositiveTrace87.regs p v).K) -
      (TenPositiveTrace87.regs p v).H * ((TenPositiveTrace87.regs p v).D *
        (TenPositiveTrace87.regs p v).B +
        (TenPositiveTrace87.regs p v).h * TenPositiveTrace87.ecl p v) := rfl

end Generic

variable {R : Type*} [CommRing R]

/-- Folding: `OmegaFold = Ω + L B`. -/
theorem omegaFold_eq (p : Fin 4 → R) (v : Fin 10 → R) :
    omegaFold p v = omega p v + weight p v * (TenPositiveTrace87.regs p v).B := by
  simp only [omegaFold, omega, omegaAt, Sq, e2q, weight]
  ring

theorem norm16_four (r : Regs R) (Z : R) :
    norm16 r (4 * Z) = 16 * TenPositiveTrace76.normValue r Z := by
  simp only [norm16, TenPositiveTrace76.normValue]
  ring

theorem norm16_eq (r : Regs R) (Z : R) :
    norm16 r Z = (r.Q - 1) * Z ^ 2 - 16 * (r.M ^ 2 * r.Gn * (r.Q * r.V ^ 2 - 1)) := by
  simp only [norm16]
  ring

/-- The folded carrier is the 87 carrier minus `M (OmegaFold - b V B)`. -/
theorem regs118_Z_shift (p : Fin 4 → R) (v : Fin 10 → R) :
    (regs118 p v).Z = (TenPositiveTrace87.regs p v).Z - (TenPositiveTrace87.regs p v).M *
      (omegaFold p v - (TenPositiveTrace87.regs p v).b * (TenPositiveTrace87.regs p v).V *
        (TenPositiveTrace87.regs p v).B) := by
  rw [regs118_Z_def, TenPositiveTrace87.Z_def, TenPositiveTrace87.M_def]
  ring

/-- The folded carrier is the weight-`L` carrier minus `M Ω`. -/
theorem regs118_Z_split (p : Fin 4 → R) (v : Fin 10 → R) :
    (regs118 p v).Z = (TenPositiveTrace87.regs p v).h * (TenPositiveTrace87.regs p v).D *
      ((TenPositiveTrace87.regs p v).H * (v 7 - weight p v * (TenPositiveTrace87.regs p v).B) +
        (TenPositiveTrace87.regs p v).K) -
      (TenPositiveTrace87.regs p v).H * ((TenPositiveTrace87.regs p v).D *
        (TenPositiveTrace87.regs p v).B +
        (TenPositiveTrace87.regs p v).h * TenPositiveTrace87.ecl p v) -
      (TenPositiveTrace87.regs p v).M * omega p v := by
  rw [regs118_Z_def, omegaFold_eq, TenPositiveTrace87.M_def]
  ring

/-- Only the carrier reads `n`. -/
theorem value118_update (p : Fin 4 → R) (v : Fin 10 → R) (x : R) :
    value118 p (Function.update v 7 x) = norm16 (TenPositiveTrace87.regs p v)
      ((TenPositiveTrace87.regs p (Function.update v 7 x)).Z -
        (TenPositiveTrace87.regs p v).M * (omegaFold p v - (TenPositiveTrace87.regs p v).b *
          (TenPositiveTrace87.regs p v).V * (TenPositiveTrace87.regs p v).B)) := by
  set v' := Function.update v 7 x with hv'
  have hQ : (TenPositiveTrace87.regs p v').Q = (TenPositiveTrace87.regs p v).Q := rfl
  have hM : (TenPositiveTrace87.regs p v').M = (TenPositiveTrace87.regs p v).M := rfl
  have hG : (TenPositiveTrace87.regs p v').Gn = (TenPositiveTrace87.regs p v).Gn := rfl
  have hV : (TenPositiveTrace87.regs p v').V = (TenPositiveTrace87.regs p v).V := rfl
  have hb : (TenPositiveTrace87.regs p v').b = (TenPositiveTrace87.regs p v).b := rfl
  have hB : (TenPositiveTrace87.regs p v').B = (TenPositiveTrace87.regs p v).B := rfl
  have hc : omegaFold p v' = omegaFold p v := rfl
  rw [value118_norm, regs118_Z_shift]
  simp only [norm16]
  rw [hQ, hM, hG, hV, hb, hB, hc]

end DiophantineConsistency.TenPositiveTrace118

namespace Trace118Omega
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace87 Trace87Factors Trace87Residue
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

set_option maxHeartbeats 2000000 in
/-- `Ω` in the scalar form of `Trace118Estimate`, with all its hypotheses, and
the weight `L = A U³ b²`. -/
theorem omega_data (p : Fin 4 → ℕ) (v : Fin 10 → V) (hb : 0<(p 0:V)) (hv : ∀j,0<v j) :
    ∃ x u e S e2 c0 : DiffRing V,
      TenPositiveTrace118.omega (ports p) (fun j => ι (v j))=
        Trace118Estimate.omegaOf x u e S e2 c0 (regs (ports p) (fun j => ι (v j))).b
          (regs (ports p) (fun j => ι (v j))).V ∧
      TenPositiveTrace118.weight (ports p) (fun j => ι (v j))=
        x*(u*u*u)*((regs (ports p) (fun j => ι (v j))).b*(regs (ports p) (fun j => ι (v j))).b) ∧
      2≤x ∧ 1≤u ∧ 1≤e ∧ 0<c0 ∧ c0≤u ∧ 0≤S ∧ S≤e ∧ 0≤e2 ∧ e2≤e ∧
      (regs (ports p) (fun j => ι (v j))).V=
        (1+2*((x*x-1)*(u*u*e)))*(regs (ports p) (fun j => ι (v j))).b-c0 ∧
      x=ι (A p v)+1 ∧ u=ι (U p v) ∧ e=ι (E p v) ∧ c0=ι (c p v) := by
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
  have hY0 : 0≤YY := by linarith
  have hX0 : 0≤XX := by linarith
  let S : DiffRing V := kk*YY*(XX*YY*YY*kk+kk-kk*YY*(YY+1))
  let e2 : DiffRing V := kk*YY*(kk*YY)
  have hS : TenPositiveTrace118.Sq (ports p) (fun j => ι (v j))=S := by
    change rr.k*rr.Y*(rr.X*rr.Y*rr.Y*rr.k+rr.k-rr.k*rr.Y*(rr.Y+1))=_
    rw [hkr,hYr,hXr]
  have he2 : TenPositiveTrace118.e2q (ports p) (fun j => ι (v j))=e2 := by
    change rr.k*rr.Y*(rr.k*rr.Y)=_
    rw [hkr,hYr]
  refine ⟨a0+1,u,e,S,e2,cc,?_,?_,by linarith,pos1 _ hU,pos1 _ hE,?_,ι_le_ι.mpr hCU,?_,?_,?_,?_,?_,
    rfl,rfl,rfl,rfl⟩
  · change TenPositiveTrace118.omegaAt (rr.Am1+1) rr.U rr.E
      (TenPositiveTrace118.Sq (ports p) (fun j => ι (v j)))
      (TenPositiveTrace118.e2q (ports p) (fun j => ι (v j))) rr.c rr.b rr.V=_
    rw [hS,he2,hAr,hUr,hEr,hcr]
    rfl
  · change (rr.Am1+1)*(rr.U*rr.U*rr.U)*(rr.b*rr.b)=_
    rw [hAr,hUr]
  · rw [←map_zero (ι : V →+* DiffRing V)]; exact ι_lt_ι.mpr hC
  · -- S = k² Y ((X - 2) Y² + Y (Y - 1) + 1) ≥ 0
    have hid : S=kk*kk*(YY*((XX-2)*YY*YY+YY*(YY-1)+1)) := by dsimp only [S]; ring
    rw [hid]
    have h1 : 0≤(XX-2)*YY*YY := mul_nonneg (mul_nonneg (by linarith) hY0) hY0
    have h2 : 0≤YY*(YY-1) := mul_nonneg hY0 (by linarith)
    exact mul_nonneg (mul_nonneg hk0 hk0) (mul_nonneg hY0 (by linarith))
  · have hXY : 0≤XX*YY-1 := by
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
  · exact mul_self_nonneg (kk*YY)
  · have hid : e-e2=1+kk*kk*(XX*XX*YY^4+(XX-1)*YY^2) := by
      rw [heE]; dsimp only [e2]; ring
    have h0 : 0≤kk*kk*(XX*XX*YY^4+(XX-1)*YY^2) := by
      apply mul_nonneg (mul_nonneg hk0 hk0)
      have t1 := mul_nonneg (mul_nonneg hX0 hX0) (pow_nonneg hY0 4)
      have t2 := mul_nonneg (show (0:DiffRing V)≤XX-1 by linarith) (pow_nonneg hY0 2)
      linarith
    linarith
  · rw [show rr.V=_ from hVF]
    ring

/-- `Ω ≥ 0` once `V > 0`. -/
theorem omega_nonneg (p : Fin 4 → ℕ) (v : Fin 10 → V) (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hVpos : 0<(regs (ports p) (fun j => ι (v j))).V) :
    0≤TenPositiveTrace118.omega (ports p) (fun j => ι (v j)) ∧
      0≤TenPositiveTrace118.weight (ports p) (fun j => ι (v j)) ∧
      1≤(regs (ports p) (fun j => ι (v j))).b := by
  obtain ⟨x,u,e,S,e2,c,hom,hw,hx,hu,he,hc,hcu,hS0,hSe,he20,he2,hVF,_,_,_,_⟩ := omega_data p v hb hv
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
  have hb1 := hdisc _ hbpos
  refine ⟨?_,?_,hb1⟩
  · rw [hom]
    exact Trace118Estimate.omega_nonneg x u e S e2 c bb _ hx hu he hc hcu hS0 hSe he20 he2 hVF hb1
  · rw [hw]
    exact mul_nonneg (mul_nonneg (by linarith) (mul_nonneg (mul_nonneg (by linarith) (by linarith))
      (by linarith))) (mul_self_nonneg bb)

#print axioms Trace118Omega.omega_data
#print axioms Trace118Omega.omega_nonneg
end Trace118Omega
