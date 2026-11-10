import DiophantineConsistency.BFS943.Centred87Regs
import DiophantineConsistency.BFS943.Trace87Factors

/-! # The ten-positive 89-operation, degree-210 centred equation

Package 179 (`179-affine-horizons-centered-certificates/positive/late172`),
mode `centerAp1`: the circuit `centerAp1_radix67.json` (89 operations, exact
degree 210, weight `L = bV`). It is package 172's 87/214 free-inverse circuit
with the transport gate `n - L B` replaced by `n - V (b B + g₊)` at the
centre `g₊ = (A + 1) U E` (rows `g0 = Ap1 · UE`, `bB`, `bB_g0`, `LBt`; in the
Lean registers `A - 1` is `Am1`, so `A + 1 = Am1 + 2`). So
`value89 = TenPositiveCentred87.valueAt` at `centre`.

`Trace89Centre.gnat` is the natural representative of the centre at positive
inputs, and `gnat_bound` is 179's `g₊² < 4 G` (`G = E F0`). -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.TenPositiveTrace89

section Generic
variable {R : Type*} [Add R] [Sub R] [Mul R] [OfNat R 1] [OfNat R 2] [OfNat R 3] [OfNat R 4]
  [OfNat R 6]

/-- The centre `g₊ = (A + 1) U E`. -/
def centre (p : Fin 4 → R) (v : Fin 10 → R) : R :=
  let r := TenPositiveTrace87.regs p v
  (r.Am1 + 2) * (r.U * r.E)

/-- The value of the 89-operation circuit (its output row `N`). -/
def value89 (p : Fin 4 → R) (v : Fin 10 → R) : R :=
  TenPositiveCentred87.valueAt p v (centre p v)

end Generic

end DiophantineConsistency.TenPositiveTrace89

namespace Trace89Centre
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace87 Trace87Factors
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The natural centre `(A + 1) U E` (`A p v` is the register `Am1`). -/
def gnat (p : Fin 4 → ℕ) (v : Fin 10 → V) : V := (A p v+2)*(U p v*E p v)

theorem centre_eval (p : Fin 4 → ℕ) (v : Fin 10 → V) :
    TenPositiveTrace89.centre (ports p) (fun j => ι (v j)) = ι (gnat p v) := by
  have hA : (regs (ports p) (fun j => ι (v j))).Am1=ι (A p v) := by
    simp only [Am1_def,X_def,Y_def,q_def,h_def,ports,A,X,Y,q,b,map_mul,map_add,map_one,
      map_natCast]
  change ((regs (ports p) (fun j => ι (v j))).Am1+2)*((regs (ports p) (fun j => ι (v j))).U*
    (regs (ports p) (fun j => ι (v j))).E)=_
  rw [hA,U_eval,E_eval]
  simp only [gnat,map_mul,map_add,map_ofNat]

theorem gnat_update (p : Fin 4 → ℕ) (v : Fin 10 → V) (x : V) :
    gnat p (Function.update v 7 x)=gnat p v := rfl

/-- 179's `g₊² < 4 G`: `4 E (1 + a) - g₊² = 4 E + (U E)² (3 A² + 4 A - 4)` at
`A = Am1 ≥ 1`. -/
theorem gnat_bound (p : Fin 4 → ℕ) (v : Fin 10 → V) (hb : 0<(p 0:V)) (hv : ∀j,0<v j) :
    gnat p v*gnat p v<4*(E p v*(1+delta p v*U p v*U p v*E p v)) := by
  have hb0 : 0<b p v := mul_pos hb (hv 0)
  have hq : 0<q p v := add_pos hb0 (by simp)
  have hy : 0<Y p v := mul_pos hq (hv 6)
  have hx : 0<X p v := mul_pos hq (hv 5)
  have hA : 0<A p v := add_pos (mul_pos hx hy) hy
  obtain ⟨_,_,hE,_⟩ := factors_positive p v hb hv
  apply ι_lt_ι.mp
  have hx1 : (1:DiffRing V)≤ι (A p v) := by
    rw [←map_one (ι : V →+* DiffRing V),ι_le_ι]; exact pos_iff_one_le.mp hA
  have he : (0:DiffRing V)<ι (E p v) := by
    rw [←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hE
  simp only [gnat,delta,map_mul,map_add,map_one,map_ofNat]
  set x : DiffRing V := ι (A p v)
  set u : DiffRing V := ι (U p v)
  set e : DiffRing V := ι (E p v)
  have hkey : 4*(e*(1+x*(x+2)*u*u*e))-(x+2)*(u*e)*((x+2)*(u*e))=
      4*e+(u*e)*(u*e)*(3*x*x+4*x-4) := by ring
  have hpoly : (0:DiffRing V)<3*x*x+4*x-4 := by nlinarith
  have hsq : (0:DiffRing V)≤(u*e)*(u*e) := mul_self_nonneg _
  have hpos : (0:DiffRing V)<4*e+(u*e)*(u*e)*(3*x*x+4*x-4) := by
    have := mul_nonneg hsq (le_of_lt hpoly)
    linarith
  linarith

#print axioms Trace89Centre.centre_eval
#print axioms Trace89Centre.gnat_bound
end Trace89Centre
