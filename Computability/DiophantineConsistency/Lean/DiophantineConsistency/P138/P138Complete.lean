import DiophantineConsistency.P138.P138Guard
import DiophantineConsistency.P138.P138Interp
import DiophantineConsistency.ZRows.Intersective19

/-! # Completeness of package 138's 924/107 equation (stage C8, the assembly)

From an internal halt `first (run T) = 0` of machine 215, in every model `V` of `𝗜𝚺₁`, this
module produces an integer zero `x : Fin 11 → DiffRing V` of `P138Value.value portsR`
(`complete`), following `P138_ROUTE.md` C8:

1. the canonical record `Cn` (`P138Canonical.canonical`), fixing `x 0, x 1, x 2, x 3, x 5, x 6,
   x 8`;
2. the guard Pell pair `s, g` (`P138Guard.guard`), so `x 10 = s` and `BP = p0²` with
   `p0 = d τ g`;
3. the interpolation `r, f` (`P138Interp.interp`), so `x 4 = r`, `s ∣ r`, `Df = f²`;
4. a root `t` of `π(t) = (t² + 3)(t³ − 19)` modulo `s·r` (`ZRowsIntersective19.root`), and the
   residue target `a0 = t − κ`; the interpolation gives `x 7 = T` with `s·r ∣ T − a0` and an
   ordinate `y` with `Q V² − (Q − 1) y² = 1`;
5. since `K = H κ` (`reg_K`), `zc = H (κ + T)` and `Ac = H⁵ π(κ + T)`; as `κ + T ≡ t (mod s·r)`,
   `π(κ + T) = s·r·e₀` for an exact quotient `e₀`, so `Ac = S·H⁴e₀` with `S = H r s`;
6. `x 9 = n = H⁴e₀ + p0·f·y`, so `Z = n S − Ac = S·p0·f·y`;
7. `P138Value.value_eq_product`: `value = (Q − 1) Z² − S² BP Df (Q V² − 1)
   = S² p0² f² ((Q − 1) y² − (Q V² − 1)) = 0`.

No division is used: `e₀` is the quotient of a proved divisibility in `DiffRing V`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.P138Complete
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing P138Value P138Ports P138Canonical
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC

attribute [local irreducible] Source34Ports.betaNat Source34Ports.lowNat Source34Ports.highNat
  Source34Kernel.paramKernel Mixed121Kernel.rho coneA coneB

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The residue step: if `m ∣ π(t)` and `m ∣ T − (t − κ)`, then `π(κ + T) = m·e₀`. -/
theorem shifted_root {m t κ T : DiffRing V} (ht : m ∣ (t ^ 2 + 3) * (t ^ 3 - 19))
    (hT : m ∣ T - (t - κ)) :
    ∃ e0 : DiffRing V, ((κ + T) ^ 2 + 3) * ((κ + T) ^ 3 - 19) = m * e0 := by
  have hd1 : m ∣ (κ + T) - t := by
    rwa [show (κ + T) - t = T - (t - κ) by ring]
  have hd2 := dvd_trans hd1 (ZRowsIntersective19.poly19_sub_dvd (κ + T) t)
  have hd3 : m ∣ ZRowsIntersective19.poly19 t := by
    have e : ZRowsIntersective19.poly19 t = (t ^ 2 + 3) * (t ^ 3 - 19) := by
      simp only [ZRowsIntersective19.poly19, ZRowsIntersective19.f1, ZRowsIntersective19.f2]
      ring
    rw [e]; exact ht
  have hd4 := dvd_add hd2 hd3
  rw [sub_add_cancel] at hd4
  obtain ⟨e0, he0⟩ := hd4
  refine ⟨e0, ?_⟩
  rw [← he0]
  simp only [ZRowsIntersective19.poly19, ZRowsIntersective19.f1, ZRowsIntersective19.f2]
  ring

/-- **C8. Completeness**: an internal halt of machine 215 gives an integer zero of the 924/107
polynomial at the six ports. -/
theorem complete (T : V) (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :
    ∃ x : Fin 11 → DiffRing V, value portsR x = 0 := by
  obtain ⟨Cn⟩ := canonical T hT
  obtain ⟨_Dn, s, g, _hDn, hs, hg, _hgn, _hD4, hguard⟩ := P138Guard.guard Cn
  obtain ⟨r, f, hr, _hsr, hall⟩ :=
    P138Interp.interp Cn s g hs hg (fun x hx h10 => (hguard x hx h10).2)
  obtain ⟨t, ht⟩ := ZRowsIntersective19.root (s * r) (mul_pos hs hr)
  obtain ⟨u7, y, hu7, hreg⟩ := hall (t - Cn.κ)
  obtain ⟨e0, he0⟩ := shifted_root ht hu7
  rw [map_mul] at he0
  -- the assembly coordinate `n = H⁴ e₀ + p0 f y`
  obtain ⟨x, hxdef⟩ : ∃ x : Fin 11 → DiffRing V, x =
      ![ι Cn.j, ι Cn.C, ι Cn.z, ι Cn.h, ι r, ι Cn.v, ι Cn.w, u7, ι Cn.c,
        (4 * ι Cn.a + 3) ^ 4 * e0 + (ι Cn.d * ι Cn.τ * ι g) * ι f * y, ι s] := ⟨_, rfl⟩
  have hx : Matches Cn x := by subst hxdef; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hx4 : x 4 = ι r := by subst hxdef; rfl
  have hx7 : x 7 = u7 := by subst hxdef; rfl
  have hx9 : x 9 = (4 * ι Cn.a + 3) ^ 4 * e0 + (ι Cn.d * ι Cn.τ * ι g) * ι f * y := by subst hxdef; rfl
  have hx10 : x 10 = ι s := by subst hxdef; rfl
  refine ⟨x, ?_⟩
  obtain ⟨hDf, hnorm⟩ := hreg x hx hx4 hx7 hx10
  have hBP := (hguard x hx hx10).2
  have hS : (regs (portsR (V := V)) x).S = ι s * ι r * (4 * ι Cn.a + 3) := by
    rw [S_eq, hx10, hx4, reg_H Cn hx]
  have hAc : (regs (portsR (V := V)) x).Ac = (4 * ι Cn.a + 3) ^ 5 * (ι s * ι r) * e0 := by
    rw [Ac_eq, zc_eq, reg_K Cn hx, hx7, reg_H Cn hx]
    linear_combination (4 * ι Cn.a + 3) ^ 5 * he0
  have hZ : (regs (portsR (V := V)) x).Z = (regs (portsR (V := V)) x).S * ((ι Cn.d * ι Cn.τ * ι g) * ι f * y) := by
    rw [Z_eq, hx9]
    linear_combination (4 * ι Cn.a + 3) ^ 4 * e0 * hS - hAc
  rw [value, value_eq_product, hZ, hBP, hDf]
  linear_combination
    (-((regs (portsR (V := V)) x).S ^ 2 * (ι Cn.d * ι Cn.τ * ι g) ^ 2 * ι f ^ 2)) * hnorm

#print axioms shifted_root
#print axioms complete

end DiophantineConsistency.P138Complete
