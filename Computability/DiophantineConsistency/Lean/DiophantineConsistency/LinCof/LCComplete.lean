import DiophantineConsistency.LinCof.LCGuard
import DiophantineConsistency.LinCof.LCInterp
import DiophantineConsistency.P138.P138Complete
import DiophantineConsistency.ZRows.Intersective19

/-! # Completeness of the linear-cofactor circuits

From an internal halt `first (run T) = 0` of machine 215, in every model `V` of `𝗜𝚺₁`, an integer
zero `x : Fin 11 → DiffRing V` of `LCValue.valueK portsR x κ ω Λ ψ (lw²)` for every slot filling
that obeys a `SlotLaw` of exponent `e ≤ 1`, takes the canonical `k` at the canonical record, and
whose centre `ψ` does not read `x 9`.  The radical weight is `wt = lw²` for an ARBITRARY ring
element `lw` (172: `lw = 32`; package 144: `8`; package 135: `2`).

1. the canonical record `Cn` (`P138Canonical.canonical`), fixing `x 0, x 1, x 2, x 5, x 6, x 8`
   (`LCMatches`), and `x 3` through the `k`-slot hypothesis;
2. the guard Pell pair `s, g` (`LCGuard.lc_guard`): `x 10 = s`, `P = (τ g)²`;
3. the strong pair `u, r, f` (`LCInterp.lc_interp`): `x 4 = r`, `B = u²`, `Df = f²`;
4. a root `t` of `π(t) = (t² + 3)(t³ − 19)` modulo `s·r` (`ZRowsIntersective19.root`), residue
   target `a0 = t − (κ + v)`; the interpolation gives `x 7 = T` with `s·r ∣ T − a0` and `y` with
   `Cy = δ y²`;
5. `zc = Dc·(T + κ + v)` (`K = H κ`, `Y − q³ = v M`, `Dc = H M`), so
   `Ac = Dc⁵ π(κ + v + T) = Dc⁵·s·r·e₀ = S·H⁴e₀` with `S = M⁴·(s r)·Dc`;
6. `x 9 = n − ψ`, `n = H⁴e₀ + lw·u·f·y + τ·g`, so `Z = S (n) − Ac = S·(α + β)`,
   `α = lw u f y`, `β = τ g`;
7. `LCValue.value_eq_zero_of` with `wt·B·Df·Cy = lw²u²f²·δy² = δ α²`.

Differences from `P138Complete.complete`: the shift is `κ + v` (the extra `H·(Y − q³)` in `zc`);
the witness has two radicals `α + β` instead of the single product `p0·f·y`; the centre `ψ`
shifts `n`; `x 3` is supplied by the `k`-slot.  No division is used. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.LCComplete
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing P138Ports LCValue LCCanonical
open P138Canonical (Canonical)
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC

attribute [local irreducible] Source34Ports.betaNat Source34Ports.lowNat Source34Ports.highNat
  Source34Kernel.paramKernel Mixed121Kernel.rho coneA coneB

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **The zero at a canonical record.**  For a prescribed `x 3 = h3` and weight root `lw` there
are a base point `x0` and an assembly value `n` such that every `x` agreeing with `x0` off the
coordinate `9` matches the record, has `x 3 = h3`, and is a zero of `valueK … ψ (lw²)` as soon as
`x 9 = n − ψ`, the slots obey a `SlotLaw` of exponent `e ≤ 1`, and `κ` is the record's `k`. -/
theorem lc_zero (Cn : Canonical V) {e : ℕ} (he : e ≤ 1) (lw h3 : DiffRing V) :
    ∃ (x0 : Fin 11 → DiffRing V) (n : DiffRing V), ∀ x : Fin 11 → DiffRing V,
      (∀ i, i ≠ 9 → x i = x0 i) →
        LCMatches Cn x ∧ x 3 = h3 ∧
          ∀ κ ω Λ ψ : DiffRing V, x 9 = n - ψ → SlotLaw (portsR (V := V)) x κ ω Λ e →
            κ = ι Cn.k → valueK (portsR (V := V)) x κ ω Λ ψ (lw ^ 2) = 0 := by
  obtain ⟨Dn, s, g, hs, _hg0, hD, hg⟩ := LCGuard.lc_guard Cn he
  obtain ⟨u, r, f, _hu, hr, hall⟩ := LCInterp.lc_interp Cn s hs
  obtain ⟨t, ht⟩ := ZRowsIntersective19.root (s * r) (mul_pos hs hr)
  obtain ⟨T7, y, hT7, hreg⟩ := hall (t - (Cn.κ + ι Cn.v))
  obtain ⟨e0, he0⟩ := P138Complete.shifted_root ht hT7
  rw [map_mul] at he0
  obtain ⟨x0, hx0def⟩ : ∃ x0 : Fin 11 → DiffRing V, x0 =
      ![ι Cn.j, ι Cn.C, ι Cn.z, h3, ι r, ι Cn.Y, ι Cn.w, T7, ι Cn.c, 0, ι s] := ⟨_, rfl⟩
  have h0 : x0 0 = ι Cn.j := by subst hx0def; rfl
  have h1 : x0 1 = ι Cn.C := by subst hx0def; rfl
  have h2 : x0 2 = ι Cn.z := by subst hx0def; rfl
  have h3' : x0 3 = h3 := by subst hx0def; rfl
  have h4 : x0 4 = ι r := by subst hx0def; rfl
  have h5 : x0 5 = ι Cn.Y := by subst hx0def; rfl
  have h6 : x0 6 = ι Cn.w := by subst hx0def; rfl
  have h7 : x0 7 = T7 := by subst hx0def; rfl
  have h8 : x0 8 = ι Cn.c := by subst hx0def; rfl
  have h10 : x0 10 = ι s := by subst hx0def; rfl
  refine ⟨x0, (4 * ι Cn.a + 3) ^ 4 * e0 + lw * ι u * ι f * y + ι Cn.τ * ι g, ?_⟩
  intro x hag
  have hx : LCMatches Cn x :=
    { x0 := (hag 0 (by decide)).trans h0
      x1 := (hag 1 (by decide)).trans h1
      x2 := (hag 2 (by decide)).trans h2
      x5 := (hag 5 (by decide)).trans h5
      x6 := (hag 6 (by decide)).trans h6
      x8 := (hag 8 (by decide)).trans h8 }
  have hx3 : x 3 = h3 := (hag 3 (by decide)).trans h3'
  have hx4 : x 4 = ι r := (hag 4 (by decide)).trans h4
  have hx7 : x 7 = T7 := (hag 7 (by decide)).trans h7
  have hx10 : x 10 = ι s := (hag 10 (by decide)).trans h10
  refine ⟨hx, hx3, ?_⟩
  intro κ ω Λ ψ hx9 hlaw hκ
  obtain ⟨hB, hDf, hCy⟩ := hreg x κ ω Λ ψ (lw ^ 2) hx hx4 hx7
  have hP := LCGuard.lc_P Cn hD hg hx κ ω Λ ψ (lw ^ 2) hlaw hκ hx10
  have hH := lc_H Cn hx κ ω Λ ψ (lw ^ 2)
  have hK := lc_K Cn hx κ ω Λ ψ (lw ^ 2)
  have hYq := lc_Yq Cn hx κ ω Λ ψ (lw ^ 2)
  -- `zc = Dc·(T + κ + v)`
  have hzc : (regsK (portsR (V := V)) x κ ω Λ ψ (lw ^ 2)).zc =
      (regsK (portsR (V := V)) x κ ω Λ ψ (lw ^ 2)).Dc * (T7 + Cn.κ + ι Cn.v) := by
    rw [zc_eq, hx7, hK, Dc_eq]
    linear_combination (regsK (portsR (V := V)) x κ ω Λ ψ (lw ^ 2)).H * hYq
  -- `Ac = S·H⁴e₀`
  have hAc : (regsK (portsR (V := V)) x κ ω Λ ψ (lw ^ 2)).Ac =
      (regsK (portsR (V := V)) x κ ω Λ ψ (lw ^ 2)).S * ((4 * ι Cn.a + 3) ^ 4 * e0) := by
    rw [Ac_eq, hzc, S_eq_Dc, hx10, hx4, Dc_eq, hH]
    linear_combination
      ((4 * ι Cn.a + 3) * (regsK (portsR (V := V)) x κ ω Λ ψ (lw ^ 2)).M) ^ 5 * he0
  -- `Z = S·(α + β)`
  have hZ : (regsK (portsR (V := V)) x κ ω Λ ψ (lw ^ 2)).Z =
      (regsK (portsR (V := V)) x κ ω Λ ψ (lw ^ 2)).S *
        (lw * ι u * ι f * y + ι Cn.τ * ι g) := by
    rw [Z_eq, Psi_reg, hx9]
    linear_combination (-1 : DiffRing V) * hAc
  -- `wt·B·Df·Cy = δ α²`
  have hC : lw ^ 2 * (regsK (portsR (V := V)) x κ ω Λ ψ (lw ^ 2)).B *
        (regsK (portsR (V := V)) x κ ω Λ ψ (lw ^ 2)).Df *
        (regsK (portsR (V := V)) x κ ω Λ ψ (lw ^ 2)).Cy =
      (regsK (portsR (V := V)) x κ ω Λ ψ (lw ^ 2)).delta * (lw * ι u * ι f * y) ^ 2 := by
    rw [hB, hDf]
    linear_combination (lw ^ 2 * ι u ^ 2 * ι f ^ 2) * hCy
  exact value_eq_zero_of (portsR (V := V)) x κ ω Λ ψ (lw ^ 2) (lw * ι u * ι f * y)
    (ι Cn.τ * ι g) hZ hP hC

/-- **Generic completeness.**  Slot fillers `kf, ωf, Λf, ψf` (functions of the point) such that
the slots obey a `SlotLaw` of exponent `e ≤ 1` everywhere, `kf` is the record's `k` at every
matching point with a suitable `x 3`, and the centre `ψf` does not read `x 9`. -/
theorem lc_complete {e : ℕ} (he : e ≤ 1) (lw : DiffRing V)
    (kf ωf Λf ψf : (Fin 11 → DiffRing V) → DiffRing V)
    (hlaw : ∀ x, SlotLaw (portsR (V := V)) x (kf x) (ωf x) (Λf x) e)
    (hk : ∀ Cn : Canonical V, ∃ h3 : DiffRing V, ∀ x, LCMatches Cn x → x 3 = h3 →
      kf x = ι Cn.k)
    (hψ : ∀ x t, ψf (Function.update x 9 t) = ψf x)
    (T : V) (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :
    ∃ x : Fin 11 → DiffRing V,
      valueK (portsR (V := V)) x (kf x) (ωf x) (Λf x) (ψf x) (lw ^ 2) = 0 := by
  obtain ⟨Cn⟩ := P138Canonical.canonical T hT
  obtain ⟨h3, hh3⟩ := hk Cn
  obtain ⟨x0, n, hpt⟩ := lc_zero Cn he lw h3
  obtain ⟨x, hxdef⟩ : ∃ x : Fin 11 → DiffRing V, x = Function.update x0 9 (n - ψf x0) :=
    ⟨_, rfl⟩
  have hag : ∀ i, i ≠ 9 → x i = x0 i := by
    subst hxdef
    exact fun i hi => Function.update_of_ne hi _ _
  have hx9 : x 9 = n - ψf x := by
    subst hxdef
    exact (Function.update_self _ _ _).trans (by rw [hψ x0 (n - ψf x0)])
  obtain ⟨hx, hx3, hzero⟩ := hpt x hag
  exact ⟨x, hzero (kf x) (ωf x) (Λf x) (ψf x) hx9 (hlaw x) (hh3 x hx hx3)⟩

/-! ## The two slot families -/

/-- Completeness for every circuit with the 298-type slots `k298 / kq298 / L298` (`e = 0`). -/
theorem lc_complete298 (lw : DiffRing V) (ψf : (Fin 11 → DiffRing V) → DiffRing V)
    (hψ : ∀ x t, ψf (Function.update x 9 t) = ψf x)
    (T : V) (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :
    ∃ x : Fin 11 → DiffRing V,
      valueK (portsR (V := V)) x (k298 (portsR (V := V)) x) (kq298 (portsR (V := V)) x)
        (L298 (portsR (V := V)) x) (ψf x) (lw ^ 2) = 0 :=
  lc_complete (e := 0) (Nat.zero_le 1) lw (k298 (portsR (V := V))) (kq298 (portsR (V := V)))
    (L298 (portsR (V := V))) ψf (fun x => slotLaw298 (portsR (V := V)) x)
    (fun Cn => by
      obtain ⟨h3, hh3⟩ := k298_exists Cn
      exact ⟨ι h3, fun x hx hx3 => k298_canonical Cn hx hh3 hx3⟩)
    hψ T hT

/-- Completeness for every circuit with the 300-type slots `k300 / kq300 / L300` (`e = 1`):
package 172's 300/144 and the five sibling points of packages 135 and 144. -/
theorem lc_complete300 (lw : DiffRing V) (ψf : (Fin 11 → DiffRing V) → DiffRing V)
    (hψ : ∀ x t, ψf (Function.update x 9 t) = ψf x)
    (T : V) (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :
    ∃ x : Fin 11 → DiffRing V,
      valueK (portsR (V := V)) x (k300 (portsR (V := V)) x) (kq300 (portsR (V := V)) x)
        (L300 (portsR (V := V)) x) (ψf x) (lw ^ 2) = 0 :=
  lc_complete (e := 1) le_rfl lw (k300 (portsR (V := V))) (kq300 (portsR (V := V)))
    (L300 (portsR (V := V))) ψf (fun x => slotLaw300 (portsR (V := V)) x)
    (fun Cn => ⟨ι Cn.h, fun x hx hx3 => k300_canonical Cn hx hx3⟩)
    hψ T hT

/-! ## Package 172's two forms -/

/-- The centre of 298/146 does not read `x 9` (only `Z` does). -/
theorem psi298_update9 (x : Fin 11 → DiffRing V) (t : DiffRing V) :
    psi298 (portsR (V := V)) (Function.update x 9 t) = psi298 (portsR (V := V)) x := rfl

/-- The centre of 300/144 does not read `x 9`. -/
theorem psi300_update9 (x : Fin 11 → DiffRing V) (t : DiffRing V) :
    psi300 (portsR (V := V)) (Function.update x 9 t) = psi300 (portsR (V := V)) x := rfl

/-- **Completeness of 298/146**: an internal halt of machine 215 gives an integer zero. -/
theorem complete298 (T : V) (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :
    ∃ x : Fin 11 → DiffRing V, LCValue.value298 (portsR (V := V)) x = 0 := by
  obtain ⟨x, h⟩ := lc_complete298 (32 : DiffRing V) (psi298 (portsR (V := V)))
    psi298_update9 T hT
  rw [show (32 : DiffRing V) ^ 2 = 1024 by norm_num] at h
  exact ⟨x, h⟩

/-- **Completeness of 300/144**: an internal halt of machine 215 gives an integer zero. -/
theorem complete300 (T : V) (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :
    ∃ x : Fin 11 → DiffRing V, LCValue.value300 (portsR (V := V)) x = 0 := by
  obtain ⟨x, h⟩ := lc_complete300 (32 : DiffRing V) (psi300 (portsR (V := V)))
    psi300_update9 T hT
  rw [show (32 : DiffRing V) ^ 2 = 1024 by norm_num] at h
  exact ⟨x, h⟩

#print axioms lc_zero
#print axioms lc_complete
#print axioms complete298
#print axioms complete300

end DiophantineConsistency.LCComplete
