import DiophantineConsistency.Z10.Z10BridgeComplete
import DiophantineConsistency.Z10.Z10Interp
import DiophantineConsistency.Z10.Z10Carrier
import DiophantineConsistency.Z10.Z10Squares
import DiophantineConsistency.ZRows.Intersective23
import DiophantineConsistency.ZRows.ModelPellExistence

/-! # Ten-integer package 106: completeness

Completeness steps C7–C11 of the route, which close the completeness half: an
internal halting run of machine 215 gives an integer zero of the equation of
package 106 (`complete`), and of each of its three variants (`complete_variant`).

From the registers of `Z10BridgeComplete.bridge_complete`:

* **C7** (guard radicand). `a0 = r (1 + (9Δ − 3) r z²)` with `r = b Q` a positive square.
  `9Δ − 3 = 3 (3Δ' + 2)` and `r ≡ 1 (mod 3)`, so `(9Δ − 3) r` has 3-adic valuation one
  (`not_square`); Pell's theorem (`ModelPellExistence.exists_pos`) gives `z > 0` making the
  cofactor a square.
* **C8** (interpolation, `Z10Interp.interp` with `N = z`): `ξ = z x`, and every class of `y`
  modulo `ξ` keeps `a1` a square.
* **C9** (intersective root, `ZRowsIntersective23.root`): with `T = S T'`, the class
  `y ≡ t₀ − T' (mod ξ)` for a root `t₀` of `π(t) = (t³ − t − 1)(t² + 23)` modulo `ξ` gives
  `ξ ∣ π(T' + y)`, so `Σ = ξ S⁵` divides `Θ = S⁵ π(T' + y)`.
* **C10** (`N9Norm.norm2_zero_of_root`): `m = Θ/Σ + √a0 + √a1`.
* **C11** (`Z10Regs.exists_shift`): the variants are translates of polar in `m`.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Z10Complete
open Nine121 Nine121.N105Layout Z10Regs

section Ring
variable {𝔸 : Type*} [CommRing 𝔸]

/-- The intersective quintic respects congruences. -/
theorem pi_sub (u v : 𝔸) :
    (u ^ 3 - u - 1) * (u ^ 2 + 23) - (v ^ 3 - v - 1) * (v ^ 2 + 23) =
      (u - v) * (u ^ 4 + u ^ 3 * v + u ^ 2 * v ^ 2 + 22 * u ^ 2 + u * v ^ 3 + 22 * u * v - u +
        v ^ 4 + 22 * v ^ 2 - v - 23) := by
  ring

/-- The registers `T, S, r, Delta` read only the first six unknowns. -/
theorem regs6_congr (p : Fin 4 → 𝔸) {x x' : Fin 10 → 𝔸} (h0 : x 0 = x' 0) (h1 : x 1 = x' 1)
    (h2 : x 2 = x' 2) (h3 : x 3 = x' 3) (h4 : x 4 = x' 4) (h5 : x 5 = x' 5) :
    (regs p x).T = (regs p x').T ∧ (regs p x).S = (regs p x').S ∧
      (regs p x).r = (regs p x').r ∧ (regs p x).Delta = (regs p x').Delta := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  simp only [T_def, W_def, C_def, b_def, S_def, A_def, halfA_def, halfU_def, uv_def, V_def,
    L_def, X_def, Y_def, g_def, r_def, Q_def, Phalf_def, U_def, K_def, k2_def, Delta_def,
    cap_def, h0, h1, h2, h3, h4, h5]

end Ring

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ModelDifferenceRing ArithmeticPellRecurrence
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] Mixed121Ports.ports

/-- The ports in the ring of differences. -/
local notation "pR" => Source31Facts.portsR (V := V) Mixed121Ports.ports

/-- **The Pell discriminant of the guard is not a square**: `3 (3Δ' + 2)(3ρ + 1)` has
3-adic valuation one. -/
theorem not_square (Δ' ρ s : V) : s * s ≠ 3 * (3 * Δ' + 2) * (3 * ρ + 1) := by
  intro hs
  apply Z10Bootstrap.three_not_dvd_one (V := V)
  have h := congrArg (ι (V := V)) hs
  obtain ⟨t, rfl | rfl | rfl⟩ := Z10Squares.mod3_split s
  · simp only [map_mul, map_add, map_ofNat, map_one] at h
    have h3 : (3 : DiffRing V) * (3 * ι t * ι t) = 3 * ((3 * ι Δ' + 2) * (3 * ι ρ + 1)) := by
      linear_combination h
    have h4 := mul_left_cancel₀ (show (3 : DiffRing V) ≠ 0 by norm_num) h3
    exact ⟨1 - ι t * ι t + 3 * ι Δ' * ι ρ + ι Δ' + 2 * ι ρ, by linear_combination h4⟩
  · simp only [map_mul, map_add, map_ofNat, map_one] at h
    exact ⟨(3 * ι Δ' + 2) * (3 * ι ρ + 1) - 3 * ι t * ι t - 2 * ι t, by linear_combination h⟩
  · simp only [map_mul, map_add, map_ofNat, map_one] at h
    exact ⟨(3 * ι Δ' + 2) * (3 * ι ρ + 1) - 3 * ι t * ι t - 4 * ι t - 1,
      by linear_combination h⟩

set_option maxHeartbeats 1000000 in
/-- **Completeness**: a halting run gives an integer zero of the polar equation. -/
theorem zero_of_halt (T : V) (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :
    ∃ x : Fin 10 → DiffRing V, value pR x = 0 := by
  obtain ⟨t, g0, c0, k0, l, w, s, Xn, a, pp, hdone⟩ := Z10BridgeComplete.bridge_complete T hT
  -- the registers of the first six unknowns
  obtain ⟨x0, hx0⟩ : ∃ x0 : Fin 10 → DiffRing V, x0 = ![t, g0, c0, k0, l, w, 0, 0, 0, 0] :=
    ⟨_, rfl⟩
  have D0 := hdone x0 (by rw [hx0]; rfl) (by rw [hx0]; rfl) (by rw [hx0]; rfl)
    (by rw [hx0]; rfl) (by rw [hx0]; rfl) (by rw [hx0]; rfl)
  -- C7: the guard radicand
  obtain ⟨Δn, hΔn⟩ := nonneg_iff.mp D0.hDelta.le
  have hΔn0 : 0 < Δn := by
    have h := D0.hDelta; rw [hΔn, ← map_zero (ι (V := V))] at h; exact ι_lt_ι.mp h
  obtain ⟨Δ', hΔ'⟩ : ∃ Δ' : V, Δ' = Δn - 1 := ⟨_, rfl⟩
  have hΔ1 : Δn = Δ' + 1 := by rw [hΔ', tsub_add_cancel_of_le (pos_iff_one_le.mp hΔn0)]
  obtain ⟨rn, hrn⟩ : ∃ rn : V, rn = Exp.exp s * xcoord (Xn + 1) pp *
      (Exp.exp s * xcoord (Xn + 1) pp) := ⟨_, rfl⟩
  have hr0 : (regs pR x0).r = ι rn := by
    rw [r_def, D0.hb, D0.hQ, hrn]; simp only [map_mul]; ring
  have hrn0 : 0 < rn := by
    have h1 : 0 < Exp.exp s * xcoord (Xn + 1) pp :=
      mul_pos (exp_pos _) (lt_of_lt_of_le (by norm_num) (one_le_x _ _))
    rw [hrn]; exact mul_pos h1 h1
  obtain ⟨k3, hk3⟩ := Z10Bootstrap.r_mod3 pR x0
  rw [hr0] at hk3
  have hk3' : ι rn - 1 = ι (3 : V) * k3 := by rw [map_ofNat]; exact hk3
  obtain ⟨ρ, hρ⟩ := P138FirstIndex.nat_quot (show (0 : V) < 3 by norm_num) (by
    have := ι_le_ι.mpr (pos_iff_one_le.mp hrn0); rw [map_one] at this; linarith) hk3'
  have hrnρ : (ι rn : DiffRing V) = 3 * ι ρ + 1 := by
    rw [hρ, map_ofNat] at hk3'; linear_combination hk3'
  have hD0 : 0 < 3 * (3 * Δ' + 2) * (3 * ρ + 1) :=
    mul_pos (mul_pos (by norm_num) (lt_of_lt_of_le (by norm_num) (le_add_left le_rfl)))
      (lt_of_lt_of_le (by norm_num) (le_add_left le_rfl))
  obtain ⟨X, zz, hzz, hX⟩ :=
    ModelPellExistence.exists_pos _ hD0 (fun s' => not_square Δ' ρ s')
  -- C8: interpolation
  obtain ⟨xi, hxi0, ⟨xx, hxx⟩, hall⟩ := Z10Interp.interp a (2 * Xn + 1) zz Xn hzz rfl
  -- C9: the intersective class
  obtain ⟨T', hT'⟩ := D0.hST
  obtain ⟨t0, ht0⟩ := ZRowsIntersective23.root xi hxi0
  obtain ⟨y, s1, hyc, ha1⟩ := hall (t0 - T')
  obtain ⟨x1, hx1⟩ : ∃ x1 : Fin 10 → DiffRing V,
      x1 = ![t, g0, c0, k0, l, w, ι xx, y, ι zz, 0] := ⟨_, rfl⟩
  have D1 := hdone x1 (by rw [hx1]; rfl) (by rw [hx1]; rfl) (by rw [hx1]; rfl)
    (by rw [hx1]; rfl) (by rw [hx1]; rfl) (by rw [hx1]; rfl)
  have hx17 : x1 7 = y := by rw [hx1]; rfl
  have hx18 : x1 8 = ι zz := by rw [hx1]; rfl
  have hx16 : x1 6 = ι xx := by rw [hx1]; rfl
  have hxi1 : (regs pR x1).xi = ι xi := by
    rw [xi_def, hx18, hx16, hxx, map_mul]
  obtain ⟨eT, eS, er, eD⟩ := regs6_congr pR (x := x1) (x' := x0)
    ((show x1 0 = t by rw [hx1]; rfl).trans (show x0 0 = t by rw [hx0]; rfl).symm)
    ((show x1 1 = g0 by rw [hx1]; rfl).trans (show x0 1 = g0 by rw [hx0]; rfl).symm)
    ((show x1 2 = c0 by rw [hx1]; rfl).trans (show x0 2 = c0 by rw [hx0]; rfl).symm)
    ((show x1 3 = k0 by rw [hx1]; rfl).trans (show x0 3 = k0 by rw [hx0]; rfl).symm)
    ((show x1 4 = l by rw [hx1]; rfl).trans (show x0 4 = l by rw [hx0]; rfl).symm)
    ((show x1 5 = w by rw [hx1]; rfl).trans (show x0 5 = w by rw [hx0]; rfl).symm)
  have hT1 : (regs pR x1).T = (regs pR x1).S * T' := by
    rw [eT, eS]; exact hT'
  have hpi : (ι xi : DiffRing V) ∣ ((T' + y) ^ 3 - (T' + y) - 1) * ((T' + y) ^ 2 + 23) := by
    have e : ((T' + y) ^ 3 - (T' + y) - 1) * ((T' + y) ^ 2 + 23) =
        (t0 ^ 3 - t0 - 1) * (t0 ^ 2 + 23) + ((T' + y) - t0) *
          ((T' + y) ^ 4 + (T' + y) ^ 3 * t0 + (T' + y) ^ 2 * t0 ^ 2 + 22 * (T' + y) ^ 2 +
            (T' + y) * t0 ^ 3 + 22 * (T' + y) * t0 - (T' + y) + t0 ^ 4 + 22 * t0 ^ 2 - t0 -
            23) := by
      rw [← pi_sub]; ring
    have h1 : (ι xi : DiffRing V) ∣ (T' + y) - t0 := by
      have e2 : (T' + y) - t0 = y - (t0 - T') := by ring
      rw [e2]; exact hyc
    rw [e]
    exact dvd_add ht0 (dvd_mul_of_dvd_left h1 _)
  obtain ⟨θ0, hθ0⟩ := hpi
  have hTheta : (regs pR x1).Theta = (regs pR x1).Sigma * θ0 := by
    rw [Z10Carrier.Theta_quotient pR x1 hT1, Sigma_def, hxi1, hx17, hθ0]; ring
  -- the two square roots
  have hr1 : (regs pR x1).r = ι rn := by rw [er, hr0]
  have hΔx1 : (regs pR x1).Delta = ι Δn := by rw [eD, hΔn]
  have hXι : (ι X : DiffRing V) * ι X =
      3 * (3 * ι Δ' + 2) * (3 * ι ρ + 1) * ι zz * ι zz + 1 := by
    have h := congrArg (ι (V := V)) hX
    simpa only [map_add, map_mul, map_ofNat, map_one] using h
  have hΔι : (ι Δn : DiffRing V) = ι Δ' + 1 := by rw [hΔ1, map_add, map_one]
  have hrnι : (ι rn : DiffRing V) =
      ι (Exp.exp s) * ι (xcoord (Xn + 1) pp) * (ι (Exp.exp s) * ι (xcoord (Xn + 1) pp)) := by
    rw [hrn]; simp only [map_mul]
  have ha0 : (regs pR x1).a0 = (ι (Exp.exp s) * ι (xcoord (Xn + 1) pp) * ι X) *
      (ι (Exp.exp s) * ι (xcoord (Xn + 1) pp) * ι X) := by
    rw [a0_def, hr1, hΔx1, hx18]
    linear_combination ι X * ι X * hrnι - ι rn * hXι +
      3 * ι rn * (3 * ι Δ' + 2) * ι zz * ι zz * hrnρ + 9 * ι rn * ι rn * ι zz * ι zz * hΔι
  have ha1' : (regs pR x1).a1 = s1 * s1 := by
    rw [Z10Interp.regs_a1, D1.hhalfA, D1.hB1, D1.hC, hxi1, hx17]
    have e : (2 * ι Xn + 1 : DiffRing V) = ι (2 * Xn + 1) := by
      simp only [map_add, map_mul, map_ofNat, map_one]
    rw [e]; exact ha1
  -- C10: the last unknown
  refine ⟨Function.update x1 9 (θ0 + (ι (Exp.exp s) * ι (xcoord (Xn + 1) pp) * ι X) + s1), ?_⟩
  rw [value, regs_update, Function.update_self]
  show Nine121.N9Norm.norm2 ((regs pR x1).Sigma *
      (θ0 + (ι (Exp.exp s) * ι (xcoord (Xn + 1) pp) * ι X) + s1) - (regs pR x1).Theta)
      (regs pR x1).Sigma (regs pR x1).a0 (regs pR x1).a1 = 0
  rw [hTheta, ha0, ha1']
  have e : (regs pR x1).Sigma * (θ0 + (ι (Exp.exp s) * ι (xcoord (Xn + 1) pp) * ι X) + s1) -
      (regs pR x1).Sigma * θ0 =
      (regs pR x1).Sigma * ((ι (Exp.exp s) * ι (xcoord (Xn + 1) pp) * ι X) + s1) := by ring
  rw [e, ← sq, ← sq]
  exact Nine121.N9Norm.norm2_zero_of_root _ _ _

/-- **Completeness for the variants** (linear, cubic, sixterm): C11. -/
theorem zero_of_halt_variant (σ : Regs (DiffRing V) → DiffRing V → DiffRing V) (T : V)
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :
    ∃ x : Fin 10 → DiffRing V, valueS σ pR x = 0 :=
  (exists_shift σ pR).mpr (zero_of_halt T hT)

#print axioms not_square
#print axioms zero_of_halt
#print axioms zero_of_halt_variant

end DiophantineConsistency.Z10Complete
