import DiophantineConsistency.P125.P125Value
import DiophantineConsistency.P137.P137Complete

/-! # Completeness of package 125's three-root 488/118 and 464/119 equations

From an internal halt `first (run T) = 0` of machine 215, in every model `V` of `𝗜𝚺₁`, this
module produces integer zeros `x : Fin 11 → DiffRing V` of `P125Value.valueD portsR`
(`complete_direct`) and of `P125Value.valueC portsR` (`complete_centered`), following `PROOF.md`
§6 of package 125. The front is package 138's with the native index, so the canonical record and
the residue step are reused unchanged:

1. the canonical record `Cn` (`P138Canonical.canonical`), fixing `x 0, x 1, x 2, x 3, x 5, x 6,
   x 8`;
2. the guard Pell pair of package 137 (`P137Complete.guard`): `g² = 1 + 4 (3 Budget − 4) τ² s²`.
   The guard cofactor here is `Dg = 1 + (3 Budget − 4) Dt s²`, without the factor `4`, so
   `x 10 = 2 s` and `Dt Dg = (τ g)²`;
3. the strong pair and the interpolation (`interp`, the argument of `P137Complete.interp` with no
   multiplier: the strong register here is `I = r c²`): `r, f > 0` with `Df = f²`, and for every
   residue target `a0` a value `x 7 = T` with `2 s r ∣ T − a0` and an ordinate `y` with
   `Q V² − (Q − 1) y² = 1`, so that `δ Cy = ((Q − 1) y)²`;
4. a root `t` of `π(t) = (t² + 3)(t³ − 19)` modulo `2 s r` (`ZRowsIntersective19.root`), target
   `a0 = t − κ`, exact quotient `e₀` (`P138Complete.shifted_root`), `Ac = S H⁴ e₀`;
5. `x 9 = n = H⁴ e₀ + 3 f + (Q − 1) y + 9 τ g`, with `Q` written in closed form, so the definition
   is not circular. Then the direct slot is `S n − Ac = S (3 f + (Q − 1) y + 9 τ g)`, the sum of
   the three roots of the radicands `(3S)² Df`, `S² δ Cy`, `(9S)² Dt Dg`, and
   `P125Value.out_of_roots` gives the zero.

The centered form reads the slot `S (n + Q V) − Ac`; `Q V` does not read `x 9`, so the direct
zero with `x 9` replaced by `x 9 − Q V` is a centered zero (`P125Value.valueC_shift`).

No division is used: `e₀` and `T` are quotients of proved divisibilities in `DiffRing V`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.P125Complete
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing P138Value P138Ports P138Canonical ArithmeticPellRecurrence
open ZRowsLinearInterpolation
open P125Value (back)
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC

attribute [local irreducible] Source34Ports.betaNat Source34Ports.lowNat Source34Ports.highNat
  Source34Kernel.paramKernel Mixed121Kernel.rho coneA coneB

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The strong pair and the interpolation -/

/-- **The supported-modulus interpolation, without a point or a multiplier.** For `s > 0` there
are `r, f > 0` such that, with `Δ = (a+1)(a+3)` and `I = r c²`, `1 + Δ I² = f²`, and every
residue target `a0` modulo `s r` is hit by some `T`, with an ordinate `y` solving the auxiliary
norm `Q V² − (Q − 1) y² = 1`, `Q = Δ² I²`, `V = f² (c − R + 4 I T) − c`. -/
theorem interp (Cn : Canonical V) (s : V) (hs : 0 < s) :
    ∃ r f : V, 0 < r ∧
      (1 + (ι Cn.a + 1) * (ι Cn.a + 3) * (ι r * ι Cn.c ^ 2) ^ 2 : DiffRing V) = ι f ^ 2 ∧
      ∀ a0 : DiffRing V, ∃ T y : DiffRing V,
        (ι (s * r) : DiffRing V) ∣ T - a0 ∧
        ((ι Cn.a + 1) * (ι Cn.a + 3)) ^ 2 * (ι r * ι Cn.c ^ 2) ^ 2 *
            (ι f ^ 2 * (ι Cn.c - ι Cn.R + 4 * (ι r * ι Cn.c ^ 2) * T) - ι Cn.c) ^ 2 -
          (((ι Cn.a + 1) * (ι Cn.a + 3)) ^ 2 * (ι r * ι Cn.c ^ 2) ^ 2 - 1) * y ^ 2 = 1 := by
  have hc := P138Interp.c_pos Cn
  have hN : 0 < 4 * s * (Cn.c * Cn.c) := mul_pos (mul_pos (by norm_num) hs) (mul_pos hc hc)
  obtain ⟨n0, hn0, hNI, hall⟩ := ZRowsLinearInterpolation.supported_interpolation Cn.a Cn.R
    (4 * s * (Cn.c * Cn.c)) (P138Interp.R_mod_four Cn) hN ⟨s * (Cn.c * Cn.c), by ring⟩
  obtain ⟨m, hm⟩ := hNI
  have hI : ycoord n0 Cn.a = Cn.c * Cn.c * (4 * s * m) := by
    rw [hm]; ring
  have hIpos : 0 < ycoord n0 Cn.a := lt_of_lt_of_le hn0 (time_le_y n0 Cn.a)
  have hm0 : 0 < m := by
    rcases (Arithmetic.zero_le m).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, mul_zero] at hm
      exact (ne_of_gt hIpos) hm
  have hr : 0 < 4 * s * m := mul_pos (mul_pos (by norm_num) hs) hm0
  -- ring forms of the strong pair
  have HI := congrArg (ι (V := V)) hI
  have Nf := congrArg (ι (V := V)) (norm n0 Cn.a)
  simp only [map_add, map_mul, map_ofNat, map_one] at HI Nf
  unfold delta at Nf
  simp only [map_add, map_mul, map_ofNat, map_one] at Nf
  rw [HI] at Nf
  refine ⟨4 * s * m, xcoord n0 Cn.a, hr, ?_, ?_⟩
  · simp only [map_mul, map_ofNat]
    linear_combination (-1 : DiffRing V) * Nf
  intro a0
  have hM : 0 < s * (4 * s * m) := mul_pos hs hr
  have hMI : s * (4 * s * m) ∣ ycoord n0 Cn.a * ycoord n0 Cn.a :=
    ⟨Cn.c * Cn.c * Cn.c * Cn.c * (4 * m), by rw [hI]; ring⟩
  obtain ⟨T, y, hdvd, hnorm⟩ := hall _ hM hMI a0
  refine ⟨T, y, hdvd, ?_⟩
  rw [HI] at hnorm
  unfold delta at hnorm
  rw [← Cn.c_main] at hnorm
  simp only [map_add, map_mul, map_ofNat, map_one] at hnorm ⊢
  linear_combination hnorm

/-! ## The assembly -/

/-- **Completeness of the direct form.** An internal halt of machine 215 gives an integer zero of
the 488/118 polynomial at the six ports. -/
theorem complete_direct (T : V)
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :
    ∃ x : Fin 11 → DiffRing V, P125Value.valueD portsR x = 0 := by
  obtain ⟨Cn⟩ := canonical T hT
  obtain ⟨s, g, hs, _hg, hgg⟩ := P137Complete.guard Cn
  have hs' : 0 < 2 * s := mul_pos (by norm_num) hs
  have h2s : (ι (2 * s) : DiffRing V) = 2 * ι s := by simp only [map_mul, map_ofNat]
  obtain ⟨r, f, hr, hDf0, hall⟩ := interp Cn (2 * s) hs'
  obtain ⟨t, ht⟩ := ZRowsIntersective19.root (2 * s * r) (mul_pos hs' hr)
  obtain ⟨u7, y, hu7, hnorm⟩ := hall (t - Cn.κ)
  obtain ⟨e0, he0⟩ := P138Complete.shifted_root ht hu7
  rw [map_mul] at he0
  -- the assembly coordinate `n = H⁴ e₀ + 3 f + (Q − 1) y + 9 τ g`
  obtain ⟨x, hxdef⟩ : ∃ x : Fin 11 → DiffRing V, x =
      ![ι Cn.j, ι Cn.C, ι Cn.z, ι Cn.h, ι r, ι Cn.v, ι Cn.w, u7, ι Cn.c,
        (4 * ι Cn.a + 3) ^ 4 * e0 + 3 * ι f +
          (((ι Cn.a + 1) * (ι Cn.a + 3)) ^ 2 * (ι r * ι Cn.c ^ 2) ^ 2 - 1) * y +
          9 * (ι Cn.τ * ι g), ι (2 * s)] := ⟨_, rfl⟩
  have hx : Matches Cn x := by subst hxdef; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hx4 : x 4 = ι r := by subst hxdef; rfl
  have hx7 : x 7 = u7 := by subst hxdef; rfl
  have hx9 : x 9 = (4 * ι Cn.a + 3) ^ 4 * e0 + 3 * ι f +
      (((ι Cn.a + 1) * (ι Cn.a + 3)) ^ 2 * (ι r * ι Cn.c ^ 2) ^ 2 - 1) * y +
      9 * (ι Cn.τ * ι g) := by
    subst hxdef; rfl
  have hx10 : x 10 = ι (2 * s) := by subst hxdef; rfl
  clear hxdef
  refine ⟨x, ?_⟩
  have eD := reg_Delta Cn hx
  have eR := reg_R Cn hx
  -- the back-end closed forms, over the native registers
  have ieq : (back (portsR (V := V)) x (kN portsR x)).I = x 4 * x 8 ^ 2 :=
    P125Value.I_eq _ _ _
  have dfeq : (back (portsR (V := V)) x (kN portsR x)).Df =
      1 + (regs (portsR (V := V)) x).Delta * (back (portsR (V := V)) x (kN portsR x)).I ^ 2 :=
    P125Value.Df_eq _ _ _
  have qeq : (back (portsR (V := V)) x (kN portsR x)).Q =
      (regs (portsR (V := V)) x).Delta ^ 2 * (back (portsR (V := V)) x (kN portsR x)).I ^ 2 :=
    P125Value.Q_eq _ _ _
  have veq : (back (portsR (V := V)) x (kN portsR x)).V =
      (back (portsR (V := V)) x (kN portsR x)).Df *
        (x 8 - (regs (portsR (V := V)) x).R +
          4 * (back (portsR (V := V)) x (kN portsR x)).I * x 7) - x 8 :=
    P125Value.V_eq _ _ _
  have dgeq : P125Value.Dg (portsR (V := V)) x (kN portsR x) =
      1 + (3 * (regs (portsR (V := V)) x).Budget - 4) * (regs (portsR (V := V)) x).Dt *
        x 10 ^ 2 :=
    P125Value.Dg_def _ _ _
  have zdeq : P125Value.zD (portsR (V := V)) x (kN portsR x) =
      x 9 * (regs (portsR (V := V)) x).S - (regs (portsR (V := V)) x).Ac :=
    P125Value.zD_def _ _ _
  -- the strong pair
  have hI : (back (portsR (V := V)) x (kN portsR x)).I = ι r * ι Cn.c ^ 2 := by
    rw [ieq, hx4, hx.x8]
  have hDf : (back (portsR (V := V)) x (kN portsR x)).Df = ι f ^ 2 := by
    rw [dfeq, eD, hI]
    linear_combination hDf0
  have hQ : (back (portsR (V := V)) x (kN portsR x)).Q =
      ((ι Cn.a + 1) * (ι Cn.a + 3)) ^ 2 * (ι r * ι Cn.c ^ 2) ^ 2 := by
    rw [qeq, eD, hI]
  have hV : (back (portsR (V := V)) x (kN portsR x)).V =
      ι f ^ 2 * (ι Cn.c - ι Cn.R + 4 * (ι r * ι Cn.c ^ 2) * u7) - ι Cn.c := by
    rw [veq, hDf, eR, hI, hx.x8, hx7]
  have hQV : ((ι Cn.a + 1) * (ι Cn.a + 3)) ^ 2 * (ι r * ι Cn.c ^ 2) ^ 2 *
      (back (portsR (V := V)) x (kN portsR x)).V ^ 2 -
        (((ι Cn.a + 1) * (ι Cn.a + 3)) ^ 2 * (ι r * ι Cn.c ^ 2) ^ 2 - 1) * y ^ 2 = 1 := by
    rw [hV]
    linear_combination hnorm
  -- the second root: `δ Cy = ((Q − 1) y)²`
  have he : (back (portsR (V := V)) x (kN portsR x)).delta *
      (back (portsR (V := V)) x (kN portsR x)).Cy =
        ((((ι Cn.a + 1) * (ι Cn.a + 3)) ^ 2 * (ι r * ι Cn.c ^ 2) ^ 2 - 1) * y) ^ 2 := by
    rw [P125Value.Cy_eq, P125Value.delta_def, hQ]
    linear_combination
      (((ι Cn.a + 1) * (ι Cn.a + 3)) ^ 2 * (ι r * ι Cn.c ^ 2) ^ 2 - 1) * hQV
  -- the third root: `Dt Dg = (τ g)²`
  have hDg : (regs (portsR (V := V)) x).Dt * P125Value.Dg (portsR (V := V)) x (kN portsR x) =
      (ι Cn.τ * ι g) ^ 2 := by
    rw [dgeq, reg_Dt Cn hx, P138Guard.reg_Budget Cn hx, hx10, h2s]
    linear_combination (-(ι Cn.τ * ι Cn.τ)) * hgg
  -- the saturated carrier
  have hS : (regs (portsR (V := V)) x).S = ι (2 * s) * ι r * (4 * ι Cn.a + 3) := by
    rw [S_eq, hx10, hx4, reg_H Cn hx]
  have hAc : (regs (portsR (V := V)) x).Ac = (4 * ι Cn.a + 3) ^ 5 * (ι (2 * s) * ι r) * e0 := by
    rw [Ac_eq, zc_eq, reg_K Cn hx, hx7, reg_H Cn hx]
    linear_combination (4 * ι Cn.a + 3) ^ 5 * he0
  have hζ : P125Value.zD (portsR (V := V)) x (kN portsR x) =
      (regs (portsR (V := V)) x).S * (3 * ι f +
        (((ι Cn.a + 1) * (ι Cn.a + 3)) ^ 2 * (ι r * ι Cn.c ^ 2) ^ 2 - 1) * y +
        9 * (ι Cn.τ * ι g)) := by
    rw [zdeq, hx9, hAc]
    linear_combination (4 * ι Cn.a + 3) ^ 4 * e0 * hS
  exact P125Value.out_of_roots portsR x (kN portsR x) _ hDf he hDg hζ

/-- **Completeness of the centered form.** An internal halt of machine 215 gives an integer zero
of the 464/119 polynomial at the six ports: the zero of `complete_direct`, with `x 9 = n`
replaced by `n − Q V`. -/
theorem complete_centered (T : V)
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :
    ∃ x : Fin 11 → DiffRing V, P125Value.valueC portsR x = 0 := by
  obtain ⟨x, hx⟩ := complete_direct T hT
  exact ⟨Function.update x 9 (x 9 - (back portsR x (kN portsR x)).shift),
    (P125Value.valueC_shift portsR x).trans hx⟩

#print axioms interp
#print axioms complete_direct
#print axioms complete_centered

end DiophantineConsistency.P125Complete
