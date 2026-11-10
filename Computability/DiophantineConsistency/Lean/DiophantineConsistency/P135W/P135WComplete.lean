import DiophantineConsistency.P135W.P135WValue
import DiophantineConsistency.P137.P137Complete
import DiophantineConsistency.ZRows.QuarticInterpolation

/-! # Completeness of package 135's 398/121 equation

From an internal halt `first (run T) = 0` of machine 215, in every model `V` of `𝗜𝚺₁`, this
module produces an integer zero `x : Fin 11 → DiffRing V` of `P135WValue.value portsR`
(`complete`):

1. the canonical record `Cn` of package 138 (`P138Canonical.canonical`), read at the weak scale
   `x 5 = (1 + 2 v_old) q²`; `P137Complete.weak_regs` identifies the front registers with the
   canonical values;
2. the guard Pell pair `s, g` (`guard`): the discriminant is package 138's `Budget − 4`, so the
   pair is that of `P138Guard.guard`, restated in the ring: `g² = 1 + (Budget − 4) τ² s²`.
   Then `P = (τ g)²`;
3. the strong pair and the interpolation (`interp`, the argument of `LCInterp.lc_interp`, stated
   over the canonical record without a point): `u, r, f` with `r (a + 2) d² = u²` and
   `1 + Δ c⁴ u² = f²`, and for every residue target `a0` modulo `s r` a value `x 7 = T` and an
   ordinate `y` with `Q V² − (Q − 1) y² = 1`. The cofactor `B = A r Dm` is linear in `r`, so the
   modulus `u (s r)` only divides `I⁴` and the quartic interpolation
   (`ZRowsQuarticInterpolation.supported_interpolation4`) is used;
4. the saturated carrier, exactly as in `P137Complete.complete`: `zc = M H (T + κ + v_old)`, a
   root of `(t² + 3)(t³ − 19)` modulo `s r` (`ZRowsIntersective19.root`) and the exact quotient
   `e₀` (`P138Complete.shifted_root`) give `Ac = S · H⁴ e₀`;
5. `x 9 = n = H⁴ e₀ + 2 u f y + τ g`, so `Z = S (2 u f y + τ g)`; with `P = (τ g)²` and
   `4 B Df Cy = δ (2 u f y)²` the norm form of the output vanishes
   (`P135WValue.value_eq_zero_of`).

No division and no three-square theorem is used. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.P135WComplete
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing P138Ports P138Canonical
open ArithmeticPellRecurrence (xcoord ycoord)
open P137Front P135WValue
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC

attribute [local irreducible] Source34Ports.betaNat Source34Ports.lowNat Source34Ports.highNat
  Source34Kernel.paramKernel Mixed121Kernel.rho coneA coneB

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The guard Pell pair -/

/-- **The guard pair.** The discriminant `Budget − 4` is package 138's, so its Pell pair serves:
there are `s, g > 0` with `g² = 1 + (Budget − 4) τ² s²`. -/
theorem guard (Cn : Canonical V) :
    ∃ s g : V, 0 < s ∧ 0 < g ∧ (ι g : DiffRing V) ^ 2 =
      1 + (P138Guard.budget Cn - 4) * (ι Cn.τ * ι Cn.τ) * ι s ^ 2 := by
  obtain ⟨Dn, s, g, _, hs, hg, hgg, hD4, _⟩ := P138Guard.guard Cn
  have h := hD4 (P138Guard.canonX Cn) (P138Guard.canonX_matches Cn)
  rw [P138Value.D4_eq, P138Guard.reg_Budget Cn (P138Guard.canonX_matches Cn)] at h
  refine ⟨s, g, hs, hg, ?_⟩
  have hgR := congrArg (ι (V := V)) hgg
  simp only [map_add, map_mul, map_one] at hgR
  rw [h]
  linear_combination hgR

/-! ## The strong pair and the interpolation -/

/-- **The quartic supported-modulus interpolation, without a point.** For `s > 0` there are
`u, r > 0` and `f` with `r (a + 2) d² = u²` and `1 + Δ c⁴ u² = f²` (`Δ = (a+1)(a+3)`), such
that every residue target `a0` modulo `s r` is hit by some `T`, with an ordinate `y` solving
the auxiliary norm `Q V² − (Q − 1) y² = 1`, `Q = Δ² c⁴ u²`,
`V = f² (c − R + 4 c² u² T) − c`. -/
theorem interp (Cn : Canonical V) (s : V) (hs : 0 < s) :
    ∃ u r f : V, 0 < u ∧ 0 < r ∧
      (ι r * (ι Cn.a + 2) * (ι Cn.d * ι Cn.d) : DiffRing V) = ι u ^ 2 ∧
      (1 + (ι Cn.a + 1) * (ι Cn.a + 3) * ι Cn.c ^ 4 * ι u ^ 2 : DiffRing V) = ι f ^ 2 ∧
      ∀ a0 : DiffRing V, ∃ T y : DiffRing V, (ι (s * r) : DiffRing V) ∣ T - a0 ∧
        ((ι Cn.a + 1) * (ι Cn.a + 3)) ^ 2 * ι Cn.c ^ 4 * ι u ^ 2 *
            (ι f ^ 2 * (ι Cn.c - ι Cn.R + 4 * ι Cn.c ^ 2 * ι u ^ 2 * T) - ι Cn.c) ^ 2 -
          (((ι Cn.a + 1) * (ι Cn.a + 3)) ^ 2 * ι Cn.c ^ 4 * ι u ^ 2 - 1) * y ^ 2 = 1 := by
  have hA : 0 < Cn.a + 2 := by simp
  have hd := P138Interp.d_pos Cn
  have hc := P138Interp.c_pos Cn
  have hN : 0 < 4 * s * ((Cn.a + 2) * Cn.d * (Cn.c * Cn.c)) :=
    mul_pos (mul_pos (by norm_num) hs) (mul_pos (mul_pos hA hd) (mul_pos hc hc))
  obtain ⟨n0, hn0, hNI, hall⟩ := ZRowsQuarticInterpolation.supported_interpolation4 Cn.a Cn.R
    (4 * s * ((Cn.a + 2) * Cn.d * (Cn.c * Cn.c))) (P138Interp.R_mod_four Cn) hN
    ⟨s * ((Cn.a + 2) * Cn.d * (Cn.c * Cn.c)), by ring⟩
  obtain ⟨m, hm⟩ := hNI
  have hIpos : 0 < ycoord n0 Cn.a :=
    lt_of_lt_of_le hn0 (ArithmeticPellRecurrence.time_le_y n0 Cn.a)
  have hm0 : 0 < m := by
    rcases (Arithmetic.zero_le m).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, mul_zero] at hm
      exact (ne_of_gt hIpos) hm
  obtain ⟨t, ht⟩ : ∃ t : V, t = 4 * s * m := ⟨_, rfl⟩
  have ht0 : 0 < t := by
    rw [ht]
    exact mul_pos (mul_pos (by norm_num) hs) hm0
  obtain ⟨u, hu⟩ : ∃ u : V, u = (Cn.a + 2) * Cn.d * t := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : V, r = (Cn.a + 2) * (t * t) := ⟨_, rfl⟩
  have hu0 : 0 < u := by
    rw [hu]
    exact mul_pos (mul_pos hA hd) ht0
  have hr0 : 0 < r := by
    rw [hr]
    exact mul_pos hA (mul_pos ht0 ht0)
  have hI : ycoord n0 Cn.a = Cn.c * Cn.c * u := by
    rw [hm, hu, ht]
    ring
  have hruV : r * (Cn.a + 2) * (Cn.d * Cn.d) = u * u := by
    rw [hr, hu]
    ring
  have hM : 0 < u * (s * r) := mul_pos hu0 (mul_pos hs hr0)
  have hMI : u * (s * r) ∣
      ycoord n0 Cn.a * ycoord n0 Cn.a * (ycoord n0 Cn.a * ycoord n0 Cn.a) :=
    ⟨(Cn.a + 2) ^ 2 * Cn.d ^ 3 * Cn.c ^ 8 * (4 * m), by rw [hI, hu, hr, ht]; ring⟩
  -- the record-side identities, transported to `DiffRing V`
  have HI := congrArg (ι (V := V)) hI
  simp only [map_mul] at HI
  have hδ : ι (ArithmeticPellRecurrence.delta Cn.a) = (ι Cn.a + 1) * (ι Cn.a + 3) := by
    unfold ArithmeticPellRecurrence.delta
    simp only [map_add, map_mul, map_one, map_ofNat]
  have Nf := congrArg (ι (V := V)) (ArithmeticPellRecurrence.norm n0 Cn.a)
  simp only [map_add, map_mul, map_one] at Nf
  rw [HI, hδ] at Nf
  have hru : ι r * (ι Cn.a + 2) * (ι Cn.d * ι Cn.d) = ι u ^ 2 := by
    have h := congrArg (ι (V := V)) hruV
    simp only [map_add, map_mul, map_ofNat] at h
    linear_combination h
  refine ⟨u, r, xcoord n0 Cn.a, hu0, hr0, hru, ?_, ?_⟩
  · linear_combination (-1 : DiffRing V) * Nf
  intro a0
  obtain ⟨Told, y, hdvd, hnorm⟩ := hall (u * (s * r)) hM hMI (ι u * a0)
  have hMsplit : (ι (u * (s * r)) : DiffRing V) = ι u * ι (s * r) := map_mul _ _ _
  rw [hMsplit] at hdvd
  have hudvd : (ι u : DiffRing V) ∣ Told := by
    have h1 : (ι u : DiffRing V) ∣ Told - ι u * a0 := dvd_trans (dvd_mul_right _ _) hdvd
    have h2 := dvd_add h1 (dvd_mul_right (ι u : DiffRing V) a0)
    rwa [sub_add_cancel] at h2
  obtain ⟨T, hT⟩ := hudvd
  have hune : (ι u : DiffRing V) ≠ 0 := by
    have hlt : (0 : DiffRing V) < ι u := by
      rw [← map_zero (ι (V := V))]
      exact ι_lt_ι.mpr hu0
    exact ne_of_gt hlt
  refine ⟨T, y, ?_, ?_⟩
  · obtain ⟨q, hq⟩ := hdvd
    refine ⟨q, ?_⟩
    have key : ι u * (T - a0 - ι (s * r) * q) = 0 := by
      rw [hT] at hq
      linear_combination hq
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h hune
    · exact sub_eq_zero.mp h
  · rw [← Cn.c_main] at hnorm
    rw [hT, HI, hδ] at hnorm
    linear_combination hnorm

/-! ## The assembly -/

/-- **Completeness.** An internal halt of machine 215 gives an integer zero of the 398/121
polynomial at the six ports. -/
theorem complete (T : V) (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :
    ∃ x : Fin 11 → DiffRing V, value portsR x = 0 := by
  obtain ⟨Cn⟩ := canonical T hT
  obtain ⟨s, g, hs, hg, hgg⟩ := guard Cn
  obtain ⟨u, r, f, hu, hr, hru, hDf0, hall⟩ := interp Cn s hs
  obtain ⟨t, ht⟩ := ZRowsIntersective19.root (s * r) (mul_pos hs hr)
  obtain ⟨u7, y, hu7, hnorm⟩ := hall (t - (Cn.κ + ι Cn.v))
  obtain ⟨e0, he0⟩ := P138Complete.shifted_root ht hu7
  rw [map_mul] at he0
  -- the scale `v = (1 + 2 v_old) q²` and the assembly coordinate `n = H⁴ e₀ + 2 u f y + τ g`
  obtain ⟨x, hxdef⟩ : ∃ x : Fin 11 → DiffRing V, x =
      ![ι Cn.j, ι Cn.C, ι Cn.z, ι Cn.h, ι r, (1 + ι Cn.v * 2) * (ι Cn.q * ι Cn.q), ι Cn.w, u7,
        ι Cn.c, (4 * ι Cn.a + 3) ^ 4 * e0 + (2 * ι u * ι f * y + ι Cn.τ * ι g), ι s] :=
    ⟨_, rfl⟩
  have hx0 : x 0 = ι Cn.j := by subst hxdef; rfl
  have hx1 : x 1 = ι Cn.C := by subst hxdef; rfl
  have hx2 : x 2 = ι Cn.z := by subst hxdef; rfl
  have hx3 : x 3 = ι Cn.h := by subst hxdef; rfl
  have hx4 : x 4 = ι r := by subst hxdef; rfl
  have hx5 : x 5 = (1 + ι Cn.v * 2) * (ι Cn.q * ι Cn.q) := by subst hxdef; rfl
  have hx6 : x 6 = ι Cn.w := by subst hxdef; rfl
  have hx7 : x 7 = u7 := by subst hxdef; rfl
  have hx8 : x 8 = ι Cn.c := by subst hxdef; rfl
  have hx9 : x 9 = (4 * ι Cn.a + 3) ^ 4 * e0 + (2 * ι u * ι f * y + ι Cn.τ * ι g) := by
    subst hxdef; rfl
  have hx10 : x 10 = ι s := by subst hxdef; rfl
  clear hxdef
  refine ⟨x, ?_⟩
  have hx := P137Complete.matches_update Cn hx0 hx1 hx2 hx3 hx6 hx8
  have hq : (front (portsR (V := V)) x).q = ι Cn.q :=
    (tr_q portsR x (ι Cn.v) (P138Value.kN portsR (Function.update x 5 (ι Cn.v)))).symm.trans
      (reg_q Cn hx)
  have hq2 : (front (portsR (V := V)) x).q2 = ι Cn.q * ι Cn.q := by rw [q2_def, hq]
  have hv : x 5 = (1 + ι Cn.v * 2) * (front (portsR (V := V)) x).q2 := by rw [hq2, hx5]
  obtain ⟨eH, eD, eA, eR, eDm, eDt, eB, eK⟩ := P137Complete.weak_regs Cn x hx hv
  have hM : (front (portsR (V := V)) x).M = ι Cn.q * ι Cn.q * 2 := by rw [M_def, hq2]
  -- the guard: `P = (τ g)²`
  have hP : (back (portsR (V := V)) x).P = (ι Cn.τ * ι g) ^ 2 := by
    rw [P_eq, Dguard_def, eDt, eB, hx10]
    linear_combination (-(ι Cn.τ * ι Cn.τ)) * hgg
  -- the strong pair
  have hB : (back (portsR (V := V)) x).B = ι u ^ 2 := by
    rw [B_eq, eA, eDm, hx4]
    linear_combination hru
  have hDf : (back (portsR (V := V)) x).Df = ι f ^ 2 := by
    rw [Df_eq, hB, eD, hx8]
    linear_combination hDf0
  have hQV : (back (portsR (V := V)) x).Q * (back (portsR (V := V)) x).V ^ 2 -
      ((back (portsR (V := V)) x).Q - 1) * y ^ 2 = 1 := by
    rw [Q_eq, V_eq, hDf, hB, eD, eR, hx7, hx8]
    linear_combination hnorm
  have hCy : (back (portsR (V := V)) x).Cy = (back (portsR (V := V)) x).delta * y ^ 2 := by
    rw [Cy_eq, delta_def]
    linear_combination hQV
  have hC : 4 * (back (portsR (V := V)) x).B * (back (portsR (V := V)) x).Df *
      (back (portsR (V := V)) x).Cy =
      (back (portsR (V := V)) x).delta * (2 * ι u * ι f * y) ^ 2 := by
    rw [hCy, hB, hDf]
    ring
  -- the saturated carrier
  have hS : (front (portsR (V := V)) x).S =
      (front (portsR (V := V)) x).M ^ 5 * ((4 * ι Cn.a + 3) * (ι r * ι s)) := by
    rw [S_eq, eH, hx4, hx10]
  have hzc : (front (portsR (V := V)) x).zc =
      (front (portsR (V := V)) x).M * (4 * ι Cn.a + 3) * (Cn.κ + ι Cn.v + u7) := by
    rw [zc_eq, eK, eH, hx7, hx5, hq2]
    linear_combination (-((4 * ι Cn.a + 3) * ι Cn.v)) * hM
  have hAc : (front (portsR (V := V)) x).Ac =
      ((front (portsR (V := V)) x).M * (4 * ι Cn.a + 3)) ^ 5 * (ι s * ι r) * e0 := by
    rw [Ac_eq, hzc, Dcar_def, eH]
    linear_combination ((front (portsR (V := V)) x).M * (4 * ι Cn.a + 3)) ^ 5 * he0
  have hZ : (front (portsR (V := V)) x).Z =
      (front (portsR (V := V)) x).S * (2 * ι u * ι f * y + ι Cn.τ * ι g) := by
    rw [Z_eq, hx9, hAc]
    linear_combination (4 * ι Cn.a + 3) ^ 4 * e0 * hS
  exact value_eq_zero_of portsR x (2 * ι u * ι f * y) (ι Cn.τ * ι g) hZ hP hC

#print axioms guard
#print axioms interp
#print axioms complete

end DiophantineConsistency.P135WComplete
