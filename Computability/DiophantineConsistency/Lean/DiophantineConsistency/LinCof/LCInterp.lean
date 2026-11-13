import DiophantineConsistency.LinCof.LCCanonical
import DiophantineConsistency.ZRows.QuarticInterpolation

/-! # The strong pair of the linear-cofactor circuit

With `I = y_{n0}(a)`, `f = x_{n0}(a)` (`f² = 1 + Δ I²`, `Δ = (a+1)(a+3)`), the circuit needs

    B = r·A·Dm = u²,   Df = 1 + Δ c⁴ B = f²,   Q = Δ² c⁴ B = (Δ I)²,   Cy = Q V² − 1 = (Q − 1) y²

at a matching point with `x 4 = r`, `x 7 = T`.  As `Dm = d²` and `A = a + 2`, take

    I = c²·u,   u = A·d·t,   r = A·t²,   t = 4·s·m     (so `N = 4·s·A·d·c² ∣ I`, `I = N·m`).

Then `A·U = c²·B = c²u²`, so `V = f²(c − R + 4·I·(u·T)) − c`: the interpolation variable of
`ZRowsQuarticInterpolation.supported_interpolation4` is `u·T`.  To make `T` hit a prescribed
residue `a0` modulo `s·r` the interpolation is asked for `u·a0` modulo `M = u·(s·r)`, which is
admissible because `M ∣ I⁴` (`I⁴ = M · A²d³c⁸·4m`); `ι u` is then cancelled.

Differences from `P138Interp.interp`: the cofactor is linear (`B = r·A·Dm`, not `BP·r²`-like), so
`r` must carry the factor `A` and the modulus `u·s·r` is only a divisor of `I⁴` (138: of `I`),
hence the quartic interpolation; and the guard's `p0 = d τ g` no longer enters the strong pair.
Nothing here depends on the slots, on the weight `wt`, or on `x 10`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.LCInterp
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing P138Ports LCValue LCCanonical
open P138Canonical (Canonical)
open ArithmeticPellRecurrence (xcoord ycoord)

attribute [local irreducible] Source34Ports.betaNat Source34Ports.lowNat Source34Ports.highNat
  Source34Kernel.paramKernel Mixed121Kernel.rho coneA coneB

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The strong pair.  For the guard ordinate `s > 0` there are `u, r > 0` and `f` such that
every residue `a0` modulo `s·r` is attained by some `T` for which, at every matching point with
`x 4 = r` and `x 7 = T` (any slots), `B = u²`, `Df = f²` and `Cy = δ·y²`. -/
theorem lc_interp (Cn : Canonical V) (s : V) (hs : 0 < s) :
    ∃ u r f : V, 0 < u ∧ 0 < r ∧
      ∀ a0 : DiffRing V, ∃ T y : DiffRing V, (ι (s * r) : DiffRing V) ∣ T - a0 ∧
        ∀ (x : Fin 11 → DiffRing V) (κ ω Λ ψ wt : DiffRing V), LCMatches Cn x → x 4 = ι r →
          x 7 = T →
          (regsK (portsR (V := V)) x κ ω Λ ψ wt).B = ι u ^ 2 ∧
          (regsK (portsR (V := V)) x κ ω Λ ψ wt).Df = ι f ^ 2 ∧
          (regsK (portsR (V := V)) x κ ω Λ ψ wt).Cy =
            (regsK (portsR (V := V)) x κ ω Λ ψ wt).delta * y ^ 2 := by
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
  refine ⟨u, r, xcoord n0 Cn.a, hu0, hr0, ?_⟩
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
  · intro x κ ω Λ ψ wt hx hx4 hx7
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
    rw [← Cn.c_main] at hnorm
    rw [hT, HI, hδ] at hnorm
    -- the registers
    have hB : (regsK (portsR (V := V)) x κ ω Λ ψ wt).B = ι u ^ 2 := by
      rw [B_eq, lc_A Cn hx κ ω Λ ψ wt, lc_Dm Cn hx κ ω Λ ψ wt, hx4]
      linear_combination hru
    have hΔ := lc_Delta Cn hx κ ω Λ ψ wt
    have hDf : (regsK (portsR (V := V)) x κ ω Λ ψ wt).Df = ι (xcoord n0 Cn.a) ^ 2 := by
      rw [Df_eq, hB, hΔ, hx.x8]
      linear_combination (-1 : DiffRing V) * Nf
    have hV : (regsK (portsR (V := V)) x κ ω Λ ψ wt).V =
        ι (xcoord n0 Cn.a) ^ 2 *
          (ι Cn.c - ι Cn.R + 4 * (ι Cn.c * ι Cn.c * ι u) * (ι u * T)) - ι Cn.c := by
      rw [V_eq, hDf, U_eq, lc_A Cn hx κ ω Λ ψ wt, lc_Dm Cn hx κ ω Λ ψ wt,
        lc_R Cn hx κ ω Λ ψ wt, hx.x8, hx7, hx4]
      linear_combination (ι (xcoord n0 Cn.a) ^ 2 * (4 * ι Cn.c ^ 2 * T)) * hru
    have hQ : (regsK (portsR (V := V)) x κ ω Λ ψ wt).Q =
        ((ι Cn.a + 1) * (ι Cn.a + 3) * (ι Cn.c * ι Cn.c * ι u)) ^ 2 := by
      rw [Q_eq, hB, hΔ, hx.x8]
      ring
    have hCy : (regsK (portsR (V := V)) x κ ω Λ ψ wt).Cy =
        (regsK (portsR (V := V)) x κ ω Λ ψ wt).delta * y ^ 2 := by
      rw [Cy_eq, delta_eq, hQ, hV]
      linear_combination hnorm
    exact ⟨hB, hDf, hCy⟩

#print axioms lc_interp

end DiophantineConsistency.LCInterp
