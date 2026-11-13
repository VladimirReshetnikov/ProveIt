import DiophantineConsistency.P137.P137Value
import DiophantineConsistency.P138.P138Complete

/-! # Completeness of package 137's 648/115 equation

From an internal halt `first (run T) = 0` of machine 215, in every model `V` of `𝗜𝚺₁`, this
module produces an integer zero `x : Fin 11 → DiffRing V` of `P137Value.value portsR`
(`complete`), following `PROOF.md` §6 of package 137:

1. the canonical record `Cn` of package 138 (`P138Canonical.canonical`). The weak front reads
   the scale `v` as `Y = v q`, so the new scale is `x 5 = (1 + 2 v_old) q²`; then the weak
   front at `x` is package 138's front at `Function.update x 5 v_old` (`P137Front.tr_*`), and
   every front register takes its canonical value (`weak_regs`);
2. the guard Pell pair `s, g` (`guard`): `Budget > 64`, and `3 Budget − 4` is `2` modulo `3`,
   hence not a square (`not_square_mod_three`), so neither is `4 (3 Budget − 4) τ²`; the Pell
   existence theorem gives `g² = 1 + 4 (3 Budget − 4) τ² s²`. Then `P = (τ g)²` and
   `BP = p0²` with `p0 = d τ g`;
3. the strong pair and the interpolation (`interp`, the argument of `P138Interp.interp`, stated
   without a point): `r, f > 0` with `Df = f²`, and for every residue target `a0` a value
   `x 7 = T` with `s r ∣ T − a0` and an ordinate `y` with `Q V² − (Q − 1) y² = 1`;
4. the saturated carrier: `K = H κ` and `v − q² = M v_old` give `zc = M H (T + κ + v_old)`,
   so `Ac = (M H)⁵ π(T + κ + v_old)` with `π(t) = (t² + 3)(t³ − 19)`. A root `t` of `π`
   modulo `s r` (`ZRowsIntersective19.root`) and the target `a0 = t − (κ + v_old)` give an
   exact quotient `e₀` (`P138Complete.shifted_root`), and `Ac = S · H⁴ e₀`, `S = M⁵ H r s`;
5. `x 9 = n = H⁴ e₀ + p0 f y`, so `Z = S n − Ac = S p0 f y`, and
   `P137Value.value_eq_product` gives
   `value = S² p0² f² ((Q − 1) y² − (Q V² − 1)) = 0`.

The order is that of the source: canonical data, guard, `p0`, one strong pair, the residue,
the interpolated `T` and `y`, then `n`. No division is used. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.P137Complete
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing P138Ports P138Canonical ArithmeticPellRecurrence
open ZRowsLinearInterpolation P137Front P137Value
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC

/-! ## One more transfer -/

section Generic
variable {𝔸 : Type*} [CommRing 𝔸]

/-- The projector register does not read `v`. -/
theorem tr_K (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) (v' κ : 𝔸) :
    (P138Value.regsK p (Function.update x 5 v') κ).K = (front p x).K := by
  rw [P138Value.K_eq, tr_X, upd_8, K_def]; ring

end Generic

attribute [local irreducible] Source34Ports.betaNat Source34Ports.lowNat Source34Ports.highNat
  Source34Kernel.paramKernel Mixed121Kernel.rho coneA coneB

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Squares modulo three -/

theorem three_mul_ne (A M : DiffRing V) : 3 * A ≠ 3 * M + 2 ∧ 3 * A + 1 ≠ 3 * M + 2 := by
  have key : ∀ w : DiffRing V, 3 * w ≠ 2 ∧ 3 * w ≠ 1 := by
    intro w
    rcases le_or_gt w 0 with h | h
    · exact ⟨fun e => by linarith, fun e => by linarith⟩
    · have h1 := P138Bootstrap.one_le_of_pos' h
      exact ⟨fun e => by linarith, fun e => by linarith⟩
  exact ⟨fun e => (key (A - M)).1 (by linear_combination e),
    fun e => (key (A - M)).2 (by linear_combination e)⟩

/-- No square of a number of the model is `2` modulo `3`. -/
theorem not_square_mod_three (t : V) (M : DiffRing V) : (ι t : DiffRing V) ^ 2 ≠ 3 * M + 2 := by
  have h3 : (0 : V) < 3 := by simp
  have hlt : t % 3 ≤ 2 := by
    have h : t % 3 < 2 + 1 := by rw [two_add_one_eq_three]; exact mod_lt t h3
    exact LO.FirstOrder.Arithmetic.lt_succ_iff_le.mp h
  have hd := congrArg (ι (V := V)) (div_add_mod t 3)
  simp only [map_add, map_mul, map_ofNat] at hd
  intro e
  rcases le_two_iff_eq_zero_or_one_or_two.mp hlt with h | h | h
  · rw [h, map_zero] at hd
    exact (three_mul_ne (3 * ι (t / 3) ^ 2) M).1 (by rw [← e, ← hd]; ring)
  · rw [h, map_one] at hd
    exact (three_mul_ne (3 * ι (t / 3) ^ 2 + 2 * ι (t / 3)) M).2 (by rw [← e, ← hd]; ring)
  · rw [h, map_ofNat] at hd
    exact (three_mul_ne (3 * ι (t / 3) ^ 2 + 4 * ι (t / 3) + 1) M).2 (by rw [← e, ← hd]; ring)

/-! ## The guard Pell pair -/

/-- **The guard pair.** `Budget > 64` at the canonical data, and `3 Budget − 4` is not a square,
so there are `s, g > 0` with `g² = 1 + 4 (3 Budget − 4) τ² s²`. -/
theorem guard (Cn : Canonical V) :
    ∃ s g : V, 0 < s ∧ 0 < g ∧ (ι g : DiffRing V) ^ 2 =
      1 + 4 * (3 * P138Guard.budget Cn - 4) * (ι Cn.τ * ι Cn.τ) * ι s ^ 2 := by
  have hm0 := P138Guard.canonX_matches Cn
  obtain ⟨_, h64⟩ := canonical_budget Cn hm0
  rw [P138Guard.reg_Budget Cn hm0] at h64
  obtain ⟨Dn, hDn⟩ := nonneg_iff.mp
    (show (0 : DiffRing V) ≤ 3 * P138Guard.budget Cn - 4 by linarith)
  have hDpos : 0 < Dn := ι_lt_ι.mp (by rw [map_zero, ← hDn]; linarith)
  have hτpos := P138Interp.τ_pos Cn
  have h2τ : 0 < 2 * Cn.τ := mul_pos (by norm_num) hτpos
  -- `D (2τ)²` is not a square
  have hns : ∀ t : V, t * t ≠ Dn * (2 * Cn.τ) * (2 * Cn.τ) := by
    intro t ht
    have hdvd : (2 * Cn.τ) * (2 * Cn.τ) ∣ t * t := ⟨Dn, by rw [ht]; ring⟩
    obtain ⟨t', rfl⟩ := ZRowsCoprimeSquares.dvd_of_mul_self_dvd_mul_self hdvd
    have hsq : t' * t' = Dn := by
      apply ArithmeticBinomLegendre.cancel_left (mul_pos h2τ h2τ)
      calc 2 * Cn.τ * (2 * Cn.τ) * (t' * t') = 2 * Cn.τ * t' * (2 * Cn.τ * t') := by ring
        _ = Dn * (2 * Cn.τ) * (2 * Cn.τ) := ht
        _ = 2 * Cn.τ * (2 * Cn.τ) * Dn := by ring
    have hsqR : (ι t' : DiffRing V) ^ 2 = 3 * (P138Guard.budget Cn - 2) + 2 := by
      have h := congrArg (ι (V := V)) hsq
      rw [map_mul, ← hDn] at h
      linear_combination h
    exact not_square_mod_three t' _ hsqR
  have hd0 : 0 < Dn * (2 * Cn.τ) * (2 * Cn.τ) := mul_pos (mul_pos hDpos h2τ) h2τ
  obtain ⟨g, s, hs, hg⟩ := ModelPellExistence.exists_pos (Dn * (2 * Cn.τ) * (2 * Cn.τ)) hd0 hns
  have hgpos : 0 < g := by
    rcases (Arithmetic.zero_le g).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, zero_mul] at hg
      exact absurd hg (ne_of_lt (lt_of_lt_of_le _root_.zero_lt_one le_add_self))
  refine ⟨s, g, hs, hgpos, ?_⟩
  have hgR := congrArg (ι (V := V)) hg
  simp only [map_add, map_mul, map_one, map_ofNat] at hgR
  rw [hDn]
  linear_combination hgR

/-! ## The strong pair and the interpolation -/

/-- **The supported-modulus interpolation, without a point.** For `s, p0 > 0` there are
`r, f > 0` such that, with `Δ = (a+1)(a+3)` and `U = (a+2) r c²`,
`1 + Δ U² p0² = f²`, and every residue target `a0` modulo `s r` is hit by some `T`, with an
ordinate `y` solving the auxiliary norm `Q V² − (Q − 1) y² = 1`, `Q = Δ² U² p0²`,
`V = f² (c − R + 4 U p0² T) − c`. -/
theorem interp (Cn : Canonical V) (s p0 : V) (hs : 0 < s) (hp0 : 0 < p0) :
    ∃ r f : V, 0 < r ∧
      (1 + (ι Cn.a + 1) * (ι Cn.a + 3) * ((ι Cn.a + 2) * (ι r * ι Cn.c ^ 2)) ^ 2 * ι p0 ^ 2 :
        DiffRing V) = ι f ^ 2 ∧
      ∀ a0 : DiffRing V, ∃ T y : DiffRing V,
        (ι (s * r) : DiffRing V) ∣ T - a0 ∧
        ((ι Cn.a + 1) * (ι Cn.a + 3)) ^ 2 * ((ι Cn.a + 2) * (ι r * ι Cn.c ^ 2)) ^ 2 * ι p0 ^ 2 *
            (ι f ^ 2 * (ι Cn.c - ι Cn.R +
              4 * ((ι Cn.a + 2) * (ι r * ι Cn.c ^ 2)) * ι p0 ^ 2 * T) - ι Cn.c) ^ 2 -
          (((ι Cn.a + 1) * (ι Cn.a + 3)) ^ 2 * ((ι Cn.a + 2) * (ι r * ι Cn.c ^ 2)) ^ 2 *
            ι p0 ^ 2 - 1) * y ^ 2 = 1 := by
  have hc := P138Interp.c_pos Cn
  have hA : 0 < Cn.a + 2 := by simp
  have hN : 0 < 4 * s * ((Cn.a + 2) * p0 * Cn.c * Cn.c) :=
    mul_pos (mul_pos (by norm_num) hs) (mul_pos (mul_pos (mul_pos hA hp0) hc) hc)
  obtain ⟨n0, hn0, hNI, hall⟩ := ZRowsLinearInterpolation.supported_interpolation Cn.a Cn.R
    (4 * s * ((Cn.a + 2) * p0 * Cn.c * Cn.c)) (P138Interp.R_mod_four Cn) hN
    ⟨s * ((Cn.a + 2) * p0 * Cn.c * Cn.c), by ring⟩
  obtain ⟨m, hm⟩ := hNI
  have hI : ycoord n0 Cn.a = (Cn.a + 2) * p0 * Cn.c * Cn.c * (4 * s * m) := by
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
  have hM : 0 < p0 * s * (4 * s * m) := mul_pos (mul_pos hp0 hs) hr
  have hMI : p0 * s * (4 * s * m) ∣ ycoord n0 Cn.a * ycoord n0 Cn.a :=
    ⟨(Cn.a + 2) * (Cn.a + 2) * p0 * Cn.c * Cn.c * Cn.c * Cn.c * (4 * m), by rw [hI]; ring⟩
  obtain ⟨Told, y, hdvd, hnorm⟩ := hall _ hM hMI (ι p0 * a0)
  -- `T_old = p0·T`
  have hMsplit : (ι (p0 * s * (4 * s * m)) : DiffRing V) = ι p0 * ι (s * (4 * s * m)) := by
    simp only [map_mul]; ring
  rw [hMsplit] at hdvd
  have hp0dvd : (ι p0 : DiffRing V) ∣ Told := by
    have h1 : (ι p0 : DiffRing V) ∣ Told - ι p0 * a0 := dvd_trans (dvd_mul_right _ _) hdvd
    have h2 := dvd_add h1 (dvd_mul_right (ι p0 : DiffRing V) a0)
    rwa [sub_add_cancel] at h2
  obtain ⟨T, hT⟩ := hp0dvd
  have hp0ne : (ι p0 : DiffRing V) ≠ 0 := by
    have hlt : (0 : DiffRing V) < ι p0 := by
      rw [← map_zero (ι (V := V))]; exact ι_lt_ι.mpr hp0
    exact ne_of_gt hlt
  refine ⟨T, y, ?_, ?_⟩
  · obtain ⟨q, hq⟩ := hdvd
    refine ⟨q, ?_⟩
    have key : ι p0 * (T - a0 - ι (s * (4 * s * m)) * q) = 0 := by
      rw [hT] at hq
      linear_combination hq
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h hp0ne
    · exact sub_eq_zero.mp h
  · rw [hT, HI] at hnorm
    unfold delta at hnorm
    rw [← Cn.c_main] at hnorm
    simp only [map_add, map_mul, map_ofNat, map_one] at hnorm ⊢
    linear_combination hnorm

/-! ## The weak front at the canonical data -/

/-- A point with the six canonical coordinates other than the scale matches the record once the
scale is replaced by the canonical one. -/
theorem matches_update (Cn : Canonical V) {x : Fin 11 → DiffRing V}
    (h0 : x 0 = ι Cn.j) (h1 : x 1 = ι Cn.C) (h2 : x 2 = ι Cn.z) (h3 : x 3 = ι Cn.h)
    (h6 : x 6 = ι Cn.w) (h8 : x 8 = ι Cn.c) :
    Matches Cn (Function.update x 5 (ι Cn.v)) :=
  ⟨(Function.update_of_ne (by decide) _ _).trans h0,
    (Function.update_of_ne (by decide) _ _).trans h1,
    (Function.update_of_ne (by decide) _ _).trans h2,
    (Function.update_of_ne (by decide) _ _).trans h3,
    Function.update_self _ _ _,
    (Function.update_of_ne (by decide) _ _).trans h6,
    (Function.update_of_ne (by decide) _ _).trans h8⟩

/-- **The weak front takes the canonical values** at the scale `v = (1 + 2 v_old) q²`. -/
theorem weak_regs (Cn : Canonical V) (x : Fin 11 → DiffRing V)
    (hx : Matches Cn (Function.update x 5 (ι Cn.v)))
    (hv : x 5 = (1 + ι Cn.v * 2) * (front (portsR (V := V)) x).q2) :
    (front (portsR (V := V)) x).H = 4 * ι Cn.a + 3 ∧
    (front (portsR (V := V)) x).Delta = (ι Cn.a + 1) * (ι Cn.a + 3) ∧
    (front (portsR (V := V)) x).A = ι Cn.a + 2 ∧
    (front (portsR (V := V)) x).R = ι Cn.R ∧
    (front (portsR (V := V)) x).Dm = ι Cn.d * ι Cn.d ∧
    (front (portsR (V := V)) x).Dt = ι Cn.τ * ι Cn.τ ∧
    (front (portsR (V := V)) x).Budget = P138Guard.budget Cn ∧
    (front (portsR (V := V)) x).K = (4 * ι Cn.a + 3) * Cn.κ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (tr_H portsR x (ι Cn.v) hv _).symm.trans (reg_H Cn hx)
  · exact (tr_Delta portsR x (ι Cn.v) hv _).symm.trans (reg_Delta Cn hx)
  · exact (tr_A portsR x (ι Cn.v) hv _).symm.trans (reg_A Cn hx)
  · exact (tr_R portsR x (ι Cn.v) _).symm.trans (reg_R Cn hx)
  · exact (tr_Dm portsR x (ι Cn.v) hv _).symm.trans (reg_Dm Cn hx)
  · exact (tr_Dt portsR x (ι Cn.v) hv).symm.trans (reg_Dt Cn hx)
  · exact (tr_Budget portsR x (ι Cn.v) hv).symm.trans (P138Guard.reg_Budget Cn hx)
  · have h := (tr_K portsR x (ι Cn.v) _).symm.trans (reg_K Cn hx)
    rw [reg_H Cn hx] at h
    exact h

/-! ## The assembly -/

/-- **Completeness.** An internal halt of machine 215 gives an integer zero of the 648/115
polynomial at the six ports. -/
theorem complete (T : V) (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :
    ∃ x : Fin 11 → DiffRing V, value portsR x = 0 := by
  obtain ⟨Cn⟩ := canonical T hT
  obtain ⟨s, g, hs, hg, hgg⟩ := guard Cn
  have hp0 : 0 < Cn.d * Cn.τ * g :=
    mul_pos (mul_pos (P138Interp.d_pos Cn) (P138Interp.τ_pos Cn)) hg
  obtain ⟨r, f, hr, hDf0, hall⟩ := interp Cn s (Cn.d * Cn.τ * g) hs hp0
  obtain ⟨t, ht⟩ := ZRowsIntersective19.root (s * r) (mul_pos hs hr)
  obtain ⟨u7, y, hu7, hnorm⟩ := hall (t - (Cn.κ + ι Cn.v))
  obtain ⟨e0, he0⟩ := P138Complete.shifted_root ht hu7
  have ep0 : (ι (Cn.d * Cn.τ * g) : DiffRing V) = ι Cn.d * ι Cn.τ * ι g := by
    simp only [map_mul]
  rw [map_mul] at he0
  rw [ep0] at hDf0 hnorm
  -- the scale `v = (1 + 2 v_old) q²` and the assembly coordinate `n = H⁴ e₀ + p0 f y`
  obtain ⟨x, hxdef⟩ : ∃ x : Fin 11 → DiffRing V, x =
      ![ι Cn.j, ι Cn.C, ι Cn.z, ι Cn.h, ι r, (1 + ι Cn.v * 2) * (ι Cn.q * ι Cn.q), ι Cn.w, u7,
        ι Cn.c, (4 * ι Cn.a + 3) ^ 4 * e0 + (ι Cn.d * ι Cn.τ * ι g) * ι f * y, ι s] := ⟨_, rfl⟩
  have hx0 : x 0 = ι Cn.j := by subst hxdef; rfl
  have hx1 : x 1 = ι Cn.C := by subst hxdef; rfl
  have hx2 : x 2 = ι Cn.z := by subst hxdef; rfl
  have hx3 : x 3 = ι Cn.h := by subst hxdef; rfl
  have hx4 : x 4 = ι r := by subst hxdef; rfl
  have hx5 : x 5 = (1 + ι Cn.v * 2) * (ι Cn.q * ι Cn.q) := by subst hxdef; rfl
  have hx6 : x 6 = ι Cn.w := by subst hxdef; rfl
  have hx7 : x 7 = u7 := by subst hxdef; rfl
  have hx8 : x 8 = ι Cn.c := by subst hxdef; rfl
  have hx9 : x 9 = (4 * ι Cn.a + 3) ^ 4 * e0 + (ι Cn.d * ι Cn.τ * ι g) * ι f * y := by
    subst hxdef; rfl
  have hx10 : x 10 = ι s := by subst hxdef; rfl
  clear hxdef
  refine ⟨x, ?_⟩
  have hx := matches_update Cn hx0 hx1 hx2 hx3 hx6 hx8
  have hq : (front (portsR (V := V)) x).q = ι Cn.q :=
    (tr_q portsR x (ι Cn.v) (P138Value.kN portsR (Function.update x 5 (ι Cn.v)))).symm.trans
      (reg_q Cn hx)
  have hq2 : (front (portsR (V := V)) x).q2 = ι Cn.q * ι Cn.q := by rw [q2_def, hq]
  have hv : x 5 = (1 + ι Cn.v * 2) * (front (portsR (V := V)) x).q2 := by rw [hq2, hx5]
  obtain ⟨eH, eD, eA, eR, eDm, eDt, eB, eK⟩ := weak_regs Cn x hx hv
  have hM : (front (portsR (V := V)) x).M = ι Cn.q * ι Cn.q * 2 := by rw [M_def, hq2]
  -- the guard: `P = (τ g)²`, `BP = (d τ g)²`
  have hP : (back (portsR (V := V)) x).P = (ι Cn.τ * ι g) ^ 2 := by
    rw [P_eq, D4_eq, eDt, eB, hx10]
    linear_combination (-(ι Cn.τ * ι Cn.τ)) * hgg
  have hBP : (back (portsR (V := V)) x).BP = (ι Cn.d * ι Cn.τ * ι g) ^ 2 := by
    rw [BP_def, hP, eDm]; ring
  -- the strong pair
  have hU : (back (portsR (V := V)) x).U = (ι Cn.a + 2) * (ι r * ι Cn.c ^ 2) := by
    rw [U_eq, eA, hx4, hx8]
  have hDf : (back (portsR (V := V)) x).Df = ι f ^ 2 := by
    rw [Df_eq, eD, hU, hBP]
    linear_combination hDf0
  have hQV : (back (portsR (V := V)) x).Q * (back (portsR (V := V)) x).V ^ 2 -
      ((back (portsR (V := V)) x).Q - 1) * y ^ 2 = 1 := by
    rw [Q_eq, V_eq, hDf, eD, eR, hU, hBP, hx7, hx8]
    linear_combination hnorm
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
      (front (portsR (V := V)) x).S * ((ι Cn.d * ι Cn.τ * ι g) * ι f * y) := by
    rw [Z_eq, hx9, hAc]
    linear_combination (4 * ι Cn.a + 3) ^ 4 * e0 * hS
  rw [value_eq_product, hZ, hBP, hDf]
  linear_combination
    (-((front (portsR (V := V)) x).S ^ 2 * (ι Cn.d * ι Cn.τ * ι g) ^ 2 * ι f ^ 2)) * hQV

#print axioms tr_K
#print axioms not_square_mod_three
#print axioms guard
#print axioms interp
#print axioms weak_regs
#print axioms complete

end DiophantineConsistency.P137Complete
