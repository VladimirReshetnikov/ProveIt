import DiophantineConsistency.P113.P113Canonical
import DiophantineConsistency.P113.P113Roots
import DiophantineConsistency.P138.P138Complete

/-! # Completeness of package 113's twelve-integer equation

From an internal halt `first (run T) = 0` of machine 215, in every model `V` of `𝗜𝚺₁`, this module
produces an integer zero `x : Fin 12 → DiffRing V` of `P113Value.value portsR` (`complete`),
following `PROOF.md` §6 of package 113 (`integer12_saturated`). The front is package 138's with
the native index (`kk_eq`), so package 138's canonical record is reused, with the strict cones of
`P113Canonical.canonical_strict`. The witness order is the source's:

1. the canonical record `Cn`, fixing `x 0, x 1, x 2, x 3, x 5, x 6, x 8`;
2. **the strict guards**: `G > 0` from the cones `q ≤ 2 Uc, Uc < q`, `q ≤ 2 Vc, Vc < q`
   (`guard_pos`), and `η ζ > 0`;
3. **the joint positivity witness** `t = x 10` with `Pair = G η ζ − (t² − G − η ζ + 1)² > 0`
   (`joint_positivity`: the nearest square to `G + η ζ − 1`);
4. **the guard Pell pair** `s = x 11 > 0`, `g` with `(3 Pair − 4) s² + 1 = g²` (`guard_pell`:
   `s = 1, g = 0` at `Pair = 1`, otherwise `3 Pair − 4 ≡ 2 (mod 3)` is not a square and
   `ModelPellExistence.exists_pos` applies);
5. **the strong pair and the interpolation** (`interp`): with `N = 4 s τ c²`, the supported-modulus
   interpolation fixes `I = ψ_a(n₀) = τ U`, `U = s r c²` (`x 4 = r`), `f = χ_a(n₀)`, so
   `Df = 1 + Δ U² E = 1 + Δ I² = f²` (`E = τ²`); every residue target `a₀` modulo `U` is hit by
   `T = x 7` through the old auxiliary coordinate `T_old = τ T` (requested modulo `τ U ∣ I²`);
6. a root of `π(t) = (t² + 3)(t³ − 19)` modulo `U` (`ZRowsIntersective19.root`), target
   `a₀ = t − κ` with `K = H κ` (`K_val`), so `Ac = H⁵ π(κ + T) = S e₀`, `S = U H⁵`;
7. `x 9 = n = e₀ + y + 3 τ f + 9 g − V`, with `V` in closed form, so
   `Z = S (n + V) − Ac = S (y + 3 τ f + 9 g)`; the three roots `S δ y`, `3 δ S τ f`, `9 δ S g`
   of `δ fc`, `δ fa`, `δ fb` sum to `δ Z`, so `δ⁴ value = 0` (`P113Value.value_scale`) and
   `δ ≠ 0` (`P113Roots.delta_ne`).

No division is used: `e₀` and `T` are quotients of proved divisibilities in `DiffRing V`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.P113Complete
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing P138Ports P138Canonical ArithmeticPellRecurrence
open ZRowsLinearInterpolation P113Front
open P138EarlyFold (ι_tsub' pos_of_ι)
open P138Bootstrap (one_le_of_pos')
open ModelArithmetic (ι_pos)
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC

attribute [local irreducible] Source34Ports.betaNat Source34Ports.lowNat Source34Ports.highNat
  Source34Kernel.paramKernel Mixed121Kernel.rho coneA coneB

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Arithmetic -/

theorem natural {A : DiffRing V} (h : 0 < A) : ∃ a : V, 0 < a ∧ A = ι a := by
  obtain ⟨a, ha⟩ := nonneg_iff.mp h.le
  exact ⟨a, pos_of_ι (by rw [← ha]; exact h), ha⟩

/-- **The guard from the cones**: `q ≤ 2A, A < q, q ≤ 2B, B < q ⇒ AB > (q − A − B)²`. -/
theorem guard_pos {A B Q : DiffRing V} (h1 : Q ≤ 2 * A) (h2 : A < Q) (h3 : Q ≤ 2 * B)
    (h4 : B < Q) : 0 < A * B - (Q - A - B) ^ 2 := by
  have hQ : 0 < Q := by linarith
  nlinarith [mul_pos hQ (sub_pos.mpr h2), mul_nonneg (sub_nonneg.mpr h1) (sub_pos.mpr h4).le,
    mul_nonneg (sub_nonneg.mpr h1) (sub_pos.mpr h2).le,
    mul_nonneg (sub_nonneg.mpr h3) (sub_pos.mpr h4).le]

/-- **Joint positivity.** For `G, M > 0` some `t` has `G M − (t² − G − M + 1)² > 0`: take the
nearest square to `N = G + M − 1`; its error `e` satisfies `e ≤ √N`, and `N ≤ G M`. -/
theorem joint_positivity (G M : DiffRing V) (hG : 0 < G) (hM : 0 < M) :
    ∃ t : DiffRing V, 0 < G * M - (t * t - G - M + 1) ^ 2 := by
  have hG1 : 1 ≤ G := one_le_of_pos' hG
  have hM1 : 1 ≤ M := one_le_of_pos' hM
  have hNM : G + M - 1 ≤ G * M := by nlinarith [mul_nonneg (sub_nonneg.mpr hG1) (sub_nonneg.mpr hM1)]
  have hGM : 0 < G * M := mul_pos hG hM
  obtain ⟨n, hn⟩ : ∃ n : V, G + M - 1 = ι n := nonneg_iff.mp (by linarith)
  set a : V := √n with ha
  have hs1 : a * a ≤ n := sqrt_spec_le n
  have hs2 : n < (a + 1) * (a + 1) := sqrt_spec_lt n
  have h1 : ι a * ι a ≤ (ι n : DiffRing V) := by rw [← map_mul]; exact ι_le_ι.mpr hs1
  have h2 : (ι n : DiffRing V) + 1 ≤ (ι a + 1) * (ι a + 1) := by
    have := ι_le_ι.mpr (lt_iff_succ_le.mp hs2)
    simpa only [map_add, map_mul, map_one] using this
  have ha0 : (0 : DiffRing V) ≤ ι a := ι_nonneg a
  by_cases hc : n ≤ a * a + a
  · -- `t = a`, error `e = n − a² ≤ a`
    have hc' : (ι n : DiffRing V) ≤ ι a * ι a + ι a := by
      have := ι_le_ι.mpr hc; simpa only [map_add, map_mul] using this
    refine ⟨ι a, ?_⟩
    rw [show ι a * ι a - G - M + 1 = -(ι n - ι a * ι a) by rw [← hn]; ring, neg_sq]
    rcases eq_or_lt_of_le (sub_nonneg.mpr h1) with he | he
    · rw [← he]; simpa using hGM
    · have hle : (ι n - ι a * ι a) ^ 2 ≤ ι a * ι a := by
        rw [sq]
        exact mul_le_mul (by linarith) (by linarith) he.le ha0
      nlinarith
  · -- `t = a + 1`, error `e = (a + 1)² − n ≤ a`, and `a² < n`
    have hc' : ι a * ι a + ι a + 1 ≤ (ι n : DiffRing V) := by
      have := ι_le_ι.mpr (lt_iff_succ_le.mp (not_le.mp hc))
      simpa only [map_add, map_mul, map_one] using this
    refine ⟨ι a + 1, ?_⟩
    rw [show (ι a + 1) * (ι a + 1) - G - M + 1 = (ι a + 1) * (ι a + 1) - ι n by rw [← hn]; ring]
    have he0 : 0 ≤ (ι a + 1) * (ι a + 1) - ι n := by linarith
    have hle : ((ι a + 1) * (ι a + 1) - ι n) ^ 2 ≤ ι a * ι a := by
      rw [sq]
      exact mul_le_mul (by linarith) (by linarith) he0 ha0
    nlinarith

/-- No square is `2` modulo `3`: `u² ≠ 3P − 4`. -/
theorem not_square_three (P u : DiffRing V) : u * u ≠ 3 * P - 4 := by
  intro h
  obtain ⟨t, ht | ht | ht⟩ := P113Roots.mod3' u
  · exact (P125Roots.three_mul (3 * t ^ 2 - P + 1)).2 (by rw [ht] at h; linear_combination h)
  · exact (P125Roots.three_mul (3 * t ^ 2 + 2 * t - P + 2)).1 (by rw [ht] at h; linear_combination h)
  · exact (P125Roots.three_mul (3 * t ^ 2 + 4 * t - P + 3)).1 (by rw [ht] at h; linear_combination h)

/-- **The guard Pell pair**: for `Pair > 0`, some `s > 0`, `g` have `(3 Pair − 4) s² + 1 = g²`. -/
theorem guard_pell (P : DiffRing V) (hP : 0 < P) :
    ∃ s g : V, 0 < s ∧ (3 * P - 4) * (ι s * ι s) + 1 = ι g * ι g := by
  obtain ⟨p, hp0, rfl⟩ := natural hP
  rcases eq_or_lt_of_le (pos_iff_one_le.mp hp0) with h1 | h2
  · refine ⟨1, 0, by norm_num, ?_⟩
    rw [← h1]; simp only [map_one, map_zero]; norm_num
  · have hp2 : (2 : V) ≤ p := by
      have h : (1 : V) + 1 ≤ p := lt_iff_succ_le.mp h2
      rwa [one_add_one_eq_two] at h
    have hp4 : (4 : V) ≤ 3 * p := calc
      (4 : V) ≤ 3 * 2 := by norm_num
      _ ≤ 3 * p := mul_le_mul_of_nonneg_left hp2 (by norm_num)
    have hd : (ι (3 * p - 4) : DiffRing V) = 3 * ι p - 4 := by
      rw [P138EarlyFold.ι_tsub' hp4, map_mul, map_ofNat, map_ofNat]
    have hd0 : 0 < 3 * p - 4 := by
      apply pos_of_ι
      rw [hd]
      have := ι_le_ι.mpr hp2; rw [map_ofNat] at this; linarith
    have hns : ∀ s : V, s * s ≠ 3 * p - 4 := by
      intro s hs
      apply not_square_three (ι p) (ι s)
      rw [← map_mul, hs, hd]
    obtain ⟨x, y, hy, hxy⟩ := ModelPellExistence.exists_pos (3 * p - 4) hd0 hns
    refine ⟨y, x, hy, ?_⟩
    have := congrArg (ι (V := V)) hxy
    simp only [map_mul, map_add, map_one] at this
    rw [hd] at this
    linear_combination -this

/-! ## The registers at the canonical point -/

section Registers
variable {𝔸 : Type*} [CommRing 𝔸] (p : Fin 6 → 𝔸) (x : Fin 12 → 𝔸)

/-- 113's native index is package 138's native index of the front. -/
theorem kk_eq : kk p x = P138Value.kN p (front x) := by
  unfold P138Value.kN
  rw [show (P138Value.regsK p (front x) 0).R = (P138Value.regsK p (front x) (kk p x)).R from rfl,
    show (P138Value.regsK p (front x) 0).E = (P138Value.regsK p (front x) (kk p x)).E from rfl,
    P138Value.E_def, ← R_eq, ← X_eq, ← Y_eq, front_3]
  unfold kk
  rw [P113Value.k_def]; ring

end Registers

theorem front_regs (x : Fin 12 → DiffRing V) :
    P138Value.regsK (portsR (V := V)) (front x) (kk portsR x) = P138Value.regs portsR (front x) := by
  rw [kk_eq]

section Canonical
variable (Cn : Canonical V) {x : Fin 12 → DiffRing V} (hx : Matches Cn (front x))
local notation "𝓠" => P113Value.regs (portsR (V := V)) x
include hx

theorem q_val : (𝓠).q = ι Cn.q := by rw [q_eq, front_regs x]; exact reg_q Cn hx
theorem F_val : (𝓠).F = ι Cn.F := by rw [F_eq, front_regs x]; exact reg_F Cn hx
theorem X_val : (𝓠).X = ι Cn.X := by rw [X_eq, front_regs x]; exact reg_X Cn hx
theorem a_val : (𝓠).a = ι Cn.a := by rw [a_eq, front_regs x]; exact reg_a Cn hx
theorem H_val : (𝓠).H = 4 * ι Cn.a + 3 := by rw [H_eq, front_regs x]; exact reg_H Cn hx
theorem Delta_val : (𝓠).Delta = (ι Cn.a + 1) * (ι Cn.a + 3) := by
  rw [Delta_eq, front_regs x]; exact reg_Delta Cn hx
theorem R_val : (𝓠).R = ι Cn.R := by rw [R_eq, front_regs x]; exact reg_R Cn hx
theorem k_val : (𝓠).k = ι Cn.k := by rw [← k_eq, front_regs x]; exact reg_k Cn hx
theorem eta_val : (𝓠).eta = ι Cn.η := by rw [eta_eq, front_regs x]; exact reg_eta Cn hx
theorem zeta_val : (𝓠).zeta = ι Cn.ζ := by
  rw [P113Value.zeta_def, k_val Cn hx, eta_val Cn hx, Cn.k_split, map_add]; ring
theorem E_val : (𝓠).E = ι Cn.τ * ι Cn.τ := by
  rw [← Dt_eq, front_regs x]; exact reg_Dt Cn hx
theorem x1_val : x 1 = ι Cn.C := hx.x1
theorem x8_val : x 8 = ι Cn.c := hx.x8

/-- `K = H κ` with `κ = c² − γ (d + X + a c)`, from `d = X + a c + γ H`, `d² = 1 + Δ c²`. -/
theorem K_val : (𝓠).K = (4 * ι Cn.a + 3) *
    (ι Cn.c ^ 2 - ι Cn.γ * (ι Cn.d + ι Cn.X + ι Cn.a * ι Cn.c)) := by
  have hd1 : ι Cn.d = ι Cn.X + ι Cn.a * ι Cn.c + ι Cn.γ * (4 * ι Cn.a + 3) := by
    rw [Cn.d_split]; simp only [map_add, map_mul, map_ofNat]
  have hd2 := congrArg (ι (V := V)) Cn.d_norm
  simp only [map_add, map_mul, map_one, map_ofNat] at hd2
  rw [P113Value.K_def, X_val Cn hx, a_val Cn hx, x8_val Cn hx]
  linear_combination hd2 - (ι Cn.d + ι Cn.X + ι Cn.a * ι Cn.c) * hd1

/-- The guard determinant at the canonical point. -/
theorem G_val : (𝓠).G = (portsR 4 * ι Cn.F) * (portsR 5 * ι Cn.C) -
    (ι Cn.q - portsR 4 * ι Cn.F - portsR 5 * ι Cn.C) ^ 2 := by
  rw [P113Value.G_def, F_val Cn hx, q_val Cn hx, x1_val Cn hx]

end Canonical

/-- **`G > 0` at the canonical data with the strict cones.** -/
theorem canonical_G_pos (Cn : Canonical V) (hF : Exp.exp 1113 * Cn.F < Cn.q)
    (hC : Cn.C * Exp.exp 666104 < Cn.q) :
    0 < (portsR 4 * ι Cn.F) * (portsR 5 * ι Cn.C) -
      (ι Cn.q - portsR 4 * ι Cn.F - portsR 5 * ι Cn.C) ^ 2 := by
  have hU1 : ι Cn.q ≤ 2 * (portsR 4 * ι Cn.F) := by
    rw [p4_exp, ← map_mul, show (2 : DiffRing V) = ι 2 by rw [map_ofNat], ← map_mul]
    exact ι_le_ι.mpr Cn.cone_F.1
  have hU2 : portsR 4 * ι Cn.F < ι Cn.q := by
    rw [p4_exp, ← map_mul]; exact ι_lt_ι.mpr hF
  have hV1 : ι Cn.q ≤ 2 * (portsR 5 * ι Cn.C) := by
    rw [p5_exp, ← map_mul, show (2 : DiffRing V) = ι 2 by rw [map_ofNat], ← map_mul,
      mul_comm (Exp.exp _)]
    exact ι_le_ι.mpr Cn.cone_C.1
  have hV2 : portsR 5 * ι Cn.C < ι Cn.q := by
    rw [p5_exp, ← map_mul, mul_comm (Exp.exp _)]; exact ι_lt_ι.mpr hC
  exact guard_pos hU1 hU2 hV1 hV2

/-! ## The strong pair and the interpolation -/

/-- **The interpolation with `E = τ²` folded into the strong register.** For `s > 0` there are
`r, f > 0` such that, with `U = s r c²` and `I = τ U`, `1 + Δ U² τ² = f²`, and every residue target
`a0` modulo `U` is hit by some `T`, with an ordinate `y` solving
`Q V² − (Q − 1) y² = 1`, `Q = Δ² U² τ²`, `V = f² (c − R + 4 U τ² T) − c`. -/
theorem interp (Cn : Canonical V) (s : V) (hs : 0 < s) :
    ∃ r f : V, 0 < r ∧
      (1 + (ι Cn.a + 1) * (ι Cn.a + 3) * ((ι s * ι r * (ι Cn.c * ι Cn.c)) *
        (ι s * ι r * (ι Cn.c * ι Cn.c))) * (ι Cn.τ * ι Cn.τ) : DiffRing V) = ι f * ι f ∧
      ∀ a0 : DiffRing V, ∃ T y : DiffRing V,
        (ι (s * r * (Cn.c * Cn.c)) : DiffRing V) ∣ T - a0 ∧
        (ι Cn.a + 1) * (ι Cn.a + 3) * ((ι Cn.a + 1) * (ι Cn.a + 3)) *
            ((ι s * ι r * (ι Cn.c * ι Cn.c)) * (ι s * ι r * (ι Cn.c * ι Cn.c))) *
            (ι Cn.τ * ι Cn.τ) *
            ((ι f * ι f * (ι Cn.c - ι Cn.R + 4 * (ι s * ι r * (ι Cn.c * ι Cn.c)) *
              (ι Cn.τ * ι Cn.τ) * T) - ι Cn.c) *
             (ι f * ι f * (ι Cn.c - ι Cn.R + 4 * (ι s * ι r * (ι Cn.c * ι Cn.c)) *
              (ι Cn.τ * ι Cn.τ) * T) - ι Cn.c)) -
          ((ι Cn.a + 1) * (ι Cn.a + 3) * ((ι Cn.a + 1) * (ι Cn.a + 3)) *
            ((ι s * ι r * (ι Cn.c * ι Cn.c)) * (ι s * ι r * (ι Cn.c * ι Cn.c))) *
            (ι Cn.τ * ι Cn.τ) - 1) * (y * y) = 1 := by
  have hc := P138Interp.c_pos Cn
  have hτ := P138Interp.τ_pos Cn
  have hN : 0 < 4 * s * (Cn.τ * (Cn.c * Cn.c)) :=
    mul_pos (mul_pos (by norm_num) hs) (mul_pos hτ (mul_pos hc hc))
  obtain ⟨n0, hn0, hNI, hall⟩ := ZRowsLinearInterpolation.supported_interpolation Cn.a Cn.R
    (4 * s * (Cn.τ * (Cn.c * Cn.c))) (P138Interp.R_mod_four Cn) hN
    ⟨s * (Cn.τ * (Cn.c * Cn.c)), by ring⟩
  obtain ⟨m, hm⟩ := hNI
  have hIpos : 0 < ycoord n0 Cn.a := lt_of_lt_of_le hn0 (time_le_y n0 Cn.a)
  have hm0 : 0 < m := by
    rcases (Arithmetic.zero_le m).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, mul_zero] at hm
      exact (ne_of_gt hIpos) hm
  set r : V := 4 * m with hrdef
  have hr : 0 < r := mul_pos (by norm_num) hm0
  set U : V := s * r * (Cn.c * Cn.c) with hUdef
  have hI : ycoord n0 Cn.a = Cn.τ * U := by rw [hm, hUdef, hrdef]; ring
  have hU0 : 0 < U := mul_pos (mul_pos hs hr) (mul_pos hc hc)
  -- ring forms of the strong pair
  have HI := congrArg (ι (V := V)) hI
  have Nf := congrArg (ι (V := V)) (norm n0 Cn.a)
  simp only [map_add, map_mul, map_one] at HI Nf
  unfold delta at Nf
  simp only [map_add, map_mul, map_ofNat, map_one] at Nf
  rw [HI] at Nf
  have hUι : (ι U : DiffRing V) = ι s * ι r * (ι Cn.c * ι Cn.c) := by
    rw [hUdef]; simp only [map_mul]
  refine ⟨r, xcoord n0 Cn.a, hr, ?_, ?_⟩
  · rw [← hUι]
    linear_combination (-1 : DiffRing V) * Nf
  intro a0
  -- request `T_old ≡ τ a0 (mod τ U)`, `τ U ∣ I²`
  have hM : 0 < Cn.τ * U := mul_pos hτ hU0
  have hMI : Cn.τ * U ∣ ycoord n0 Cn.a * ycoord n0 Cn.a := ⟨Cn.τ * U, by rw [hI]⟩
  obtain ⟨Told, y, hdvd, hnorm⟩ := hall _ hM hMI (ι Cn.τ * a0)
  have hMsplit : (ι (Cn.τ * U) : DiffRing V) = ι Cn.τ * ι U := map_mul _ _ _
  rw [hMsplit] at hdvd
  have hτdvd : (ι Cn.τ : DiffRing V) ∣ Told := by
    have h1 : (ι Cn.τ : DiffRing V) ∣ Told - ι Cn.τ * a0 := dvd_trans (dvd_mul_right _ _) hdvd
    have h2 := dvd_add h1 (dvd_mul_right (ι Cn.τ : DiffRing V) a0)
    rwa [sub_add_cancel] at h2
  obtain ⟨T, hT⟩ := hτdvd
  have hτne : (ι Cn.τ : DiffRing V) ≠ 0 := ne_of_gt (ι_pos hτ)
  refine ⟨T, y, ?_, ?_⟩
  · obtain ⟨w, hw⟩ := hdvd
    refine ⟨w, ?_⟩
    have key : ι Cn.τ * (T - a0 - ι U * w) = 0 := by
      rw [hT] at hw
      linear_combination hw
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h hτne
    · exact sub_eq_zero.mp h
  · rw [hT, HI] at hnorm
    unfold delta at hnorm
    rw [← Cn.c_main] at hnorm
    simp only [map_add, map_mul, map_ofNat, map_one] at hnorm
    rw [← hUι]
    linear_combination hnorm

/-! ## The assembly -/

/-- **Completeness.** An internal halt of machine 215 gives an integer zero of package 113's
polynomial at the six ports. -/
theorem complete (T : V) (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :
    ∃ x : Fin 12 → DiffRing V, P113Value.value portsR x = 0 := by
  obtain ⟨Cn, hFc, hCc⟩ := P113Canonical.canonical_strict T hT
  -- the strict guards and the joint positivity witness
  set G0 : DiffRing V := (portsR 4 * ι Cn.F) * (portsR 5 * ι Cn.C) -
    (ι Cn.q - portsR 4 * ι Cn.F - portsR 5 * ι Cn.C) ^ 2 with hG0
  have hG : 0 < G0 := canonical_G_pos Cn hFc hCc
  have hM : 0 < (ι Cn.η : DiffRing V) * ι Cn.ζ := mul_pos (ι_pos Cn.η_pos) (ι_pos Cn.ζ_pos)
  obtain ⟨t, ht⟩ := joint_positivity G0 (ι Cn.η * ι Cn.ζ) hG hM
  -- the guard Pell pair
  obtain ⟨s, g, hs, hsg⟩ := guard_pell _ ht
  -- the strong pair and the interpolation
  obtain ⟨r, f, hr, hDf0, hall⟩ := interp Cn s hs
  have hU0 : 0 < s * r * (Cn.c * Cn.c) :=
    mul_pos (mul_pos hs hr) (mul_pos (P138Interp.c_pos Cn) (P138Interp.c_pos Cn))
  set κ0 : DiffRing V := ι Cn.c ^ 2 - ι Cn.γ * (ι Cn.d + ι Cn.X + ι Cn.a * ι Cn.c) with hκ0
  obtain ⟨t0, ht0⟩ := ZRowsIntersective19.root (s * r * (Cn.c * Cn.c)) hU0
  obtain ⟨u7, y, hu7, hnorm⟩ := hall (t0 - κ0)
  obtain ⟨e0, he0⟩ := P138Complete.shifted_root ht0 hu7
  simp only [map_mul] at he0
  -- the closed forms
  set Uc : DiffRing V := ι s * ι r * (ι Cn.c * ι Cn.c) with hUc
  set Vc : DiffRing V := ι f * ι f * (ι Cn.c - ι Cn.R + 4 * Uc * (ι Cn.τ * ι Cn.τ) * u7) -
    ι Cn.c with hVc
  -- the assembly coordinate `n = e₀ + y + 3 τ f + 9 g − V`
  obtain ⟨x, hxdef⟩ : ∃ x : Fin 12 → DiffRing V, x =
      ![ι Cn.j, ι Cn.C, ι Cn.z, ι Cn.h, ι r, ι Cn.v, ι Cn.w, u7, ι Cn.c,
        e0 + y + 3 * (ι Cn.τ * ι f) + 9 * ι g - Vc, t, ι s] := ⟨_, rfl⟩
  have hx : Matches Cn (front x) := by subst hxdef; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hx4 : x 4 = ι r := by subst hxdef; rfl
  have hx7 : x 7 = u7 := by subst hxdef; rfl
  have hx8 : x 8 = ι Cn.c := by subst hxdef; rfl
  have hx9 : x 9 = e0 + y + 3 * (ι Cn.τ * ι f) + 9 * ι g - Vc := by subst hxdef; rfl
  have hx10 : x 10 = t := by subst hxdef; rfl
  have hx11 : x 11 = ι s := by subst hxdef; rfl
  clear hxdef
  refine ⟨x, ?_⟩
  have eD := Delta_val Cn hx
  have eR := R_val Cn hx
  have eE := E_val Cn hx
  have eH := H_val Cn hx
  have eK := K_val Cn hx
  -- the strong pair
  have hU : (P113Value.regs portsR x).U = Uc := by rw [P113Value.U_def, hx11, hx4, hx8, ← hUc]
  have hDf : (P113Value.regs portsR x).Df = ι f * ι f := by
    rw [P113Value.Df_def, eD, hU, eE]; exact hDf0
  have hQ : (P113Value.regs portsR x).Q = (ι Cn.a + 1) * (ι Cn.a + 3) *
      ((ι Cn.a + 1) * (ι Cn.a + 3)) * (Uc * Uc) * (ι Cn.τ * ι Cn.τ) := by
    rw [P113Value.Q_def, eD, hU, eE]
  have hV : (P113Value.regs portsR x).V = Vc := by
    rw [P113Value.V_def, P113Value.b_def, hDf, eR, hU, eE, hx8, hx7, ← hVc]
  -- the first root: `δ Cy = (δ y)²`
  have hCy : (P113Value.regs portsR x).delta * (P113Value.regs portsR x).Cy =
      ((P113Value.regs portsR x).delta * y) ^ 2 := by
    rw [P113Value.Cy_def, P113Value.delta_def, hV, hQ]
    linear_combination ((ι Cn.a + 1) * (ι Cn.a + 3) * ((ι Cn.a + 1) * (ι Cn.a + 3)) *
      (Uc * Uc) * (ι Cn.τ * ι Cn.τ) - 1) * hnorm
  -- the second root: `E Df = (τ f)²`
  have hEDf : (P113Value.regs portsR x).E * (P113Value.regs portsR x).Df =
      (ι Cn.τ * ι f) ^ 2 := by rw [eE, hDf]; ring
  -- the third root: the guard
  have hPair : (P113Value.regs portsR x).Pair = G0 * (ι Cn.η * ι Cn.ζ) -
      (t * t - G0 - ι Cn.η * ι Cn.ζ + 1) ^ 2 := by
    rw [P113Value.Pair_def, G_val Cn hx, ← hG0, eta_val Cn hx, zeta_val Cn hx, hx10]; ring
  have hDg : (3 * (P113Value.regs portsR x).Pair - 4) * (x 11 * x 11) + 1 = ι g * ι g := by
    rw [hPair, hx11]; exact hsg
  -- the saturated carrier
  have hS : (P113Value.regs portsR x).S = Uc * (4 * ι Cn.a + 3) ^ 5 := by
    rw [P113Value.S_def, hU, eH]
  have hAc : (P113Value.regs portsR x).Ac = Uc * (4 * ι Cn.a + 3) ^ 5 * e0 := by
    rw [P113Value.Ac_def, P113Value.zc_def, eK, hx7, eH]
    rw [← hκ0]
    linear_combination (4 * ι Cn.a + 3) ^ 5 * he0
  have hZ : (P113Value.regs portsR x).Z = (P113Value.regs portsR x).S *
      (y + 3 * (ι Cn.τ * ι f) + 9 * ι g) := by
    rw [P113Value.Z_def, hx9, hV, hAc, hS]; ring
  -- the scaled three-root norm vanishes
  have hδ := P113Roots.delta_ne portsR x portFacts
  have hnorm3 : ZRowsThreeRoot.norm3 ((P113Value.regs portsR x).delta * (P113Value.regs portsR x).Z)
      ((P113Value.regs portsR x).delta * (P113Value.regs portsR x).fc)
      ((P113Value.regs portsR x).delta * (P113Value.regs portsR x).fa)
      ((P113Value.regs portsR x).delta * (P113Value.regs portsR x).fb) = 0 := by
    refine ZRowsThreeRoot.norm3_of_roots
      (α := (P113Value.regs portsR x).S * ((P113Value.regs portsR x).delta * y))
      (β := 3 * (P113Value.regs portsR x).delta * (P113Value.regs portsR x).S *
        (ι Cn.τ * ι f))
      (γ := 9 * (P113Value.regs portsR x).delta * (P113Value.regs portsR x).S * ι g) ?_ ?_ ?_ ?_
    · rw [P113Roots.rad_x, hCy]; ring
    · rw [P113Roots.rad_y, hEDf]; ring
    · rw [P113Roots.rad_z, hDg]; ring
    · rw [hZ]; ring
  have h4 := P113Value.value_scale (portsR (V := V)) x
  rw [hnorm3] at h4
  exact (mul_eq_zero.mp h4).resolve_left (pow_ne_zero 4 hδ)

#print axioms guard_pos
#print axioms joint_positivity
#print axioms guard_pell
#print axioms kk_eq
#print axioms K_val
#print axioms interp
#print axioms complete

end DiophantineConsistency.P113Complete
