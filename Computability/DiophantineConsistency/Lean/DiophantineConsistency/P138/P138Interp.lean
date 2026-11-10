import DiophantineConsistency.P138.P138Canonical
import DiophantineConsistency.ZRows.LinearInterpolation

/-! # The supported-modulus interpolation at the canonical data (stage 6b glue)

At the canonical record `Cn : P138Canonical.Canonical V` and a guard pair `s, g` (`P138Guard.guard`,
which gives `BP = p0²` with `p0 = d τ g` at every matching point with `x 10 = s`), this module
produces the interpolation outputs of the final assembly (`P138_ROUTE.md` C8, steps 3 and 5):

* `x 4 = r` with `r > 0` and `s ∣ r`: the strong pair `I = ψ_A(n0) = A·p0·c²·r`,
  `f = χ_A(n0)`, from `ZRowsLinearInterpolation.supported_interpolation` with
  `N = 4·s·A·p0·c²` (so `r = 4·s·m`);
* for every residue target `a0` (C8 takes a root of `π(·+κ)` modulo `s·r`,
  `ZRowsIntersective19.root`), a value `x 7 = T` with `T ≡ a0 (mod s·r)` and an auxiliary
  ordinate `y` such that, at every point matching the canonical data with `x 4 = r`, `x 7 = T`,
  `x 10 = s`, the strong-pair register is a square, `Df = f²`, and the auxiliary norm
  `Q V² − (Q − 1) y² = 1` holds for the registers `Q` and `V` of `P138Value.regs`.

The modulus is `M = p0·s·r = s·I/(A c²)`, which divides `I²`; the interpolation hits
`T_old = p0·T ≡ p0·a0 (mod M)`, and `T` is the exact quotient by `p0`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.P138Interp
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing P138Value P138Ports P138Canonical ArithmeticPellRecurrence
open ZRowsLinearInterpolation

attribute [local irreducible] Source34Ports.betaNat Source34Ports.lowNat Source34Ports.highNat
  Source34Kernel.paramKernel Mixed121Kernel.rho coneA coneB

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem d_pos (Cn : Canonical V) : 0 < Cn.d := by
  rcases (Arithmetic.zero_le Cn.d).lt_or_eq with h | h
  · exact h
  · exfalso
    have hn := Cn.d_norm
    rw [← h, zero_mul] at hn
    exact absurd hn (ne_of_lt (lt_of_lt_of_le _root_.zero_lt_one le_self_add))

theorem τ_pos (Cn : Canonical V) : 0 < Cn.τ := by
  rcases (Arithmetic.zero_le Cn.τ).lt_or_eq with h | h
  · exact h
  · exfalso
    have hn := Cn.τ_norm
    rw [← h, zero_mul] at hn
    exact absurd hn (ne_of_lt (lt_of_lt_of_le _root_.zero_lt_one le_self_add))

theorem c_pos (Cn : Canonical V) : 0 < Cn.c := by
  rw [Cn.c_main]
  have hR : 0 < Cn.R := by rw [Cn.R_odd]; exact lt_of_lt_of_le _root_.zero_lt_one le_add_self
  exact lt_of_lt_of_le hR (time_le_y Cn.R Cn.a)

theorem R_mod_four (Cn : Canonical V) : Cn.R % 4 = 3 := by
  obtain ⟨m, hm⟩ := Cn.R_mod
  rw [hm, add_comm, mod_add_mul' _ _ (by norm_num : (0:V) < 4)]
  exact mod_eq_self_of_lt (by norm_num)

/-- **Stage 6b at the canonical data.** -/
theorem interp (Cn : Canonical V) (s g : V) (hs : 0 < s) (hg : 0 < g)
    (hBP : ∀ x : Fin 11 → DiffRing V, Matches Cn x → x 10 = ι s →
      (regs (portsR (V := V)) x).BP = (ι Cn.d * ι Cn.τ * ι g) ^ 2) :
    ∃ r f : V, 0 < r ∧ s ∣ r ∧ ∀ a0 : DiffRing V, ∃ T y : DiffRing V,
      (ι (s * r) : DiffRing V) ∣ T - a0 ∧
      ∀ x : Fin 11 → DiffRing V, Matches Cn x → x 4 = ι r → x 7 = T → x 10 = ι s →
        (regs (portsR (V := V)) x).Df = ι f ^ 2 ∧
        (regs (portsR (V := V)) x).Q * (regs (portsR (V := V)) x).V ^ 2 -
          ((regs (portsR (V := V)) x).Q - 1) * y ^ 2 = 1 := by
  have hp0 : 0 < Cn.d * Cn.τ * g := mul_pos (mul_pos (d_pos Cn) (τ_pos Cn)) hg
  have hc := c_pos Cn
  have hA : 0 < Cn.a + 2 := by simp
  have hN : 0 < 4 * s * ((Cn.a + 2) * (Cn.d * Cn.τ * g) * Cn.c * Cn.c) :=
    mul_pos (mul_pos (by norm_num) hs) (mul_pos (mul_pos (mul_pos hA hp0) hc) hc)
  obtain ⟨n0, hn0, hNI, hall⟩ := ZRowsLinearInterpolation.supported_interpolation Cn.a Cn.R
    (4 * s * ((Cn.a + 2) * (Cn.d * Cn.τ * g) * Cn.c * Cn.c)) (R_mod_four Cn) hN
    ⟨s * ((Cn.a + 2) * (Cn.d * Cn.τ * g) * Cn.c * Cn.c), by ring⟩
  obtain ⟨m, hm⟩ := hNI
  have hI : ycoord n0 Cn.a = (Cn.a + 2) * (Cn.d * Cn.τ * g) * Cn.c * Cn.c * (4 * s * m) := by
    rw [hm]; ring
  have hIpos : 0 < ycoord n0 Cn.a := lt_of_lt_of_le hn0 (time_le_y n0 Cn.a)
  have hm0 : 0 < m := by
    rcases (Arithmetic.zero_le m).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, mul_zero] at hm
      exact (ne_of_gt hIpos) hm
  have hr : 0 < 4 * s * m := mul_pos (mul_pos (by norm_num) hs) hm0
  refine ⟨4 * s * m, xcoord n0 Cn.a, hr, ⟨4 * m, by ring⟩, ?_⟩
  intro a0
  have hM : 0 < Cn.d * Cn.τ * g * s * (4 * s * m) := mul_pos (mul_pos hp0 hs) hr
  have hMI : Cn.d * Cn.τ * g * s * (4 * s * m) ∣ ycoord n0 Cn.a * ycoord n0 Cn.a :=
    ⟨(Cn.a + 2) * (Cn.a + 2) * (Cn.d * Cn.τ * g) * Cn.c * Cn.c * Cn.c * Cn.c * (4 * m),
      by rw [hI]; ring⟩
  obtain ⟨Told, y, hdvd, hnorm⟩ := hall _ hM hMI (ι (Cn.d * Cn.τ * g) * a0)
  -- `T_old = p0·T`
  have hMsplit : (ι (Cn.d * Cn.τ * g * s * (4 * s * m)) : DiffRing V) =
      ι (Cn.d * Cn.τ * g) * ι (s * (4 * s * m)) := by
    simp only [map_mul]; ring
  rw [hMsplit] at hdvd
  have hp0dvd : (ι (Cn.d * Cn.τ * g) : DiffRing V) ∣ Told := by
    have h1 : (ι (Cn.d * Cn.τ * g) : DiffRing V) ∣ Told - ι (Cn.d * Cn.τ * g) * a0 :=
      dvd_trans (dvd_mul_right _ _) hdvd
    have h2 := dvd_add h1 (dvd_mul_right (ι (Cn.d * Cn.τ * g) : DiffRing V) a0)
    rwa [sub_add_cancel] at h2
  obtain ⟨T, hT⟩ := hp0dvd
  have hp0ne : (ι (Cn.d * Cn.τ * g) : DiffRing V) ≠ 0 := by
    have hlt : (0 : DiffRing V) < ι (Cn.d * Cn.τ * g) := by
      rw [← map_zero (ι (V := V))]; exact ι_lt_ι.mpr hp0
    exact ne_of_gt hlt
  refine ⟨T, y, ?_, ?_⟩
  · obtain ⟨q, hq⟩ := hdvd
    refine ⟨q, ?_⟩
    have key : ι (Cn.d * Cn.τ * g) * (T - a0 - ι (s * (4 * s * m)) * q) = 0 := by
      rw [hT] at hq
      linear_combination hq
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h hp0ne
    · exact sub_eq_zero.mp h
  · intro x hx hx4 hx7 hx10
    have hBPx := hBP x hx hx10
    have eA := reg_A Cn hx
    have eD := reg_Delta Cn hx
    have eR := reg_R Cn hx
    -- ring forms of the strong pair
    have HI := congrArg (ι (V := V)) hI
    have Nf := congrArg (ι (V := V)) (norm n0 Cn.a)
    simp only [map_add, map_mul, map_ofNat, map_one] at HI Nf
    unfold delta at Nf
    simp only [map_add, map_mul, map_ofNat, map_one] at Nf
    rw [HI] at Nf
    have hDf : (regs (portsR (V := V)) x).Df = ι (xcoord n0 Cn.a) ^ 2 := by
      rw [Df_eq, U_eq, eA, eD, hBPx, hx.x8, hx4]
      simp only [map_mul, map_ofNat]
      linear_combination (-1 : DiffRing V) * Nf
    refine ⟨hDf, ?_⟩
    rw [V_eq, Q_eq, hDf, U_eq, eA, eD, eR, hBPx, hx.x8, hx7, hx4]
    rw [hT, HI] at hnorm
    unfold delta at hnorm
    rw [← Cn.c_main] at hnorm
    simp only [map_add, map_mul, map_ofNat, map_one] at hnorm ⊢
    linear_combination hnorm

#print axioms d_pos
#print axioms τ_pos
#print axioms c_pos
#print axioms R_mod_four
#print axioms interp

end DiophantineConsistency.P138Interp
