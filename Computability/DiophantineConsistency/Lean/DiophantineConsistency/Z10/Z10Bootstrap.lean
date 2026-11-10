import DiophantineConsistency.Z10.Z10Regs
import DiophantineConsistency.P138.P138Bootstrap

/-! # Unconditional residues of the ten-integer registers, and what cannot vanish

Package 106, integer lane (`66_TEN_INTEGER_PROOF.md` §1 and §3; steps S1 and S2 of the route).
Everything here holds at every signed assignment `x : Fin 10 → ·` and for every port tuple: no
zero of the equation is assumed before `Sigma_ne`, and no port fact is used at all.

**Residues** (any commutative ring `𝔸`; divisibility is that of `𝔸`).

* The scale: `radix = 4^1067470`, so `3 ∣ radix − 1` and `2 ∣ radix`.
* The prefix at a base `b ≡ 1 (mod 3)`: `Bc`, `N0`, `NN` are `1`, the weight word is
  `31 ≡ 1`, the target word is `22 ≡ 1`, hence `mask ≡ 0`, `Tc ≡ 0` and `3 ∣ Xc`
  (`Xc = (NN − 1)(Sc + 1) + NN · Tc`). Also `b ∣ Bc, N0, NN, Yc, cap` and, when `b ∣ g`,
  `b ∣ Sc` and `b ∣ Xc + 1`.
* The registers: `b = 6t + 4` is even and `≡ 1 (mod 3)`; `X` is odd, `3 ∣ X`, `b ∣ X + 1`,
  `b ∣ Y`; `B1 ≡ 3 (mod 4)`; `2b ∣ U, A`; `3 ∣ A, Phalf, K`; `b ∣ K`; `Q ≡ 1 (mod b²)` and
  `(mod 3)`; `C ≡ −1 (mod 6)`; `3 ∣ D`; `r ≡ 1`, `a0 ≡ 1`, `a1 ≡ 0 (mod 3)`; `S` is odd.

**Non-vanishing** (the ring of differences `DiffRing V` of a model `V` of `𝗜𝚺₁`).

* `b_ne`, `X_ne`, `S_ne`: `b`, `X`, `S` are not zero; `a0_ne_a1`: the two radicands differ
  (they differ modulo three).
* `cubic_ne`, `Theta_ne`: `rho³ − rho S² − S³` is odd because `S` is, and `rho² + 23 S² > 0`; so
  the intersective quintic `Theta` does not vanish.
* `Sigma_ne`, `xi_ne`, `z_x_ne`: at a zero of the polar value the support modulus
  `Sigma = xi S⁵` is not zero (at `Sigma = 0` the norm is `Theta⁴`), hence `z ≠ 0` and `x ≠ 0`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Z10Bootstrap
open Nine121 Nine121.N105Layout Z10Regs

/-! ## The radix scale -/

/-- A residue `1` is kept by powers. -/
theorem dvd_pow_sub_one {𝔸 : Type*} [CommRing 𝔸] {d u : 𝔸} (h : d ∣ u - 1) (n : ℕ) :
    d ∣ u ^ n - 1 := by
  induction n with
  | zero => rw [pow_zero, sub_self]; exact dvd_zero d
  | succ n ih =>
    have e : u ^ (n + 1) - 1 = (u ^ n - 1) * u + (u - 1) := by ring
    rw [e]; exact dvd_add (ih.mul_right _) h

theorem three_dvd_four_pow_sub_one (n : ℕ) : (3 : ℤ) ∣ 4 ^ n - 1 :=
  dvd_pow_sub_one ⟨1, by norm_num⟩ n

theorem radix_eq : radix = 4 ^ 1067470 := by
  have h : (2134940 : ℕ) = 2 * 1067470 := by norm_num
  have h4 : (2 : ℤ) ^ 2 = 4 := by norm_num
  unfold radix
  rw [h, pow_mul, h4]

theorem radix_mod3 : (3 : ℤ) ∣ radix - 1 := by
  rw [radix_eq]; exact three_dvd_four_pow_sub_one _

theorem radix_even : (2 : ℤ) ∣ radix := by
  unfold radix; exact dvd_pow_self 2 (by norm_num)

section Generic
variable {𝔸 : Type*} [CommRing 𝔸]

theorem radix_cast_mod3 : (3 : 𝔸) ∣ (radix : 𝔸) - 1 := by
  obtain ⟨c, hc⟩ := radix_mod3
  have h := congrArg (Int.cast : ℤ → 𝔸) hc
  push_cast at h
  exact ⟨(c : 𝔸), h⟩

theorem radix_cast_even : (2 : 𝔸) ∣ (radix : 𝔸) := by
  obtain ⟨c, hc⟩ := radix_even
  have h := congrArg (Int.cast : ℤ → 𝔸) hc
  push_cast at h
  exact ⟨(c : 𝔸), h⟩

/-- A sum of `n` terms of residue `1` has residue `n`. -/
theorem sum_sub_card {n : ℕ} (f : Fin n → 𝔸) {d : 𝔸} (h : ∀ i, d ∣ f i - 1) :
    d ∣ (∑ i, f i) - (n : 𝔸) := by
  have e : (∑ i, f i) - (n : 𝔸) = ∑ i, (f i - 1) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one]
  rw [e]; exact Finset.dvd_sum fun i _ => h i

/-! ## The prefix at a base `b ≡ 1 (mod 3)` -/

section Prefix
variable (p : Fin 4 → 𝔸) (b g : 𝔸)

theorem Bc_mod3 (hb : (3 : 𝔸) ∣ b - 1) : (3 : 𝔸) ∣ Bc b - 1 := by
  have e : Bc b - 1 = ((radix : 𝔸) - 1) * (b * b) + (b - 1) * (b + 1) := by unfold Bc; ring
  rw [e]; exact dvd_add (radix_cast_mod3.mul_right _) (hb.mul_right _)

theorem N0_mod3 (hb : (3 : 𝔸) ∣ b - 1) : (3 : 𝔸) ∣ N0 b - 1 :=
  dvd_pow_sub_one (Bc_mod3 b hb) 117

theorem NN_mod3 (hb : (3 : 𝔸) ∣ b - 1) : (3 : 𝔸) ∣ NN b - 1 :=
  dvd_pow_sub_one (Bc_mod3 b hb) 1986

/-- The weight word has `31 ≡ 1 (mod 3)` terms. -/
theorem ell_mod3 (hb : (3 : 𝔸) ∣ b - 1) : (3 : 𝔸) ∣ ell b - 1 := by
  have h : (3 : 𝔸) ∣ ell b - ((31 : ℕ) : 𝔸) :=
    sum_sub_card (fun i => Bc b ^ weights i) fun i => dvd_pow_sub_one (Bc_mod3 b hb) (weights i)
  have e : ell b - 1 = ell b - ((31 : ℕ) : 𝔸) + 3 * 10 := by push_cast; ring
  rw [e]; exact dvd_add h (dvd_mul_right _ _)

/-- The target word has `22 ≡ 1 (mod 3)` terms. -/
theorem AT_mod3 (hb : (3 : 𝔸) ∣ b - 1) : (3 : 𝔸) ∣ AT b - 1 := by
  have h : (3 : 𝔸) ∣ AT b - ((22 : ℕ) : 𝔸) :=
    sum_sub_card (fun k => Bc b ^ targets k) fun k => dvd_pow_sub_one (Bc_mod3 b hb) (targets k)
  have e : AT b - 1 = AT b - ((22 : ℕ) : 𝔸) + 3 * 7 := by push_cast; ring
  rw [e]; exact dvd_add h (dvd_mul_right _ _)

theorem mask_mod3 (hb : (3 : 𝔸) ∣ b - 1) : (3 : 𝔸) ∣ mask b := by
  unfold mask; exact dvd_sub (N0_mod3 b hb) (hb.mul_left _)

theorem Tc_mod3 (hb : (3 : 𝔸) ∣ b - 1) : (3 : 𝔸) ∣ Tc b := by
  have e : Tc b = mask b + (N0 b - 1) * (AT b * (Bc b - 2)) + (AT b - 1) * (Bc b - 2) +
      (Bc b - 1) - 3 := by unfold Tc; ring
  rw [e]
  exact dvd_sub (dvd_add (dvd_add (dvd_add (mask_mod3 b hb) ((N0_mod3 b hb).mul_right _))
    ((AT_mod3 b hb).mul_right _)) (Bc_mod3 b hb)) (dvd_refl 3)

/-- **`3 ∣ X`**: `X = (NN − 1)(Sc + 1) + NN · Tc`. -/
theorem Xc_mod3 (hb : (3 : 𝔸) ∣ b - 1) : (3 : 𝔸) ∣ Xc p b g := by
  have e : Xc p b g = (NN b - 1) * (Sc p b g + 1) + NN b * Tc b := by unfold Xc; ring
  rw [e]; exact dvd_add ((NN_mod3 b hb).mul_right _) ((Tc_mod3 b hb).mul_left _)

theorem b_dvd_Bc : b ∣ Bc b := ⟨(radix : 𝔸) * b, by unfold Bc; ring⟩

theorem bb_dvd_Bc : b * b ∣ Bc b := ⟨(radix : 𝔸), by unfold Bc; ring⟩

theorem two_dvd_Bc : (2 : 𝔸) ∣ Bc b := by
  unfold Bc; exact radix_cast_even.mul_right _

theorem b_dvd_N0 : b ∣ N0 b := (b_dvd_Bc b).trans (dvd_pow_self _ (by norm_num))

theorem b_dvd_NN : b ∣ NN b := (b_dvd_Bc b).trans (dvd_pow_self _ (by norm_num))

theorem b_dvd_Sc (hg : b ∣ g) : b ∣ Sc p b g := by
  unfold Sc; exact dvd_add hg ((b_dvd_N0 b).mul_right _)

/-- **`b ∣ X + 1`** when `b ∣ g`. -/
theorem b_dvd_Xc_succ (hg : b ∣ g) : b ∣ Xc p b g + 1 := by
  have e : Xc p b g + 1 = NN b * (Sc p b g + Tc b + 1) - Sc p b g := by unfold Xc; ring
  rw [e]; exact dvd_sub ((b_dvd_NN b).mul_right _) (b_dvd_Sc p b g hg)

theorem b_dvd_Yc : b ∣ Yc b := Dvd.intro _ rfl

theorem b_dvd_capc : b ∣ cap b := Dvd.intro _ rfl

end Prefix

/-! ## The registers -/

section Regs
variable (p : Fin 4 → 𝔸) (x : Fin 10 → 𝔸)
local notation "𝓡" => regs p x

theorem b_even : (2 : 𝔸) ∣ (𝓡).b := ⟨3 * x 0 + 2, by rw [b_def]; ring⟩

theorem b_mod3 : (3 : 𝔸) ∣ (𝓡).b - 1 := ⟨2 * x 0 + 1, by rw [b_def]; ring⟩

theorem b_dvd_g : (𝓡).b ∣ (𝓡).g := ⟨x 1, g_def p x⟩

theorem b_dvd_k2 : (𝓡).b ∣ (𝓡).k2 := ⟨6 * x 3 + 4, k2_def p x⟩

theorem k2_mod3 : (3 : 𝔸) ∣ (𝓡).k2 - 1 := by
  have e : (𝓡).k2 - 1 = ((𝓡).b - 1) * (6 * x 3 + 4) + 3 * (2 * x 3 + 1) := by
    rw [k2_def]; ring
  rw [e]; exact dvd_add ((b_mod3 p x).mul_right _) (dvd_mul_right _ _)

theorem X_mod3 : (3 : 𝔸) ∣ (𝓡).X := by
  rw [X_def]; exact Xc_mod3 p _ _ (b_mod3 p x)

theorem b_dvd_X1 : (𝓡).b ∣ (𝓡).X + 1 := by
  rw [X_def]; exact b_dvd_Xc_succ p _ _ (b_dvd_g p x)

theorem X_odd : (2 : 𝔸) ∣ (𝓡).X + 1 := (b_even p x).trans (b_dvd_X1 p x)

theorem b_dvd_Y : (𝓡).b ∣ (𝓡).Y := by
  rw [Y_def]; exact b_dvd_Yc _

theorem b_dvd_cap : (𝓡).b ∣ (𝓡).cap := by
  rw [cap_def]; exact b_dvd_capc _

/-- `B1 = 2X + 1 ≡ 3 (mod 4)`. -/
theorem B1_mod4 : (4 : 𝔸) ∣ (𝓡).B1 + 1 := by
  obtain ⟨c, hc⟩ := X_odd p x
  exact ⟨c, by rw [B1_def]; linear_combination 2 * hc⟩

theorem U_eq : (𝓡).U = 2 * x 4 * (𝓡).Y * (𝓡).X := by
  rw [U_def, halfU_def, L_def]; ring

theorem halfA_eq : (𝓡).halfA = (𝓡).halfU * (1 + (𝓡).V) := by
  rw [halfA_def, uv_def]; ring

theorem A_eq : (𝓡).A = (𝓡).U * (1 + (𝓡).V) := by
  rw [A_def, halfA_eq, U_def]; ring

theorem X_dvd_halfU : (𝓡).X ∣ (𝓡).halfU := ⟨(𝓡).L, by rw [halfU_def]; ring⟩

theorem Y_dvd_halfU : (𝓡).Y ∣ (𝓡).halfU := ⟨x 4 * (𝓡).X, by rw [halfU_def, L_def]; ring⟩

theorem U_dvd_A : (𝓡).U ∣ (𝓡).A := ⟨_, A_eq p x⟩

theorem two_b_dvd_U : 2 * (𝓡).b ∣ (𝓡).U := by
  rw [U_def]; exact mul_dvd_mul_left 2 ((b_dvd_Y p x).trans (Y_dvd_halfU p x))

theorem two_b_dvd_A : 2 * (𝓡).b ∣ (𝓡).A := (two_b_dvd_U p x).trans (U_dvd_A p x)

theorem three_dvd_U : (3 : 𝔸) ∣ (𝓡).U := by
  rw [U_def]; exact ((X_mod3 p x).trans (X_dvd_halfU p x)).mul_left 2

theorem three_dvd_A : (3 : 𝔸) ∣ (𝓡).A := (three_dvd_U p x).trans (U_dvd_A p x)

theorem three_dvd_Phalf : (3 : 𝔸) ∣ (𝓡).Phalf := by
  rw [Phalf_def]; exact (three_dvd_U p x).mul_right _

theorem b_dvd_K : (𝓡).b ∣ (𝓡).K := by
  rw [K_def]; exact dvd_add (b_dvd_X1 p x) ((b_dvd_k2 p x).mul_right _)

theorem three_dvd_K : (3 : 𝔸) ∣ (𝓡).K := by
  have e : (𝓡).K = (𝓡).X + ((𝓡).k2 - 1) * ((𝓡).Phalf - 1) + (𝓡).Phalf := by
    rw [K_def]; ring
  rw [e]
  exact dvd_add (dvd_add (X_mod3 p x) ((k2_mod3 p x).mul_right _)) (three_dvd_Phalf p x)

/-- `Q ≡ 1 (mod b²)`. -/
theorem Q_mod_bb : (𝓡).b * (𝓡).b ∣ (𝓡).Q - 1 := by
  obtain ⟨c, hc⟩ := b_dvd_K p x
  exact ⟨((𝓡).Phalf * (𝓡).Phalf - 1) * (c * c), by rw [Q_def, hc]; ring⟩

theorem Q_mod3 : (3 : 𝔸) ∣ (𝓡).Q - 1 := by
  have e : (𝓡).Q - 1 = (𝓡).K * (((𝓡).Phalf * (𝓡).Phalf - 1) * (𝓡).K) := by
    rw [Q_def]; ring
  rw [e]; exact (three_dvd_K p x).mul_right _

theorem C_mod3 : (3 : 𝔸) ∣ (𝓡).C + 1 := ⟨2 * x 2, by rw [C_def]; ring⟩

theorem C_odd : (2 : 𝔸) ∣ (𝓡).C + 1 := ⟨3 * x 2, by rw [C_def]; ring⟩

theorem D_mod3 : (3 : 𝔸) ∣ (𝓡).D := by
  have e : (𝓡).D = (𝓡).A * ((𝓡).A * ((𝓡).C * (𝓡).C)) - ((𝓡).C + 1) * (4 * ((𝓡).C - 1)) := by
    rw [D_def]; ring
  rw [e]; exact dvd_sub ((three_dvd_A p x).mul_right _) ((C_mod3 p x).mul_right _)

theorem r_mod3 : (3 : 𝔸) ∣ (𝓡).r - 1 := by
  have e : (𝓡).r - 1 = ((𝓡).b - 1) * (𝓡).Q + ((𝓡).Q - 1) := by rw [r_def]; ring
  rw [e]; exact dvd_add ((b_mod3 p x).mul_right _) (Q_mod3 p x)

theorem a0_mod3 : (3 : 𝔸) ∣ (𝓡).a0 - 1 := by
  have e : (𝓡).a0 - 1 = ((𝓡).r - 1) + 3 * ((3 * (𝓡).Delta - 1) * ((𝓡).r * x 8) ^ 2) := by
    rw [a0_def]; ring
  rw [e]; exact dvd_add (r_mod3 p x) (dvd_mul_right _ _)

theorem a1_mod3 : (3 : 𝔸) ∣ (𝓡).a1 := by
  rw [a1_def]; exact ((D_mod3 p x).mul_right _).mul_right _

theorem S_odd : (2 : 𝔸) ∣ (𝓡).S + 1 := ⟨(𝓡).A - 2, by rw [S_def]; ring⟩

end Regs

end Generic

/-! ## What cannot vanish -/

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing
open P138Bootstrap (one_le_of_pos' odd_ne_zero' even_or_odd')

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem three_not_dvd_one : ¬ (3 : DiffRing V) ∣ 1 := by
  rintro ⟨c, hc⟩
  rcases le_or_gt c 0 with h | h
  · linarith
  · have := one_le_of_pos' h; linarith

/-- An odd element is not zero. -/
theorem ne_of_two_dvd_succ {u : DiffRing V} (h : (2 : DiffRing V) ∣ u + 1) : u ≠ 0 := by
  obtain ⟨c, hc⟩ := h
  intro h0
  rw [h0] at hc
  exact odd_ne_zero' (c - 1) (by linear_combination -hc)

section RegsV
variable (p : Fin 4 → DiffRing V) (x : Fin 10 → DiffRing V)
local notation "𝓡" => regs p x

theorem b_ne : (𝓡).b ≠ 0 := by
  intro h
  have h3 := b_mod3 p x
  rw [h, _root_.zero_sub] at h3
  exact three_not_dvd_one (dvd_neg.mp h3)

theorem X_ne : (𝓡).X ≠ 0 := ne_of_two_dvd_succ (X_odd p x)

theorem S_ne : (𝓡).S ≠ 0 := ne_of_two_dvd_succ (S_odd p x)

/-- **The two radicands differ**: `a0 ≡ 1`, `a1 ≡ 0 (mod 3)`. -/
theorem a0_ne_a1 : (𝓡).a0 ≠ (𝓡).a1 := by
  intro h
  have h0 := a0_mod3 p x
  rw [h] at h0
  have h1 := dvd_sub (a1_mod3 p x) h0
  rw [sub_sub_cancel] at h1
  exact three_not_dvd_one h1

/-- The cubic factor is odd, because `S` is. -/
theorem cubic_ne : (𝓡).rho ^ 3 - (𝓡).rho * (𝓡).S ^ 2 - (𝓡).S ^ 3 ≠ 0 := by
  obtain ⟨s, hs⟩ := S_odd p x
  have hS : (𝓡).S = 2 * s - 1 := by linear_combination hs
  apply ne_of_two_dvd_succ
  obtain ⟨t, ht | ht⟩ := even_or_odd' (𝓡).rho
  · exact ⟨4 * t ^ 3 - t * (2 * s - 1) ^ 2 - 4 * s ^ 3 + 6 * s ^ 2 - 3 * s + 1, by
      rw [ht, hS]; ring⟩
  · exact ⟨4 * t ^ 3 + 6 * t ^ 2 + 2 * t - (2 * t + 1) * (2 * s ^ 2 - 2 * s) - 4 * s ^ 3 +
      6 * s ^ 2 - 3 * s + 1, by rw [ht, hS]; ring⟩

/-- **The intersective quintic does not vanish.** -/
theorem Theta_ne : (𝓡).Theta ≠ 0 := by
  rw [Theta_def]
  refine mul_ne_zero (cubic_ne p x) ?_
  have h1 : 0 < (𝓡).S ^ 2 := lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 (S_ne p x)).symm
  have h2 := sq_nonneg (𝓡).rho
  exact (show (0 : DiffRing V) < (𝓡).rho ^ 2 + 23 * (𝓡).S ^ 2 by linarith).ne'

/-- **At a zero the support modulus is not zero**: at `Sigma = 0` the norm is `Theta⁴`. -/
theorem Sigma_ne (hz : value p x = 0) : (𝓡).Sigma ≠ 0 := by
  intro h0
  rw [value_def, h0, N9Norm.norm2] at hz
  have h : (𝓡).Theta ^ 4 = 0 := by linear_combination hz
  exact Theta_ne p x (pow_eq_zero_iff (by norm_num) |>.mp h)

theorem xi_ne (hz : value p x = 0) : (𝓡).xi ≠ 0 := fun h =>
  Sigma_ne p x hz (by rw [Sigma_def, h, zero_mul])

/-- **At a zero, `z ≠ 0` and `x ≠ 0`.** -/
theorem z_x_ne (hz : value p x = 0) : x 8 ≠ 0 ∧ x 6 ≠ 0 := by
  have h := xi_ne p x hz
  rw [xi_def] at h
  exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩

end RegsV

#print axioms radix_eq
#print axioms Xc_mod3
#print axioms a0_ne_a1
#print axioms Theta_ne
#print axioms Sigma_ne
#print axioms z_x_ne

end DiophantineConsistency.Z10Bootstrap
