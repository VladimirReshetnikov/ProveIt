import DiophantineConsistency.Z10.Z10Contract

/-! # Ten-integer package 106: the code of a positive source zero

Completeness steps C2 and C3 of the route. A positive zero of the 31-input
parent source is packed into the first two unknowns of the equation:

* **C2** (`code_of_source`). `N101Contract.code_of_source` gives digits
  `zᵢ < 2ᵏ` whose successors are a zero of the gapN86 rows. The base of
  package 106 must be a square with `b = 6t + 4`, so the digits are re-based at
  `b = 2^(2s)` with `s = k + 1`: `4^s ≡ 4 (mod 6)` (`exp_six`, from
  `2ⁿ ≢ 0 (mod 3)` and a square of a unit modulo three), and `4 ∣ b`
  (`four_dvd_exp`). The low word is `g = Σ zᵢ Bcᵂⁱ`; all weights are positive
  and `b ∣ Bc`, so `g = b · g₀` (`dvd_code`), and `g < b · Bc¹¹⁶ = cap`
  (`code_lt`).
* **C3** (`top_digit`, `code_ge`, `cap_sq_le`). Row 3 of gapN86 reads
  `a = E + s + s N` in successor coordinates, so the digit packed at the top
  weight `116` (index 20) is at least two. Hence `Bc¹¹⁶ ≤ g` and
  `cap² ≤ g³`, the hypothesis of `Z10Guard.guard_complete`.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Z10Code
open Nine121 Nine121.N105Layout Z10Regs
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ModelDifferenceRing ModelDigitTransfer
open Z10Prefix
open Nine121.N105Contract (weights_lt)
open Nine121.N101Contract (exp_two')

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] Mixed121Ports.ports

/-- The ports in the ring of differences. -/
local notation "pR" => Source31Facts.portsR (V := V) Mixed121Ports.ports

/-! ## The base `4^s` -/

/-- Three does not divide a power of two. -/
theorem not_three_dvd_exp (n : V) : ¬ (3 : V) ∣ Exp.exp n := by
  intro h
  have hp2 : Pow2 (3 : V) := Pow2.of_dvd h (exp_pow2 n)
  have htwo : (2 : V) ∣ 3 := hp2.two_dvd (by simp)
  have hz : (3 : V) % 2 = 0 := mod_eq_zero_iff_dvd.mpr htwo
  have hone : (3 : V) % 2 = 1 := by
    have h := mod_mul_add_of_lt (1 : V) (2 : V) (by simp : (1 : V) < 2)
    simpa only [show (1 : V) * 2 + 1 = 3 by ring] using h
  rw [hone] at hz
  exact (by simp : (1 : V) ≠ 0) hz

/-- A power of four is `≡ 1 (mod 3)`. -/
theorem exp_even_three (n : V) : ∃ m : V, Exp.exp (2 * n) = 3 * m + 1 := by
  have ha : Exp.exp (2 * n) = Exp.exp n * Exp.exp n := by rw [two_mul, exp_add]
  obtain ⟨q, r, hqr, hr⟩ : ∃ q r : V, Exp.exp n = 3 * q + r ∧ r < 3 :=
    ⟨Exp.exp n / 3, Exp.exp n % 3, (div_add_mod _ _).symm, mod_lt _ (by norm_num)⟩
  have hr2 : r ≤ 2 := by
    apply lt_succ_iff_le.mp
    rwa [show (2 : V) + 1 = 3 by norm_num]
  rcases le_two_iff_eq_zero_or_one_or_two.mp hr2 with rfl | rfl | rfl
  · exact absurd ⟨q, by rw [hqr, add_zero]⟩ (not_three_dvd_exp n)
  · exact ⟨3 * (q * q) + 2 * q, by rw [ha, hqr]; ring⟩
  · exact ⟨3 * (q * q) + 4 * q + 1, by rw [ha, hqr]; ring⟩

/-- A positive power of four is `≡ 4 (mod 6)`. -/
theorem exp_six (s : V) (hs : 1 ≤ s) : ∃ t : V, Exp.exp (2 * s) = 6 * t + 4 := by
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 1 := ⟨s - 1, (tsub_add_cancel_of_le hs).symm⟩
  obtain ⟨m, hm⟩ := exp_even_three n
  refine ⟨2 * m, ?_⟩
  rw [show 2 * (n + 1) = 2 + 2 * n by ring, exp_add, exp_two', hm]
  ring

/-- Four divides a positive power of four. -/
theorem four_dvd_exp (s : V) (hs : 1 ≤ s) : (4 : V) ∣ Exp.exp (2 * s) := by
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 1 := ⟨s - 1, (tsub_add_cancel_of_le hs).symm⟩
  refine ⟨Exp.exp (2 * n), ?_⟩
  rw [show 2 * (n + 1) = 2 + 2 * n by ring, exp_add, exp_two']

/-! ## The low word -/

/-- The square of the base is at most the code base. -/
theorem sq_le_Bcm (b : V) : b * b ≤ Bcm b := by
  rw [Bcm]
  exact le_mul_of_one_le_left (Arithmetic.zero_le _) (one_le_exp _)

/-- The base is at most the code base. -/
theorem le_Bcm {b : V} (hb : 0 < b) : b ≤ Bcm b :=
  le_trans (le_mul_of_one_le_left (Arithmetic.zero_le _) (pos_iff_one_le.mp hb)) (sq_le_Bcm b)

/-- The base divides the code base. -/
theorem dvd_Bcm (b : V) : b ∣ Bcm b := ⟨Exp.exp (2134940 : V) * b, by rw [Bcm]; ring⟩

/-- A packed digit vector below `b` is below `b B¹¹⁶`. -/
theorem code_lt {b B : V} (hbB : b ≤ B) (hb : 0 < b) (z : Fin 31 → V) (hz : ∀ i, z i < b) :
    ∑ i, z i * B ^ weights i < b * B ^ 116 := by
  let f : ℕ → V := fun j => if h : LowMask.Pos weights j then z (Classical.choose h) else 0
  have hfw : ∀ i, f (weights i) = z i := by
    intro i
    have h : LowMask.Pos weights (weights i) := ⟨i, rfl⟩
    simp only [f, dif_pos h]
    congr 1
    exact weights_injective (Classical.choose_spec h)
  have hsum : ∑ i, z i * B ^ weights i = dsum B f (116 + 1) := by
    rw [LowMask.dsum_weights B weights weights_injective (116 + 1) weights_lt f
      (fun j _ hp => by simp only [f, dif_neg hp])]
    exact Finset.sum_congr rfl (fun i _ => by rw [hfw])
  rw [hsum]
  apply dsum_lt_mul hbB
  intro j _
  by_cases hp : LowMask.Pos weights j
  · simp only [f, dif_pos hp]; exact hz _
  · simp only [f, dif_neg hp]; exact hb

/-- Every weight is positive, so a divisor of the base divides the packed word. -/
theorem dvd_code {b B : V} (hbB : b ∣ B) (z : Fin 31 → V) : b ∣ ∑ i, z i * B ^ weights i :=
  Finset.dvd_sum (fun i _ => Dvd.dvd.mul_left
    (dvd_trans hbB (dvd_pow_self B (Nat.one_le_iff_ne_zero.mp (Z10Contract.weights_pos i)))) _)

/-- A nonzero digit at the top weight makes the packed word at least `B¹¹⁶`. -/
theorem code_ge (B : V) (z : Fin 31 → V) (h : 1 ≤ z 20) : B ^ 116 ≤ ∑ i, z i * B ^ weights i := by
  have hle : z 20 * B ^ weights 20 ≤ ∑ j, z j * B ^ weights j :=
    Finset.single_le_sum (f := fun j => z j * B ^ weights j)
      (fun j _ => Arithmetic.zero_le _) (Finset.mem_univ 20)
  have hw : weights 20 = 116 := by decide +kernel
  rw [hw] at hle
  refine le_trans ?_ hle
  calc B ^ 116 = 1 * B ^ 116 := (one_mul _).symm
    _ ≤ z 20 * B ^ 116 := mul_le_mul h le_rfl (Arithmetic.zero_le _) (Arithmetic.zero_le _)

/-- **The top digit.** At a zero of the gapN86 rows in successor coordinates the digit of
index 20 (weight 116) is at least two. -/
theorem top_digit (z : Fin 31 → V) (h : ∀ r, N101Source.rows pR (fun i => ι (z i + 1)) r = 0) :
    2 ≤ z 20 := by
  have h3 : (1 : DiffRing V) * ι (z 20 + 1) + (-1) * ι (z 17 + 1) + (-1) * ι (z 9 + 1) +
      (-1) * (ι (z 9 + 1) * ι (z 16 + 1)) = 0 := h 3
  have e : z 20 + 1 = z 17 + 1 + (z 9 + 1) + (z 9 + 1) * (z 16 + 1) := by
    apply ι_injective
    simp only [map_add, map_mul, map_one] at h3 ⊢
    linear_combination h3
  have e' : z 20 = z 17 + z 9 + z 9 * z 16 + z 9 + z 16 + 2 := by
    apply add_right_cancel (b := (1 : V))
    rw [e]; ring
  rw [e']
  exact le_add_left le_rfl

/-! ## The cap -/

/-- The cap of the low word is a natural. -/
theorem ι_cap (b : V) : ι (b * Bcm b ^ 116) = cap (ι b) := by
  rw [Z10Regs.cap, map_mul, map_pow, ι_Bcm]

theorem cube_aux {b P g : V} (hbb : b * b ≤ P) (hg : P ≤ g) : b * P * (b * P) ≤ g * g * g := by
  calc b * P * (b * P) = b * b * (P * P) := by ring
    _ ≤ P * (P * P) := mul_le_mul hbb le_rfl (Arithmetic.zero_le _) (Arithmetic.zero_le _)
    _ ≤ g * (g * g) := mul_le_mul hg
        (mul_le_mul hg hg (Arithmetic.zero_le _) (Arithmetic.zero_le _))
        (Arithmetic.zero_le _) (Arithmetic.zero_le _)
    _ = g * g * g := by ring

/-- A low word of at least `Bc¹¹⁶` satisfies `cap² ≤ g³`. -/
theorem cap_sq_le {b g : V} (hb : 0 < b) (hg : Bcm b ^ 116 ≤ g) :
    b * Bcm b ^ 116 * (b * Bcm b ^ 116) ≤ g * g * g := by
  have hB1 : 1 ≤ Bcm b := le_trans (pos_iff_one_le.mp hb) (le_Bcm hb)
  have hBP : Bcm b ≤ Bcm b ^ 116 := by
    calc Bcm b = Bcm b ^ 1 := (pow_one _).symm
      _ ≤ Bcm b ^ 116 := pow_le_pow_right₀ hB1 (by norm_num)
  exact cube_aux (le_trans (sq_le_Bcm b) hBP) hg

/-! ## The code -/

/-- **The code of a positive source zero.** A base `b = 2^(2s) = 6t + 4` and digits
`zᵢ < b` whose packed word `g = Σ zᵢ Bcᵂⁱ = b g₀` satisfies `Bc¹¹⁶ ≤ g < b Bc¹¹⁶`, with the
successors of the digits a zero of the gapN86 rows. -/
theorem code_of_source (x : Fin 31 → V) (hx : ∀ i, 0 < x i)
    (hz : ∀ r, Source31Rows.rows pR (fun i => ι (x i)) r = 0) :
    ∃ s t g0 : V, ∃ z : Fin 31 → V,
      Exp.exp (2 * s) = 6 * t + 4 ∧ (4 : V) ∣ Exp.exp (2 * s) ∧
      (∀ i, z i < Exp.exp (2 * s)) ∧
      ∑ i, z i * Bcm (Exp.exp (2 * s)) ^ weights i = Exp.exp (2 * s) * g0 ∧
      Bcm (Exp.exp (2 * s)) ^ 116 ≤ ∑ i, z i * Bcm (Exp.exp (2 * s)) ^ weights i ∧
      ∑ i, z i * Bcm (Exp.exp (2 * s)) ^ weights i <
        Exp.exp (2 * s) * Bcm (Exp.exp (2 * s)) ^ 116 ∧
      ∀ r, N101Source.rows pR (fun i => ι (z i + 1)) r = 0 := by
  obtain ⟨k, z, hzk, -, -, hrz⟩ := Nine121.N101Contract.code_of_source x hx hz
  have hs1 : (1 : V) ≤ k + 1 := le_add_left le_rfl
  obtain ⟨t, ht⟩ := exp_six (k + 1) hs1
  have hk : Exp.exp k ≤ Exp.exp (2 * (k + 1)) := exp_monotone_le.mpr (by
    calc k ≤ k + (k + 2) := le_add_right le_rfl
      _ = 2 * (k + 1) := by ring)
  have hzs : ∀ i, z i < Exp.exp (2 * (k + 1)) := fun i => lt_of_lt_of_le (hzk i) hk
  obtain ⟨g0, hg0⟩ := dvd_code (dvd_Bcm (Exp.exp (2 * (k + 1)))) z
  have h20 : 1 ≤ z 20 := le_trans (by norm_num) (top_digit z hrz)
  exact ⟨k + 1, t, g0, z, ht, four_dvd_exp (k + 1) hs1, hzs, hg0, code_ge _ z h20,
    code_lt (le_Bcm (exp_pos _)) (exp_pos _) z hzs, hrz⟩

#print axioms exp_six
#print axioms top_digit
#print axioms cap_sq_le
#print axioms code_of_source

end DiophantineConsistency.Z10Code
