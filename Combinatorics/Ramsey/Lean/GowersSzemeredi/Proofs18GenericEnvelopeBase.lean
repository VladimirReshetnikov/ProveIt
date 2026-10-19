import GowersSzemeredi.Proofs18UniformCovers
import GowersSzemeredi.Proofs18ExponentialCalculus

/-! Power-of-two envelopes for the single-piece step in any dimension
(Notes L.7a, F3c).

Every quantity of the step is bounded by `X^(2^μ)` (densities, exponents) or
`exp(X^(2^μ))` (thresholds), with `X = 2/α`. Products and powers then add
log-degrees, so the final comparison is arithmetic on the exponents `μ`.
* The calculus: `pw_*` for powers, `ex_*` for single exponentials.
* The fixed parameters of dimension `k`:
  - `θ₁⁻¹ ≤ X^(2^(2^(k+5)+2))`, `θ₂⁻¹ ≤ X^(2^(2^(k+5)+6))`;
  - the budget, `θ₂/2` and `δ` above `X^(-2^(2^(k+5)+7))` (`fixDeg`);
  - the Bohr radius `ζ⁻¹ ≤ exp(X^(2^(2^(k+6)+1)))`;
  - Lemma 15.6's threshold `≤ X^(2^(2^(k+4)+3k+16))`.

The 19 declarations of this module that the final route does not use are in
`Proofs18GenericEnvelopeBaseSide`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-! ### The power calculus -/

section Calculus

variable {X : Real}

theorem one_le_pw (hX : 2 ≤ X) (a : Nat) : 1 ≤ X ^ (2 ^ a) :=
  one_le_pow₀ (le_trans (by norm_num) hX)

theorem pw_mono (hX : 2 ≤ X) {x : Real} {a b : Nat} (h : x ≤ X ^ (2 ^ a)) (hab : a ≤ b) :
    x ≤ X ^ (2 ^ b) :=
  h.trans (pow_le_pow_right₀ (le_trans (by norm_num) hX) (Nat.pow_le_pow_right (by norm_num) hab))

theorem pw_mul (hX : 2 ≤ X) {x y : Real} {a : Nat} (hy0 : 0 ≤ y)
    (hx : x ≤ X ^ (2 ^ a)) (hy : y ≤ X ^ (2 ^ a)) : x * y ≤ X ^ (2 ^ (a + 1)) := by
  have hX0 : 0 ≤ X := le_trans (by norm_num) hX
  calc x * y ≤ X ^ (2 ^ a) * X ^ (2 ^ a) := mul_le_mul hx hy hy0 (pow_nonneg hX0 _)
    _ = X ^ (2 ^ (a + 1)) := by rw [← pow_add, pow_succ, mul_two]

theorem pw_mul' (hX : 2 ≤ X) {x y : Real} {a b : Nat} (hy0 : 0 ≤ y)
    (hx : x ≤ X ^ (2 ^ a)) (hy : y ≤ X ^ (2 ^ b)) : x * y ≤ X ^ (2 ^ (max a b + 1)) :=
  pw_mul hX hy0 (pw_mono hX hx (le_max_left a b)) (pw_mono hX hy (le_max_right a b))

theorem pw_pow (hX : 2 ≤ X) {x : Real} {a c n : Nat} (hx0 : 0 ≤ x) (hx : x ≤ X ^ (2 ^ a))
    (hn : n ≤ 2 ^ c) : x ^ n ≤ X ^ (2 ^ (a + c)) := by
  calc x ^ n ≤ (X ^ (2 ^ a)) ^ n := pow_le_pow_left₀ hx0 hx n
    _ ≤ (X ^ (2 ^ a)) ^ (2 ^ c) := pow_le_pow_right₀ (one_le_pw hX a) hn
    _ = X ^ (2 ^ (a + c)) := by rw [← pow_mul, ← pow_add]

theorem pw_const (hX : 2 ≤ X) {c : Real} {a : Nat} (hc : c ≤ 2 ^ (2 ^ a)) : c ≤ X ^ (2 ^ a) :=
  hc.trans (pow_le_pow_left₀ (by norm_num) hX _)

/-- A factor of 32 adds five to a natural power-of-two budget. -/
theorem mul32_nat_le_pw (hX : 2 ≤ X) {P q j : Nat}
    (hP : P ≤ 2 ^ q) (hq : q + 5 ≤ 2 ^ j) : 32 * (P : Real) ≤ X ^ (2 ^ j) := by
  refine pw_const hX ?_
  have hnat : 32 * P ≤ 2 ^ (2 ^ j) := by
    calc 32 * P ≤ 2 ^ 5 * 2 ^ q := Nat.mul_le_mul (by norm_num) hP
      _ = 2 ^ (q + 5) := by rw [← pow_add]; ring_nf
      _ ≤ 2 ^ (2 ^ j) := Nat.pow_le_pow_right (by norm_num) hq
  exact_mod_cast hnat

theorem pw_X (hX : 2 ≤ X) (a : Nat) : X ≤ X ^ (2 ^ a) := by
  calc X = X ^ 1 := (pow_one X).symm
    _ ≤ X ^ (2 ^ a) := pow_le_pow_right₀ (le_trans (by norm_num) hX) (Nat.one_le_two_pow)

/-- `X^n ≤ X^(2^a)` once `n ≤ 2^a`. -/
theorem pw_natpow (hX : 2 ≤ X) {n a : Nat} (hn : n ≤ 2 ^ a) : X ^ n ≤ X ^ (2 ^ a) :=
  pow_le_pow_right₀ (le_trans (by norm_num) hX) hn

/-- Dividing a density by a controlled factor adds one reciprocal power degree. -/
theorem density_div_bounds_pw {X t d : Real} {a : Nat} (hX : 2 ≤ X)
    (ht : 0 < t ∧ t ≤ 1 ∧ t⁻¹ ≤ X ^ (2 ^ a)) (hd : 1 ≤ d)
    (hdi : d ≤ X ^ (2 ^ a)) :
    0 < t / d ∧ t / d ≤ 1 ∧ (t / d)⁻¹ ≤ X ^ (2 ^ (a + 1)) := by
  refine ⟨div_pos ht.1 (zero_lt_one.trans_le hd),
    (div_le_self ht.1.le hd).trans ht.2.1, ?_⟩
  rw [inv_div, div_eq_mul_inv]
  exact pw_mul hX (inv_pos.mpr ht.1).le hdi ht.2.2

/-- The face-budget denominator fits the same power slot when `k + 2 ≤ a`. -/
theorem budget_denominator_le_pw {X : Real} {k a : Nat} (hX : 2 ≤ X)
    (hka : k + 2 ≤ a) : 2 * ((2 : Real) ^ k + 1) ≤ X ^ (2 ^ a) := by
  calc 2 * ((2 : Real) ^ k + 1) ≤ (2 : Real) ^ (k + 2) := by
        have : (1 : Real) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
        rw [pow_add]; norm_num; linarith
    _ ≤ X ^ (k + 2) := pow_le_pow_left₀ (by norm_num) hX _
    _ ≤ X ^ (2 ^ a) := pw_natpow hX (hka.trans (Nat.lt_two_pow_self.le))

theorem ex_of_pw {x : Real} {a : Nat} (h : x ≤ X ^ (2 ^ a)) : x ≤ Real.exp (X ^ (2 ^ a)) :=
  le_exp_pow_of_le_pow h

theorem ex_mono (hX : 2 ≤ X) {x : Real} {a b : Nat} (h : x ≤ Real.exp (X ^ (2 ^ a)))
    (hab : a ≤ b) : x ≤ Real.exp (X ^ (2 ^ b)) :=
  h.trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ (le_trans (by norm_num) hX)
    (Nat.pow_le_pow_right (by norm_num) hab)))

theorem ex_mul (hX : 2 ≤ X) {x y : Real} {a : Nat} (hy0 : 0 ≤ y)
    (hx : x ≤ Real.exp (X ^ (2 ^ a))) (hy : y ≤ Real.exp (X ^ (2 ^ a))) :
    x * y ≤ Real.exp (X ^ (2 ^ (a + 1))) := by
  have h := exp_mul_le hX hy0 hx hy
  refine h.trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ (le_trans (by norm_num) hX) ?_))
  rw [pow_succ]; have := Nat.one_le_two_pow (n := a); omega

theorem ex_mul' (hX : 2 ≤ X) {x y : Real} {a b : Nat} (hy0 : 0 ≤ y)
    (hx : x ≤ Real.exp (X ^ (2 ^ a))) (hy : y ≤ Real.exp (X ^ (2 ^ b))) :
    x * y ≤ Real.exp (X ^ (2 ^ (max a b + 1))) :=
  ex_mul hX hy0 (ex_mono hX hx (le_max_left a b)) (ex_mono hX hy (le_max_right a b))

/-- A nonnegative base and exponent suffice for the exponential power bound. -/
theorem ex_rpow_of_nonneg (hX : 2 ≤ X) {b e : Real} {a c : Nat} (hb0 : 0 ≤ b)
    (hb : b ≤ Real.exp (X ^ (2 ^ a))) (he0 : 0 ≤ e) (he : e ≤ X ^ (2 ^ c)) :
    b ^ e ≤ Real.exp (X ^ (2 ^ (max a c + 1))) := by
  calc b ^ e ≤ Real.exp (X ^ (2 ^ a)) ^ e := Real.rpow_le_rpow hb0 hb he0
    _ = Real.exp (X ^ (2 ^ a) * e) := (Real.exp_mul _ _).symm
    _ ≤ Real.exp (X ^ (2 ^ (max a c + 1))) := Real.exp_le_exp.mpr
      (pw_mul' hX he0 le_rfl he)

/-- `b^e ≤ exp(X^(2^(max a c + 1)))` for `1 ≤ b ≤ exp(X^(2^a))` and `0 ≤ e ≤ X^(2^c)`. -/
theorem ex_rpow (hX : 2 ≤ X) {b e : Real} {a c : Nat} (hb1 : 1 ≤ b)
    (hb : b ≤ Real.exp (X ^ (2 ^ a))) (he0 : 0 ≤ e) (he : e ≤ X ^ (2 ^ c)) :
    b ^ e ≤ Real.exp (X ^ (2 ^ (max a c + 1))) := by
  exact ex_rpow_of_nonneg hX (zero_le_one.trans hb1) hb he0 he

end Calculus

/-- The eighth-power density loss adds four to the reciprocal power budget. -/
theorem section16ThetaTwo_inv_le_pw {t X : Real} {a : Nat} (hX : 2 ≤ X) (ha : 2 ≤ a)
    (ht : 0 < t) (hi : t⁻¹ ≤ X ^ (2 ^ a)) :
    (section16ThetaTwo t)⁻¹ ≤ X ^ (2 ^ (a + 4)) := by
  unfold section16ThetaTwo
  rw [mul_inv, Real.rpow_neg (by norm_num), inv_inv, ← inv_pow,
    show (32 : Real) = ((32 : Nat) : Real) by norm_num, Real.rpow_natCast]
  have h32 := pw_mono hX (pw_const hX (a := 5) (by norm_num : (2 : Real) ^ 32 ≤ 2 ^ (2 ^ 5)))
    (show 5 ≤ a + 3 by omega)
  have h8 := pw_pow hX (inv_pos.mpr ht).le hi (by norm_num : 8 ≤ (2 : Nat) ^ 3)
  exact pw_mul hX (pow_nonneg (inv_pos.mpr ht).le _) h32 h8

/-- A product of `≤ 2^c` factors, each at most `X^(2^a)`, is at most `X^(2^(a+c))`. -/
theorem prod_le_pw {ι : Type*} (s : Finset ι) {X : Real} (hX : 2 ≤ X) {f : ι → Real} {a c : Nat}
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h : ∀ i ∈ s, f i ≤ X ^ (2 ^ a)) (hs : s.card ≤ 2 ^ c) :
    ∏ i ∈ s, f i ≤ X ^ (2 ^ (a + c)) := by
  calc ∏ i ∈ s, f i ≤ ∏ _i ∈ s, X ^ (2 ^ a) := Finset.prod_le_prod h0 h
    _ = (X ^ (2 ^ a)) ^ s.card := Finset.prod_const _
    _ ≤ X ^ (2 ^ (a + c)) := pw_pow hX (zero_le_one.trans (one_le_pw hX a)) le_rfl hs

theorem nonTop_card_le (k : Nat) :
    (Finset.univ.filter (fun e : Fin k → Bool => e ≠ fun _ => true)).card ≤ 2 ^ k := by
  rw [nonTopVertices_card]; exact Nat.sub_le _ _

theorem nonTop_card_le_k {k : Nat} {e : Fin k → Bool} (he : e ≠ fun _ => true) :
    (section16VertexDirections e).card ≤ k := by
  have := section16VertexDirections_card_lt he
  omega

/-! ### The fixed parameters of dimension `k` -/

section Fixed

variable {alpha : Real}

theorem two_div_ge_two (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) : 2 ≤ 2 / alpha := by
  have := two_div_alpha_ge_four ha ha2; linarith

/-- `(α(α/2)/4)⁻¹ = 8/α² ≤ X³`. -/
theorem quarter_base_inv_le (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    (alpha * (alpha / 2) / 4)⁻¹ ≤ (2 / alpha) ^ 3 := by
  have ha1 : alpha ≤ 1 := by linarith
  have e1 : (alpha * (alpha / 2) / 4)⁻¹ = 8 / alpha ^ 2 := by field_simp; ring
  have e2 : (2 / alpha) ^ 3 = 8 / alpha ^ 3 := by rw [div_pow]; norm_num
  rw [e1, e2]
  exact div_le_div_of_nonneg_left (by norm_num) (pow_pos ha 3)
    (pow_le_pow_of_le_one ha.le ha1 (by norm_num))

/-- `3^(k+1) ≤ X^(2^a)` once `k + 2 ≤ a`. -/
theorem three_pow_le_pw {X : Real} (hX : 2 ≤ X) {k a : Nat} (hka : k + 2 ≤ a) :
    (((3 ^ (k + 1) : Nat) : Real)) ≤ X ^ (2 ^ a) := by
  refine pw_const hX ?_
  have h1 : 3 ^ (k + 1) ≤ 4 ^ (k + 1) := Nat.pow_le_pow_left (by norm_num) _
  have h2 : (4 : Nat) ^ (k + 1) = 2 ^ (2 * (k + 1)) := by
    rw [pow_mul]; norm_num
  have h3 : 2 * (k + 1) ≤ 2 ^ a := by
    have := Nat.lt_two_pow_self (n := k)
    have h4 : 2 ^ (k + 2) ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hka
    have h5 : 2 ^ (k + 2) = 4 * 2 ^ k := by rw [pow_add]; ring
    omega
  have h6 : 3 ^ (k + 1) ≤ 2 ^ (2 ^ a) :=
    h1.trans (h2 ▸ Nat.pow_le_pow_right (by norm_num) h3)
  exact_mod_cast h6

/-- `16^m ≤ X^(2^(k+3))` for `m ≤ k + 1`. -/
theorem sixteen_pow_le_pw {X : Real} (hX : 2 ≤ X) {k m : Nat} (hm : m ≤ k + 1) :
    (16 : Real) ^ m ≤ X ^ (2 ^ (k + 3)) := by
  refine pw_const hX ?_
  have h1 : (16 : Real) ^ m = 2 ^ (4 * m) := by rw [pow_mul]; norm_num
  rw [h1]
  refine pow_le_pow_right₀ (by norm_num) ?_
  have := Nat.lt_two_pow_self (n := k)
  have h5 : 2 ^ (k + 3) = 8 * 2 ^ k := by rw [pow_add]; ring
  omega

end Fixed

/-! ### Shared scalar estimates for the single-piece controls -/

namespace GenParams

variable {alpha : Real}

/-- The uniform base at the slice scale: `uniformBase = 8VX/(Bs)`. -/
theorem uniformBase_slice (V : Real) {B s : Real} (ha : 0 < alpha) (hB : 0 < B) (hs : 0 < s) :
    uniformBase V 1 B (alpha / 2) (s / 2) = 8 * V * (2 / alpha) * B⁻¹ * s⁻¹ := by
  unfold uniformBase
  field_simp
  ring

/-- `8VX/B ≤ X^(2^μ₀)`, at any budget degree `b ≥ 7`. -/
theorem slice_const_le_deg {V B : Real} {μV b μ0 : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (hV : 1 ≤ V) (hVμ : V ≤ 2 ^ (2 ^ μV)) (hB : 0 < B)
    (h7 : 7 ≤ b)
    (hBi : B⁻¹ ≤ (2 / alpha) ^ (2 ^ b)) (hμ0 : max μV b + 2 ≤ μ0) :
    8 * V * (2 / alpha) * B⁻¹ ≤ (2 / alpha) ^ (2 ^ μ0) := by
  have hX := two_div_ge_two ha ha2
  set m := max μV b
  have hm7 : 7 ≤ m := le_trans h7 (le_max_right μV b)
  have hV' : V ≤ (2 / alpha) ^ (2 ^ m) := pw_mono hX (pw_const hX hVμ) (le_max_left _ _)
  have hB' : B⁻¹ ≤ (2 / alpha) ^ (2 ^ m) := pw_mono hX hBi (le_max_right _ _)
  have h8 : (8 : Real) ≤ (2 / alpha) ^ (2 ^ m) :=
    pw_mono hX (pw_const hX (a := 2) (by norm_num)) (by omega)
  have hXm : 2 / alpha ≤ (2 / alpha) ^ (2 ^ m) := pw_X hX m
  have h1 := pw_mul hX (by linarith) h8 hV'
  have h2 := pw_mul hX (inv_pos.mpr hB).le hXm hB'
  have h3 := pw_mul hX (by positivity) h1 h2
  have e : 8 * V * (2 / alpha) * B⁻¹ = 8 * V * ((2 / alpha) * B⁻¹) := by ring
  rw [e]
  exact pw_mono hX h3 (by omega)

end GenParams

/-- The uniform slice density at any positive budget with a reciprocal-power bound. -/
theorem uniform_baseC_recipPowerLB_of_budget {alpha V B : Real} {D μV b μ0 : Nat}
    (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) (hV : 1 ≤ V) (hVμ : V ≤ 2 ^ (2 ^ μV))
    (hB0 : 0 < B) (hB1 : B ≤ 1) (h7 : 7 ≤ b)
    (hBi : B⁻¹ ≤ (2 / alpha) ^ (2 ^ b)) (hμ0 : max μV b + 2 ≤ μ0) :
    RecipPowerLB (2 / alpha)
      (fun s => s / 2 / uCount V D (alpha / 2) B (s / 2))
      (D * 2 ^ μ0 + 1) (D + 1) := by
  have hX := two_div_ge_two ha ha2
  have hc := GenParams.slice_const_le_deg ha ha2 hV hVμ hB0 h7 hBi hμ0
  intro s hs hs1
  have hQ1 := one_le_uCount V D (alpha / 2) B (s / 2)
  have hQeq := uCount_eq hV D (half_pos ha) (by linarith) hB0 hB1 (half_pos hs) (by linarith)
  rw [GenParams.uniformBase_slice V ha hB0 hs] at hQeq
  dsimp only
  refine ⟨div_pos (half_pos hs) (zero_lt_one.trans_le hQ1),
    (div_le_one (zero_lt_one.trans_le hQ1)).mpr (by linarith), ?_⟩
  rw [inv_div, hQeq]
  set X := 2 / alpha
  calc (8 * V * X * B⁻¹ * s⁻¹) ^ D / (s / 2) = 2 * s⁻¹ * (8 * V * X * B⁻¹ * s⁻¹) ^ D := by ring
    _ ≤ X * s⁻¹ * (X ^ (2 ^ μ0) * s⁻¹) ^ D := by gcongr
    _ = X ^ (D * 2 ^ μ0 + 1) * s⁻¹ ^ (D + 1) := by ring

namespace GenParams

variable {alpha : Real}

/-- `c(θ_S)` for the base density: the first half of `dens_step`. -/
theorem cS_step {X : Real} (hX : 2 ≤ X) {c : Real → Real} {a0 b0 : Nat}
    (hc : RecipPowerLB X c a0 b0) {θ : Real} {m μa μb : Nat} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hθi : θ⁻¹ ≤ X ^ (2 ^ m)) (ha0 : a0 ≤ 2 ^ μa) (hb0 : b0 ≤ 2 ^ μb) (hμa : μa ≤ m) :
    0 < c θ ∧ c θ ≤ 1 ∧ (c θ)⁻¹ ≤ X ^ (2 ^ (m + μb + 1)) := by
  have hX1 : (1 : Real) ≤ X := by linarith
  obtain ⟨hc0, hc1, hci⟩ := hc.apply_le hX1 hθ0 hθ1 hθi
  refine ⟨hc0, hc1, hci.trans (pow_le_pow_right₀ hX1 ?_)⟩
  have h1 : 2 ^ m * b0 ≤ 2 ^ m * 2 ^ μb := Nat.mul_le_mul_left _ hb0
  have h2 : 2 ^ m * 2 ^ μb = 2 ^ (m + μb) := by rw [← pow_add]
  have h3 : 2 ^ μa ≤ 2 ^ (m + μb) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

section Steps

variable {X : Real}

/-- `ρ = ρ₁²/8`. -/
theorem rho_step (hX : 2 ≤ X) {r : Real} {m : Nat} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hri : r⁻¹ ≤ X ^ (2 ^ m)) (hm : 1 ≤ m) :
    0 < r / 2 * (r / 2 / 2) ∧ r / 2 * (r / 2 / 2) ≤ 1 ∧
      (r / 2 * (r / 2 / 2))⁻¹ ≤ X ^ (2 ^ (m + 2)) := by
  refine ⟨by positivity, ?_, ?_⟩
  · have : r / 2 * (r / 2 / 2) ≤ 1 * 1 :=
      mul_le_mul (by linarith) (by linarith) (by positivity) zero_le_one
    linarith
  · rw [show (r / 2 * (r / 2 / 2))⁻¹ = 8 * (r⁻¹ * r⁻¹) by field_simp; ring]
    have hsq := pw_mul hX (inv_pos.mpr hr0).le hri hri
    have h8 : (8 : Real) ≤ X ^ (2 ^ (m + 1)) :=
      pw_mono hX (pw_const hX (a := 2) (by norm_num)) (by omega)
    exact pw_mul hX (by positivity) h8 hsq

/-- `θ_S = ρ³/4`. -/
theorem thetaS_step (hX : 2 ≤ X) {R : Real} {m : Nat} (hR0 : 0 < R) (hR1 : R ≤ 1)
    (hRi : R⁻¹ ≤ X ^ (2 ^ m)) :
    0 < singlePieceTheta R 1 ∧ singlePieceTheta R 1 ≤ 1 ∧
      (singlePieceTheta R 1)⁻¹ ≤ X ^ (2 ^ (m + 3)) := by
  have hval : singlePieceTheta R 1 = R ^ 3 / 4 := by unfold singlePieceTheta; norm_num
  rw [hval]
  refine ⟨by positivity, ?_, ?_⟩
  · have h3 : R ^ 3 ≤ 1 := pow_le_one₀ hR0.le hR1
    linarith
  · rw [inv_div, show (4 : Real) / R ^ 3 = 4 * R⁻¹ ^ 3 by rw [inv_pow]; ring]
    have h3 := pw_pow hX (inv_pos.mpr hR0).le hRi (show 3 ≤ 2 ^ 2 by norm_num)
    have h4 : (4 : Real) ≤ X ^ (2 ^ (m + 2)) :=
      pw_mono hX (pw_const hX (a := 1) (by norm_num)) (by omega)
    exact pw_mul hX (by positivity) h4 h3

end Steps

/-- The density-to-η estimate under its exact scalar absorption condition. -/
theorem eta_step_of_cube_le {alpha d : Real} {k m : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (hd0 : 0 < d) (hd1 : d ≤ 1) (hdi : d⁻¹ ≤ (2 / alpha) ^ (2 ^ m)) (hcube : 2 * (k + 2) ^ 3 + k + 3 ≤ 2 ^ m) :
    0 < (2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)) * (d / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4) ∧
      (2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)) * (d / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4) ≤
        alpha / 8 ∧
      ((2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)) * (d / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4))⁻¹ ≤
        (2 / alpha) ^ (2 ^ (m + 1)) := by
  have hX := two_div_ge_two ha ha2
  have hz : ((2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)))⁻¹ = 2 ^ (2 * (k + 2) ^ 3) := by
    rw [zpow_neg, inv_inv, show (2 * ((k + 1) + 1) ^ 3 : Int) = ((2 * (k + 2) ^ 3 : Nat) : Int) by
      push_cast; ring, zpow_natCast]
  have hz1 : (2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num) (neg_nonpos.mpr (by positivity))
  have h2k : (2 : Real) ≤ 2 ^ (k + 1) := le_self_pow₀ (by norm_num) (by omega)
  have hin0 : 0 < d / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4 := by positivity
  refine ⟨by positivity, ?_, ?_⟩
  · have h1 : d / (2 : Real) ^ (k + 1) ≤ 1 / 2 := by rw [div_le_iff₀ (by positivity)]; nlinarith
    have h3 := mul_le_mul h1 (by nlinarith : alpha ^ 2 ≤ alpha / 2) (by positivity) (by norm_num)
    exact (mul_le_mul hz1 (by linarith) hin0.le zero_le_one).trans_eq (one_mul _)
  · rw [mul_inv, hz, show (d / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4)⁻¹ =
      (2 : Real) ^ (k + 1) * (2 / alpha) ^ 2 * d⁻¹ by field_simp; ring, ← mul_assoc, ← mul_assoc]
    refine pw_mul hX (inv_pos.mpr hd0).le ?_ hdi
    calc (2 : Real) ^ (2 * (k + 2) ^ 3) * 2 ^ (k + 1) * (2 / alpha) ^ 2
        ≤ (2 / alpha) ^ (2 * (k + 2) ^ 3) * (2 / alpha) ^ (k + 1) * (2 / alpha) ^ 2 := by gcongr
      _ ≤ (2 / alpha) ^ (2 ^ m) := by
          rw [← pow_add, ← pow_add]; exact pow_le_pow_right₀ (one_le_two.trans hX) (by omega)

/-- The η-to-input estimate under its exact scalar denominator condition. -/
theorem yIn_step_of_den_le {alpha e : Real} {k m : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (he0 : 0 < e) (he8 : e ≤ alpha / 8) (hei : e⁻¹ ≤ (2 / alpha) ^ (2 ^ m)) (hden : 2 * (2 * (k + 3)) ^ (k + 3) ≤ 2 ^ (2 ^ m)) :
    0 < (e / 2) / (2 * (k + 1 + 2 : Nat) : Real) ^ (k + 1 + 2) ∧
      (e / 2) / (2 * (k + 1 + 2 : Nat) : Real) ^ (k + 1 + 2) ≤ alpha ∧
      ((e / 2) / (2 * (k + 1 + 2 : Nat) : Real) ^ (k + 1 + 2))⁻¹ ≤ (2 / alpha) ^ (2 ^ (m + 1)) := by
  have hX := two_div_ge_two ha ha2
  have hden1 : (1 : Real) ≤ (2 * (k + 1 + 2 : Nat) : Real) ^ (k + 1 + 2) :=
    one_le_pow₀ (by push_cast; linarith)
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    have : e / 2 ≤ alpha := by linarith
    nlinarith
  · rw [inv_div]
    have hc : 2 * (2 * (k + 1 + 2 : Nat) : Real) ^ (k + 1 + 2) ≤ (2 / alpha) ^ (2 ^ m) := by
      refine pw_const hX ?_
      exact_mod_cast hden
    calc (2 * (k + 1 + 2 : Nat) : Real) ^ (k + 1 + 2) / (e / 2)
        = 2 * (2 * (k + 1 + 2 : Nat) : Real) ^ (k + 1 + 2) * e⁻¹ := by
          rw [div_eq_mul_inv, inv_div]; ring
      _ ≤ (2 / alpha) ^ (2 ^ (m + 1)) := pw_mul hX (inv_pos.mpr he0).le hc hei

end GenParams

namespace GenParams

variable {alpha : Real}

/-- `⌊Q⌋ + 1 ≤ X^(2^(m+1))` for `1 ≤ Q ≤ X^(2^m)`. -/
theorem floor_succ_le_pw {X Q : Real} {m : Nat} (hX : 2 ≤ X) (hQ1 : 1 ≤ Q) (hQ : Q ≤ X ^ (2 ^ m)) :
    ((⌊Q⌋₊ : Nat) : Real) + 1 ≤ X ^ (2 ^ (m + 1)) := by
  have hfl : ((⌊Q⌋₊ : Nat) : Real) ≤ Q := Nat.floor_le (le_trans zero_le_one hQ1)
  have h2 : (2 : Real) ≤ X ^ (2 ^ m) := hX.trans (pw_X hX _)
  have h3 := pw_mul hX (le_trans zero_le_one hQ1) h2 hQ
  have h4 : ((⌊Q⌋₊ : Nat) : Real) + 1 ≤ 2 * Q := by linarith
  exact h4.trans h3

/-- `(familyRecExp k p q / 2)⁻¹ = 4 p (q+1)^(2·2^(k+1))`. -/
theorem half_familyRecExp_inv (k p q : Nat) :
    (familyRecExp k p q / 2)⁻¹ = 4 * ((p : Real) * ((q : Real) + 1) ^ (2 * 2 ^ (k + 1))) := by
  unfold familyRecExp
  rw [inv_div, div_inv_eq_mul]
  push_cast
  ring

end GenParams

section Calc

variable {X : Real}

/-- `c^(1/e)` for a constant `1 ≤ c ≤ 2^(2^j)` and `e⁻¹ ≤ X^(2^m)`. -/
theorem ex_root (hX : 2 ≤ X) {c e : Real} {j m : Nat} (hc1 : 1 ≤ c) (hc : c ≤ 2 ^ (2 ^ j))
    (he : 0 < e) (hei : e⁻¹ ≤ X ^ (2 ^ m)) : c ^ (1 / e) ≤ Real.exp (X ^ (2 ^ (max j m + 1))) := by
  rw [one_div]
  exact ex_rpow hX hc1 (ex_of_pw (pw_const hX hc)) (inv_pos.mpr he).le hei

/-- `4 ≤ X^2`. -/
theorem four_le_pw_one (hX : 2 ≤ X) : (4 : Real) ≤ X ^ (2 ^ 1) := by
  rw [pow_one]; nlinarith

/-- Multiplying two densities and dividing by four costs two envelope levels. -/
theorem inv_mul_div_four_le_pw (hX : 2 ≤ X) {x y : Real} {a : Nat}
    (hx : 0 < x) (hy : 0 < y) (hxi : x⁻¹ ≤ X ^ (2 ^ a)) (hyi : y⁻¹ ≤ X ^ (2 ^ a)) :
    (x * y / 4)⁻¹ ≤ X ^ (2 ^ (a + 2)) := by
  rw [show (x * y / 4)⁻¹ = 4 * (x⁻¹ * y⁻¹) by field_simp]
  have hxy := pw_mul hX (inv_pos.mpr hy).le hxi hyi
  have h4 : (4 : Real) ≤ X ^ (2 ^ (a + 1)) :=
    (four_le_pw_one hX).trans (pw_mono hX le_rfl (by omega))
  exact pw_mul hX
    (mul_nonneg (inv_pos.mpr hx).le (inv_pos.mpr hy).le) h4 hxy

end Calc

theorem familyRecThr_le_exp {X : Real} (hX : 2 ≤ X) {k K p q μK c : Nat}
    (hKμ : K ≤ 2 ^ (2 ^ μK)) (hpμ : p ≤ 2 ^ (2 ^ μK)) (hq : (q : Real) + 1 ≤ X ^ (2 ^ c)) :
    (familyRecThr k K p q : Real) ≤ Real.exp (X ^ (2 ^ (max μK (c + (k + 2)) + 3))) := by
  have hq0 : (0 : Real) ≤ (q : Real) + 1 := by positivity
  have hK' : (K : Real) ≤ X ^ (2 ^ μK) := pw_const hX (by exact_mod_cast hKμ)
  have hp' : (p : Real) ≤ X ^ (2 ^ μK) := pw_const hX (by exact_mod_cast hpμ)
  have hbase : ((K * (q + 1) : Nat) : Real) ≤ X ^ (2 ^ (max μK c + 1)) := by
    push_cast
    exact pw_mul' hX hq0 hK' hq
  have hk2 : 2 * 2 ^ (k + 1) ≤ 2 ^ (k + 2) := by rw [pow_succ 2 (k + 1)]; omega
  have hpow := pw_pow hX hq0 hq hk2
  have hn1 := pw_mul' hX (pow_nonneg hq0 _) hp' hpow
  have h2 : (2 : Real) ≤ X ^ (2 ^ (max μK (c + (k + 2)) + 1)) := hX.trans (pw_X hX _)
  have hn : ((2 * (p * (q + 1) ^ (2 * 2 ^ (k + 1))) : Nat) : Real) ≤
      X ^ (2 ^ (max μK (c + (k + 2)) + 1 + 1)) := by
    push_cast
    exact pw_mul hX (by positivity) h2 hn1
  unfold familyRecThr
  rw [Nat.cast_pow, ← Real.rpow_natCast]
  exact ex_mono hX (ex_rpow_of_nonneg hX (Nat.cast_nonneg _) (ex_of_pw hbase)
    (Nat.cast_nonneg _) hn) (by omega)

end LeanProofs.GowersSzemeredi
