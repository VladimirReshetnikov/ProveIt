import Mathlib.Algebra.Ring.Divisibility.Basic
import DiophantineConsistency.ModelExponentialCongruence
import DiophantineConsistency.ArithmeticHalfBinomialSandwich
import DiophantineConsistency.ArithmeticBinomExpansion
import DiophantineConsistency.ArithmeticPellCongruences

/-! # Integer ratio bounds for Jones's Lemma 2.25, in every model of `𝗜𝚺₁`

The analytic part of `Diophantine.Paper1982.Ratio` (`lemma_2_24`, `rho_split_c`,
`ratio_core`, `B3_real`, `Y_lower`, `K_index`, with `Jones1978.core_estimate`,
`nearest_of_estimate`, `estimate_of_floor`, `two_ψ_lt` and Lemma 2.22's
`pow_of_congruence`), with every real inequality cleared of denominators.

Put `a = A − 2`, `p = P − 2` (so `ψ_A(n) = ycoord n a`, `ψ_P(n) = ycoord n p`),
`α = 2A − 1 = 2a+3`, `π = 2P − 1 = 2p+3`, `Nn = (U+1)^(2R)`, `D = U^R`, with
`A = M(U+1)`, `P = 2M²U`, `M = RY`. The exact identity `(2P)^R·Nn = (2A)^(2R)·D`
(`ratio_key_identity`), the represented growth bounds `power_le_ycoord`/`ycoord_le_power`
and the integer Bernoulli inequality `ArithmeticPow.perturbation` give

* `ratio_lower`: `α·K·Nn ≤ (α + 4R)·C·D`, replacing `C ≥ Kρ(1 − 2R/A)`;
* `ratio_upper`: `π·C·D ≤ (π + 2R)·K·Nn`, replacing `C ≤ Kρ(1 + 2R/P)`;

for `K = ψ_P(R+1)`, `C = ψ_A(2R+1)`, `ρ = Nn/D`. Lemma 2.24 is the internal central split
`Nn = Q·D + v`, `Q = C(2R,R) + U·w'`, `U·v ≤ 2^(2R)·D`. The consequences:

* `ratio_floor_le`, `ratio_le_floor` (for `nearest_of_estimate`): the integer form of (B3),
  `2C < K(2Y+1)` and `2KY < 2C + K` (`B3_bounds`), forces `Q = Y` once `4v < D`;
* `ratio_D_le` (for `Y_lower`): `U^R ≤ 2Y`;
* `ratio_construct_upper`, `ratio_construct_lower` (for `estimate_of_floor`): at `Y = Q` and
  `8v < D`, `64C ≤ (64Q+25)K` and `64KQ ≤ 64C + 25K`; `B3_of_bounds` turns these into
  `4096(C − KQ)² ≤ 625K²` and (B3) in `DiffRing V`;
* `ratio_K_index` (for `K_index`): (B2), (B4) and `K < 2C` force `K = ψ_P(R+1)`;
* `ratio_power_of_congruence` (Lemma 2.22, sufficiency, base two): from
  `(4a+3) ∣ 2(W²−1) − 3WC`, `C = ψ_A(B)`, `W³ < A`, `(2^B)³ < A` it follows `W = 2^B`,
  because `4a+3` divides `2(W − 2^B)(2^B·W + 1)`, whose absolute value is `< 4a+3`.

All numeric size comparisons are proved once in an ordered ring (`poly_sizes`) and
transported along `ι : V → DiffRing V`. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.ModelRatio

/-! ### Polynomial size facts in an ordered ring -/

section Generic
variable {S : Type*} [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]

/-- All numeric size comparisons used below, for `r ≥ 8`, `y ≥ 64`, `u ≥ 64`
(with `M = ry`, `A = M(u+1)`, `P = 2M²u`). -/
theorem poly_sizes (r y u : S) (hr : 8 ≤ r) (hy : 64 ≤ y) (hu : 64 ≤ u) :
    4*r*(2*y+1)+1 ≤ 2*(r*y*(u+1)) ∧
    2*r*(4*y+1)+1 ≤ 2*(2*(r*y)*(r*y)*u) ∧
    3*r+2 ≤ 2*(r*y)*(r*y)*u ∧
    4*(r*y*(u+1))+1 ≤ 2*(2*(r*y)*(r*y)*u) ∧
    16*r*(8*y+1)+17 ≤ 17*(2*(2*(r*y)*(r*y)*u)) ∧
    4*r*(64*y+25)+25 ≤ 25*(2*(r*y*(u+1))) := by
  have hr0 : (0 : S) ≤ r := by linarith
  have hy1 : (1 : S) ≤ y := by linarith
  have hu1 : (1 : S) ≤ u := by linarith
  have hm : (512 : S) ≤ r*y := calc
    (512 : S) = 8*64 := by norm_num
    _ ≤ r*y := mul_le_mul hr hy (by norm_num) hr0
  have hm0 : (0 : S) ≤ r*y := by linarith
  have hry : r*1 ≤ r*y := mul_le_mul_of_nonneg_left hy1 hr0
  have hmu : r*y*64 ≤ r*y*u := mul_le_mul_of_nonneg_left hu hm0
  have hmm : r*y*512 ≤ r*y*(r*y) := mul_le_mul_of_nonneg_left hm hm0
  have hmmu : r*y*(r*y)*1 ≤ r*y*(r*y)*u :=
    mul_le_mul_of_nonneg_left hu1 (mul_nonneg hm0 hm0)
  have hmu0 : (0 : S) ≤ r*y*u := by linarith
  have hmum : r*y*u*512 ≤ r*y*u*(r*y) := mul_le_mul_of_nonneg_left hm hmu0
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

end Generic

section Model
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPow ArithmeticPellRecurrence ArithmeticBinomPascal ArithmeticBinomExpansion
  ArithmeticHalfBinomialSandwich ModelDifferenceRing ModelArithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Small arithmetic helpers -/

theorem mr_pos_succ (x : V) : 0 < x+1 :=
  lt_of_lt_of_le (by simp : (0 : V) < 1) (le_add_of_nonneg_left (by simp))

theorem mr_pos_add_two (x : V) : 0 < x+2 :=
  lt_of_lt_of_le (by simp : (0 : V) < 2) (le_add_of_nonneg_left (by simp))

theorem mr_one_le_odd (x : V) : 1 ≤ 2*x+3 :=
  le_trans (by norm_num : (1 : V) ≤ 3) (le_add_of_nonneg_left (by simp))

theorem mr_pos_odd (x : V) : 0 < 2*x+3 :=
  lt_of_lt_of_le (by simp : (0 : V) < 1) (mr_one_le_odd x)

theorem mr_succ_lt_odd (x : V) : x+1 < 2*x+3 := calc
  x+1 < x+1+(x+2) := lt_add_of_pos_right _ (mr_pos_add_two x)
  _ = 2*x+3 := by ring

theorem mr_add_one_add_one (x : V) : x+1+1 = x+2 := by ring

theorem sub_two_of (a A : V) (h : a+2 = A) : A-2 = a := by
  rw [← h, add_tsub_cancel_right]

theorem sub_one_of_add_two (p : V) : p+2-1 = p+1 := by
  rw [show p+2 = p+1+1 by ring, add_tsub_cancel_right]

/-- `P² − 1 = delta (P − 2)` with `P = p + 2`. -/
theorem sq_sub_one_eq_delta (p : V) : (p+2)*(p+2)-1 = delta p := by
  rw [show (p+2)*(p+2) = delta p+1 by unfold delta; ring, add_tsub_cancel_right]

theorem dvd_of_add_dvd {d x y : V} (hd : 0 < d) (hsum : d ∣ x+y) (hy : d ∣ y) : d ∣ x := by
  apply mod_eq_zero_iff_dvd.mp
  have hz : (x+y)%d = 0 := mod_eq_zero_iff_dvd.mpr hsum
  rwa [mod_add_remove_right_of_dvd hy hd] at hz

theorem ratio_power_two_six : power (2 : V) 6 = 64 := by
  rw [show (6 : V) = 0+1+1+1+1+1+1 by norm_num]
  simp only [power_succ, power_zero]
  norm_num

theorem ratio_power_two_three : power (2 : V) 3 = 8 := by
  rw [show (3 : V) = 0+1+1+1 by norm_num]
  simp only [power_succ, power_zero]
  norm_num

theorem ratio_power_three (U : V) : power U 3 = U*U*U := by
  rw [show (3 : V) = 0+1+1+1 by norm_num]
  simp only [power_succ, power_zero]
  ring

/-- `2^(6R+3) = 8·64^R`. -/
theorem exp_six_eq (R : V) : Exp.exp (6*R+3) = 8*power 64 R := by
  rw [← ArithmeticPow.power_two, power_add, ← power_iterate, ratio_power_two_six,
    ratio_power_two_three]
  ring

/-- A multiple of a positive `J` strictly inside `(-J, J)` vanishes (discreteness). -/
theorem eq_zero_of_dvd_small {J x : DiffRing V} (hJ : 0 < J) (hd : J ∣ x) (h1 : x < J)
    (h2 : -J < x) : x = 0 := by
  obtain ⟨k, rfl⟩ := hd
  rcases lt_trichotomy k 0 with hk | hk | hk
  · exfalso
    have hk1 : (1 : DiffRing V) ≤ -k := model_discrete (-k) (by linarith)
    have h3 : J*1 ≤ J*(-k) := mul_le_mul_of_nonneg_left hk1 hJ.le
    linarith
  · rw [hk, mul_zero]
  · exfalso
    have hk1 : (1 : DiffRing V) ≤ k := model_discrete k hk
    have h3 : J*1 ≤ J*k := mul_le_mul_of_nonneg_left hk1 hJ.le
    linarith

/-! ### Size facts in the model -/

theorem model_sizes (R Y U : V) (hR : 8 ≤ R) (hY : 64 ≤ Y) (hU : 64 ≤ U) :
    4*R*(2*Y+1)+1 ≤ 2*(R*Y*(U+1)) ∧
    2*R*(4*Y+1)+1 ≤ 2*(2*(R*Y)*(R*Y)*U) ∧
    3*R+2 ≤ 2*(R*Y)*(R*Y)*U ∧
    4*(R*Y*(U+1))+1 ≤ 2*(2*(R*Y)*(R*Y)*U) ∧
    16*R*(8*Y+1)+17 ≤ 17*(2*(2*(R*Y)*(R*Y)*U)) ∧
    4*R*(64*Y+25)+25 ≤ 25*(2*(R*Y*(U+1))) := by
  have hr : (8 : DiffRing V) ≤ ι R := by simpa only [map_ofNat] using ι_le_ι.mpr hR
  have hy : (64 : DiffRing V) ≤ ι Y := by simpa only [map_ofNat] using ι_le_ι.mpr hY
  have hu : (64 : DiffRing V) ≤ ι U := by simpa only [map_ofNat] using ι_le_ι.mpr hU
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := poly_sizes (ι R) (ι Y) (ι U) hr hy hu
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply ι_le_ι.mp; simp only [map_add, map_mul, map_one, map_ofNat]; exact g1
  · apply ι_le_ι.mp; simp only [map_add, map_mul, map_one, map_ofNat]; exact g2
  · apply ι_le_ι.mp; simp only [map_add, map_mul, map_one, map_ofNat]; exact g3
  · apply ι_le_ι.mp; simp only [map_add, map_mul, map_one, map_ofNat]; exact g4
  · apply ι_le_ι.mp; simp only [map_add, map_mul, map_one, map_ofNat]; exact g5
  · apply ι_le_ι.mp; simp only [map_add, map_mul, map_one, map_ofNat]; exact g6

theorem basic_sizes (R Y U M A P : V) (hR : 8 ≤ R) (hY : 64 ≤ Y) (hU : 64 ≤ U)
    (hM : M = R*Y) (hA : A = M*(U+1)) (hP : P = 2*M*M*U) :
    512 ≤ M ∧ U+1 ≤ A ∧ 2 ≤ A ∧ 2 ≤ P := by
  have hM512 : 512 ≤ M := by
    rw [hM]
    calc (512 : V) = 8*64 := by norm_num
      _ ≤ R*Y := mul_le_mul hR hY (by simp) (by simp)
  have hM1 : 1 ≤ M := le_trans (by norm_num) hM512
  have hUA : U+1 ≤ A := by rw [hA]; exact le_mul_of_one_le_left (by simp) hM1
  have hA2 : 2 ≤ A :=
    le_trans (le_trans (by norm_num : (2 : V) ≤ 64+1) (add_le_add hU (le_refl 1))) hUA
  have hP2 : 2 ≤ P := by
    rw [hP]
    calc (2 : V) = 2*1*1*1 := by ring
      _ ≤ 2*M*M*U :=
        mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hM1 (by simp)) hM1 (by simp) (by simp))
          (le_trans (by norm_num) hU) (by simp) (by simp)
  exact ⟨hM512, hUA, hA2, hP2⟩

/-- The parameter inequalities for `α = 2a+3 = 2A−1` and `π = 2p+3 = 2P−1`. -/
theorem ratio_params (R Y U M A P a p : V) (hR : 8 ≤ R) (hY : 64 ≤ Y) (hU : 64 ≤ U)
    (hM : M = R*Y) (hA : A = M*(U+1)) (hP : P = 2*M*M*U) (ha : a+2 = A) (hp : p+2 = P) :
    4*R*(2*Y+1) ≤ 2*a+3 ∧ 4*R ≤ 2*a+3 ∧ 2*R*(4*Y+1) ≤ 2*p+3 ∧ 2*R ≤ 2*p+3 ∧
      3*R+1 ≤ p+1 ∧ 4*(a+2) ≤ 2*p+3 ∧ 16*R*(8*Y+1) ≤ 17*(2*p+3) ∧
      4*R*(64*Y+25) ≤ 25*(2*a+3) := by
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := model_sizes R Y U hR hY hU
  have eA : 2*a+3+1 = 2*(R*Y*(U+1)) := by rw [← hM, ← hA, ← ha]; ring
  have eA' : a+2 = R*Y*(U+1) := by rw [← hM, ← hA, ha]
  have eP : 2*p+3+1 = 2*(2*(R*Y)*(R*Y)*U) := by rw [← hM, ← hP, ← hp]; ring
  have eP' : p+1+1 = 2*(R*Y)*(R*Y)*U := by rw [← hM, ← hP, ← hp]; ring
  have h1 : 4*R*(2*Y+1) ≤ 2*a+3 := (add_le_add_iff_right (1 : V)).mp (g1.trans_eq eA.symm)
  have h2 : 4*R ≤ 2*a+3 :=
    le_trans (le_mul_of_one_le_right (by simp) (le_add_of_nonneg_left (by simp))) h1
  have h3 : 2*R*(4*Y+1) ≤ 2*p+3 := (add_le_add_iff_right (1 : V)).mp (g2.trans_eq eP.symm)
  have h4 : 2*R ≤ 2*p+3 :=
    le_trans (le_mul_of_one_le_right (by simp) (le_add_of_nonneg_left (by simp))) h3
  have h5 : 3*R+1 ≤ p+1 := by
    apply (add_le_add_iff_right (1 : V)).mp
    rw [eP', show 3*R+1+1 = 3*R+2 by ring]
    exact g3
  have h6 : 4*(a+2) ≤ 2*p+3 := by
    apply (add_le_add_iff_right (1 : V)).mp
    rw [eA', eP]
    exact g4
  have h7 : 16*R*(8*Y+1) ≤ 17*(2*p+3) := by
    apply (add_le_add_iff_right (17 : V)).mp
    rw [show 17*(2*p+3)+17 = 17*(2*p+3+1) by ring, eP]
    exact g5
  have h8 : 4*R*(64*Y+25) ≤ 25*(2*a+3) := by
    apply (add_le_add_iff_right (25 : V)).mp
    rw [show 25*(2*a+3)+25 = 25*(2*a+3+1) by ring, eA]
    exact g6
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-! ### The integer sandwich (replaces `ratio_core`) -/

/-- `(2P)^R·(U+1)^(2R) = (2A)^(2R)·U^R` for `A = M(U+1)`, `P = 2M²U`. -/
theorem ratio_key_identity (M U R : V) :
    power (2*(2*M*M*U)) R*power (U+1) (2*R) = power (2*(M*(U+1))) (2*R)*power U R := by
  have h2R : power (2*M) (2*R) = power (2*M) R*power (2*M) R := by
    rw [two_mul R, power_add]
  have e1 : power (2*(2*M*M*U)) R = power (2*M) (2*R)*power U R := by
    rw [h2R, show 2*(2*M*M*U) = (2*M)*(2*M)*U by ring, power_mul_base ((2*M)*(2*M)) U R,
      power_mul_base (2*M) (2*M) R]
  have e2 : power (2*(M*(U+1))) (2*R) = power (2*M) (2*R)*power (U+1) (2*R) := by
    rw [show 2*(M*(U+1)) = (2*M)*(U+1) by ring, power_mul_base (2*M) (U+1) (2*R)]
  rw [e1, e2]
  ring

/-- Lower sandwich: `α·K·(U+1)^(2R) ≤ (α + 4R)·C·U^R` with `α = 2A − 1`. -/
theorem ratio_lower (M U R a p : V) (ha : a+2 = M*(U+1)) (hp : p+2 = 2*M*M*U)
    (hR : 4*R ≤ 2*a+3) :
    (2*a+3)*ycoord (R+1) p*power (U+1) (2*R) ≤
      (2*a+3+4*R)*ycoord (2*R+1) a*power U R := by
  have hid := ratio_key_identity M U R
  rw [← hp, ← ha] at hid
  have hpert : (2*a+3)*power (2*(a+2)) (2*R) ≤ (2*a+3+4*R)*power (2*a+3) (2*R) := by
    have h := perturbation (2*a+3) 1 (2*R) ((show 2*(2*R)*1 = 4*R by ring).trans_le hR)
    rwa [show 2*a+3+1 = 2*(a+2) by ring, show 2*a+3+2*(2*R)*1 = 2*a+3+4*R by ring] at h
  calc (2*a+3)*ycoord (R+1) p*power (U+1) (2*R)
      ≤ (2*a+3)*power (2*(p+2)) R*power (U+1) (2*R) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (ycoord_le_power p R) (by simp)) (by simp)
    _ = (2*a+3)*(power (2*(p+2)) R*power (U+1) (2*R)) := by ring
    _ = (2*a+3)*(power (2*(a+2)) (2*R)*power U R) := by rw [hid]
    _ = (2*a+3)*power (2*(a+2)) (2*R)*power U R := by ring
    _ ≤ (2*a+3+4*R)*power (2*a+3) (2*R)*power U R :=
        mul_le_mul_of_nonneg_right hpert (by simp)
    _ ≤ (2*a+3+4*R)*ycoord (2*R+1) a*power U R :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (power_le_ycoord a (2*R)) (by simp)) (by simp)

/-- Upper sandwich: `π·C·U^R ≤ (π + 2R)·K·(U+1)^(2R)` with `π = 2P − 1`. -/
theorem ratio_upper (M U R a p : V) (ha : a+2 = M*(U+1)) (hp : p+2 = 2*M*M*U)
    (hR : 2*R ≤ 2*p+3) :
    (2*p+3)*ycoord (2*R+1) a*power U R ≤
      (2*p+3+2*R)*ycoord (R+1) p*power (U+1) (2*R) := by
  have hid := ratio_key_identity M U R
  rw [← hp, ← ha] at hid
  have hpert : (2*p+3)*power (2*(p+2)) R ≤ (2*p+3+2*R)*power (2*p+3) R := by
    have h := perturbation (2*p+3) 1 R ((show 2*R*1 = 2*R by ring).trans_le hR)
    rwa [show 2*p+3+1 = 2*(p+2) by ring, show 2*p+3+2*R*1 = 2*p+3+2*R by ring] at h
  calc (2*p+3)*ycoord (2*R+1) a*power U R
      ≤ (2*p+3)*power (2*(a+2)) (2*R)*power U R :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (ycoord_le_power a (2*R)) (by simp)) (by simp)
    _ = (2*p+3)*(power (2*(a+2)) (2*R)*power U R) := by ring
    _ = (2*p+3)*(power (2*(p+2)) R*power (U+1) (2*R)) := by rw [hid]
    _ = (2*p+3)*power (2*(p+2)) R*power (U+1) (2*R) := by ring
    _ ≤ (2*p+3+2*R)*power (2*p+3) R*power (U+1) (2*R) :=
        mul_le_mul_of_nonneg_right hpert (by simp)
    _ ≤ (2*p+3+2*R)*ycoord (R+1) p*power (U+1) (2*R) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (power_le_ycoord p R) (by simp)) (by simp)

/-! ### Abstract consequences of the sandwich -/

/-- Soundness, `Q ≤ Y` (with `Nn ≥ Q·D`; replaces half of `nearest_of_estimate`). -/
theorem ratio_floor_le (α K C Nn D R Y Q : V) (hα0 : 0 < α) (hK : 0 < K) (hD : 0 < D)
    (hL : α*K*Nn ≤ (α+4*R)*C*D) (hQ : Q*D ≤ Nn) (hB3 : 2*C < K*(2*Y+1))
    (hα : 4*R*(2*Y+1) ≤ α) : Q ≤ Y := by
  by_contra hlt
  have hYQ : Y+1 ≤ Q := lt_iff_succ_le.mp (lt_of_not_ge hlt)
  have h1 : α*K*(Y+1)*D ≤ (α+4*R)*C*D := calc
    α*K*(Y+1)*D ≤ α*K*Q*D :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hYQ (by simp)) (by simp)
    _ = α*K*(Q*D) := by ring
    _ ≤ α*K*Nn := mul_le_mul_of_nonneg_left hQ (by simp)
    _ ≤ (α+4*R)*C*D := hL
  have hpos : 0 < (α+4*R)*D :=
    mul_pos (lt_of_lt_of_le hα0 (le_add_of_nonneg_right (by simp))) hD
  have h2 : (2*α*(Y+1))*(K*D) < ((α+4*R)*(2*Y+1))*(K*D) := calc
    (2*α*(Y+1))*(K*D) = 2*(α*K*(Y+1)*D) := by ring
    _ ≤ 2*((α+4*R)*C*D) := mul_le_mul_of_nonneg_left h1 (by simp)
    _ = ((α+4*R)*D)*(2*C) := by ring
    _ < ((α+4*R)*D)*(K*(2*Y+1)) := mul_lt_mul_of_pos_left hB3 hpos
    _ = ((α+4*R)*(2*Y+1))*(K*D) := by ring
  have h3 : (α+4*R)*(2*Y+1) ≤ 2*α*(Y+1) := calc
    (α+4*R)*(2*Y+1) = (2*α*Y+α)+4*R*(2*Y+1) := by ring
    _ ≤ (2*α*Y+α)+α := add_le_add le_rfl hα
    _ = 2*α*(Y+1) := by ring
  exact absurd h2 (not_lt.mpr (mul_le_mul_of_nonneg_right h3 (by simp)))

/-- Soundness, `Y ≤ Q` (with `Nn = Q·D + v`, `4v < D`; the other half of
`nearest_of_estimate`). -/
theorem ratio_le_floor (π K C Nn D R Y Q v : V) (hπ0 : 0 < π) (hK : 0 < K) (hD : 0 < D)
    (hU : π*C*D ≤ (π+2*R)*K*Nn) (hN : Nn = Q*D+v) (hv : 4*v < D)
    (hB3 : 2*K*Y < 2*C+K) (hπ : 2*R*(4*Y+1) ≤ π) : Y ≤ Q := by
  by_contra hlt
  have hQY : Q+1 ≤ Y := lt_iff_succ_le.mp (lt_of_not_ge hlt)
  have hQle : Q ≤ Y := le_trans (le_add_of_nonneg_right (by simp)) hQY
  have h4N : 4*Nn < (4*Q+1)*D := by
    rw [hN]
    calc 4*(Q*D+v) = 4*Q*D+4*v := by ring
      _ < 4*Q*D+D := add_lt_add_of_le_of_lt le_rfl hv
      _ = (4*Q+1)*D := by ring
  have hpos : 0 < 2*(π+2*R)*K :=
    mul_pos (mul_pos (by simp) (lt_of_lt_of_le hπ0 (le_add_of_nonneg_right (by simp)))) hK
  have h2 : (8*π*Y)*(K*D) < (2*(π+2*R)*(4*Q+1)+4*π)*(K*D) := calc
    (8*π*Y)*(K*D) = 4*(π*D)*(2*K*Y) := by ring
    _ < 4*(π*D)*(2*C+K) := mul_lt_mul_of_pos_left hB3 (mul_pos (by simp) (mul_pos hπ0 hD))
    _ = 8*(π*C*D)+4*π*K*D := by ring
    _ ≤ 8*((π+2*R)*K*Nn)+4*π*K*D :=
        add_le_add (mul_le_mul_of_nonneg_left hU (by simp)) le_rfl
    _ = (2*(π+2*R)*K)*(4*Nn)+4*π*K*D := by ring
    _ < (2*(π+2*R)*K)*((4*Q+1)*D)+4*π*K*D :=
        add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left h4N hpos) le_rfl
    _ = (2*(π+2*R)*(4*Q+1)+4*π)*(K*D) := by ring
  have h4 : 4*R*(4*Q+1) ≤ 2*π := calc
    4*R*(4*Q+1) ≤ 4*R*(4*Y+1) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_left hQle (by simp)) le_rfl) (by simp)
    _ = 2*(2*R*(4*Y+1)) := by ring
    _ ≤ 2*π := mul_le_mul_of_nonneg_left hπ (by simp)
  have h3 : 2*(π+2*R)*(4*Q+1)+4*π ≤ 8*π*Y := calc
    2*(π+2*R)*(4*Q+1)+4*π = (8*π*Q+6*π)+4*R*(4*Q+1) := by ring
    _ ≤ (8*π*Q+6*π)+2*π := add_le_add le_rfl h4
    _ = 8*π*(Q+1) := by ring
    _ ≤ 8*π*Y := mul_le_mul_of_nonneg_left hQY (by simp)
  exact absurd h2 (not_lt.mpr (mul_le_mul_of_nonneg_right h3 (by simp)))

/-- `U^R ≤ 2Y` from the lower sandwich and (B3) (replaces `Y_lower`). -/
theorem ratio_D_le (α K C Nn D R Y : V) (hα0 : 0 < α) (hK : 0 < K) (hD : 0 < D)
    (hL : α*K*Nn ≤ (α+4*R)*C*D) (hB3 : 2*C < K*(2*Y+1)) (hα : 4*R ≤ α)
    (hDD : D*D ≤ Nn) : D ≤ 2*Y := by
  by_contra hlt
  have h : 2*Y+1 ≤ D := lt_iff_succ_le.mp (lt_of_not_ge hlt)
  have hpos : 0 < (α+4*R)*D :=
    mul_pos (lt_of_lt_of_le hα0 (le_add_of_nonneg_right (by simp))) hD
  have hc : 2*(α*K*Nn) < 2*(α*K*Nn) := calc
    2*(α*K*Nn) ≤ 2*((α+4*R)*C*D) := mul_le_mul_of_nonneg_left hL (by simp)
    _ = ((α+4*R)*D)*(2*C) := by ring
    _ < ((α+4*R)*D)*(K*(2*Y+1)) := mul_lt_mul_of_pos_left hB3 hpos
    _ ≤ ((α+α)*D)*(K*(2*Y+1)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (add_le_add le_rfl hα) (by simp)) (by simp)
    _ = 2*(α*K)*((2*Y+1)*D) := by ring
    _ ≤ 2*(α*K)*(D*D) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h (by simp)) (by simp)
    _ ≤ 2*(α*K)*Nn := mul_le_mul_of_nonneg_left hDD (by simp)
    _ = 2*(α*K*Nn) := by ring
  exact absurd hc (_root_.lt_irrefl _)

/-- Construction, `64C ≤ (64Q+25)K` (with `Nn = Q·D + v`, `8v < D`). -/
theorem ratio_construct_upper (π K C Nn D R Q v : V) (hπ0 : 0 < π) (hK : 0 < K)
    (hD : 0 < D) (hU : π*C*D ≤ (π+2*R)*K*Nn) (hN : Nn = Q*D+v) (hv : 8*v < D)
    (hπ : 16*R*(8*Q+1) ≤ 17*π) : 64*C ≤ (64*Q+25)*K := by
  by_contra hlt
  have h : (64*Q+25)*K < 64*C := lt_of_not_ge hlt
  have h8N : 8*Nn < (8*Q+1)*D := by
    rw [hN]
    calc 8*(Q*D+v) = 8*Q*D+8*v := by ring
      _ < 8*Q*D+D := add_lt_add_of_le_of_lt le_rfl hv
      _ = (8*Q+1)*D := by ring
  have hpos1 : 0 < 8*π*D := mul_pos (mul_pos (by simp) hπ0) hD
  have hpos2 : 0 < 64*(π+2*R)*K :=
    mul_pos (mul_pos (by simp) (lt_of_lt_of_le hπ0 (le_add_of_nonneg_right (by simp)))) hK
  have h2 : (8*π*(64*Q+25))*(K*D) < (64*(π+2*R)*(8*Q+1))*(K*D) := calc
    (8*π*(64*Q+25))*(K*D) = (8*π*D)*((64*Q+25)*K) := by ring
    _ < (8*π*D)*(64*C) := mul_lt_mul_of_pos_left h hpos1
    _ = 512*(π*C*D) := by ring
    _ ≤ 512*((π+2*R)*K*Nn) := mul_le_mul_of_nonneg_left hU (by simp)
    _ = (64*(π+2*R)*K)*(8*Nn) := by ring
    _ < (64*(π+2*R)*K)*((8*Q+1)*D) := mul_lt_mul_of_pos_left h8N hpos2
    _ = (64*(π+2*R)*(8*Q+1))*(K*D) := by ring
  have h3 : 64*(π+2*R)*(8*Q+1) ≤ 8*π*(64*Q+25) := calc
    64*(π+2*R)*(8*Q+1) = (512*π*Q+64*π)+8*(16*R*(8*Q+1)) := by ring
    _ ≤ (512*π*Q+64*π)+8*(17*π) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hπ (by simp))
    _ = 8*π*(64*Q+25) := by ring
  exact absurd h2 (not_lt.mpr (mul_le_mul_of_nonneg_right h3 (by simp)))

/-- Construction, `64KQ ≤ 64C + 25K` (with `Nn ≥ Q·D`). -/
theorem ratio_construct_lower (α K C Nn D R Q : V) (hα0 : 0 < α) (hK : 0 < K) (hD : 0 < D)
    (hL : α*K*Nn ≤ (α+4*R)*C*D) (hQ : Q*D ≤ Nn) (hup : 64*C ≤ (64*Q+25)*K)
    (hα : 4*R*(64*Q+25) ≤ 25*α) : 64*K*Q ≤ 64*C+25*K := by
  have h1 : (α*K*Q)*D ≤ ((α+4*R)*C)*D := calc
    (α*K*Q)*D = α*K*(Q*D) := by ring
    _ ≤ α*K*Nn := mul_le_mul_of_nonneg_left hQ (by simp)
    _ ≤ (α+4*R)*C*D := hL
  have h2 : α*K*Q ≤ (α+4*R)*C := le_of_mul_le_mul_right h1 hD
  by_contra hlt
  have h : 64*C+25*K < 64*K*Q := lt_of_not_ge hlt
  have hc : α*(64*C+25*K) < α*(64*C+25*K) := calc
    α*(64*C+25*K) < α*(64*K*Q) := mul_lt_mul_of_pos_left h hα0
    _ = 64*(α*K*Q) := by ring
    _ ≤ 64*((α+4*R)*C) := mul_le_mul_of_nonneg_left h2 (by simp)
    _ = 64*α*C+4*R*(64*C) := by ring
    _ ≤ 64*α*C+4*R*((64*Q+25)*K) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hup (by simp))
    _ = 64*α*C+(4*R*(64*Q+25))*K := by ring
    _ ≤ 64*α*C+(25*α)*K := add_le_add le_rfl (mul_le_mul_of_nonneg_right hα (by simp))
    _ = α*(64*C+25*K) := by ring
  exact absurd hc (_root_.lt_irrefl _)

/-! ### (B3) in the ring of differences -/

/-- (B3) `4(C − KY)² < K²` gives the integer bounds `2C < K(2Y+1)`, `2KY < 2C + K`
(replaces `B3_real`). -/
theorem B3_bounds (C K Y : V) (h : (4 : DiffRing V)*(ι C - ι K*ι Y)^2 < ι K^2) :
    2*C < K*(2*Y+1) ∧ 2*K*Y < 2*C+K := by
  have h' : (2*(ι C - ι K*ι Y))^2 < (ι K)^2 := by
    have e : (2*(ι C - ι K*ι Y))^2 = (4 : DiffRing V)*(ι C - ι K*ι Y)^2 := by ring
    rw [e]; exact h
  have habs := abs_lt.mp (abs_lt_of_sq_lt_sq h' (ι_nonneg K))
  constructor
  · apply ι_lt_ι.mp
    simp only [map_mul, map_add, map_one, map_ofNat]
    linarith [habs.2]
  · apply ι_lt_ι.mp
    simp only [map_mul, map_add, map_ofNat]
    linarith [habs.1]

/-- The construction bounds give `4096(C−KQ)² ≤ 625K²` and (B3). -/
theorem B3_of_bounds (C K Q : V) (hK : 0 < K) (h1 : 64*C ≤ (64*Q+25)*K)
    (h2 : 64*K*Q ≤ 64*C+25*K) :
    (4096 : DiffRing V)*(ι C - ι K*ι Q)^2 ≤ 625*ι K^2 ∧
      (4 : DiffRing V)*(ι C - ι K*ι Q)^2 < ι K^2 := by
  have h1' : (64 : DiffRing V)*ι C ≤ (64*ι Q+25)*ι K := by
    simpa only [map_mul, map_add, map_ofNat] using ι_le_ι.mpr h1
  have h2' : (64 : DiffRing V)*ι K*ι Q ≤ 64*ι C+25*ι K := by
    simpa only [map_mul, map_add, map_ofNat] using ι_le_ι.mpr h2
  have hK' : (0 : DiffRing V) < ι K := by simpa only [map_zero] using ι_lt_ι.mpr hK
  have hsq : (64*(ι C - ι K*ι Q))^2 ≤ (25*ι K)^2 := sq_le_sq' (by linarith) (by linarith)
  have hA : (4096 : DiffRing V)*(ι C - ι K*ι Q)^2 ≤ 625*ι K^2 := by
    have e1 : (64*(ι C - ι K*ι Q))^2 = (4096 : DiffRing V)*(ι C - ι K*ι Q)^2 := by ring
    have e2 : (25*ι K)^2 = (625 : DiffRing V)*ι K^2 := by ring
    rw [e1, e2] at hsq
    exact hsq
  refine ⟨hA, ?_⟩
  have hK2 : (0 : DiffRing V) < ι K^2 := pow_pos hK' 2
  linarith

/-! ### The index of `K` (replaces `K_index`) -/

/-- (B2), (B4) and `K < 2C` (from (B3)) force `K = ψ_P(R+1)`, with `P = p + 2`. -/
theorem ratio_K_index (R a p K C z h : V) (hR : 1 ≤ R) (hRp : 3*R+1 ≤ p+1)
    (hpA : 4*(a+2) ≤ 2*p+3) (hC : C = ycoord (2*R+1) a) (hz : z*z = 1+delta p*K*K)
    (hB4 : K = R+1+h*(p+1)) (hKC : K < 2*C) : K = ycoord (R+1) p := by
  obtain ⟨t, -, -, ht⟩ := ArithmeticPellClassification.solution_index p z K hz
  obtain ⟨-, s, -, hts⟩ :=
    ArithmeticPellCongruences.residue_quotients t p (p+1) (dvd_refl _)
  have hm : 0 < p+1 := mr_pos_succ p
  have hR1 : R+1 < p+1 := by
    have h2R : 0 < 2*R := mul_pos (by simp) (lt_of_lt_of_le (by simp) hR)
    have h3 : R+1 < 3*R+1 := calc
      R+1 < R+1+2*R := lt_add_of_pos_right _ h2R
      _ = 3*R+1 := by ring
    exact lt_of_lt_of_le h3 hRp
  have he : t+(p+1)*s = R+1+h*(p+1) := by rw [← hts, ht]; exact hB4
  have hmod : t%(p+1) = R+1 := by
    have h1 : (t+(p+1)*s)%(p+1) = (R+1+h*(p+1))%(p+1) := by rw [he]
    rwa [mod_add_mul' t s hm, mod_add_mul (R+1) h hm, mod_eq_self_of_lt hR1] at h1
  have hdm := div_add_mod t (p+1)
  rw [hmod] at hdm
  rcases zero_or_succ (t/(p+1)) with h0 | ⟨j, hj⟩
  · rw [h0, mul_zero, zero_add] at hdm
    rw [← ht, hdm]
  · exfalso
    rw [hj] at hdm
    have ht4 : 4*R+1 ≤ t := calc
      4*R+1 = (3*R+1)+R := by ring
      _ ≤ (p+1)+R := add_le_add hRp le_rfl
      _ ≤ (p+1)*(j+1)+(R+1) :=
          add_le_add (le_mul_of_one_le_right (by simp) (le_add_of_nonneg_left (by simp)))
            (le_add_of_nonneg_right (by simp))
      _ = t := hdm
    have hX : 0 < power (2*(a+2)) (2*R) :=
      power_pos _ _ (mul_pos (by simp) (mr_pos_add_two a))
    have h2R : 2 ≤ power 2 R := by
      simpa only [power_one] using power_mono_exponent (2 : V) 1 R (by norm_num) hR
    have h4 : (4 : V) ≤ power 2 (2*R) := by
      rw [two_mul R, power_add]
      calc (4 : V) = 2*2 := by norm_num
        _ ≤ power 2 R*power 2 R := mul_le_mul h2R h2R (by simp) (by simp)
    have h2R4 : 2*R ≤ 4*R := calc
      2*R ≤ 2*R+2*R := le_add_of_nonneg_right (by simp)
      _ = 4*R := by ring
    have hbig : 2*C < ycoord t p := calc
      2*C ≤ 2*power (2*(a+2)) (2*R) := by
          rw [hC]; exact mul_le_mul_of_nonneg_left (ycoord_le_power a (2*R)) (by simp)
      _ < 4*power (2*(a+2)) (2*R) := mul_lt_mul_of_pos_right (by norm_num) hX
      _ ≤ power 2 (2*R)*power (2*(a+2)) (2*R) := mul_le_mul_of_nonneg_right h4 (by simp)
      _ = power (4*(a+2)) (2*R) := by
          rw [← power_mul_base, show (2 : V)*(2*(a+2)) = 4*(a+2) by ring]
      _ ≤ power (2*p+3) (2*R) := power_mono_base _ _ _ hpA
      _ ≤ power (2*p+3) (4*R) := power_mono_exponent _ _ _ (mr_one_le_odd p) h2R4
      _ ≤ ycoord (4*R+1) p := power_le_ycoord p (4*R)
      _ ≤ ycoord t p := (ordinate_strictMono p).monotone ht4
    rw [ht] at hbig
    exact absurd (lt_trans hKC hbig) (_root_.lt_irrefl _)

/-! ### Lemma 2.22 at base two (sufficiency) -/

/-- If `J = 4a+3 = 2AV − V² − 1` (with `V = 2`, `A = a+2`) divides `2(W²−1) − 3WC`, where
`C = ψ_A(B)`, and `W³ < A`, `(2^B)³ < A`, then `W = 2^B`. -/
theorem ratio_power_of_congruence (a B W C : V) (hW : 0 < W)
    (hE3 : Exp.exp B*Exp.exp B*Exp.exp B < a+2) (hW3 : W*W*W < a+2)
    (hC : C = ycoord B a)
    (hcong : (4*ι a+3 : DiffRing V) ∣ 2*(ι W^2-1) - 3*ι W*ι C) : W = Exp.exp B := by
  have hpc := ModelExponentialCongruence.pow_congruence a B
  rw [← hC] at hpc
  obtain ⟨E, hE⟩ : ∃ E, Exp.exp B = E := ⟨_, rfl⟩
  rw [hE] at hpc hE3
  rw [hE]
  have hE1 : 1 ≤ E := by rw [← hE]; exact one_le_exp B
  have hW1 : 1 ≤ W := pos_iff_one_le.mp hW
  have hEd : ι E*ι E*ι E+1 ≤ ι a+2 := by
    have h0 := ι_le_ι.mpr (lt_iff_succ_le.mp hE3)
    simpa only [map_add, map_mul, map_one, map_ofNat] using h0
  have hWd : ι W*ι W*ι W+1 ≤ ι a+2 := by
    have h0 := ι_le_ι.mpr (lt_iff_succ_le.mp hW3)
    simpa only [map_add, map_mul, map_one, map_ofNat] using h0
  have he1 : (1 : DiffRing V) ≤ ι E := by simpa only [map_one] using ι_le_ι.mpr hE1
  have hw1 : (1 : DiffRing V) ≤ ι W := by simpa only [map_one] using ι_le_ι.mpr hW1
  have ha0 : (0 : DiffRing V) ≤ ι a := ι_nonneg a
  have hd : (4*ι a+3 : DiffRing V) ∣ 2*(ι W - ι E)*(ι E*ι W+1) := by
    have key : (2*(ι W - ι E)*(ι E*ι W+1) : DiffRing V) =
        ι E*(2*(ι W^2-1) - 3*ι W*ι C) + ι W*(3*ι E*ι C - 2*(ι E^2-1)) := by ring
    rw [key]
    exact dvd_add (dvd_mul_of_dvd_right hcong _) (dvd_mul_of_dvd_right hpc _)
  have hq0 : (0 : DiffRing V) ≤ ι E*ι W+1 := by
    have := mul_nonneg (ι_nonneg E) (ι_nonneg W)
    linarith
  have hzero : (2*(ι W - ι E)*(ι E*ι W+1) : DiffRing V) = 0 := by
    apply eq_zero_of_dvd_small (by linarith) hd
    · rcases le_total (ι W) (ι E) with hle | hle
      · have hp := mul_nonneg (show (0 : DiffRing V) ≤ ι E - ι W by linarith) hq0
        linarith
      · have hb1 : (ι W - ι E)*(ι E*ι W+1) ≤ (ι W - 1)*(ι W*ι W+1) := by
          refine mul_le_mul ?_ ?_ hq0 ?_
          · linarith
          · have := mul_le_mul_of_nonneg_right hle (ι_nonneg W)
            linarith
          · linarith
        have hb2 : ι W ≤ ι W*ι W := le_mul_of_one_le_right (ι_nonneg W) hw1
        linarith
    · rcases le_total (ι W) (ι E) with hle | hle
      · have hb1 : (ι E - ι W)*(ι E*ι W+1) ≤ (ι E - 1)*(ι E*ι E+1) := by
          refine mul_le_mul ?_ ?_ hq0 ?_
          · linarith
          · have := mul_le_mul_of_nonneg_left hle (ι_nonneg E)
            linarith
          · linarith
        have hb2 : ι E ≤ ι E*ι E := le_mul_of_one_le_right (ι_nonneg E) he1
        linarith
      · have hp := mul_nonneg (show (0 : DiffRing V) ≤ ι W - ι E by linarith) hq0
        linarith
  have hq : (0 : DiffRing V) < ι E*ι W+1 := by
    have := mul_nonneg (ι_nonneg E) (ι_nonneg W)
    linarith
  rcases mul_eq_zero.mp hzero with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 (ne_of_gt (by norm_num : (0 : DiffRing V) < 2))
    · exact ι_injective (sub_eq_zero.mp h2)
  · exact absurd h1 hq.ne'

/-- The modulus `2AV' − V'² − 1` at `V' = 2`, `A = a + 2`. -/
theorem modulus_eq (A a V' : V) (ha : a+2 = A) (hV : V' = 2) :
    (2*ι A*ι V' - ι V'*ι V' - 1 : DiffRing V) = 4*ι a+3 := by
  rw [hV, ← ha]
  simp only [map_add, map_ofNat]
  ring

/-- The two sides of (B13) at `V' = 2`. -/
theorem numerator_eq (V' W C : V) (hV : V' = 2) :
    ι V'*(ι W^2-1) - (ι V'^2-1)*ι W*ι C = (2*(ι W^2-1) - 3*ι W*ι C : DiffRing V) := by
  rw [hV]
  simp only [map_ofNat]
  ring

/-! ### The ratio method, assembled -/

/-- Soundness of the ratio method: (B3) at the true Pell values gives `U^R ≤ 2Y`, and,
once `4·2^(2R) < U`, the central split `Y = C(2R,R) + U·w'`. -/
theorem ratio_sound (R Y U M A P a p : V) (hR : 8 ≤ R) (hY : 64 ≤ Y) (hU : 64 ≤ U)
    (hM : M = R*Y) (hA : A = M*(U+1)) (hP : P = 2*M*M*U) (ha : a+2 = A) (hp : p+2 = P)
    (hB3a : 2*ycoord (2*R+1) a < ycoord (R+1) p*(2*Y+1))
    (hB3b : 2*ycoord (R+1) p*Y < 2*ycoord (2*R+1) a+ycoord (R+1) p) :
    power U R ≤ 2*Y ∧ (4*Exp.exp (2*R) < U → ∃ w', Y = binom (2*R) R+U*w') := by
  obtain ⟨h1, h2, h3, h4, -, -, -, -⟩ := ratio_params R Y U M A P a p hR hY hU hM hA hP ha hp
  have hL := ratio_lower M U R a p (ha.trans hA) (hp.trans hP) h2
  have hUb := ratio_upper M U R a p (ha.trans hA) (hp.trans hP) h4
  have hKpos : 0 < ycoord (R+1) p := lt_of_lt_of_le (mr_pos_succ R) (time_le_y (R+1) p)
  have hUpos : 0 < U := lt_of_lt_of_le (by norm_num) hU
  have hD : 0 < power U R := power_pos U R hUpos
  have hDD : power U R*power U R ≤ power (U+1) (2*R) := by
    rw [← power_add, ← two_mul]
    exact power_mono_base U (U+1) (2*R) (le_add_of_nonneg_right (by simp))
  refine ⟨ratio_D_le (2*a+3) _ _ _ _ R Y (mr_pos_odd a) hKpos hD hL hB3a h2 hDD, ?_⟩
  intro hU4
  obtain ⟨v, w', hN, hv⟩ := central_split U R (le_trans (by norm_num) hU)
  have h4v : 4*v < power U R := by
    have h0 : U*(4*v) < U*power U R := calc
      U*(4*v) = 4*(U*v) := by ring
      _ ≤ 4*(Exp.exp (2*R)*power U R) := mul_le_mul_of_nonneg_left hv (by simp)
      _ = (4*Exp.exp (2*R))*power U R := by ring
      _ < U*power U R := mul_lt_mul_of_pos_right hU4 hD
    exact lt_of_mul_lt_mul_left h0 (by simp)
  refine ⟨w', le_antisymm ?_ ?_⟩
  · exact ratio_le_floor (2*p+3) _ _ _ _ R Y _ v (mr_pos_odd p) hKpos hD hUb hN h4v hB3b h3
  · exact ratio_floor_le (2*a+3) _ _ _ _ R Y _ (mr_pos_odd a) hKpos hD hL
      (by rw [hN]; exact le_add_of_nonneg_right (by simp)) hB3a h1

/-- Necessity of the ratio method: at `Y = Q = C(2R,R) + U·w'` (central split with
`8v < U^R`) the true Pell values satisfy `64|C − KQ| ≤ 25K`. -/
theorem ratio_construct (R Q U M A P a p v : V) (hR : 8 ≤ R) (hQ : 64 ≤ Q) (hU : 64 ≤ U)
    (hM : M = R*Q) (hA : A = M*(U+1)) (hP : P = 2*M*M*U) (ha : a+2 = A) (hp : p+2 = P)
    (hN : power (U+1) (2*R) = Q*power U R+v) (hv : 8*v < power U R) :
    64*ycoord (2*R+1) a ≤ (64*Q+25)*ycoord (R+1) p ∧
      64*ycoord (R+1) p*Q ≤ 64*ycoord (2*R+1) a+25*ycoord (R+1) p := by
  obtain ⟨-, h2, -, h4, -, -, h7, h8⟩ := ratio_params R Q U M A P a p hR hQ hU hM hA hP ha hp
  have hL := ratio_lower M U R a p (ha.trans hA) (hp.trans hP) h2
  have hUb := ratio_upper M U R a p (ha.trans hA) (hp.trans hP) h4
  have hKpos : 0 < ycoord (R+1) p := lt_of_lt_of_le (mr_pos_succ R) (time_le_y (R+1) p)
  have hD : 0 < power U R := power_pos U R (lt_of_lt_of_le (by norm_num) hU)
  have hup := ratio_construct_upper (2*p+3) _ _ _ _ R Q v (mr_pos_odd p) hKpos hD hUb hN hv h7
  exact ⟨hup, ratio_construct_lower (2*a+3) _ _ _ _ R Q (mr_pos_odd a) hKpos hD hL
    (by rw [hN]; exact le_add_of_nonneg_right (by simp)) hup h8⟩

end Model

end DiophantineConsistency.ModelRatio
