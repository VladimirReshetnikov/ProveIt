import DiophantineConsistency.ModelRatioBounds

/-! # Jones 1982, Lemma 2.25 inside every model of `𝗜𝚺₁`

Externally (`Diophantine.Paper1982.Ratio`, `Jones1982.lemma_2_25`) the lemma says: for
`R ≥ 8`, `N ≥ 8`, `b ≤ R`, `0 < b ≤ N`,

  `N² ∣ C(2R, R)` and `b` is a power of two

iff there are positive `h, s, w, φ` and `A, B', C, K, M, P, U, V, W, Y` with
(B1) `P = 2M²U`, (B2) `(P²−1)K² + 1 = □`, (B3) `4(C − KY)² < K²`,
(B4) `K = R + 1 + h(P − 1)`, (B5) `M = RY`, (B6) `A = M(U+1)`, (B7) `B' = 2R + 1`,
(B8) `C = B' + φ`, (B9) `U = N²w`, (B10) `Y = N²s`, (B11) `W = bw`, (B12) `V = 2`,
(B13) `(V²−1)WC ≡ V(W²−1) (mod 2AV − V² − 1)`, (B14) `C = ψ_A(B')`.

Here the same statement is proved in an arbitrary model `V` of `𝗜𝚺₁` (the model type is
`V`, so Jones's unknown `V` is called `V'`). Conventions:

* `ψ_A(n)` is the represented ordinate `ycoord n (A-2)` of `ArithmeticPellRecurrence`
  (base `A = a + 2`); `C(2R,R)` is `ArithmeticBinomPascal.binom (2*R) R`; `U^R` is the
  represented `ArithmeticPow.power U R`; `2^k` is `Exp.exp k`.
* (B2) is `∃ z, z*z = (P*P-1)*K*K+1` in `V`; (B4) uses truncated `P-1` (harmless, `P ≥ 2`).
* (B3) and the extra construction bound `4096(C−KY)² ≤ 625K²` are stated in the ring of
  differences `DiffRing V` (signs matter).
* (B13) is the integer divisibility `(2AV'−V'²−1) ∣ V'(W²−1) − (V'²−1)WC` in `DiffRing V`,
  i.e. the `ℤ`-form `Nat.modEq_iff_dvd` of the printed congruence.

## Replacing the real-number ratio argument (proved in `ModelRatioBounds`)

The external proof writes `ρ = (U+1)^(2R)/U^R`, `ε = R/A`, uses the real Pell bounds
`(2a)ⁿ(1 − n/(2a)) ≤ ψ_a(n+1) ≤ (2a)ⁿ` and the 1978 `core_estimate`
`|C − Kρ| ≤ 2Kρε`, and then `nearest_of_estimate`/`estimate_of_floor`. Here every real
inequality is cleared of denominators. With `α = 2A − 1 = 2a+3`, `π = 2P − 1 = 2p+3`,
`Nn = (U+1)^(2R)`, `D = U^R` and the exact identity `(2P)^R·Nn = (2A)^(2R)·D`
(`ratio_key_identity`), the represented growth bounds `power_le_ycoord`,
`ycoord_le_power` and the integer perturbation inequality `ArithmeticPow.perturbation`
(the integer Bernoulli bound) give the two sandwich inequalities

* `ratio_lower`: `α·K·Nn ≤ (α + 4R)·C·D`  (replaces `C ≥ Kρ(1 − 2ε)`);
* `ratio_upper`: `π·C·D ≤ (π + 2R)·K·Nn`  (replaces `C ≤ Kρ(1 + 2R/P)`).

Lemma 2.24 is the internal central split `ArithmeticBinomExpansion.central_split`:
`Nn = Q·D + v` with `Q = C(2R,R) + U·w'` and `U·v ≤ 2^(2R)·D`, so `c·v < D` once
`c·2^(2R) < U` (this replaces `rho_split_c`'s `0 ≤ f < 1/c`). Then:

* `ratio_floor_le` / `ratio_le_floor` (soundness, replace `nearest_of_estimate`):
  (B3) in the integer form `2C < K(2Y+1)`, `2KY < 2C + K` forces `Q = Y`;
* `ratio_D_le` (replaces `Y_lower`): `U^R ≤ 2Y`, whence `R·U^R < A`,
  `2^(6R+3) < A`, `W³ < A` (the article's (3)–(6));
* `ratio_construct_upper` / `ratio_construct_lower` (necessity, replace
  `estimate_of_floor`): `64C ≤ (64Q+25)K` and `64KQ ≤ 64C + 25K`, i.e.
  `64|C − KQ| ≤ 25K`, whence `4096(C−KQ)² ≤ 625K²` and (B3).

The index argument `ratio_K_index` uses the internal classification `solution_index`,
`residue_quotients` (`ψ_P(t) ≡ t mod P−1`) and a direct growth comparison instead of
`two_ψ_lt`. Lemma 2.22 is `ModelExponentialCongruence.pow_congruence` (necessity) and
`ratio_power_of_congruence` (sufficiency, by the exact-divisibility argument
`J ∣ 2(W − 2^B)(2^B·W + 1)` with `|2(W − 2^B)(2^B·W + 1)| < J`). The power-of-two divisor
step uses Foundation's `Pow2.of_dvd`.

No `Paper1982`/`Diophantine` module is imported (they need the Mathlib tactic umbrella,
which collides with Foundation). -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.ModelRatio

section Model
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPow ArithmeticPellRecurrence ArithmeticBinomPascal ArithmeticBinomExpansion
  ArithmeticHalfBinomialSandwich ModelDifferenceRing ModelArithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### The conditions (B1)–(B12), (B14) -/

/-- Conditions (B1)–(B12) and (B14) of Lemma 2.25 in a model. (B3) is stated in the ring
of differences; `ψ_A(B')` is `ycoord B' (A-2)`. -/
structure B25core (R N b h s w φ A B' C K M P U V' W Y : V) : Prop where
  B1 : P = 2*M*M*U
  B2 : ∃ z : V, z*z = (P*P-1)*K*K+1
  B3 : (4 : DiffRing V)*(ι C - ι K*ι Y)^2 < ι K^2
  B4 : K = R+1+h*(P-1)
  B5 : M = R*Y
  B6 : A = M*(U+1)
  B7 : B' = 2*R+1
  B8 : C = B'+φ
  B9 : U = N*N*w
  B10 : Y = N*N*s
  B11 : W = b*w
  B12 : V' = 2
  B14 : C = ycoord B' (A-2)

/-- The sizes implied by the initial conditions (`Jones1982.B25core.sizes`). -/
theorem B25core.sizes {R N b h s w φ A B' C K M P U V' W Y : V}
    (hR : 8 ≤ R) (hN : 8 ≤ N) (hs : 0 < s) (hw : 0 < w)
    (hB : B25core R N b h s w φ A B' C K M P U V' W Y) :
    64 ≤ U ∧ 64 ≤ Y ∧ 512 ≤ M ∧ 2 ≤ A ∧ 2 ≤ P ∧ 0 < B' ∧ B' ≤ C ∧ 0 < V' ∧ V' < A ∧
      0 < 2*A*V' - V'*V' - 1 := by
  have hNN : 64 ≤ N*N := calc
    (64 : V) = 8*8 := by norm_num
    _ ≤ N*N := mul_le_mul hN hN (by simp) (by simp)
  have hU : 64 ≤ U := by
    rw [hB.B9]; exact le_trans hNN (le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hw))
  have hY : 64 ≤ Y := by
    rw [hB.B10]; exact le_trans hNN (le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hs))
  obtain ⟨hM, -, hA2, hP2⟩ := basic_sizes R Y U M A P hR hY hU hB.B5 hB.B6 hB.B1
  have hA512 : 512 ≤ A := le_trans hM (by
    rw [hB.B6]; exact le_mul_of_one_le_right (by simp) (le_add_of_nonneg_left (by simp)))
  refine ⟨hU, hY, hM, hA2, hP2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hB.B7]; exact lt_of_lt_of_le (by simp : (0 : V) < 1) (le_add_of_nonneg_left (by simp))
  · rw [hB.B8]; exact le_add_of_nonneg_right (by simp)
  · rw [hB.B12]; simp
  · rw [hB.B12]; exact lt_of_lt_of_le (by norm_num) hA512
  · rw [hB.B12]
    apply tsub_pos_of_lt
    apply lt_tsub_iff_right.mpr
    calc (1 : V)+2*2 < 2*512*2 := by norm_num
      _ ≤ 2*A*2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA512 (by simp)) (by simp)

/-- The sufficiency part of Lemma 2.25, first half (the article's (3)–(6)): the Pell
values are the true ones, `U^R ≤ 2Y` (in place of `U^(R−1) < Y`), and the sizes
`R·U^R < A`, `2^(6R+3) < A`, `W³ < A`. -/
theorem B25core.core {R N b h s w φ A B' C K M P U V' W Y : V}
    (hR : 8 ≤ R) (hN : 8 ≤ N) (hbN : b ≤ N) (hs : 0 < s) (hw : 0 < w)
    (hB : B25core R N b h s w φ A B' C K M P U V' W Y) :
    C = ycoord (2*R+1) (A-2) ∧ K = ycoord (R+1) (P-2) ∧ power U R ≤ 2*Y ∧
      R*power U R < A ∧ Exp.exp (6*R+3) < A ∧ W*W*W < A := by
  obtain ⟨hU, hY, hM512, hA2, hP2, -⟩ := hB.sizes hR hN hs hw
  have ha : A-2+2 = A := tsub_add_cancel_of_le hA2
  have hp : P-2+2 = P := tsub_add_cancel_of_le hP2
  have hR1 : 1 ≤ R := le_trans (by norm_num) hR
  have hC : C = ycoord (2*R+1) (A-2) := by rw [hB.B14, hB.B7]
  obtain ⟨-, -, -, -, h5, h6, -, -⟩ :=
    ratio_params R Y U M A P (A-2) (P-2) hR hY hU hB.B5 hB.B6 hB.B1 ha hp
  obtain ⟨hB3a, hB3b⟩ := B3_bounds C K Y hB.B3
  have hY1 : 1 ≤ Y := le_trans (by norm_num) hY
  have hKC : K < 2*C := by
    have h1 : K+K < 2*C+K := calc
      K+K = 2*K*1 := by ring
      _ ≤ 2*K*Y := mul_le_mul_of_nonneg_left hY1 (by simp)
      _ < 2*C+K := hB3b
    exact (add_lt_add_iff_right K).mp h1
  obtain ⟨z, hz⟩ := hB.B2
  have ePP : P*P-1 = delta (P-2) := by rw [← sq_sub_one_eq_delta (P-2), hp]
  have hz' : z*z = 1+delta (P-2)*K*K := by rw [hz, ePP]; exact add_comm _ _
  have e1 : P-1 = P-2+1 := by
    have h0 := sub_one_of_add_two (P-2)
    rwa [hp] at h0
  have hB4 : K = R+1+h*(P-2+1) := by rw [hB.B4, e1]
  have hK : K = ycoord (R+1) (P-2) :=
    ratio_K_index R (A-2) (P-2) K C z h hR1 h5 h6 hC hz' hB4 hKC
  rw [hC, hK] at hB3a hB3b
  obtain ⟨hDY, -⟩ :=
    ratio_sound R Y U M A P (A-2) (P-2) hR hY hU hB.B5 hB.B6 hB.B1 ha hp hB3a hB3b
  refine ⟨hC, hK, hDY, ?_⟩
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM512
  have hRD : R*power U R < A := calc
    R*power U R ≤ R*(2*Y) := mul_le_mul_of_nonneg_left hDY (by simp)
    _ = M*2 := by rw [hB.B5]; ring
    _ < M*(U+1) :=
        mul_lt_mul_of_pos_left
          (lt_of_lt_of_le (by norm_num : (2 : V) < 64+1) (add_le_add hU le_rfl)) hMpos
    _ = A := hB.B6.symm
  have hexp : Exp.exp (6*R+3) < A := by
    rw [exp_six_eq R]
    calc 8*power 64 R ≤ 8*power U R :=
          mul_le_mul_of_nonneg_left (power_mono_base 64 U R hU) (by simp)
      _ ≤ R*power U R := mul_le_mul_of_nonneg_right hR (by simp)
      _ < A := hRD
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have hWU : W ≤ U := by
    rw [hB.B11, hB.B9]
    exact mul_le_mul_of_nonneg_right
      (le_trans hbN (le_mul_of_one_le_right (by simp) hN1)) (by simp)
  have hW3 : W*W*W < A := calc
    W*W*W ≤ U*U*U := mul_le_mul (mul_le_mul hWU hWU (by simp) (by simp)) hWU (by simp) (by simp)
    _ = power U 3 := (ratio_power_three U).symm
    _ ≤ power U R :=
        power_mono_exponent U 3 R (le_trans (by norm_num) hU) (le_trans (by norm_num) hR)
    _ ≤ R*power U R := le_mul_of_one_le_left (by simp) hR1
    _ < A := hRD
  exact ⟨hRD, hexp, hW3⟩

/-- The sufficiency part of Lemma 2.25, second half: given `W = 2^(2R+1)` (from
Lemma 2.22), `N² ∣ C(2R,R)` and `b` is a power of two (the article's (7)–(9)). -/
theorem B25core.dvd {R N b h s w φ A B' C K M P U V' W Y : V}
    (hR : 8 ≤ R) (hN : 8 ≤ N) (hbN : b ≤ N) (hs : 0 < s) (hw : 0 < w)
    (hB : B25core R N b h s w φ A B' C K M P U V' W Y) (hW : W = Exp.exp (2*R+1)) :
    N*N ∣ binom (2*R) R ∧ ∃ k, b = Exp.exp k := by
  obtain ⟨hU, hY, -, hA2, hP2, -⟩ := hB.sizes hR hN hs hw
  obtain ⟨hC, hK, -⟩ := hB.core hR hN hbN hs hw
  have hbpow : ∃ k, b = Exp.exp k := by
    have hd : b ∣ Exp.exp (2*R+1) := ⟨w, by rw [← hW, hB.B11]⟩
    exact ⟨_, (exp_of_exponential (exponential_of_pow2 (Pow2.of_dvd hd (exp_pow2 _)))).symm⟩
  refine ⟨?_, hbpow⟩
  have ha : A-2+2 = A := tsub_add_cancel_of_le hA2
  have hp : P-2+2 = P := tsub_add_cancel_of_le hP2
  obtain ⟨hB3a, hB3b⟩ := B3_bounds C K Y hB.B3
  rw [hC, hK] at hB3a hB3b
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have h8b : 8*b ≤ N*N := mul_le_mul hN hbN (by simp) (by simp)
  have hU4 : 4*Exp.exp (2*R) < U := calc
    4*Exp.exp (2*R) < 16*Exp.exp (2*R) := mul_lt_mul_of_pos_right (by norm_num) (exp_pos _)
    _ = 8*W := by rw [hW, exp_succ]; ring
    _ = (8*b)*w := by rw [hB.B11]; ring
    _ ≤ N*N*w := mul_le_mul_of_nonneg_right h8b (by simp)
    _ = U := hB.B9.symm
  obtain ⟨-, hsplit⟩ :=
    ratio_sound R Y U M A P (A-2) (P-2) hR hY hU hB.B5 hB.B6 hB.B1 ha hp hB3a hB3b
  obtain ⟨w', hYQ⟩ := hsplit hU4
  have hNpos : 0 < N*N :=
    mul_pos (lt_of_lt_of_le (by simp) hN1) (lt_of_lt_of_le (by simp) hN1)
  have h1 : N*N ∣ binom (2*R) R+U*w' := ⟨s, by rw [← hYQ, hB.B10]⟩
  have h2 : N*N ∣ U*w' := ⟨w*w', by rw [hB.B9]; ring⟩
  exact dvd_of_add_dvd hNpos h1 h2

/-! ### Necessity -/

/-- The necessity part of Lemma 2.25 (`Jones1982.exists_B25core`): from `N² ∣ C(2R,R)` and
`b = 2^k` all quantities of (B1)–(B12), (B14) exist, with `W = 2^(2R+1)`, `B' + W < C`
and the sharper `4096(C − KY)² ≤ 625K²`. -/
theorem exists_B25core (R N b : V) (hR : 8 ≤ R) (hN : 8 ≤ N) (hbR : b ≤ R) (hb : 0 < b)
    (hbN : b ≤ N) (hdvd : N*N ∣ binom (2*R) R) (hpow : ∃ k, b = Exp.exp k) :
    ∃ h s w φ A B' C K M P U V' W Y : V, 0 < h ∧ 0 < s ∧ 0 < w ∧ 0 < φ ∧
      B25core R N b h s w φ A B' C K M P U V' W Y ∧ W = Exp.exp (2*R+1) ∧ B'+W < C ∧
      (4096 : DiffRing V)*(ι C - ι K*ι Y)^2 ≤ 625*ι K^2 := by
  obtain ⟨k, hk⟩ := hpow
  have hR1 : 1 ≤ R := le_trans (by norm_num) hR
  have hRle : R ≤ 2*R+1 := calc
    R ≤ R+(R+1) := le_add_of_nonneg_right (by simp)
    _ = 2*R+1 := by ring
  have hk' : k ≤ 2*R+1 := by
    by_contra hlt
    have h1 : 2*R+1 < k := lt_of_not_ge hlt
    have h2 : Exp.exp (2*R+1) ≤ b := by rw [hk]; exact exp_monotone_le.mpr h1.le
    have h3 : b < Exp.exp (2*R+1) :=
      lt_of_le_of_lt hbR (lt_of_lt_of_le (lt_exp R) (exp_monotone_le.mpr hRle))
    exact absurd h2 (not_le.mpr h3)
  obtain ⟨w, hw⟩ : ∃ w, w = Exp.exp (2*R+1-k) := ⟨_, rfl⟩
  have hw0 : 0 < w := by rw [hw]; exact exp_pos _
  have hbw : b*w = Exp.exp (2*R+1) := by
    rw [hk, hw, ← exp_add, add_tsub_cancel_of_le hk']
  have hNN : 64 ≤ N*N := calc
    (64 : V) = 8*8 := by norm_num
    _ ≤ N*N := mul_le_mul hN hN (by simp) (by simp)
  have h8b : 8*b ≤ N*N := mul_le_mul hN hbN (by simp) (by simp)
  obtain ⟨U, hU⟩ : ∃ U, U = N*N*w := ⟨_, rfl⟩
  have hU16 : 16*Exp.exp (2*R) ≤ U := calc
    16*Exp.exp (2*R) = 8*(b*w) := by rw [hbw, exp_succ]; ring
    _ = (8*b)*w := by ring
    _ ≤ N*N*w := mul_le_mul_of_nonneg_right h8b (by simp)
    _ = U := hU.symm
  have hU64 : 64 ≤ U := by
    rw [hU]; exact le_trans hNN (le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hw0))
  have hU1 : 1 ≤ U := le_trans (by norm_num) hU64
  have hD : 0 < power U R := power_pos U R (lt_of_lt_of_le (by simp) hU1)
  obtain ⟨v, w', hsplit, hv⟩ := central_split U R hU1
  have hv8 : 8*v < power U R := by
    have h1 : U*(8*v) < U*power U R := calc
      U*(8*v) = 8*(U*v) := by ring
      _ ≤ 8*(Exp.exp (2*R)*power U R) := mul_le_mul_of_nonneg_left hv (by simp)
      _ < 16*(Exp.exp (2*R)*power U R) :=
          mul_lt_mul_of_pos_right (by norm_num) (mul_pos (exp_pos _) hD)
      _ = (16*Exp.exp (2*R))*power U R := by ring
      _ ≤ U*power U R := mul_le_mul_of_nonneg_right hU16 (by simp)
    exact lt_of_mul_lt_mul_left h1 (by simp)
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = binom (2*R) R+U*w' := ⟨_, rfl⟩
  have hNQ : N*N ∣ Q := by
    rw [hQ]; exact dvd_add hdvd ⟨w*w', by rw [hU]; ring⟩
  obtain ⟨s, hs⟩ := hNQ
  have hR2R : R ≤ 2*R := calc
    R ≤ R+R := le_add_of_nonneg_right (by simp)
    _ = 2*R := (two_mul R).symm
  have hQpos : 0 < Q := by
    rw [hQ]
    exact lt_of_lt_of_le (binom_pos (2*R) R hR2R) (le_add_of_nonneg_right (by simp))
  have hs0 : 0 < s := pos_of_mul_pos_right (show 0 < N*N*s by rw [← hs]; exact hQpos) (by simp)
  have hQ64 : 64 ≤ Q := by
    rw [hs]; exact le_trans hNN (le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hs0))
  obtain ⟨M, hM⟩ : ∃ M, M = R*Q := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = M*(U+1) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = 2*M*M*U := ⟨_, rfl⟩
  obtain ⟨-, hUA, hA2, hP2⟩ := basic_sizes R Q U M A P hR hQ64 hU64 hM hA hP
  have ha : A-2+2 = A := tsub_add_cancel_of_le hA2
  have hp : P-2+2 = P := tsub_add_cancel_of_le hP2
  obtain ⟨-, -, -, -, h5, -, -, -⟩ :=
    ratio_params R Q U M A P (A-2) (P-2) hR hQ64 hU64 hM hA hP ha hp
  have hN' : power (U+1) (2*R) = Q*power U R+v := by rw [hsplit, hQ]
  obtain ⟨hc1, hc2⟩ :=
    ratio_construct R Q U M A P (A-2) (P-2) v hR hQ64 hU64 hM hA hP ha hp hN' hv8
  have hKpos : 0 < ycoord (R+1) (P-2) :=
    lt_of_lt_of_le (mr_pos_succ R) (time_le_y (R+1) (P-2))
  obtain ⟨hB3s, hB3⟩ :=
    B3_of_bounds (ycoord (2*R+1) (A-2)) (ycoord (R+1) (P-2)) Q hKpos hc1 hc2
  -- (B4): `ψ_P(R+1) ≡ R+1 (mod P−1)` with a positive quotient
  obtain ⟨-, h, -, hKh⟩ :=
    ArithmeticPellCongruences.residue_quotients (R+1) (P-2) (P-2+1) (dvd_refl _)
  have e1 : P-1 = P-2+1 := by
    have h0 := sub_one_of_add_two (P-2)
    rwa [hp] at h0
  have hB4 : ycoord (R+1) (P-2) = R+1+h*(P-1) := by
    rw [hKh, e1, mul_comm (P-2+1) h]
  have hK2p : 2*(P-2)+3 ≤ ycoord (R+1) (P-2) := calc
    2*(P-2)+3 = power (2*(P-2)+3) 1 := (power_one _).symm
    _ ≤ power (2*(P-2)+3) R := power_mono_exponent _ 1 R (mr_one_le_odd _) hR1
    _ ≤ ycoord (R+1) (P-2) := power_le_ycoord (P-2) R
  have hR3 : R ≤ 3*R := calc
    R ≤ R+2*R := le_add_of_nonneg_right (by simp)
    _ = 3*R := by ring
  have hR1p : R+1 < 2*(P-2)+3 := calc
    R+1 ≤ 3*R+1 := add_le_add hR3 le_rfl
    _ ≤ P-2+1 := h5
    _ < 2*(P-2)+3 := mr_succ_lt_odd _
  have hh0 : 0 < h := by
    apply pos_iff_ne_zero.mpr
    intro h0
    rw [h0, mul_zero, add_zero] at hKh
    have hlt := lt_of_lt_of_le hR1p hK2p
    rw [hKh] at hlt
    exact absurd hlt (_root_.lt_irrefl _)
  -- `C > B' + W`
  have hE := exp_pos (2*R)
  have hC1 : 2*R+1 ≤ Exp.exp (2*R) := lt_iff_succ_le.mp (lt_exp (2*R))
  have hUa : U < 2*(A-2)+3 := by
    have h0 : U+1 ≤ A-2+1+1 := by rw [mr_add_one_add_one, ha]; exact hUA
    have hU' : U ≤ A-2+1 := (add_le_add_iff_right (1 : V)).mp h0
    exact lt_of_le_of_lt hU' (mr_succ_lt_odd _)
  have hR2 : 1 ≤ 2*R := le_trans hR1 hR2R
  have hCa : 2*(A-2)+3 ≤ ycoord (2*R+1) (A-2) := calc
    2*(A-2)+3 = power (2*(A-2)+3) 1 := (power_one _).symm
    _ ≤ power (2*(A-2)+3) (2*R) := power_mono_exponent _ 1 (2*R) (mr_one_le_odd _) hR2
    _ ≤ ycoord (2*R+1) (A-2) := power_le_ycoord (A-2) (2*R)
  have hCbig : 2*R+1+Exp.exp (2*R+1) < ycoord (2*R+1) (A-2) := calc
    2*R+1+Exp.exp (2*R+1) = 2*R+1+2*Exp.exp (2*R) := by rw [exp_succ]
    _ ≤ Exp.exp (2*R)+2*Exp.exp (2*R) := add_le_add hC1 le_rfl
    _ = 3*Exp.exp (2*R) := by ring
    _ < 16*Exp.exp (2*R) := mul_lt_mul_of_pos_right (by norm_num) hE
    _ ≤ U := hU16
    _ < 2*(A-2)+3 := hUa
    _ ≤ ycoord (2*R+1) (A-2) := hCa
  have hCle : 2*R+1 ≤ ycoord (2*R+1) (A-2) :=
    le_of_lt (lt_of_le_of_lt (le_add_of_nonneg_right (by simp)) hCbig)
  have ePP : P*P-1 = delta (P-2) := by rw [← sq_sub_one_eq_delta (P-2), hp]
  refine ⟨h, s, w, ycoord (2*R+1) (A-2) - (2*R+1), A, 2*R+1, ycoord (2*R+1) (A-2),
    ycoord (R+1) (P-2), M, P, U, 2, b*w, Q, hh0, hs0, hw0,
    tsub_pos_of_lt (lt_of_le_of_lt (le_add_of_nonneg_right (by simp)) hCbig),
    ⟨hP, ⟨xcoord (R+1) (P-2), ?_⟩, hB3, hB4, hM, hA, rfl, (add_tsub_cancel_of_le hCle).symm,
      hU, hs, rfl, rfl, rfl⟩,
    hbw, by rw [hbw]; exact hCbig, hB3s⟩
  rw [ArithmeticPellRecurrence.norm, ePP]
  exact add_comm _ _

/-! ### Lemma 2.25 -/

/-- **Lemma 2.25** in every model of `𝗜𝚺₁`, with (B13) as the integer divisibility
`(2AV' − V'² − 1) ∣ V'(W² − 1) − (V'² − 1)WC` in `DiffRing V`. -/
theorem lemma_2_25 (R N b : V) (hR : 8 ≤ R) (hN : 8 ≤ N) (hbR : b ≤ R) (hb : 0 < b)
    (hbN : b ≤ N) :
    (N*N ∣ binom (2*R) R ∧ ∃ k, b = Exp.exp k) ↔
      ∃ h s w φ A B' C K M P U V' W Y : V, 0 < h ∧ 0 < s ∧ 0 < w ∧ 0 < φ ∧
        B25core R N b h s w φ A B' C K M P U V' W Y ∧
        (2*ι A*ι V' - ι V'*ι V' - 1 : DiffRing V) ∣
          ι V'*(ι W^2-1) - (ι V'^2-1)*ι W*ι C := by
  constructor
  · rintro ⟨hdvd, hpow⟩
    obtain ⟨h, s, w, φ, A, B', C, K, M, P, U, V', W, Y, hh, hs, hw, hφ, hB, hW, -, -⟩ :=
      exists_B25core R N b hR hN hbR hb hbN hdvd hpow
    refine ⟨h, s, w, φ, A, B', C, K, M, P, U, V', W, Y, hh, hs, hw, hφ, hB, ?_⟩
    obtain ⟨-, -, -, hA2, -⟩ := hB.sizes hR hN hs hw
    have ha : A-2+2 = A := tsub_add_cancel_of_le hA2
    have hC : C = ycoord (2*R+1) (A-2) := by rw [hB.B14, hB.B7]
    rw [modulus_eq A (A-2) V' ha hB.B12, numerator_eq V' W C hB.B12, hW, hC]
    exact dvd_sub_comm.mp (ModelExponentialCongruence.pow_congruence (A-2) (2*R+1))
  · rintro ⟨h, s, w, φ, A, B', C, K, M, P, U, V', W, Y, hh, hs, hw, hφ, hB, hB13⟩
    obtain ⟨-, -, -, hA2, -⟩ := hB.sizes hR hN hs hw
    have ha : A-2+2 = A := tsub_add_cancel_of_le hA2
    obtain ⟨hC, -, -, -, hexp, hW3⟩ := hB.core hR hN hbN hs hw
    rw [modulus_eq A (A-2) V' ha hB.B12, numerator_eq V' W C hB.B12] at hB13
    have hW0 : 0 < W := by rw [hB.B11]; exact mul_pos hb hw
    have hE3 : Exp.exp (2*R+1)*Exp.exp (2*R+1)*Exp.exp (2*R+1) < A-2+2 := by
      rw [← exp_add, ← exp_add, show 2*R+1+(2*R+1)+(2*R+1) = 6*R+3 by ring, ha]
      exact hexp
    have hW := ratio_power_of_congruence (A-2) (2*R+1) W C hW0 hE3
      (by rw [ha]; exact hW3) hC hB13
    exact hB.dvd hR hN hbN hs hw hW

end Model

end DiophantineConsistency.ModelRatio
