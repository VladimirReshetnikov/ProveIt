import DiophantineConsistency.ModelRatio

/-! # Ten-integer package 106: the positive ratio bridge

Completeness step C5 of the route, natural-number part. Given a rank `Xn ≥ 8`,
a base `2^(2s)` with `2s ≤ 2 Xn + 1`, a low word `g > 0` and a modulus
`Yn ≥ 64`, `Yn ≥ 2^(2s)` with `Yn ∣ C(2 Xn, Xn)`, the theorem `bridge` chooses
`l, w > 0` and Pell parameters `a, pp` with

* `2^(2s) · w = 2^(2 Xn + 1)`;
* `a + 2 = Xn · (l Yn) · (4 g w Yn + 1)` (the register `halfA`);
* `pp + 2 = 2 · (Xn l Yn)² · (4 g w Yn)` (the register `Phalf`);
* `16 g² (C − K · l Yn)² ≤ K²` for `C = ψ_a(2 Xn + 1)`, `K = ψ_pp(Xn + 1)`.

The last line is the hypothesis `he` of `Z10Guard.guard_complete`. It is the
`g`-parametric form of the approximation (B3) of Jones's Lemma 2.25: the
library version `ModelRatio.B3_of_bounds` has the fixed constant `4` in place
of `16 g²`. The two generic ratio estimates `ModelRatio.ratio_lower` and
`ModelRatio.ratio_upper` are reused unchanged; the absorption of the error
terms is redone with a free scale `G = 4 g`, in the ring of differences
(`upper_bound`, `lower_bound`, `two_sided`). The factor `g` in
`U = 4 g w Yn` is what leaves room for the scale.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Z10Ratio
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ModelDifferenceRing
open ArithmeticPow ArithmeticPellRecurrence ArithmeticBinomPascal ArithmeticBinomExpansion
open ModelRatio

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Absorbing the error terms at scale `G` -/

/-- The upper half: from the ratio estimate `π C D ≤ (π + 2R) K (Q D + v)` with a small
remainder `2 G v ≤ D` and a large `π`, the scaled bound `G C ≤ (G Q + 1) K`. -/
theorem upper_bound (π K C D R Q v G : DiffRing V) (hπ0 : 0 < π) (hD : 0 < D) (hK : 0 ≤ K)
    (hG : 0 ≤ G) (hR : 0 ≤ R) (hU : π * C * D ≤ (π + 2 * R) * K * (Q * D + v))
    (hv : 2 * G * v ≤ D) (hπ : 4 * R * G * Q + 2 * R ≤ π) :
    G * C ≤ (G * Q + 1) * K := by
  have a1 : 0 ≤ D - 2 * G * v := _root_.sub_nonneg.mpr hv
  have a2 : 0 ≤ π - (4 * R * G * Q + 2 * R) := _root_.sub_nonneg.mpr hπ
  have a3 : 0 ≤ 2 * R := by linarith
  have key : 0 ≤ K * (π * (D - 2 * G * v) + D * (π - (4 * R * G * Q + 2 * R))
      + 2 * R * (D - 2 * G * v)) :=
    _root_.mul_nonneg hK (_root_.add_nonneg (_root_.add_nonneg (_root_.mul_nonneg hπ0.le a1)
      (_root_.mul_nonneg hD.le a2)) (_root_.mul_nonneg a3 a1))
  have h1 := mul_le_mul_of_nonneg_left hU hG
  have h2 : G * C * (π * D) ≤ (G * Q + 1) * K * (π * D) := by linarith
  exact le_of_mul_le_mul_right h2 (_root_.mul_pos hπ0 hD)

/-- The lower half: from the ratio estimate `α K N ≤ (α + 4R) C D` with `Q D ≤ N`, the upper
half and a large `α`, the scaled bound `G K Q ≤ G C + K`. -/
theorem lower_bound (α K C D R Q N G : DiffRing V) (hα0 : 0 < α) (hD : 0 < D) (hK : 0 ≤ K)
    (hG : 0 ≤ G) (hR : 0 ≤ R) (hL : α * K * N ≤ (α + 4 * R) * C * D) (hQ : Q * D ≤ N)
    (hup : G * C ≤ (G * Q + 1) * K) (hα : 4 * R * (G * Q + 1) ≤ α) :
    G * K * Q ≤ G * C + K := by
  have h0 := mul_le_mul_of_nonneg_left hQ (_root_.mul_nonneg hα0.le hK)
  have h1 : α * K * Q * D ≤ (α + 4 * R) * C * D := by linarith
  have h1' := le_of_mul_le_mul_right h1 hD
  have a3 : 0 ≤ 4 * R := by linarith
  have h2 := mul_le_mul_of_nonneg_left h1' hG
  have h3 := mul_le_mul_of_nonneg_left hup a3
  have h4 := mul_le_mul_of_nonneg_right hα hK
  have h5 : α * (G * K * Q) ≤ α * (G * C + K) := by linarith
  exact le_of_mul_le_mul_left h5 hα0

/-- The two one-sided bounds at scale `4 g` give `16 g² (C − K Q)² ≤ K²`. -/
theorem two_sided (g C K Q : DiffRing V) (hup : 4 * g * C ≤ (4 * g * Q + 1) * K)
    (hlo : 4 * g * K * Q ≤ 4 * g * C + K) :
    16 * (g * g) * ((C - K * Q) * (C - K * Q)) ≤ K * K := by
  have h1 : 0 ≤ K - 4 * g * (C - K * Q) := by linarith
  have h2 : 0 ≤ K + 4 * g * (C - K * Q) := by linarith
  have h3 := _root_.mul_nonneg h1 h2
  linarith

/-! ### The construction -/

/-- **The positive ratio bridge.** From `Yn ∣ C(2 Xn, Xn)` the multipliers `l, w` and the
Pell parameters of the registers `halfA`, `Phalf`, with the `g`-parametric approximation. -/
theorem bridge (s g Xn Yn : V) (hg : 0 < g) (hX8 : 8 ≤ Xn) (hs : 2 * s ≤ 2 * Xn + 1)
    (hY64 : 64 ≤ Yn) (hbY : Exp.exp (2 * s) ≤ Yn) (hdvd : Yn ∣ binom (2 * Xn) Xn) :
    ∃ l w a pp : V, 0 < l ∧ 0 < w ∧ Exp.exp (2 * s) * w = Exp.exp (2 * Xn + 1) ∧
      a + 2 = Xn * (l * Yn) * (4 * g * w * Yn + 1) ∧
      pp + 2 = 2 * (Xn * (l * Yn)) * (Xn * (l * Yn)) * (4 * g * w * Yn) ∧
      16 * (ι g * ι g) *
          ((ι (ycoord (2 * Xn + 1) a) - ι (ycoord (Xn + 1) pp) * (ι l * ι Yn)) *
            (ι (ycoord (2 * Xn + 1) a) - ι (ycoord (Xn + 1) pp) * (ι l * ι Yn))) ≤
        ι (ycoord (Xn + 1) pp) * ι (ycoord (Xn + 1) pp) := by
  -- the cofactor of the base
  obtain ⟨w, hw⟩ : ∃ w, w = Exp.exp (2 * Xn + 1 - 2 * s) := ⟨_, rfl⟩
  have hw0 : 0 < w := by rw [hw]; exact exp_pos _
  have hw1 : 1 ≤ w := pos_iff_one_le.mp hw0
  have hg1 : 1 ≤ g := pos_iff_one_le.mp hg
  have hbw : Exp.exp (2 * s) * w = Exp.exp (2 * Xn + 1) := by
    rw [hw, ← exp_add, add_tsub_cancel_of_le hs]
  -- the scale `U = 4 g w Yn`
  obtain ⟨U, hU⟩ : ∃ U, U = 4 * g * w * Yn := ⟨_, rfl⟩
  have hU8 : 8 * g * Exp.exp (2 * Xn) ≤ U := calc
    8 * g * Exp.exp (2 * Xn) = 4 * g * w * Exp.exp (2 * s) := by
      rw [show 4 * g * w * Exp.exp (2 * s) = 4 * g * (Exp.exp (2 * s) * w) by ring, hbw,
        exp_succ]
      ring
    _ ≤ 4 * g * w * Yn := mul_le_mul_of_nonneg_left hbY (by simp)
    _ = U := hU.symm
  have hU16 : 16 * g ≤ U := calc
    16 * g = 4 * g * 1 * 4 := by ring
    _ ≤ 4 * g * w * Yn :=
        mul_le_mul (mul_le_mul le_rfl hw1 (by simp) (by simp)) (le_trans (by norm_num) hY64)
          (by simp) (by simp)
    _ = U := hU.symm
  have h4gw : 1 ≤ 4 * g * w := calc
    (1 : V) = 1 * 1 * 1 := by norm_num
    _ ≤ 4 * g * w :=
        mul_le_mul (mul_le_mul (by norm_num) hg1 (by simp) (by simp)) hw1 (by simp) (by simp)
  have hU64 : 64 ≤ U := by
    rw [hU]; exact le_trans hY64 (le_mul_of_one_le_left (by simp) h4gw)
  have hU1 : 1 ≤ U := le_trans (by norm_num) hU64
  have hD : 0 < power U Xn := power_pos U Xn (lt_of_lt_of_le (by simp) hU1)
  -- the central binomial coefficient inside `(U + 1)^(2 Xn)`
  obtain ⟨v, w', hsplit, hv⟩ := central_split U Xn hU1
  have hvD : 8 * g * v ≤ power U Xn := by
    have h1 : Exp.exp (2 * Xn) * (8 * g * v) ≤ Exp.exp (2 * Xn) * power U Xn := calc
      Exp.exp (2 * Xn) * (8 * g * v) = 8 * g * Exp.exp (2 * Xn) * v := by ring
      _ ≤ U * v := mul_le_mul_of_nonneg_right hU8 (by simp)
      _ ≤ Exp.exp (2 * Xn) * power U Xn := hv
    exact le_of_mul_le_mul_left h1 (exp_pos _)
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = binom (2 * Xn) Xn + U * w' := ⟨_, rfl⟩
  have hYQ : Yn ∣ Q := by
    rw [hQ]; exact dvd_add hdvd ⟨4 * g * w * w', by rw [hU]; ring⟩
  obtain ⟨l, hl⟩ := hYQ
  have hQl : Q = l * Yn := by rw [hl, mul_comm]
  have hX2X : Xn ≤ 2 * Xn := calc
    Xn ≤ Xn + Xn := le_add_of_nonneg_right (by simp)
    _ = 2 * Xn := (two_mul Xn).symm
  have hQpos : 0 < Q := by
    rw [hQ]
    exact lt_of_lt_of_le (binom_pos (2 * Xn) Xn hX2X) (le_add_of_nonneg_right (by simp))
  have hl0 : 0 < l :=
    pos_of_mul_pos_right (show 0 < Yn * l by rw [← hl]; exact hQpos) (by simp)
  have hQ64 : 64 ≤ Q := by
    rw [hl]; exact le_trans hY64 (le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hl0))
  -- the Pell parameters
  obtain ⟨M, hM⟩ : ∃ M, M = Xn * Q := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = M * (U + 1) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = 2 * M * M * U := ⟨_, rfl⟩
  obtain ⟨hM512, -, hA2, hP2⟩ := basic_sizes Xn Q U M A P hX8 hQ64 hU64 hM hA hP
  have ha : A - 2 + 2 = A := tsub_add_cancel_of_le hA2
  have hp : P - 2 + 2 = P := tsub_add_cancel_of_le hP2
  obtain ⟨-, hRa, -, hRp, -, -, -, -⟩ :=
    ratio_params Xn Q U M A P (A - 2) (P - 2) hX8 hQ64 hU64 hM hA hP ha hp
  have hN' : power (U + 1) (2 * Xn) = Q * power U Xn + v := by rw [hsplit, hQ]
  have hlo := ratio_lower M U Xn (A - 2) (P - 2) (ha.trans hA) (hp.trans hP) hRa
  have hup := ratio_upper M U Xn (A - 2) (P - 2) (ha.trans hA) (hp.trans hP) hRp
  rw [hN'] at hlo hup
  -- transfer to the ring of differences
  have hlo' := ι_le_ι.mpr hlo
  have hup' := ι_le_ι.mpr hup
  simp only [map_mul, map_add, map_ofNat] at hlo' hup'
  have hMι : ι M = ι Xn * ι Q := by rw [hM, map_mul]
  have hPι : ι (P - 2) + 2 = 2 * ι M * ι M * ι U := by
    have h := congrArg (ι (V := V)) (hp.trans hP)
    simpa only [map_add, map_mul, map_ofNat] using h
  have hAι : ι (A - 2) + 2 = ι M * (ι U + 1) := by
    have h := congrArg (ι (V := V)) (ha.trans hA)
    simpa only [map_add, map_mul, map_one, map_ofNat] using h
  have hM512ι : (512 : DiffRing V) ≤ ι M := by
    have h := ι_le_ι.mpr hM512
    simpa only [map_ofNat] using h
  have hQ64ι : (64 : DiffRing V) ≤ ι Q := by
    have h := ι_le_ι.mpr hQ64
    simpa only [map_ofNat] using h
  have hU64ι : (64 : DiffRing V) ≤ ι U := by
    have h := ι_le_ι.mpr hU64
    simpa only [map_ofNat] using h
  have hU16ι : 16 * ι g ≤ ι U := by
    have h := ι_le_ι.mpr hU16
    simpa only [map_mul, map_ofNat] using h
  have hvι : 2 * (4 * ι g) * ι v ≤ ι (power U Xn) := by
    have h := ι_le_ι.mpr hvD
    simp only [map_mul, map_ofNat] at h
    linarith
  have hDι : (0 : DiffRing V) < ι (power U Xn) := by
    have h := ι_lt_ι.mpr hD
    rwa [map_zero] at h
  have hX0 := ι_nonneg Xn
  have hM0 := ι_nonneg M
  have hg0 := ι_nonneg g
  have hG : (0 : DiffRing V) ≤ 4 * ι g := by linarith
  have f1 := mul_le_mul_of_nonneg_left hU16ι hM0
  have f5 := mul_le_mul_of_nonneg_left hU64ι hM0
  have f7 := mul_le_mul_of_nonneg_left hQ64ι hX0
  have hπ0 : (0 : DiffRing V) < 2 * ι (P - 2) + 3 := by
    have := ι_nonneg (P - 2); linarith
  have hα0 : (0 : DiffRing V) < 2 * ι (A - 2) + 3 := by
    have := ι_nonneg (A - 2); linarith
  have hπ : 4 * ι Xn * (4 * ι g) * ι Q + 2 * ι Xn ≤ 2 * ι (P - 2) + 3 := by
    have e : 4 * ι Xn * (4 * ι g) * ι Q = 16 * (ι M * ι g) := by rw [hMι]; ring
    have f2 : 0 ≤ (ι M - 1) * (ι M * ι U) :=
      _root_.mul_nonneg (by linarith) (_root_.mul_nonneg hM0 (ι_nonneg U))
    rw [e]
    linarith
  have hα : 4 * ι Xn * (4 * ι g * ι Q + 1) ≤ 2 * ι (A - 2) + 3 := by
    have e : 4 * ι Xn * (4 * ι g * ι Q + 1) = 16 * (ι M * ι g) + 4 * ι Xn := by
      rw [hMι]; ring
    rw [e]
    linarith
  have hQN : ι Q * ι (power U Xn) ≤ ι Q * ι (power U Xn) + ι v := by
    have := ι_nonneg v; linarith
  have hupB := upper_bound (2 * ι (P - 2) + 3) (ι (ycoord (Xn + 1) (P - 2)))
    (ι (ycoord (2 * Xn + 1) (A - 2))) (ι (power U Xn)) (ι Xn) (ι Q) (ι v) (4 * ι g)
    hπ0 hDι (ι_nonneg _) hG hX0 hup' hvι hπ
  have hloB := lower_bound (2 * ι (A - 2) + 3) (ι (ycoord (Xn + 1) (P - 2)))
    (ι (ycoord (2 * Xn + 1) (A - 2))) (ι (power U Xn)) (ι Xn) (ι Q)
    (ι Q * ι (power U Xn) + ι v) (4 * ι g) hα0 hDι (ι_nonneg _) hG hX0 hlo' hQN hupB hα
  have happ := two_sided (ι g) (ι (ycoord (2 * Xn + 1) (A - 2)))
    (ι (ycoord (Xn + 1) (P - 2))) (ι Q) hupB hloB
  have hQι : ι Q = ι l * ι Yn := by rw [hQl, map_mul]
  rw [hQι] at happ
  refine ⟨l, w, A - 2, P - 2, hl0, hw0, hbw, ?_, ?_, happ⟩
  · rw [ha, hA, hM, hQl, hU]
  · rw [hp, hP, hM, hQl, hU]

#print axioms bridge

end DiophantineConsistency.Z10Ratio
