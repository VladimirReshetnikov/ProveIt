import DiophantineConsistency.P138.P138Rank
import DiophantineConsistency.ArithmeticPellFirstIndex

/-! # The first index: `2n = R + 1`

132-lowops §5, second paragraph, for the native modulus `M_index = E = XY`. At a zero, with the
main index `R` of `P138Rank`:

* `Dt = τ²` (`P138EarlyFold.guard_split`) is the first norm `τ² = 1 + ℓ(ℓ+1) k²`, `ℓ = XY²`.
  For `X > 0` it is classified at base `2(ℓ − 1) + 1` (`ArithmeticPellFirstNorm.solution_index`
  at `ℓ − 1`), for `X < 0` at base `2(λ − 2) + 1` with `λ = −ℓ` (since `ℓ(ℓ+1) = λ(λ−1)`):
  `τ = χ(n)`, `|k| = 2ψ(n)`.
* Residues modulo `|E|`: for `X > 0`, `|E| ∣ bF + 1` and `ψ(n) ≡ n`
  (`ArithmeticPellCongruences.residue_quotients`); for `X < 0`, `|E| ∣ bF + 3` and the
  **alternating residue** `ψ(n) ≡ (−1)^(n−1) n (mod bF + 3)` (`alt_residue`, new). Together with
  `k = R + 1 + hE`: `2n ≡ ±(R + 1) (mod |E|)`.
* No wrap: `n < R` (otherwise `|k|/2 = ψ_bF(n) ≥ ψ_b(R) = |c|`, by `base_mono`, against
  `|c| > |k|(|Y| − ½)`), and `3R + 1 < |E|`, so `2n = R + 1`.
* For `X > 0` the residue sign is exact, which forces `k > 0`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.P138FirstIndex
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing ZRowsCoprimeSquares P138Value P138Ports P138Bootstrap P138NoRoot
  P138Squares P138Budget P138Adjacent P138Window P138EarlyFold P138Rank
open ArithmeticPellRecurrence ArithmeticPellHalfIndex ArithmeticPellFirstNorm

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The alternating residue -/

theorem nat_quot {m : V} (hm : 0 < m) {D k : DiffRing V} (hD : 0 ≤ D) (h : D = ι m * k) :
    ∃ r : V, k = ι r := by
  apply nonneg_iff.mp
  by_contra hk
  have : ι m * k < 0 := mul_neg_of_pos_of_neg (ι_pos hm) (lt_of_not_ge hk)
  linarith

/-- One step from the residues `χ ≡ 1`, `ψ ≡ −t` at time `t` to `χ ≡ −1`, `ψ ≡ t + 1`
(`m ∣ b + 3`). -/
theorem stepA (b m w t r1 r2 : V) (hm : 0 < m) (hw : b + 3 = m * w)
    (h1 : xcoord t b = 1 + m * r1) (h2 : ycoord t b + t = m * r2) :
    ∃ r3 r4 : V, xcoord (t + 1) b + 1 = m * r3 ∧ ycoord (t + 1) b = t + 1 + m * r4 := by
  have hB : (ι b : DiffRing V) = ι m * ι w - 3 := by
    have := congrArg (ι (V := V)) hw
    simp only [map_add, map_mul, map_ofNat] at this
    linear_combination this
  have hk1 : (ι (xcoord t b) : DiffRing V) = 1 + ι m * ι r1 := by
    have := congrArg (ι (V := V)) h1; simpa only [map_add, map_mul, map_one] using this
  have hk2 : (ι (ycoord t b) : DiffRing V) + ι t = ι m * ι r2 := by
    have := congrArg (ι (V := V)) h2; simpa only [map_add, map_mul] using this
  have hX1 : (ι (xcoord (t + 1) b) : DiffRing V) =
      (ι b + 2) * ι (xcoord t b) + (ι b + 1) * (ι b + 3) * ι (ycoord t b) := by
    rw [x_succ]; unfold delta; simp only [map_add, map_mul, map_ofNat, map_one]
  have hY1 : (ι (ycoord (t + 1) b) : DiffRing V) = ι (xcoord t b) + (ι b + 2) * ι (ycoord t b) := by
    rw [y_succ]; simp only [map_add, map_mul, map_ofNat]
  have g3 : (ι (xcoord (t + 1) b) : DiffRing V) + 1 = ι m * (ι w * ι (xcoord t b) +
      (ι m * ι w - 2) * ι w * ι (ycoord t b) - ι r1) := by
    rw [hX1, hB]; linear_combination (-1 : DiffRing V) * hk1
  have g4 : (ι (ycoord (t + 1) b) : DiffRing V) - (ι t + 1) =
      ι m * (ι r1 - ι r2 + ι w * ι (ycoord t b)) := by
    rw [hY1, hB]; linear_combination hk1 - hk2
  obtain ⟨s3, hs3⟩ := nat_quot hm (by
    have := ι_nonneg (xcoord (t + 1) b); linarith) g3
  obtain ⟨s4, hs4⟩ := nat_quot hm (by
    rw [sub_nonneg]
    have := ι_le_ι.mpr (time_le_y (t + 1) b)
    simp only [map_add, map_one] at this
    linarith) g4
  refine ⟨s3, s4, ?_, ?_⟩
  · apply ι_injective; simp only [map_add, map_mul, map_one]; rw [← hs3]; linear_combination g3
  · apply ι_injective; simp only [map_add, map_mul, map_one]; rw [← hs4]
    linear_combination g4

/-- One step from `χ ≡ −1`, `ψ ≡ t` at time `t` to `χ ≡ 1`, `ψ ≡ −(t + 1)` (`m ∣ b + 3`). -/
theorem stepB (b m w t r3 r4 : V) (hm : 0 < m) (hw : b + 3 = m * w)
    (h3 : xcoord t b + 1 = m * r3) (h4 : ycoord t b = t + m * r4) :
    ∃ r1 r2 : V, xcoord (t + 1) b = 1 + m * r1 ∧ ycoord (t + 1) b + (t + 1) = m * r2 := by
  have hB : (ι b : DiffRing V) = ι m * ι w - 3 := by
    have := congrArg (ι (V := V)) hw
    simp only [map_add, map_mul, map_ofNat] at this
    linear_combination this
  have hk3 : (ι (xcoord t b) : DiffRing V) + 1 = ι m * ι r3 := by
    have := congrArg (ι (V := V)) h3; simpa only [map_add, map_mul, map_one] using this
  have hk4 : (ι (ycoord t b) : DiffRing V) = ι t + ι m * ι r4 := by
    have := congrArg (ι (V := V)) h4; simpa only [map_add, map_mul] using this
  have hX2 : (ι (xcoord (t + 1) b) : DiffRing V) =
      (ι b + 2) * ι (xcoord t b) + (ι b + 1) * (ι b + 3) * ι (ycoord t b) := by
    rw [x_succ]; unfold delta; simp only [map_add, map_mul, map_ofNat, map_one]
  have hY2 : (ι (ycoord (t + 1) b) : DiffRing V) = ι (xcoord t b) + (ι b + 2) * ι (ycoord t b) := by
    rw [y_succ]; simp only [map_add, map_mul, map_ofNat]
  have g1 : (ι (xcoord (t + 1) b) : DiffRing V) - 1 = ι m * (ι w * ι (xcoord t b) +
      (ι m * ι w - 2) * ι w * ι (ycoord t b) - ι r3) := by
    rw [hX2, hB]; linear_combination (-1 : DiffRing V) * hk3
  have g2 : (ι (ycoord (t + 1) b) : DiffRing V) + (ι t + 1) =
      ι m * (ι r3 - ι r4 + ι w * ι (ycoord t b)) := by
    rw [hY2, hB]; linear_combination hk3 - hk4
  obtain ⟨s1, hs1⟩ := nat_quot hm (by
    rw [sub_nonneg, ← map_one ι]; exact ι_le_ι.mpr (one_le_x _ _)) g1
  obtain ⟨s2, hs2⟩ := nat_quot hm (by
    have := ι_nonneg (ycoord (t + 1) b); have := ι_nonneg t; linarith) g2
  refine ⟨s1, s2, ?_, ?_⟩
  · apply ι_injective; simp only [map_add, map_mul, map_one]; rw [← hs1]; linear_combination g1
  · apply ι_injective; simp only [map_add, map_mul, map_one]; rw [← hs2]
    linear_combination g2

/-- **The alternating residue** for `m ∣ b + 3`: at every time `n`, either `χ(n) ≡ 1`,
`ψ(n) ≡ −n` or `χ(n) ≡ −1`, `ψ(n) ≡ n (mod m)`, with nonnegative quotients. -/
theorem alt_residue (b m : V) (hm : 0 < m) (hd : m ∣ b + 3) (n : V) :
    (∃ r1 r2 : V, xcoord n b = 1 + m * r1 ∧ ycoord n b + n = m * r2) ∨
      (∃ r3 r4 : V, xcoord n b + 1 = m * r3 ∧ ycoord n b = n + m * r4) := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact Or.inl ⟨0, 0, by simp, by simp⟩
  case succ n ih =>
    obtain ⟨w, hw⟩ := hd
    rcases ih with ⟨r1, r2, h1, h2⟩ | ⟨r3, r4, h3, h4⟩
    · exact Or.inr (stepA b m w n r1 r2 hm hw h1 h2)
    · exact Or.inl (stepB b m w n r3 r4 hm hw h3 h4)

/-- The alternating residue as a signed congruence: `ψ(n) ≡ ±n (mod m)` for `m ∣ b + 3`. -/
theorem alt_sign (b m : V) (hm : 0 < m) (hd : m ∣ b + 3) (n : V) :
    (ι m : DiffRing V) ∣ ι (ycoord n b) - ι n ∨ (ι m : DiffRing V) ∣ ι (ycoord n b) + ι n := by
  rcases alt_residue b m hm hd n with ⟨_, r2, _, h2⟩ | ⟨_, r4, _, h4⟩
  · right; refine ⟨ι r2, ?_⟩
    have := congrArg (ι (V := V)) h2; simp only [map_add, map_mul] at this; exact this
  · left; refine ⟨ι r4, ?_⟩
    have := congrArg (ι (V := V)) h4; simp only [map_add, map_mul] at this
    linear_combination this

/-! ## Small divisibilities -/

theorem eq_zero_of_dvd_small {m : V} {D : DiffRing V} (h : (ι m : DiffRing V) ∣ D)
    (hD : |D| < ι m) : D = 0 := by
  obtain ⟨w, rfl⟩ := h
  by_contra hne
  have hw : w ≠ 0 := by intro h0; apply hne; rw [h0, mul_zero]
  have h1 : 1 ≤ |w| := one_le_abs hw
  rw [abs_mul, abs_of_nonneg (ι_nonneg m)] at hD
  have : ι m * 1 ≤ ι m * |w| := mul_le_mul_of_nonneg_left h1 (ι_nonneg m)
  linarith

section Regs
variable (p : Fin 6 → DiffRing V) (x : Fin 11 → DiffRing V)
local notation "𝓡" => regs p x

/-- **The first index.** -/
structure FirstIndex (E : EarlyFold p x) (M : MainIndex p x E) where
  n : V
  bF : V
  hn : 2 * n = M.Rn + 1
  hk : |(𝓡).k| = ι (2 * ycoord n bF)
  hDt : (𝓡).Dt = ι (xcoord n bF) * ι (xcoord n bF)
  hbFhi : (ι bF : DiffRing V) + 2 ≤ 2 * |(𝓡).X| * |(𝓡).Y| ^ 2 + 1
  hbFlo : 2 * |(𝓡).X| * |(𝓡).Y| ^ 2 - 3 ≤ (ι bF : DiffRing V)
  hpos : 0 < (𝓡).X → (∃ ln : V, ι ln = (𝓡).X * (𝓡).Y ^ 2 ∧ bF = 2 * (ln - 1) + 1) ∧ 0 < (𝓡).k

/-- The classified first norm, before the no-wrap argument. -/
theorem first_classified (hp : PortFacts p) (mE kn τ : V) (hmE : |(𝓡).E| = ι mE)
    (hkn : |(𝓡).k| = ι kn) (hDt : (𝓡).Dt = ι τ * ι τ) :
    ∃ n bF : V, xcoord n bF = τ ∧ 2 * ycoord n bF = kn ∧
      ((ι mE : DiffRing V) ∣ ι kn - ι (2 * n) ∨ (ι mE : DiffRing V) ∣ ι kn + ι (2 * n)) ∧
      (ι bF : DiffRing V) + 2 ≤ 2 * |(𝓡).X| * |(𝓡).Y| ^ 2 + 1 ∧
      2 * |(𝓡).X| * |(𝓡).Y| ^ 2 - 3 ≤ (ι bF : DiffRing V) ∧
      (0 < (𝓡).X → (∃ ln : V, ι ln = (𝓡).X * (𝓡).Y ^ 2 ∧ bF = 2 * (ln - 1) + 1) ∧
        (ι mE : DiffRing V) ∣ ι kn - ι (2 * n)) := by
  obtain ⟨xn, hxn⟩ := abs_eq_ι (𝓡).X
  obtain ⟨yn, hyn⟩ := abs_eq_ι (𝓡).Y
  have hX4 : 4 ≤ |(𝓡).X| := by
    have := abs_X p x hp; have := abs_q_ge p x hp
    have : (1 : DiffRing V) ≤ 2 ^ 64 := one_le_pow₀ (by norm_num); linarith
  have hY3 := three_le_abs_Y p x hp
  have hmE' : (ι mE : DiffRing V) = ι xn * ι yn := by rw [← hmE, E_def, abs_mul, hxn, hyn]
  have hmEn : mE = xn * yn := ι_injective (by rw [map_mul]; exact hmE')
  have hk2 : (𝓡).k ^ 2 = ι kn * ι kn := by rw [← sq_abs, hkn]; ring
  have hY2 : (𝓡).Y ^ 2 = ι yn * ι yn := by rw [← sq_abs, hyn]; ring
  have hDt' : ι τ * ι τ = 1 + ((𝓡).X * (𝓡).Y ^ 2) * ((𝓡).X * (𝓡).Y ^ 2 + 1) * (ι kn * ι kn) := by
    rw [← hDt, Dt_eq, hk2]
  have hlam2 : (2 : V) ≤ xn * yn * yn := by
    apply ι_le_ι.mp
    rw [map_mul, map_mul, map_ofNat, ← hxn, ← hyn]
    have h12 : (4 : DiffRing V) * 3 ≤ |(𝓡).X| * |(𝓡).Y| :=
      mul_le_mul hX4 hY3 (by norm_num) (abs_nonneg _)
    have h36 : (4 : DiffRing V) * 3 * 3 ≤ |(𝓡).X| * |(𝓡).Y| * |(𝓡).Y| :=
      mul_le_mul h12 hY3 (by norm_num) (by linarith)
    linarith
  rcases lt_or_gt_of_ne (X_ne p x hp) with hXneg | hXpos
  · -- `X < 0`: base `2(λ − 2) + 1`, `λ = −ℓ`
    have hX : (𝓡).X = -ι xn := by rw [← hxn, abs_of_neg hXneg]; ring
    set lam : V := xn * yn * yn with hlam
    have hl : (𝓡).X * (𝓡).Y ^ 2 = -ι lam := by rw [hX, hY2, hlam]; simp only [map_mul]; ring
    have hl2 : (ι (lam - 2) : DiffRing V) = ι lam - 2 := by rw [ι_tsub' hlam2, map_ofNat]
    have hnorm : τ * τ = 1 + discriminant (lam - 2) * kn * kn := by
      apply ι_injective
      unfold discriminant
      simp only [map_mul, map_add, map_one, map_ofNat]
      rw [hl2, hDt', hl]; ring
    obtain ⟨n, _, hx, hy⟩ := solution_index (lam - 2) τ kn hnorm
    refine ⟨n, 2 * (lam - 2) + 1, hx, hy, ?_, ?_, ?_, fun h => absurd h (not_lt.mpr hXneg.le)⟩
    · have hd : mE ∣ 2 * (lam - 2) + 1 + 3 := by
        refine ι_dvd_iff.mp ⟨2 * ι yn, ?_⟩
        simp only [map_add, map_mul, map_ofNat, map_one]
        rw [hl2, hmE', hlam]; simp only [map_mul]; ring
      have hm0 : 0 < mE := by
        rw [hmEn]; apply pos_of_ι; rw [map_mul, ← hxn, ← hyn]; nlinarith
      rcases alt_sign (2 * (lam - 2) + 1) mE hm0 hd n with h | h
      · left
        obtain ⟨w, hw⟩ := h
        refine ⟨2 * w, ?_⟩
        rw [← hy, map_mul, map_mul, map_ofNat]; linear_combination 2 * hw
      · right
        obtain ⟨w, hw⟩ := h
        refine ⟨2 * w, ?_⟩
        rw [← hy, map_mul, map_mul, map_ofNat]; linear_combination 2 * hw
    · simp only [map_add, map_mul, map_ofNat, map_one]
      rw [hl2, hlam, map_mul, map_mul, ← hxn, ← hyn]; nlinarith
    · simp only [map_add, map_mul, map_ofNat, map_one]
      rw [hl2, hlam, map_mul, map_mul, ← hxn, ← hyn]; nlinarith
  · -- `X > 0`: base `2(ℓ − 1) + 1`
    have hX : (𝓡).X = ι xn := by rw [← hxn, abs_of_pos hXpos]
    set ln : V := xn * yn * yn with hln
    have hl : (𝓡).X * (𝓡).Y ^ 2 = ι ln := by rw [hX, hY2, hln]; simp only [map_mul]; ring
    have hl1 : (1 : V) ≤ ln := le_trans (by norm_num) hlam2
    have hl1' : (ι (ln - 1) : DiffRing V) = ι ln - 1 := by rw [ι_tsub' hl1, map_one]
    have hnorm : τ * τ = 1 + discriminant (ln - 1) * kn * kn := by
      apply ι_injective
      unfold discriminant
      simp only [map_mul, map_add, map_one, map_ofNat]
      rw [hl1', hDt', hl]; ring
    obtain ⟨n, _, hx, hy⟩ := solution_index (ln - 1) τ kn hnorm
    have hd : mE ∣ 2 * (ln - 1) + 1 + 1 := by
      refine ι_dvd_iff.mp ⟨2 * ι yn, ?_⟩
      simp only [map_add, map_mul, map_ofNat, map_one]
      rw [hl1', hmE', hln]; simp only [map_mul]; ring
    obtain ⟨_, s, _, hys⟩ := ArithmeticPellCongruences.residue_quotients n (2 * (ln - 1) + 1) mE hd
    have hexact : (ι mE : DiffRing V) ∣ ι kn - ι (2 * n) :=
      ⟨2 * ι s, by rw [← hy, hys]; simp only [map_mul, map_add, map_ofNat]; ring⟩
    refine ⟨n, 2 * (ln - 1) + 1, hx, hy, Or.inl hexact, ?_, ?_, fun _ => ⟨⟨ln, hl.symm, rfl⟩, hexact⟩⟩
    · simp only [map_add, map_mul, map_ofNat, map_one]
      rw [hl1', hln, map_mul, map_mul, ← hxn, ← hyn]; nlinarith
    · simp only [map_add, map_mul, map_ofNat, map_one]
      rw [hl1', hln, map_mul, map_mul, ← hxn, ← hyn]; nlinarith

set_option maxHeartbeats 2000000 in
theorem first_index (hp : PortFacts p) (hz : value p x = 0) (E : EarlyFold p x)
    (M : MainIndex p x E) : Nonempty (FirstIndex p x E M) := by
  have hB : 0 < (𝓡).Budget := by linarith [budget_ge p x hp hz]
  have hs := signs p x hp hz
  obtain ⟨hE3, _, _⟩ := sizes p x hp hs
  obtain ⟨hk0, _⟩ := centered p x hp hB
  have hci := (c_interval p x hp hB).1
  have hY3 := three_le_abs_Y p x hp
  obtain ⟨τ, _, _, _, hDt, _, _⟩ := guard_split p x hp hz E
  obtain ⟨mE, hmE⟩ := abs_eq_ι (𝓡).E
  obtain ⟨kn, hkn⟩ := abs_eq_ι (𝓡).k
  obtain ⟨n, bF, hx, hy, hres, hhi, hlo, hposX⟩ := first_classified p x hp mE kn τ hmE hkn hDt
  rw [M.hR] at hE3
  rw [hmE] at hE3
  -- `n < R`
  have hnR : n < M.Rn := by
    by_contra hcon
    have hle : M.Rn ≤ n := le_of_not_gt hcon
    have hbb : E.Bn - 2 ≤ bF := by
      apply ι_le_ι.mp
      rw [ι_tsub' (le_trans (by norm_num) E.hB3), map_ofNat, ← E.hBn]
      have hA : |(𝓡).A| ≤ |(𝓡).Y| * (|(𝓡).X| + 1) + 2 := by
        have e : (𝓡).A = (𝓡).Y * ((𝓡).X + 1) + 2 := by rw [A_eq, a_eq]; ring
        rw [e]
        calc |(𝓡).Y * ((𝓡).X + 1) + 2| ≤ |(𝓡).Y * ((𝓡).X + 1)| + |(2 : DiffRing V)| :=
              abs_add_le _ _
          _ ≤ |(𝓡).Y| * (|(𝓡).X| + 1) + 2 := by
              rw [abs_mul, abs_two]
              have := mul_le_mul_of_nonneg_left (abs_add_le (𝓡).X 1) (abs_nonneg (𝓡).Y)
              rw [abs_one] at this; linarith
      have hX4 : 4 ≤ |(𝓡).X| := by
        have := abs_X p x hp; have := abs_q_ge p x hp
        have : (1 : DiffRing V) ≤ 2 ^ 64 := one_le_pow₀ (by norm_num); linarith
      have h4Y : 4 * |(𝓡).Y| ≤ |(𝓡).X| * |(𝓡).Y| := mul_le_mul_of_nonneg_right hX4 (abs_nonneg _)
      have h5 : |(𝓡).X| * |(𝓡).Y| * 5 ≤ |(𝓡).X| * |(𝓡).Y| * (2 * |(𝓡).Y| - 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      nlinarith
    have h1 := (ArithmeticPellFirstIndex.base_mono (E.Bn - 2) bF hbb M.Rn).2
    have h2 : ycoord M.Rn bF ≤ ycoord n bF :=
      (ArithmeticPellStrongDivisibility.y_strictMono bF).monotone hle
    have hcn : E.cn ≤ ycoord n bF := by rw [M.hc]; exact le_trans h1 h2
    have h3 : 2 * ι E.cn ≤ |(𝓡).k| := by
      rw [hkn, ← hy, map_mul, map_ofNat]
      have := ι_le_ι.mpr hcn; linarith
    rw [E.hcn] at hci
    have : |(𝓡).k| * 5 ≤ |(𝓡).k| * (2 * |(𝓡).Y| - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    have : 0 < |(𝓡).k| := abs_pos.mpr hk0
    linarith
  -- `k ≡ R + 1 (mod |E|)`
  have hkdvd : (ι mE : DiffRing V) ∣ (𝓡).k - (ι M.Rn + 1) := by
    rw [show (𝓡).k - (ι M.Rn + 1) = x 3 * (𝓡).E by rw [k_eq, M.hR]; ring]
    exact dvd_mul_of_dvd_right (by rw [← hmE]; exact abs_dvd_self _) _
  have hkn0 : 0 < kn := pos_of_ι (by rw [← hkn]; exact abs_pos.mpr hk0)
  have hsmall : (ι (2 * n) : DiffRing V) + (ι M.Rn + 1) < ι mE := by
    have : ι n + 1 ≤ (ι M.Rn : DiffRing V) := by
      rw [← map_one ι, ← map_add]; exact ι_le_ι.mpr (lt_iff_succ_le.mp hnR)
    rw [map_mul, map_ofNat]; linarith
  have hpos2 : (0 : DiffRing V) < ι (2 * n) + (ι M.Rn + 1) := by
    have := ι_nonneg (2 * n); have := ι_nonneg M.Rn; linarith
  have hnone : ¬ (ι mE : DiffRing V) ∣ ι (2 * n) + (ι M.Rn + 1) := by
    intro h
    have := eq_zero_of_dvd_small h (by rw [abs_of_pos hpos2]; exact hsmall)
    linarith
  have hcomb : (ι mE : DiffRing V) ∣ ι (2 * n) - (ι M.Rn + 1) ∨
      (ι mE : DiffRing V) ∣ ι (2 * n) + (ι M.Rn + 1) := by
    obtain ⟨d, hd⟩ := hkdvd
    rcases eq_or_eq_neg_abs (𝓡).k with hks | hks <;> rw [hkn] at hks <;> rw [hks] at hd
    · rcases hres with ⟨w, hw⟩ | ⟨w, hw⟩
      · exact Or.inl ⟨d - w, by linear_combination hd - hw⟩
      · exact Or.inr ⟨w - d, by linear_combination hw - hd⟩
    · rcases hres with ⟨w, hw⟩ | ⟨w, hw⟩
      · exact Or.inr ⟨-(d + w), by linear_combination -hd - hw⟩
      · exact Or.inl ⟨d + w, by linear_combination hd + hw⟩
  have hnR' : 2 * n = M.Rn + 1 := by
    rcases hcomb with h | h
    · have h0 := eq_zero_of_dvd_small h (by
        rw [abs_sub_lt_iff]; constructor <;> linarith [ι_nonneg (2 * n), ι_nonneg M.Rn])
      apply ι_injective
      rw [map_add, map_one]; linarith
    · exact absurd h hnone
  refine ⟨⟨n, bF, hnR', by rw [hkn, hy], by rw [hDt, hx], hhi, hlo, fun hX0 => ?_⟩⟩
  obtain ⟨hln, hexact⟩ := hposX hX0
  refine ⟨hln, ?_⟩
  rcases eq_or_eq_neg_abs (𝓡).k with hks | hks
  · rw [hks]; exact abs_pos.mpr hk0
  · exfalso
    rw [hkn] at hks
    obtain ⟨d, hd⟩ := hkdvd
    obtain ⟨w, hw⟩ := hexact
    rw [hks] at hd
    exact hnone ⟨-(d + w), by linear_combination -hd - hw⟩

end Regs

#print axioms stepA
#print axioms stepB
#print axioms alt_residue
#print axioms alt_sign
#print axioms first_classified
#print axioms first_index

end DiophantineConsistency.P138FirstIndex
