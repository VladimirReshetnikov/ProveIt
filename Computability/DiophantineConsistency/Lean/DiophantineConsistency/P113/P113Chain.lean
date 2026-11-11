import DiophantineConsistency.P138.P138Orientation

/-! # Package 138's soundness chain on the weak window

Package 138's chain `P138FirstIndex` → `P138Ratio` → `P138Projector` → `P138Orientation` reads a
zero only through the record `P138Rank.Folded`. One field of that record, the positive budget
`0 < Budget`, is a register of 138's back end; the chain uses it only through three consequences
(`P138Budget.centered`, `c_interval`, `P138Rank.signs_of_budget`):

* the signs `0 < F q`, `0 < C q`, `0 < (q − F − C) q`;
* `k ≠ 0` and the **½-window** `|k| (|Y| − ½) < |c| < |k| (|Y| + ½)`, `0 < c (k Y)`.

A circuit whose guard gives the signs from `G > 0` and only the **weak window**
`|k| (|Y| − 1) < |c| < |k| (|Y| + 1)` (from `η ζ > 0`, `P113Fold.window_of_ez`) carries the record
`FoldedW` below instead. The chain goes through with two arithmetic changes:

* first index, no wrap: `|c| > |k| (|Y| − 1) ≥ 2 |k|` already contradicts `2 |c| ≤ |k|`;
* ratio: `(x − 3)^t < 2 |Y| + 2` instead of `2 |Y| + 1`, against
  `|H| ≥ |X| (2 |Y| + 2)` (`abs_H_ge2`), still with room to spare.

Everything else is package 138's proof, re-run over `FoldedW` (`first_indexW`, `H_largeW`,
`signed_mainW`, `projectorW`, `orientedW`). Package 113 (`P113Leaf`) is the first user. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.P113Chain
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing ZRowsCoprimeSquares P138Value P138Ports P138Bootstrap P138NoRoot
  P138Squares P138Budget P138Adjacent P138Window P138EarlyFold P138Rank P138FirstIndex P138Ratio
  P138Projector P138Orientation
open ArithmeticPellRecurrence ArithmeticPellHalfIndex ArithmeticPellFirstNorm ArithmeticPow
  ArithmeticHalfBinomialSandwich

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section Regs
variable (p : Fin 6 → DiffRing V) (x : Fin 11 → DiffRing V) (κ : DiffRing V)
local notation "𝓡" => regsK p x κ

/-- **The folded front on the weak window**: `P138Rank.Folded` with the budget replaced by the
signs, `k ≠ 0`, the weak window and the guard `η ζ > 0`. -/
structure FoldedW where
  Bn : V
  cn : V
  Rn : V
  τ : V
  hBn : |(𝓡).A| = ι Bn
  hB3 : 3 ≤ Bn
  hcn : |x 8| = ι cn
  hcn0 : 0 < cn
  hs : 0 < (𝓡).F * (𝓡).q ∧ 0 < x 1 * (𝓡).q ∧ 0 < ((𝓡).q - (𝓡).F - x 1) * (𝓡).q
  hk0 : (𝓡).k ≠ 0
  hlo : |(𝓡).k| * (|(𝓡).Y| - 1) < |x 8|
  hhi : |x 8| < |(𝓡).k| * (|(𝓡).Y| + 1)
  hcky : 0 < x 8 * ((𝓡).k * (𝓡).Y)
  hez : 0 < (𝓡).eta * ((𝓡).k - (𝓡).eta)
  hDt : (𝓡).Dt = ι τ * ι τ
  hHK : (𝓡).H ∣ Kq p x κ ^ 5
  hR : (𝓡).R = ι Rn
  hodd : Rn % 2 = 1
  hc : cn = ycoord Rn (Bn - 2)
  hDm : (𝓡).Dm = ι (xcoord Rn (Bn - 2)) * ι (xcoord Rn (Bn - 2))
  hRpos : 0 < Rn

/-! ## The first index -/

/-- `P138FirstIndex.FirstIndex` over the weak-window record. -/
structure FirstIndexW (Fd : FoldedW p x κ) where
  n : V
  bF : V
  hn : 2 * n = Fd.Rn + 1
  hk : |(𝓡).k| = ι (2 * ycoord n bF)
  hDt : (𝓡).Dt = ι (xcoord n bF) * ι (xcoord n bF)
  hbFhi : (ι bF : DiffRing V) + 2 ≤ 2 * |(𝓡).X| * |(𝓡).Y| ^ 2 + 1
  hbFlo : 2 * |(𝓡).X| * |(𝓡).Y| ^ 2 - 3 ≤ (ι bF : DiffRing V)
  hpos : 0 < (𝓡).X → (∃ ln : V, ι ln = (𝓡).X * (𝓡).Y ^ 2 ∧ bF = 2 * (ln - 1) + 1) ∧ 0 < (𝓡).k

set_option maxHeartbeats 2000000 in
/-- **The first index** `2n = R + 1` on the weak window (`P138FirstIndex.first_index`). -/
theorem first_indexW (hp : PortFacts p) (hκ : IndexModulus p x κ) (Fd : FoldedW p x κ) :
    Nonempty (FirstIndexW p x κ Fd) := by
  have hs := Fd.hs
  obtain ⟨mE, hmE, hkdvd0, hE3⟩ := modulus p x κ hp hκ hs
  have hk0 := Fd.hk0
  have hci := Fd.hlo
  have hY3 := three_le_abs_Y p x κ hp
  obtain ⟨τ, hDt⟩ : ∃ τ : V, (𝓡).Dt = ι τ * ι τ := ⟨Fd.τ, Fd.hDt⟩
  obtain ⟨kn, hkn⟩ := abs_eq_ι (𝓡).k
  rw [Fd.hR] at hE3
  have hm0 : 0 < mE := pos_of_ι (by have := ι_nonneg Fd.Rn; linarith)
  obtain ⟨n, bF, hx, hy, hres, hhi, hlo, hposX⟩ :=
    first_classified p x κ hp mE kn τ hm0 hmE hkn hDt
  -- `n < R`
  have hnR : n < Fd.Rn := by
    by_contra hcon
    have hle : Fd.Rn ≤ n := le_of_not_gt hcon
    have hbb : Fd.Bn - 2 ≤ bF := by
      apply ι_le_ι.mp
      rw [ι_tsub' (le_trans (by norm_num) Fd.hB3), map_ofNat, ← Fd.hBn]
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
        have := abs_X p x κ hp; have := abs_q_ge p x κ hp
        have : (1 : DiffRing V) ≤ 2 ^ 64 := one_le_pow₀ (by norm_num); linarith
      have h4Y : 4 * |(𝓡).Y| ≤ |(𝓡).X| * |(𝓡).Y| := mul_le_mul_of_nonneg_right hX4 (abs_nonneg _)
      have h5 : |(𝓡).X| * |(𝓡).Y| * 5 ≤ |(𝓡).X| * |(𝓡).Y| * (2 * |(𝓡).Y| - 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      nlinarith
    have h1 := (ArithmeticPellFirstIndex.base_mono (Fd.Bn - 2) bF hbb Fd.Rn).2
    have h2 : ycoord Fd.Rn bF ≤ ycoord n bF :=
      (ArithmeticPellStrongDivisibility.y_strictMono bF).monotone hle
    have hcn : Fd.cn ≤ ycoord n bF := by rw [Fd.hc]; exact le_trans h1 h2
    have h3 : 2 * ι Fd.cn ≤ |(𝓡).k| := by
      rw [hkn, ← hy, map_mul, map_ofNat]
      have := ι_le_ι.mpr hcn; linarith
    rw [Fd.hcn] at hci
    -- the weak window: `|c| > |k| (|Y| − 1) ≥ 2 |k| ≥ 4 |c|`
    have : |(𝓡).k| * 2 ≤ |(𝓡).k| * (|(𝓡).Y| - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    have := ι_nonneg Fd.cn
    have : 0 < |(𝓡).k| := abs_pos.mpr hk0
    linarith
  -- `k ≡ R + 1 (mod m)`
  have hkdvd : (ι mE : DiffRing V) ∣ (𝓡).k - (ι Fd.Rn + 1) := by rw [← Fd.hR]; exact hkdvd0
  have hsmall : (ι (2 * n) : DiffRing V) + (ι Fd.Rn + 1) < ι mE := by
    have : ι n + 1 ≤ (ι Fd.Rn : DiffRing V) := by
      rw [← map_one ι, ← map_add]; exact ι_le_ι.mpr (lt_iff_succ_le.mp hnR)
    rw [map_mul, map_ofNat]; linarith
  have hpos2 : (0 : DiffRing V) < ι (2 * n) + (ι Fd.Rn + 1) := by
    have := ι_nonneg (2 * n); have := ι_nonneg Fd.Rn; linarith
  have hnone : ¬ (ι mE : DiffRing V) ∣ ι (2 * n) + (ι Fd.Rn + 1) := by
    intro h
    have := eq_zero_of_dvd_small h (by rw [abs_of_pos hpos2]; exact hsmall)
    linarith
  have hcomb : (ι mE : DiffRing V) ∣ ι (2 * n) - (ι Fd.Rn + 1) ∨
      (ι mE : DiffRing V) ∣ ι (2 * n) + (ι Fd.Rn + 1) := by
    obtain ⟨d, hd⟩ := hkdvd
    rcases eq_or_eq_neg_abs (𝓡).k with hks | hks <;> rw [hkn] at hks <;> rw [hks] at hd
    · rcases hres with ⟨w, hw⟩ | ⟨w, hw⟩
      · exact Or.inl ⟨d - w, by linear_combination hd - hw⟩
      · exact Or.inr ⟨w - d, by linear_combination hw - hd⟩
    · rcases hres with ⟨w, hw⟩ | ⟨w, hw⟩
      · exact Or.inr ⟨-(d + w), by linear_combination -hd - hw⟩
      · exact Or.inl ⟨d + w, by linear_combination hd + hw⟩
  have hnR' : 2 * n = Fd.Rn + 1 := by
    rcases hcomb with h | h
    · have h0 := eq_zero_of_dvd_small h (by
        rw [abs_sub_lt_iff]; constructor <;> linarith [ι_nonneg (2 * n), ι_nonneg Fd.Rn])
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

/-! ## The ratio bound -/

/-- `|H| ≥ |X| (2|Y| + 2)` (`P138Ratio.abs_H_ge` has `2|Y| + 1`). -/
theorem abs_H_ge2 (hp : PortFacts p) : |(𝓡).X| * (2 * |(𝓡).Y| + 2) ≤ |(𝓡).H| := by
  have hX := abs_X_ge p x κ hp
  have hY := six_le_abs_Y p x κ hp
  have h66 : (8 : DiffRing V) ≤ 2 ^ 66 := by norm_num
  have ha : |(𝓡).Y| * (|(𝓡).X| - 1) ≤ |(𝓡).a| := by
    rw [a_eq, show (𝓡).X * (𝓡).Y + (𝓡).Y = (𝓡).Y * ((𝓡).X + 1) by ring, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have := abs_sub_abs_le_abs_sub (𝓡).X (-1)
    rw [abs_neg, abs_one, sub_neg_eq_add] at this; exact this
  have hH : 4 * |(𝓡).a| - 3 ≤ |(𝓡).H| := by
    rw [H_def]
    have := abs_sub_abs_le_abs_sub (4 * (𝓡).a) (-3)
    rw [abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : DiffRing V) ≤ 4),
      abs_of_nonneg (by norm_num : (0 : DiffRing V) ≤ 3), sub_neg_eq_add] at this
    exact this
  have hX8 : 8 ≤ |(𝓡).X| := by linarith
  have hprod := mul_nonneg (sub_nonneg.mpr hX8) (sub_nonneg.mpr hY)
  nlinarith

/-- **The ratio bound** `x (x − 3)^t < |H|` on the weak window (`P138Ratio.H_large`). -/
theorem H_largeW (hp : PortFacts p) (Fd : FoldedW p x κ) (Fi : FirstIndexW p x κ Fd) (t xn : V)
    (ht : Fd.Rn = 2 * t + 1)
    (hxn : |(𝓡).X| = ι xn) :
    (ι (xn * power (xn - 3) t) : DiffRing V) < |(𝓡).H| := by
  have hci := Fd.hhi
  obtain ⟨yn, hyn⟩ := abs_eq_ι (𝓡).Y
  have hX := abs_X_ge p x κ hp
  have hn : Fi.n = t + 1 := by
    have h := Fi.hn; rw [ht] at h
    apply ι_injective
    have h' := congrArg (ι (V := V)) h
    simp only [map_add, map_mul, map_ofNat, map_one] at h' ⊢
    linarith
  have hx3 : (3 : V) ≤ xn := by
    apply ι_le_ι.mp; rw [map_ofNat, ← hxn]
    have : (3 : DiffRing V) ≤ 2 ^ 66 := by norm_num
    linarith
  have hxsub : (ι (xn - 3) : DiffRing V) = |(𝓡).X| - 3 := by rw [ι_tsub' hx3, map_ofNat, hxn]
  set b := Fd.Bn - 2 with hb
  have hb2 : (ι (2 * b + 3) : DiffRing V) = 2 * |(𝓡).A| - 1 := by
    rw [hb]; simp only [map_add, map_mul, map_ofNat]
    rw [ι_tsub' (le_trans (by norm_num) Fd.hB3), map_ofNat, ← Fd.hBn]; ring
  have hc1 : power ((2 * b + 3) * (2 * b + 3)) t ≤ Fd.cn := by
    rw [← power_double, Fd.hc, ht]
    exact power_le_ycoord b (2 * t)
  have hK1 : ycoord (t + 1) Fi.bF ≤ power (2 * (Fi.bF + 2)) t := ycoord_le_power Fi.bF t
  have hbase : (xn - 3) * (2 * (Fi.bF + 2)) ≤ (2 * b + 3) * (2 * b + 3) := by
    apply ι_le_ι.mp
    simp only [map_mul, map_ofNat]
    rw [hxsub, hb2, map_add, map_ofNat]
    exact base_square p x κ hp Fi.hbFhi
  have hprod : power (xn - 3) t * power (2 * (Fi.bF + 2)) t ≤ Fd.cn := by
    rw [← power_mul_base]
    exact le_trans (power_mono_base _ _ t hbase) hc1
  -- `|c| < |k|(|Y| + 1)` with `|k| = 2ψ_bF(t+1)`
  have hck : Fd.cn < ycoord (t + 1) Fi.bF * (2 * yn + 2) := by
    apply ι_lt_ι.mp
    rw [Fd.hcn, Fi.hk, hn, hyn] at hci
    simp only [map_mul, map_add, map_ofNat] at hci ⊢
    linarith
  have hlt : power (xn - 3) t * power (2 * (Fi.bF + 2)) t <
      power (2 * (Fi.bF + 2)) t * (2 * yn + 2) := by
    calc power (xn - 3) t * power (2 * (Fi.bF + 2)) t ≤ Fd.cn := hprod
      _ < ycoord (t + 1) Fi.bF * (2 * yn + 2) := hck
      _ ≤ power (2 * (Fi.bF + 2)) t * (2 * yn + 2) := mul_le_mul_of_nonneg_right hK1 (by simp)
  have hpow : power (xn - 3) t < 2 * yn + 2 := by
    rw [mul_comm (power (2 * (Fi.bF + 2)) t)] at hlt
    exact lt_of_mul_lt_mul_right hlt (by simp)
  have hH := abs_H_ge2 p x κ hp
  rw [hxn, hyn] at hH
  have hxpos : (0 : DiffRing V) < ι xn := by rw [← hxn]; linarith
  have : (ι (xn * power (xn - 3) t) : DiffRing V) < ι xn * (2 * ι yn + 2) := by
    rw [map_mul]
    apply mul_lt_mul_of_pos_left _ hxpos
    have := ι_lt_ι.mpr hpow
    simpa only [map_add, map_mul, map_ofNat, map_one] using this
  linarith

/-! ## The signed projector -/

/-- `P138Projector.signed_main` over the weak-window record. -/
theorem signed_mainW (Fd : FoldedW p x κ) :
    ∃ d z : DiffRing V, d * d = (𝓡).Dm ∧
      d = ι (Exp.exp Fd.Rn) + (𝓡).a * ι Fd.cn + (4 * (𝓡).a + 3) * z := by
  obtain ⟨u, hu⟩ := P72ConvArith.odd_of_mod_two Fd.hodd
  set b := Fd.Bn - 2 with hb
  have hbB : (ι b : DiffRing V) = ι Fd.Bn - 2 := by
    rw [hb, ι_tsub' (le_trans (by norm_num) Fd.hB3), map_ofNat]
  have ha : (𝓡).a = (𝓡).A - 2 := by rw [A_eq]; ring
  rcases eq_or_eq_neg_abs (𝓡).A with hA | hA <;> rw [Fd.hBn] at hA
  · obtain ⟨z, hz⟩ := ArithmeticPellPowerRecovery.projection_quotient b Fd.Rn
    refine ⟨ι (xcoord Fd.Rn b), ι z, Fd.hDm.symm, ?_⟩
    have := congrArg (ι (V := V)) hz
    simp only [map_add, map_mul, map_ofNat] at this
    rw [this, Fd.hc, ha, hA, ← hbB]
  · obtain ⟨z1, z2, hz⟩ := neg_projection_odd b u
    refine ⟨-ι (xcoord Fd.Rn b), ι z2 - ι z1, by rw [neg_mul_neg]; exact Fd.hDm.symm, ?_⟩
    have := congrArg (ι (V := V)) hz
    simp only [map_add, map_mul, map_ofNat] at this
    rw [← hu] at this
    rw [ha, hA, Fd.hc]
    have hB' : (ι Fd.Bn : DiffRing V) = ι b + 2 := by rw [hbB]; ring
    rw [hB']
    linear_combination -this

set_option maxHeartbeats 2000000 in
/-- **The signed projector** `σ X = 2^R` on the weak window (`P138Projector.projector`). -/
theorem projectorW (hp : PortFacts p) (Fd : FoldedW p x κ) (Fi : FirstIndexW p x κ Fd) :
    ∃ σ : DiffRing V, (σ = 1 ∨ σ = -1) ∧ x 8 = σ * ι Fd.cn ∧
      σ * (𝓡).X = ι (Exp.exp Fd.Rn) := by
  obtain ⟨t, ht⟩ := P72ConvArith.odd_of_mod_two Fd.hodd
  obtain ⟨xn, hxn⟩ := abs_eq_ι (𝓡).X
  obtain ⟨d, z, hdd, hd⟩ := signed_mainW p x κ Fd
  have hHK := Fd.hHK
  have hlarge := H_largeW p x κ hp Fd Fi t xn ht hxn
  obtain ⟨σ, hσ, hcσ⟩ : ∃ σ : DiffRing V, (σ = 1 ∨ σ = -1) ∧ x 8 = σ * ι Fd.cn := by
    rcases eq_or_eq_neg_abs (x 8) with h | h <;> rw [Fd.hcn] at h
    · exact ⟨1, Or.inl rfl, by rw [h, one_mul]⟩
    · exact ⟨-1, Or.inr rfl, by rw [h]; ring⟩
  have hσσ : σ * σ = 1 := by rcases hσ with h | h <;> rw [h] <;> ring
  refine ⟨σ, hσ, hcσ, ?_⟩
  set T : DiffRing V := ι (Exp.exp Fd.Rn) with hT
  set X' := σ * (𝓡).X with hX'
  have hnorm : d * d = 1 + ((𝓡).a * (𝓡).a + (4 * (𝓡).a + 3)) * ι Fd.cn * ι Fd.cn := by
    rw [hdd, Dm_eq, Delta_def, H_def, hcσ]
    linear_combination (((𝓡).a * (𝓡).a + (4 * (𝓡).a + 3)) * ι Fd.cn * ι Fd.cn) * hσσ
  have hK : (4 * (𝓡).a + 3) ∣ (X' * X' + 2 * (𝓡).a * X' * ι Fd.cn - 1) ^ 5 := by
    have e : X' * X' + 2 * (𝓡).a * X' * ι Fd.cn - 1 = Kq p x κ := by
      unfold Kq; rw [hX', hcσ]
      linear_combination ((𝓡).X * (𝓡).X) * hσσ
    rw [e, ← H_def]; exact hHK
  have h5 := fifth_power (𝓡).a (ι Fd.cn) d T X' z hd hnorm hK
  rw [← H_def] at h5
  have hX66 : Exp.exp (66 : V) ≤ xn := by
    apply ι_le_ι.mp
    rw [← hxn]
    have := abs_X_ge p x κ hp
    have e : (ι (Exp.exp (66 : V)) : DiffRing V) = 2 ^ 66 := by
      have h := exp_nat (V := V) 66
      rw [Nat.cast_ofNat] at h
      rw [h, map_pow, map_ofNat]
    rw [e]; exact this
  have ht14 : (14 : V) ≤ t := by
    apply ι_le_ι.mp
    have h4 : (4080 : DiffRing V) ≤ ι Fd.Rn := by
      have := R_ge p x κ hp Fd.hs; rwa [Fd.hR] at this
    rw [ht] at h4; simp only [map_add, map_mul, map_ofNat, map_one] at h4; rw [map_ofNat]
    linarith
  have hheight := height_power xn t hX66 ht14
  have hT1 : (1 : DiffRing V) ≤ T := by rw [hT, ← map_one ι]; exact ι_le_ι.mpr (one_le_exp _)
  have hX'abs : |X'| = ι xn := by
    rw [hX', abs_mul, hxn]; rcases hσ with h | h <;> rw [h] <;> simp
  have hxn1 : (1 : DiffRing V) ≤ ι xn := by
    rw [← hxn]; have := abs_X_ge p x κ hp
    have : (1 : DiffRing V) ≤ 2 ^ 66 := one_le_pow₀ (by norm_num); linarith
  have hP : |(X' - T) * (T * X' + 1)| ≤ (ι xn * (T + 1)) ^ 2 := by
    rw [abs_mul]
    have h1 : |X' - T| ≤ ι xn * (T + 1) := by
      have := abs_add_le X' (-T)
      rw [← sub_eq_add_neg, abs_neg, hX'abs,
        abs_of_nonneg (by linarith : (0 : DiffRing V) ≤ T)] at this
      nlinarith
    have h2 : |T * X' + 1| ≤ ι xn * (T + 1) := by
      have := abs_add_le (T * X') 1
      rw [abs_mul, hX'abs, abs_of_nonneg (by linarith : (0 : DiffRing V) ≤ T), abs_one] at this
      nlinarith
    rw [sq]
    exact mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg (ι_nonneg _) (by linarith))
  have hP5 : |((X' - T) * (T * X' + 1)) ^ 5| < |(𝓡).H| := by
    rw [abs_pow]
    have h1 : |(X' - T) * (T * X' + 1)| ^ 5 ≤ ((ι xn * (T + 1)) ^ 2) ^ 5 :=
      pow_le_pow_left₀ (abs_nonneg _) hP 5
    have h2 : ((ι xn * (T + 1)) ^ 2) ^ 5 = ι ((xn * (Exp.exp Fd.Rn + 1)) ^ 10) := by
      rw [hT]; simp only [map_pow, map_mul, map_add, map_one]; ring
    have h3 : (ι ((xn * (Exp.exp Fd.Rn + 1)) ^ 10) : DiffRing V) ≤ ι (xn * power (xn - 3) t) := by
      apply ι_le_ι.mpr; rw [ht]; exact hheight
    linarith
  have h0 := eq_zero_of_dvd_lt h5 hP5
  rcases mul_eq_zero.mp ((pow_eq_zero_iff (by norm_num : (5 : ℕ) ≠ 0)).mp h0) with h | h
  · linear_combination h
  · exfalso
    have hT2 : (2 : DiffRing V) ≤ T := by
      have h1 : (1 : V) ≤ Fd.Rn := pos_iff_one_le.mp Fd.hRpos
      have h2 : (2 : V) ≤ Exp.exp Fd.Rn := by
        calc (2 : V) = Exp.exp 1 := exp_one.symm
          _ ≤ Exp.exp Fd.Rn := exp_monotone_le.mpr h1
      have h3 := ι_le_ι.mpr h2
      rw [map_ofNat] at h3
      rw [hT]; exact h3
    have hX'1 : 1 ≤ |X'| := by rw [hX'abs]; exact hxn1
    have : |T * X'| = 1 := by
      rw [show T * X' = -1 by linear_combination h, abs_neg, abs_one]
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : DiffRing V) ≤ T)] at this
    nlinarith

/-! ## Orientation -/

/-- `P138Orientation.Oriented` over the weak-window record. -/
structure OrientedW (Fd : FoldedW p x κ) where
  hq : 0 < (𝓡).q
  hJ : 0 < (𝓡).J
  hF : 0 < (𝓡).F
  hC : 0 < x 1
  hα : 0 < (𝓡).q - (𝓡).F - x 1
  hX : (𝓡).X = ι (Exp.exp Fd.Rn)
  hk : 0 < (𝓡).k
  hY : 0 < (𝓡).Y
  hc : x 8 = ι Fd.cn
  hA : (𝓡).A = ι Fd.Bn

set_option maxHeartbeats 1000000 in
/-- **Every sign is positive** on the weak window (`P138Orientation.oriented`). -/
theorem orientedW (hp : PortFacts p) (Fd : FoldedW p x κ) (Fi : FirstIndexW p x κ Fd) :
    Nonempty (OrientedW p x κ Fd) := by
  obtain ⟨σ, hσ, hcσ, hσX⟩ := projectorW p x κ hp Fd Fi
  obtain ⟨t, ht⟩ := P72ConvArith.odd_of_mod_two Fd.hodd
  have hσ1 : σ = 1 := by
    rcases hσ with h | h
    · exact h
    · exfalso
      obtain ⟨_, m, hm⟩ := X_mod p x κ hp
      have h3 := P72ConvArith.exp_odd_mod_three t
      rw [← ht] at h3
      have hd := div_add_mod (Exp.exp Fd.Rn) 3
      rw [h3] at hd
      have hι := congrArg (ι (V := V)) hd
      simp only [map_add, map_mul, map_ofNat] at hι
      rw [h] at hσX
      have : (3 : DiffRing V) * (ι (Exp.exp Fd.Rn / 3) + m + 1) = -1 := by
        linear_combination hι - hσX - hm
      rcases int_split (ι (Exp.exp Fd.Rn / 3) + m + 1) with h0 | h0 <;> linarith
  rw [hσ1, one_mul] at hcσ hσX
  have hXpos : 0 < (𝓡).X := by rw [hσX]; exact ι_pos (exp_pos _)
  have hk : 0 < (𝓡).k := (Fi.hpos hXpos).2
  have hcpos : 0 < x 8 := by rw [hcσ]; exact ι_pos Fd.hcn0
  have hY : 0 < (𝓡).Y := by
    have h1 : 0 < (𝓡).k * (𝓡).Y := (pos_iff_pos_of_mul_pos Fd.hcky).mp hcpos
    exact (pos_iff_pos_of_mul_pos h1).mp hk
  have hApos : 0 < (𝓡).A := by
    rw [A_eq, a_eq]; have := mul_pos hXpos hY; linarith
  have hA : (𝓡).A = ι Fd.Bn := by rw [← Fd.hBn, abs_of_pos hApos]
  have hq := q_pos p x κ hp Fd.Rn hσX
  obtain ⟨hF, hC, hα⟩ := Fd.hs
  have hJ : 0 < (𝓡).J := by
    have h1 := abs_q p x κ hp
    rw [abs_of_pos hq] at h1
    have hb := beta_pos p hp
    have : 0 < p 0 * (𝓡).J := by rw [beta_J]; linarith
    exact (pos_iff_pos_of_mul_pos this).mp hb
  exact ⟨⟨hq, hJ, (pos_iff_pos_of_mul_pos hF).mpr hq, (pos_iff_pos_of_mul_pos hC).mpr hq,
    (pos_iff_pos_of_mul_pos hα).mpr hq, hσX, hk, hY, hcσ, hA⟩⟩

/-- `η > 0` and `ζ = k − η > 0` from the guard `η ζ > 0` and `k > 0`. -/
theorem eta_zeta_pos (Fd : FoldedW p x κ) (hk : 0 < (𝓡).k) :
    0 < (𝓡).eta ∧ 0 < (𝓡).k - (𝓡).eta := by
  have he : 0 < (𝓡).eta := by
    by_contra h
    have h' : (𝓡).eta ≤ 0 := not_lt.mp h
    nlinarith [Fd.hez, h', hk]
  exact ⟨he, (pos_iff_pos_of_mul_pos Fd.hez).mp he⟩

end Regs

#print axioms first_indexW
#print axioms H_largeW
#print axioms projectorW
#print axioms orientedW
#print axioms eta_zeta_pos

end DiophantineConsistency.P113Chain
