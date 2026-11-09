import DiophantineConsistency.P138.P138Projector
import DiophantineConsistency.ArithmeticRepunit

/-! # Orientation: every sign is positive

132-lowops §5 ("the retained orientation"), with the two steps the sources leave implicit. At a
zero, after the signed projector `σX = 2^R` (`P138Projector.projector`):

* `X ≡ 2 (mod 3)` (`P138Bootstrap.X_mod`) and `2^R ≡ 2 (mod 3)` for odd `R`
  (`P72ConvArith.exp_odd_mod_three`) force `σ = 1`: `c > 0` and `X = 2^R > 0`;
* `k > 0` (`P138FirstIndex`, the `X > 0` branch), then `Y > 0` from `0 < c (kY)`, `A > 0`;
* **`q > 0`** (new, `q_pos`): `|q|` divides `X = 2^R`, so `|q| = 2^m` (`Pow2.of_dvd`). If
  `q = −2^m`, then `β = 2^N − 1` (`N = 1064921`) divides `2^m + 1 ≡ 2^(m mod N) + 1`
  (`ArithmeticRepunit.repunit_identity`), and `0 < 2^(m mod N) + 1 ≤ 2^(N−1) + 1 < β`;
* then `J, F, C, q − F − C > 0` from the centered signs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.P138Orientation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing ZRowsCoprimeSquares P138Value P138Ports P138Bootstrap P138NoRoot
  P138Squares P138Budget P138Adjacent P138Window P138EarlyFold P138Rank P138FirstIndex P138Ratio
  P138Projector
open ArithmeticPellRecurrence ArithmeticPow ArithmeticRepunit

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `2^N − 1` divides no `2^m + 1` (`N ≥ 3`). -/
theorem not_dvd_exp_add_one (N m : V) (hN : 3 ≤ N) : ¬ (Exp.exp N - 1) ∣ Exp.exp m + 1 := by
  intro h
  have hN0 : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hdm := div_add_mod m N
  set s := m / N
  set r := m % N with hr
  have hrN : r < N := mod_lt m hN0
  have hrep := repunit_identity N s
  have hexp : Exp.exp m = (Exp.exp N - 1) * (rep N s * Exp.exp r) + Exp.exp r := by
    rw [← hdm, exp_add, ← hrep]; ring
  have hd : (Exp.exp N - 1) ∣ Exp.exp r + 1 := by
    rw [hexp] at h
    obtain ⟨w, hw⟩ := h
    refine ι_dvd_iff.mp ⟨ι w - ι (rep N s * Exp.exp r), ?_⟩
    have := congrArg (ι (V := V)) hw
    simp only [map_add, map_mul, map_one] at this ⊢
    linear_combination this
  have hle := Arithmetic.le_of_dvd (by simp : (0 : V) < Exp.exp r + 1) hd
  have h1 : Exp.exp (r + 1) ≤ Exp.exp N := exp_monotone_le.mpr (lt_iff_succ_le.mp hrN)
  rw [exp_succ] at h1
  have h8 : Exp.exp (3 : V) ≤ Exp.exp N := exp_monotone_le.mpr hN
  have e8 : Exp.exp (3 : V) = 8 := by
    rw [show (3 : V) = 0 + 1 + 1 + 1 by norm_num, exp_succ, exp_succ, exp_succ, exp_zero]; norm_num
  rw [e8] at h8
  have hsub : (ι (Exp.exp N - 1) : DiffRing V) = ι (Exp.exp N) - 1 := by
    rw [P138EarlyFold.ι_tsub' (one_le_exp N), map_one]
  have a1 := ι_le_ι.mpr hle
  have a2 := ι_le_ι.mpr h1
  have a3 := ι_le_ι.mpr h8
  rw [hsub, map_add, map_one] at a1
  rw [map_mul, map_ofNat] at a2
  rw [map_ofNat] at a3
  linarith

section Regs
variable (p : Fin 6 → DiffRing V) (x : Fin 11 → DiffRing V) (κ : DiffRing V)
local notation "𝓡" => regsK p x κ

/-- **`q > 0`** once `X = 2^R`. -/
theorem q_pos (hp : PortFacts p) (Rn : V) (hX : (𝓡).X = ι (Exp.exp Rn)) : 0 < (𝓡).q := by
  obtain ⟨Qn, hQn⟩ := abs_eq_ι (𝓡).q
  have hdvd : Qn ∣ Exp.exp Rn := by
    apply ι_dvd_iff.mp
    rw [← hQn, ← hX, X_def, ← abs_of_nonneg (show (0 : DiffRing V) ≤ (𝓡).q * (𝓡).W by
      rw [← X_def, hX]; exact ι_nonneg _)]
    exact (abs_dvd_abs _ _).mpr (dvd_mul_right _ _)
  have hpow : Pow2 Qn := Pow2.of_dvd hdvd (exp_pow2 _)
  have hQe : Exp.exp (log Qn) = Qn := exp_of_exponential (exponential_of_pow2 hpow)
  rcases lt_or_gt_of_ne (q_ne p x κ hp) with hneg | hpos
  · exfalso
    have hq : (𝓡).q = -ι (Exp.exp (log Qn)) := by rw [hQe, ← hQn, abs_of_neg hneg]; ring
    have hb := hp.beta_exp
    have hβ := beta_pos p hp
    have hbJ := beta_J p x κ
    -- `J < 0`
    have hJneg : (𝓡).J < 0 := by
      have : p 0 * (𝓡).J < 0 := by
        rw [hbJ, hq]; have := ι_nonneg (Exp.exp (log Qn)); linarith
      by_contra hc
      have := mul_nonneg hβ.le (le_of_not_gt hc); linarith
    obtain ⟨jn, hjn⟩ := abs_eq_ι (𝓡).J
    have hJ : (𝓡).J = -ι jn := by rw [← hjn, abs_of_neg hJneg]; ring
    have hβn : p 0 = ι (Exp.exp (1064921 : V) - 1) := by
      rw [P138EarlyFold.ι_tsub' (one_le_exp _), map_one]; linear_combination hb
    have hdiv : (Exp.exp (1064921 : V) - 1) ∣ Exp.exp (log Qn) + 1 := by
      refine ι_dvd_iff.mp ⟨ι jn, ?_⟩
      rw [map_add, map_one, ← hβn]
      linear_combination hbJ - p 0 * hJ + hq
    exact not_dvd_exp_add_one 1064921 (log Qn) (by norm_num) hdiv
  · exact hpos

/-- **The oriented data.** -/
structure Oriented (E : EarlyFold p x κ) (M : MainIndex p x κ E) where
  hq : 0 < (𝓡).q
  hJ : 0 < (𝓡).J
  hF : 0 < (𝓡).F
  hC : 0 < x 1
  hα : 0 < (𝓡).q - (𝓡).F - x 1
  hX : (𝓡).X = ι (Exp.exp M.Rn)
  hk : 0 < (𝓡).k
  hY : 0 < (𝓡).Y
  hc : x 8 = ι E.cn
  hA : (𝓡).A = ι E.Bn

set_option maxHeartbeats 1000000 in
theorem oriented (hp : PortFacts p) (hz : valueK p x κ = 0) (E : EarlyFold p x κ)
    (M : MainIndex p x κ E) (Fi : FirstIndex p x κ E M) : Nonempty (Oriented p x κ E M) := by
  obtain ⟨σ, hσ, hcσ, hσX⟩ := projector p x κ hp hz E M Fi
  obtain ⟨t, ht⟩ := P72ConvArith.odd_of_mod_two M.hodd
  -- `σ = 1`
  have hσ1 : σ = 1 := by
    rcases hσ with h | h
    · exact h
    · exfalso
      obtain ⟨_, m, hm⟩ := X_mod p x κ hp
      have h3 := P72ConvArith.exp_odd_mod_three t
      rw [← ht] at h3
      have hd := div_add_mod (Exp.exp M.Rn) 3
      rw [h3] at hd
      have hι := congrArg (ι (V := V)) hd
      simp only [map_add, map_mul, map_ofNat] at hι
      rw [h] at hσX
      -- `−X = 3 q' + 2` and `X = 3 m + 2`
      have : (3 : DiffRing V) * (ι (Exp.exp M.Rn / 3) + m + 1) = -1 := by
        linear_combination hι - hσX - hm
      rcases int_split (ι (Exp.exp M.Rn / 3) + m + 1) with h0 | h0 <;> linarith
  rw [hσ1, one_mul] at hcσ hσX
  have hXpos : 0 < (𝓡).X := by rw [hσX]; exact ι_pos (exp_pos _)
  have hk : 0 < (𝓡).k := (Fi.hpos hXpos).2
  have hcpos : 0 < x 8 := by rw [hcσ]; exact ι_pos E.hcn0
  have hB : 0 < (𝓡).Budget := by linarith [budget_ge p x κ hp hz]
  have hY : 0 < (𝓡).Y := by
    have h := (c_interval p x κ hp hB).2.2
    have h1 : 0 < (𝓡).k * (𝓡).Y := (pos_iff_pos_of_mul_pos h).mp hcpos
    exact (pos_iff_pos_of_mul_pos h1).mp hk
  have hApos : 0 < (𝓡).A := by
    rw [A_eq, a_eq]; have := mul_pos hXpos hY; linarith
  have hA : (𝓡).A = ι E.Bn := by rw [← E.hBn, abs_of_pos hApos]
  have hq := q_pos p x κ hp M.Rn hσX
  obtain ⟨hF, hC, hα⟩ := signs p x κ hp hz
  have hJ : 0 < (𝓡).J := by
    have h1 := abs_q p x κ hp
    rw [abs_of_pos hq] at h1
    have hb := beta_pos p hp
    have : 0 < p 0 * (𝓡).J := by rw [beta_J]; linarith
    exact (pos_iff_pos_of_mul_pos this).mp hb
  exact ⟨⟨hq, hJ, (pos_iff_pos_of_mul_pos hF).mpr hq, (pos_iff_pos_of_mul_pos hC).mpr hq,
    (pos_iff_pos_of_mul_pos hα).mpr hq, hσX, hk, hY, hcσ, hA⟩⟩

end Regs

#print axioms not_dvd_exp_add_one
#print axioms q_pos
#print axioms oriented

end DiophantineConsistency.P138Orientation
