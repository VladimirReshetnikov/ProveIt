import IntegerPoints.GKSec33LGeHalf

/-!
# Graham--Kolesnik section 3.3: nonnegativity of `k`

Integer reciprocal phases at a common-multiple scale make every summand
equal to one.  They rule out `k < 0`; in the boundary case `k = 0`, the same
construction forces `l >= 1`.
-/

open Real Finset Filter

namespace LeanProofs.IntegerPoints

namespace GKSec33

/-- At any positive-factorial common-multiple scale, every character in the
Appendix A sum is exactly one. -/
theorem appendixSum_factorial_mul (N ν : ℕ) :
    GKAppendixA.appendixSum N
      (((2 * N).factorial * ν : ℕ) : ℝ) = (N : ℂ) := by
  unfold GKAppendixA.appendixSum
  rw [GKAppendixA.intRange_nat_two]
  calc
    ∑ n ∈ Finset.Ioc N (2 * N),
        e ((((2 * N).factorial * ν : ℕ) : ℝ) / (n : ℝ)) =
        ∑ _n ∈ Finset.Ioc N (2 * N), (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [Finset.mem_Ioc] at hn
      have hn0 : 0 < n := by omega
      have hd : n ∣ (2 * N).factorial :=
        Nat.dvd_factorial hn0 hn.2
      obtain ⟨m, hm⟩ := hd
      have hquot :
          (((2 * N).factorial * ν : ℕ) : ℝ) / (n : ℝ) =
            ((((m * ν : ℕ) : ℤ) : ℝ)) := by
        rw [hm]
        push_cast
        field_simp
      rw [hquot]
      exact KL.e_int ((m * ν : ℕ) : ℤ)
    _ = (N : ℂ) := by
      have hcard : 2 * N - N = N := by omega
      rw [Finset.sum_const, Nat.card_Ioc, hcard]
      simp

/-- The exponent-pair estimate specialized to the resonant factorial scales.
The replacement `C₀ = max C 0` makes the constant's required sign explicit. -/
theorem exists_resonant_bound {k l : ℝ}
    (hpair : SatisfiesExponentPairBound k l) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (N ν : ℕ), 0 < N → 0 < ν →
      (N : ℝ) ≤ C₀ *
        ((((((2 * N).factorial * ν : ℕ) : ℝ) *
              (N : ℝ) ^ (-(2 : ℝ))) ^ k * (N : ℝ) ^ l) +
          ((((2 * N).factorial * ν : ℕ) : ℝ)⁻¹ *
            (N : ℝ) ^ (2 : ℝ))) := by
  obtain ⟨P, ε, C, hε, _hεhalf, hbound⟩ := hpair 2 (by norm_num)
  let C₀ : ℝ := max C 0
  have hC₀ : 0 ≤ C₀ := by simp [C₀]
  refine ⟨C₀, hC₀, ?_⟩
  intro N ν hN hν
  let t : ℝ := (((2 * N).factorial * ν : ℕ) : ℝ)
  have hNR : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.2 hN
  have htNat : 0 < (2 * N).factorial * ν :=
    Nat.mul_pos (Nat.factorial_pos _) hν
  have ht : 0 < t := by simpa only [t] using Nat.cast_pos.2 htNat
  have hclass := ftest_neg_mem_gkClass N P ε t hN hε ht
  have hraw := hbound (N : ℝ) t (N : ℝ) (2 * (N : ℝ))
    (L9.ftest (-t)) hNR ht hclass
  rw [norm_ftest_neg_sum_eq_appendixSum N t hN] at hraw
  have hnorm : ‖GKAppendixA.appendixSum N t‖ = (N : ℝ) := by
    rw [show GKAppendixA.appendixSum N t = (N : ℂ) by
      simpa only [t] using appendixSum_factorial_mul N ν]
    simp
  rw [hnorm] at hraw
  have hNnegpow : 0 < (N : ℝ) ^ (-(2 : ℝ)) :=
    Real.rpow_pos_of_pos hNR _
  have hbase : 0 < t * (N : ℝ) ^ (-(2 : ℝ)) :=
    mul_pos ht hNnegpow
  have hNl : 0 < (N : ℝ) ^ l := Real.rpow_pos_of_pos hNR _
  have hN2 : 0 < (N : ℝ) ^ (2 : ℝ) := Real.rpow_pos_of_pos hNR _
  have hinside0 :
      0 ≤ (t * (N : ℝ) ^ (-(2 : ℝ))) ^ k * (N : ℝ) ^ l +
        t⁻¹ * (N : ℝ) ^ (2 : ℝ) :=
    add_nonneg
      (mul_nonneg (Real.rpow_nonneg hbase.le k) hNl.le)
      (mul_nonneg (inv_nonneg.mpr ht.le) hN2.le)
  have hfinal := hraw.trans
    (mul_le_mul_of_nonneg_right (le_max_left C 0) hinside0)
  simpa only [C₀, t] using hfinal

/-- The resonant estimate at `N = 1` rules out a negative first
coordinate: both terms on its right tend to zero as the multiplier grows. -/
theorem k_nonneg_of_resonant_bound {k l C₀ : ℝ}
    (hres : ∀ (N ν : ℕ), 0 < N → 0 < ν →
      (N : ℝ) ≤ C₀ *
        ((((((2 * N).factorial * ν : ℕ) : ℝ) *
              (N : ℝ) ^ (-(2 : ℝ))) ^ k * (N : ℝ) ^ l) +
          ((((2 * N).factorial * ν : ℕ) : ℝ)⁻¹ *
            (N : ℝ) ^ (2 : ℝ)))) :
    0 ≤ k := by
  by_contra hknot
  have hk : k < 0 := lt_of_not_ge hknot
  let t : ℕ → ℝ := fun ν => 2 * (ν : ℝ)
  have htend : Tendsto t atTop atTop := by
    simpa only [t] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop
        (show (0 : ℝ) < 2 by norm_num)
  have hpow : Tendsto (fun ν : ℕ => (t ν) ^ k) atTop (nhds (0 : ℝ)) := by
    simpa only [Function.comp_def, neg_neg] using
      (tendsto_rpow_neg_atTop (y := -k) (show 0 < -k by linarith)).comp htend
  have hinv : Tendsto (fun ν : ℕ => (t ν)⁻¹) atTop (nhds (0 : ℝ)) := by
    simpa only [Function.comp_def] using tendsto_inv_atTop_zero.comp htend
  have hlim : Tendsto
      (fun ν : ℕ => C₀ * ((t ν) ^ k + (t ν)⁻¹))
      atTop (nhds (0 : ℝ)) := by
    simpa only [zero_add, mul_zero] using (hpow.add hinv).const_mul C₀
  have hev : ∀ᶠ ν : ℕ in atTop,
      (1 : ℝ) ≤ C₀ * ((t ν) ^ k + (t ν)⁻¹) := by
    refine (Filter.eventually_ge_atTop (1 : ℕ)).mono ?_
    intro ν hν
    have hνpos : 0 < ν := by omega
    simpa [t, Nat.factorial] using hres 1 ν (by norm_num) hνpos
  have hcontra : (1 : ℝ) ≤ 0 := ge_of_tendsto hlim hev
  norm_num at hcontra

/-- When the first coordinate is zero, letting the resonant multiplier grow
removes the reciprocal error.  The remaining bound `N <= C₀ N^l` forces
`l >= 1`. -/
theorem l_ge_one_of_zero_resonant_bound {l C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hres : ∀ (N ν : ℕ), 0 < N → 0 < ν →
      (N : ℝ) ≤ C₀ *
        ((((((2 * N).factorial * ν : ℕ) : ℝ) *
              (N : ℝ) ^ (-(2 : ℝ))) ^ (0 : ℝ) * (N : ℝ) ^ l) +
          ((((2 * N).factorial * ν : ℕ) : ℝ)⁻¹ *
            (N : ℝ) ^ (2 : ℝ)))) :
    1 ≤ l := by
  by_contra hlnot
  have hl : l < 1 := lt_of_not_ge hlnot
  have hall : ∀ N : ℕ, 0 < N →
      (N : ℝ) ≤ C₀ * ((N : ℝ) ^ l + 1) := by
    intro N hN
    let t : ℕ → ℝ := fun ν => (((2 * N).factorial * ν : ℕ) : ℝ)
    have hfac : (0 : ℝ) < ((2 * N).factorial : ℕ) := by positivity
    have htend : Tendsto t atTop atTop := by
      simpa only [t, Nat.cast_mul] using
        (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hfac
    have hinv : Tendsto (fun ν : ℕ => (t ν)⁻¹) atTop (nhds (0 : ℝ)) := by
      simpa only [Function.comp_def] using tendsto_inv_atTop_zero.comp htend
    have herr : Tendsto
        (fun ν : ℕ => (t ν)⁻¹ * (N : ℝ) ^ (2 : ℝ))
        atTop (nhds (0 : ℝ)) := by
      simpa only [zero_mul] using hinv.mul_const ((N : ℝ) ^ (2 : ℝ))
    have hlim : Tendsto
        (fun ν : ℕ => C₀ * ((N : ℝ) ^ l +
          (t ν)⁻¹ * (N : ℝ) ^ (2 : ℝ)))
        atTop (nhds (C₀ * (N : ℝ) ^ l)) := by
      have hsum : Tendsto
          (fun ν : ℕ => (N : ℝ) ^ l +
            (t ν)⁻¹ * (N : ℝ) ^ (2 : ℝ))
          atTop (nhds ((N : ℝ) ^ l + 0)) :=
        tendsto_const_nhds.add herr
      simpa only [add_zero] using hsum.const_mul C₀
    have hev : ∀ᶠ ν : ℕ in atTop,
        (N : ℝ) ≤ C₀ * ((N : ℝ) ^ l +
          (t ν)⁻¹ * (N : ℝ) ^ (2 : ℝ)) := by
      refine (Filter.eventually_ge_atTop (1 : ℕ)).mono ?_
      intro ν hν
      have hνpos : 0 < ν := by omega
      simpa only [Real.rpow_zero, one_mul, t] using hres N ν hN hνpos
    have hNl : (N : ℝ) ≤ C₀ * (N : ℝ) ^ l := ge_of_tendsto hlim hev
    calc
      (N : ℝ) ≤ C₀ * (N : ℝ) ^ l := hNl
      _ ≤ C₀ * ((N : ℝ) ^ l + 1) := by
        apply mul_le_mul_of_nonneg_left _ hC₀
        linarith
  exact (not_forall_nat_le_const_rpow_add_one (K := C₀) (α := l) hl) hall

end GKSec33

/-- **Graham--Kolesnik, section 3.3**: every pair satisfying the exponential
sum estimate has `k >= 0`, and the boundary case `k = 0` forces `l >= 1`. -/
theorem gk_sec33_k_nonneg_holds : gk_sec33_k_nonneg := by
  intro k l hpair
  obtain ⟨C₀, hC₀, hres⟩ := GKSec33.exists_resonant_bound hpair
  refine ⟨GKSec33.k_nonneg_of_resonant_bound hres, ?_⟩
  intro hk
  subst k
  exact GKSec33.l_ge_one_of_zero_resonant_bound hC₀ hres

end LeanProofs.IntegerPoints
