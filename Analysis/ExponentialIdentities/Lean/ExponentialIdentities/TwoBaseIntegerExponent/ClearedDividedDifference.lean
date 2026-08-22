import ExponentialIdentities.TwoBaseIntegerExponent.ArbitraryNodeRepulsion

/-!
# LCM-cleared barycentric divided differences

For `N + 1` distinct integral nodes, the top divided difference has signed barycentric
denominators

`d i = ∏ j ≠ i, (node i - node j)`.

Their least common multiple clears every coefficient.  This file records the exact integral
coefficient vector, its vanishing moments below order `N`, and the resulting integer-valued
functional.  The construction is purely algebraic; no mean-value theorem for divided
differences is used here.
-/

namespace LeanProofs.TwoBaseIntegerExponent
namespace ClearedDividedDifference

open scoped BigOperators

noncomputable section

/-- The signed barycentric denominator at one node. -/
def signedDenominator (N : ℕ) (node : Fin (N + 1) → ℤ) (i : Fin (N + 1)) : ℤ :=
  ∏ j ∈ (Finset.univ.erase i), (node i - node j)

/-- The least common multiple of the absolute barycentric denominators. -/
def denominatorLCM (N : ℕ) (node : Fin (N + 1) → ℤ) : ℕ :=
  (Finset.univ : Finset (Fin (N + 1))).lcm
    (fun i ↦ (signedDenominator N node i).natAbs)

/-- The integral coefficient obtained by dividing the common denominator by the signed
barycentric denominator. -/
def clearedCoefficient (N : ℕ) (node : Fin (N + 1) → ℤ) (i : Fin (N + 1)) : ℤ :=
  (denominatorLCM N node : ℤ) / signedDenominator N node i

/-- The LCM-cleared barycentric functional on an integral value table. -/
def clearedFunctional (N : ℕ) (node value : Fin (N + 1) → ℤ) : ℤ :=
  ∑ i, clearedCoefficient N node i * value i

theorem denominator_natAbs_dvd_lcm (N : ℕ) (node : Fin (N + 1) → ℤ)
    (i : Fin (N + 1)) :
    (signedDenominator N node i).natAbs ∣ denominatorLCM N node := by
  exact Finset.dvd_lcm (Finset.mem_univ i)

/-- The clearing factor is minimal: it divides every natural number divisible by all absolute
signed denominators. -/
theorem denominatorLCM_dvd (N : ℕ) (node : Fin (N + 1) → ℤ) {m : ℕ}
    (hm : ∀ i, (signedDenominator N node i).natAbs ∣ m) :
    denominatorLCM N node ∣ m := by
  apply Finset.lcm_dvd
  intro i _
  exact hm i

theorem signedDenominator_dvd_lcm (N : ℕ) (node : Fin (N + 1) → ℤ)
    (i : Fin (N + 1)) :
    signedDenominator N node i ∣ (denominatorLCM N node : ℤ) := by
  exact Int.dvd_natCast.mpr (denominator_natAbs_dvd_lcm N node i)

theorem signedDenominator_ne_zero (N : ℕ) (node : Fin (N + 1) → ℤ)
    (hnode : Function.Injective node) (i : Fin (N + 1)) :
    signedDenominator N node i ≠ 0 := by
  rw [signedDenominator]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  rw [Finset.mem_erase] at hj
  exact sub_ne_zero.mpr (hnode.ne hj.1.symm)

theorem clearedCoefficient_mul_denominator (N : ℕ) (node : Fin (N + 1) → ℤ)
    (i : Fin (N + 1)) :
    clearedCoefficient N node i * signedDenominator N node i =
      (denominatorLCM N node : ℤ) := by
  rw [clearedCoefficient]
  exact Int.ediv_mul_cancel (signedDenominator_dvd_lcm N node i)

theorem cast_signedDenominator (N : ℕ) (node : Fin (N + 1) → ℤ)
    (i : Fin (N + 1)) :
    (signedDenominator N node i : ℝ) =
      ∏ j ∈ (Finset.univ.erase i), ((node i : ℝ) - (node j : ℝ)) := by
  simp [signedDenominator]

/-- Over the reals, a cleared coefficient is exactly the LCM divided by its signed
barycentric denominator. -/
theorem cast_clearedCoefficient (N : ℕ) (node : Fin (N + 1) → ℤ)
    (hnode : Function.Injective node) (i : Fin (N + 1)) :
    (clearedCoefficient N node i : ℝ) =
      (denominatorLCM N node : ℝ) /
        ∏ j ∈ (Finset.univ.erase i), ((node i : ℝ) - (node j : ℝ)) := by
  have hdenZ := signedDenominator_ne_zero N node hnode i
  have hdenR : (signedDenominator N node i : ℝ) ≠ 0 := by exact_mod_cast hdenZ
  rw [← cast_signedDenominator N node i]
  apply (eq_div_iff hdenR).2
  exact_mod_cast clearedCoefficient_mul_denominator N node i

/-- Every monomial moment below the divided-difference order vanishes. -/
theorem cleared_moment_eq_zero (N : ℕ) (node : Fin (N + 1) → ℤ)
    (hnode : Function.Injective node) {q : ℕ} (hq : q < N) :
    ∑ i, clearedCoefficient N node i * node i ^ q = 0 := by
  have hnodeR : Function.Injective (fun i ↦ (node i : ℝ)) := by
    intro i j hij
    apply hnode
    exact Int.cast_injective hij
  have hdd := dividedDiff_pow N (fun i ↦ (node i : ℝ)) hnodeR (Nat.le_of_lt hq)
  rw [if_neg (Nat.ne_of_gt hq)] at hdd
  rw [dividedDiff_def] at hdd
  apply Int.cast_injective (α := ℝ)
  rw [Int.cast_zero, Int.cast_sum]
  simp_rw [Int.cast_mul, Int.cast_pow]
  simp_rw [cast_clearedCoefficient N node hnode]
  calc
    ∑ i : Fin (N + 1),
        (denominatorLCM N node : ℝ) /
            (∏ j ∈ Finset.univ.erase i, ((node i : ℝ) - (node j : ℝ))) *
          (node i : ℝ) ^ q =
        (denominatorLCM N node : ℝ) *
          ∑ i : Fin (N + 1),
            (node i : ℝ) ^ q /
              ∏ j ∈ Finset.univ.erase i, ((node i : ℝ) - (node j : ℝ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = 0 := by rw [hdd, mul_zero]

/-- The real cast of the integral functional is the LCM times the ordinary divided difference
of any function with the prescribed integral values at the nodes. -/
theorem cast_clearedFunctional_eq_lcm_mul_dividedDiff
    (N : ℕ) (node value : Fin (N + 1) → ℤ) (hnode : Function.Injective node)
    (f : ℝ → ℝ) (hvalue : ∀ i, f (node i : ℝ) = (value i : ℝ)) :
    (clearedFunctional N node value : ℝ) =
      (denominatorLCM N node : ℝ) * dividedDiff N (fun i ↦ (node i : ℝ)) f := by
  rw [clearedFunctional, dividedDiff_def, Int.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Int.cast_mul, cast_clearedCoefficient N node hnode, ← hvalue i]
  ring

/-- If a real function is integral on all nodes, its divided difference becomes an integer
after multiplication by the LCM of the barycentric denominators. -/
theorem lcm_mul_dividedDiff_mem_intCast
    (N : ℕ) (node value : Fin (N + 1) → ℤ) (hnode : Function.Injective node)
    (f : ℝ → ℝ) (hvalue : ∀ i, f (node i : ℝ) = (value i : ℝ)) :
    (denominatorLCM N node : ℝ) * dividedDiff N (fun i ↦ (node i : ℝ)) f ∈
      Set.range ((↑) : ℤ → ℝ) := by
  refine ⟨clearedFunctional N node value, ?_⟩
  exact cast_clearedFunctional_eq_lcm_mul_dividedDiff N node value hnode f hvalue

/-- The four consecutive nodes used by the cubic certificate. -/
def fourNodes : Fin 4 → ℤ := ![1, 2, 3, 4]

theorem fourNodes_injective : Function.Injective fourNodes := by
  decide

theorem fourNodes_denominatorLCM : denominatorLCM 3 fourNodes = 6 := by
  decide

theorem fourNodes_denominators :
    (fun i ↦ signedDenominator 3 fourNodes i) = ![-6, 2, -2, 6] := by
  funext i
  fin_cases i <;> decide

theorem fourNodes_coefficients :
    (fun i ↦ clearedCoefficient 3 fourNodes i) = ![-1, 3, -3, 1] := by
  funext i
  fin_cases i <;> decide

/-- The concrete LCM-cleared cubic certificate is
`-value 0 + 3 value 1 - 3 value 2 + value 3`. -/
theorem fourNodes_certificate (value : Fin 4 → ℤ) :
    clearedFunctional 3 fourNodes value =
      -value 0 + 3 * value 1 - 3 * value 2 + value 3 := by
  rw [clearedFunctional]
  simp_rw [congrFun fourNodes_coefficients]
  simp [Fin.sum_univ_four]
  ring

/-- The concrete coefficient vector annihilates constant, linear, and quadratic moments. -/
theorem fourNodes_moment_eq_zero {q : ℕ} (hq : q < 3) :
    ∑ i, clearedCoefficient 3 fourNodes i * fourNodes i ^ q = 0 :=
  cleared_moment_eq_zero 3 fourNodes fourNodes_injective hq

end

end ClearedDividedDifference
end LeanProofs.TwoBaseIntegerExponent
