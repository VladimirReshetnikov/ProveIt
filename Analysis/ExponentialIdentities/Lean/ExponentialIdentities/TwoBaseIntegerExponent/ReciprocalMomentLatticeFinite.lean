import ExponentialIdentities.TwoBaseIntegerExponent.ClearedDividedDifference
import Mathlib.Analysis.Matrix.PosDef

/-!
# Finite arithmetic core of the reciprocal Stieltjes moment lattice

For `N + 1` ordered integral nodes, the Vandermonde product clears every barycentric
denominator with one factor.  This file constructs the corresponding integral cofactor
weights explicitly, transports the signed rational moments to integers, and packages them
as an integral Hankel matrix.

The analytic input from the reciprocal Stieltjes representation is deliberately exposed as
the hypothesis `PaperPositiveDefinite`: the real cast of the Hankel matrix is positive
definite.  From that hypothesis the remaining consequences are finite arithmetic: the
determinant is a positive integer, every nonzero integral coefficient vector has quadratic
value at least one, and normalization by the zeroth moment has floor `1 / k₀`.
-/

namespace LeanProofs.TwoBaseIntegerExponent
namespace ReciprocalMomentLatticeFinite

open scoped BigOperators Matrix

noncomputable section

open ClearedDividedDifference

/-! ## One-Vandermonde cofactor clearing -/

/-- Product of the gaps ending at `j`. -/
def lowerGapProduct (N : ℕ) (node : Fin (N + 1) → ℤ) (j : Fin (N + 1)) : ℤ :=
  ∏ i ∈ Finset.Iio j, (node j - node i)

/-- Product of the gaps starting at `i`. -/
def upperGapProduct (N : ℕ) (node : Fin (N + 1) → ℤ) (i : Fin (N + 1)) : ℤ :=
  ∏ j ∈ Finset.Ioi i, (node j - node i)

/-- The oriented Vandermonde product `∏_{i<j} (node j - node i)`. -/
def vandermondeDelta (N : ℕ) (node : Fin (N + 1) → ℤ) : ℤ :=
  ∏ j, lowerGapProduct N node j

/-- Product of all Vandermonde gaps not incident with `k`.  The first product contains the
pairs whose upper endpoint is below `k`; in the second, the upper endpoint is above `k` and
the lower endpoint `k` is deleted. -/
def nonincidentGapProduct (N : ℕ) (node : Fin (N + 1) → ℤ)
    (k : Fin (N + 1)) : ℤ :=
  (∏ j ∈ Finset.Iio k, lowerGapProduct N node j) *
    ∏ j ∈ Finset.Ioi k,
      ∏ i ∈ (Finset.Iio j).erase k, (node j - node i)

/-- The signed complementary-gap product.  Its sign is chosen so that multiplying by the
signed barycentric denominator at `k` gives the oriented Vandermonde product. -/
def cofactorWeight (N : ℕ) (node : Fin (N + 1) → ℤ)
    (k : Fin (N + 1)) : ℤ :=
  (-1) ^ (Finset.Ioi k).card * nonincidentGapProduct N node k

private theorem erase_eq_Iio_union_Ioi (N : ℕ) (k : Fin (N + 1)) :
    (Finset.univ.erase k : Finset (Fin (N + 1))) =
      Finset.Iio k ∪ Finset.Ioi k := by
  ext j
  simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union,
    Finset.mem_Iio, Finset.mem_Ioi]
  omega

private theorem Iio_disjoint_Ioi (N : ℕ) (k : Fin (N + 1)) :
    Disjoint (Finset.Iio k) (Finset.Ioi k) := by
  rw [Finset.disjoint_left]
  intro j hjl hju
  simp only [Finset.mem_Iio] at hjl
  simp only [Finset.mem_Ioi] at hju
  omega

/-- Splitting the signed barycentric denominator into lower and upper incident gaps exposes
the exact parity sign from the upper nodes. -/
theorem signedDenominator_eq_lower_mul_sign_upper
    (N : ℕ) (node : Fin (N + 1) → ℤ) (k : Fin (N + 1)) :
    signedDenominator N node k =
      lowerGapProduct N node k *
        ((-1) ^ (Finset.Ioi k).card * upperGapProduct N node k) := by
  rw [signedDenominator, erase_eq_Iio_union_Ioi N k,
    Finset.prod_union (Iio_disjoint_Ioi N k)]
  congr 1
  calc
    (∏ j ∈ Finset.Ioi k, (node k - node j)) =
        ∏ j ∈ Finset.Ioi k, -(node j - node k) := by
          apply Finset.prod_congr rfl
          intro j _
          ring
    _ = (-1) ^ (Finset.Ioi k).card *
        ∏ j ∈ Finset.Ioi k, (node j - node k) := by
          rw [Finset.prod_neg]
    _ = (-1) ^ (Finset.Ioi k).card * upperGapProduct N node k := rfl

private theorem prod_lowerGapProduct_Ioi_eq
    (N : ℕ) (node : Fin (N + 1) → ℤ) (k : Fin (N + 1)) :
    (∏ j ∈ Finset.Ioi k, lowerGapProduct N node j) =
      (∏ j ∈ Finset.Ioi k,
          ∏ i ∈ (Finset.Iio j).erase k, (node j - node i)) *
        upperGapProduct N node k := by
  unfold upperGapProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  have hkj : k ∈ Finset.Iio j := Finset.mem_Iio.mpr (Finset.mem_Ioi.mp hj)
  simpa only [lowerGapProduct] using
    (Finset.prod_erase_mul (Finset.Iio j) (fun i ↦ node j - node i) hkj).symm

/-- The Vandermonde product factors into the nonincident gaps and the two incident gap
products at any chosen node. -/
theorem vandermondeDelta_eq_nonincident_mul_incident
    (N : ℕ) (node : Fin (N + 1) → ℤ) (k : Fin (N + 1)) :
    vandermondeDelta N node =
      nonincidentGapProduct N node k * lowerGapProduct N node k *
        upperGapProduct N node k := by
  unfold vandermondeDelta
  calc
    (∏ j, lowerGapProduct N node j) =
        (∏ j ∈ (Finset.univ.erase k), lowerGapProduct N node j) *
          lowerGapProduct N node k := by
            exact (Finset.prod_erase_mul Finset.univ
              (lowerGapProduct N node) (Finset.mem_univ k)).symm
    _ = ((∏ j ∈ Finset.Iio k, lowerGapProduct N node j) *
          ∏ j ∈ Finset.Ioi k, lowerGapProduct N node j) *
          lowerGapProduct N node k := by
            rw [erase_eq_Iio_union_Ioi N k,
              Finset.prod_union (Iio_disjoint_Ioi N k)]
    _ = nonincidentGapProduct N node k * lowerGapProduct N node k *
          upperGapProduct N node k := by
            rw [prod_lowerGapProduct_Ioi_eq N node k]
            unfold nonincidentGapProduct
            ring

/-- One Vandermonde factor clears the signed barycentric denominator exactly. -/
theorem cofactorWeight_mul_signedDenominator
    (N : ℕ) (node : Fin (N + 1) → ℤ) (k : Fin (N + 1)) :
    cofactorWeight N node k * signedDenominator N node k =
      vandermondeDelta N node := by
  rw [cofactorWeight, signedDenominator_eq_lower_mul_sign_upper]
  have hsign :
      ((-1 : ℤ) ^ (Finset.Ioi k).card) * ((-1 : ℤ) ^ (Finset.Ioi k).card) = 1 := by
    rw [← mul_pow]
    norm_num
  rw [vandermondeDelta_eq_nonincident_mul_incident N node k]
  calc
    ((-1 : ℤ) ^ (Finset.Ioi k).card * nonincidentGapProduct N node k) *
        (lowerGapProduct N node k *
          ((-1 : ℤ) ^ (Finset.Ioi k).card * upperGapProduct N node k)) =
        (((-1 : ℤ) ^ (Finset.Ioi k).card) *
          ((-1 : ℤ) ^ (Finset.Ioi k).card)) *
          (nonincidentGapProduct N node k * lowerGapProduct N node k *
            upperGapProduct N node k) := by ring
    _ = nonincidentGapProduct N node k * lowerGapProduct N node k *
          upperGapProduct N node k := by rw [hsign, one_mul]

theorem signedDenominator_dvd_vandermondeDelta
    (N : ℕ) (node : Fin (N + 1) → ℤ) (k : Fin (N + 1)) :
    signedDenominator N node k ∣ vandermondeDelta N node := by
  refine ⟨cofactorWeight N node k, ?_⟩
  simpa [mul_comm] using (cofactorWeight_mul_signedDenominator N node k).symm

/-! ## Integral moment transport -/

/-- The signed barycentric expression which the paper identifies with a positive Stieltjes
moment. -/
def rationalBarycentricMoment (N : ℕ) (node value : Fin (N + 1) → ℤ)
    (r : ℕ) : ℚ :=
  (-1) ^ (N + r + 1) *
    ∑ i, ((node i : ℚ) ^ r * (value i : ℚ)) /
      (signedDenominator N node i : ℚ)

/-- The one-Vandermonde-cleared signed moment. -/
def clearedMoment (N : ℕ) (node value : Fin (N + 1) → ℤ) (r : ℕ) : ℤ :=
  (-1) ^ (N + r + 1) *
    ∑ i, cofactorWeight N node i * node i ^ r * value i

/-- The same signed moment cleared only by the least common multiple of the barycentric
denominators. -/
def lcmClearedMoment (N : ℕ) (node value : Fin (N + 1) → ℤ) (r : ℕ) : ℤ :=
  (-1) ^ (N + r + 1) *
    ∑ i, clearedCoefficient N node i * node i ^ r * value i

/-- Node-only common content left when the Vandermonde clearing factor is divided by the
least common multiple of the barycentric denominators. -/
def nodeCofactorContent (N : ℕ) (node : Fin (N + 1) → ℤ) : ℤ :=
  vandermondeDelta N node / (denominatorLCM N node : ℤ)

/-- The least common multiple of the barycentric denominators divides the oriented
Vandermonde product. -/
theorem denominatorLCM_dvd_vandermondeDelta
    (N : ℕ) (node : Fin (N + 1) → ℤ) :
    (denominatorLCM N node : ℤ) ∣ vandermondeDelta N node := by
  apply Int.natAbs_dvd_natAbs.mp
  simpa using denominatorLCM_dvd N node (m := (vandermondeDelta N node).natAbs) (by
    intro i
    exact Int.natAbs_dvd_natAbs.mpr
      (signedDenominator_dvd_vandermondeDelta N node i))

theorem denominatorLCM_pos
    (N : ℕ) (node : Fin (N + 1) → ℤ) (hnode : Function.Injective node) :
    0 < denominatorLCM N node := by
  apply Nat.pos_of_ne_zero
  rw [denominatorLCM, Finset.lcm_ne_zero_iff]
  intro i _
  exact Int.natAbs_ne_zero.mpr (signedDenominator_ne_zero N node hnode i)

/-- For positively oriented distinct nodes, the node-only cofactor content is positive. -/
theorem nodeCofactorContent_pos
    (N : ℕ) (node : Fin (N + 1) → ℤ) (hnode : Function.Injective node)
    (hdelta : 0 < vandermondeDelta N node) :
    0 < nodeCofactorContent N node := by
  apply Int.ediv_pos_of_pos_of_dvd hdelta
  · exact_mod_cast (denominatorLCM_pos N node hnode).le
  · exact denominatorLCM_dvd_vandermondeDelta N node

/-- At each node, the Vandermonde cofactor is exactly the node-content multiple of the
minimal-LCM cofactor. -/
theorem nodeCofactorContent_mul_clearedCoefficient
    (N : ℕ) (node : Fin (N + 1) → ℤ) (hnode : Function.Injective node)
    (i : Fin (N + 1)) :
    nodeCofactorContent N node * clearedCoefficient N node i =
      cofactorWeight N node i := by
  have hden := signedDenominator_ne_zero N node hnode i
  apply Int.eq_of_mul_eq_mul_right hden
  calc
    (nodeCofactorContent N node * clearedCoefficient N node i) *
        signedDenominator N node i =
      nodeCofactorContent N node *
        (clearedCoefficient N node i * signedDenominator N node i) := by ring
    _ = nodeCofactorContent N node * (denominatorLCM N node : ℤ) := by
      rw [clearedCoefficient_mul_denominator]
    _ = vandermondeDelta N node := by
      exact Int.ediv_mul_cancel (denominatorLCM_dvd_vandermondeDelta N node)
    _ = cofactorWeight N node i * signedDenominator N node i := by
      exact (cofactorWeight_mul_signedDenominator N node i).symm

/-- The node-only cofactor content divides every output-dependent cleared moment, with the
quotient given by the minimally LCM-cleared moment. -/
theorem nodeCofactorContent_mul_lcmClearedMoment
    (N : ℕ) (node value : Fin (N + 1) → ℤ) (hnode : Function.Injective node)
    (r : ℕ) :
    nodeCofactorContent N node * lcmClearedMoment N node value r =
      clearedMoment N node value r := by
  rw [lcmClearedMoment, clearedMoment]
  calc
    nodeCofactorContent N node *
        ((-1 : ℤ) ^ (N + r + 1) *
          ∑ i, clearedCoefficient N node i * node i ^ r * value i) =
      (-1 : ℤ) ^ (N + r + 1) *
        (nodeCofactorContent N node *
          ∑ i, clearedCoefficient N node i * node i ^ r * value i) := by ring
    _ = (-1 : ℤ) ^ (N + r + 1) *
        ∑ i, nodeCofactorContent N node *
          (clearedCoefficient N node i * node i ^ r * value i) := by
            rw [Finset.mul_sum]
    _ =
      (-1 : ℤ) ^ (N + r + 1) *
        ∑ i, (nodeCofactorContent N node * clearedCoefficient N node i) *
          node i ^ r * value i := by
            congr 1
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = (-1 : ℤ) ^ (N + r + 1) *
        ∑ i, cofactorWeight N node i * node i ^ r * value i := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          rw [nodeCofactorContent_mul_clearedCoefficient N node hnode i]

theorem nodeCofactorContent_dvd_clearedMoment
    (N : ℕ) (node value : Fin (N + 1) → ℤ) (hnode : Function.Injective node)
    (r : ℕ) :
    nodeCofactorContent N node ∣ clearedMoment N node value r := by
  refine ⟨lcmClearedMoment N node value r, ?_⟩
  exact (nodeCofactorContent_mul_lcmClearedMoment N node value hnode r).symm

/-- The explicit cofactor weights transport the rational barycentric moment to an integer
after multiplication by the single Vandermonde factor. -/
theorem cast_clearedMoment_eq_delta_mul_rationalBarycentricMoment
    (N : ℕ) (node value : Fin (N + 1) → ℤ) (hnode : Function.Injective node)
    (r : ℕ) :
    (clearedMoment N node value r : ℚ) =
      (vandermondeDelta N node : ℚ) *
        rationalBarycentricMoment N node value r := by
  rw [clearedMoment, rationalBarycentricMoment]
  push_cast
  calc
    (-1 : ℚ) ^ (N + r + 1) *
        ∑ i, (cofactorWeight N node i : ℚ) * (node i : ℚ) ^ r * (value i : ℚ) =
      (-1 : ℚ) ^ (N + r + 1) *
        ∑ i, (vandermondeDelta N node : ℚ) *
          (((node i : ℚ) ^ r * (value i : ℚ)) /
            (signedDenominator N node i : ℚ)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          have hdenZ := signedDenominator_ne_zero N node hnode i
          have hdenQ : (signedDenominator N node i : ℚ) ≠ 0 := by
            exact_mod_cast hdenZ
          have hweight : (cofactorWeight N node i : ℚ) =
              (vandermondeDelta N node : ℚ) /
                (signedDenominator N node i : ℚ) := by
            apply (eq_div_iff hdenQ).2
            exact_mod_cast cofactorWeight_mul_signedDenominator N node i
          rw [hweight]
          ring
    _ = (vandermondeDelta N node : ℚ) *
        ((-1 : ℚ) ^ (N + r + 1) *
          ∑ i, ((node i : ℚ) ^ r * (value i : ℚ)) /
            (signedDenominator N node i : ℚ)) := by
              rw [← Finset.mul_sum]
              ring

/-! ## Integral Hankel forms and the paper-supplied positivity interface -/

/-- Hankel matrix of the cleared moments. -/
def momentHankel (N d : ℕ) (node value : Fin (N + 1) → ℤ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℤ :=
  fun i j ↦ clearedMoment N node value ((i : ℕ) + (j : ℕ))

theorem momentHankel_isSymm (N d : ℕ) (node value : Fin (N + 1) → ℤ) :
    (momentHankel N d node value).IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  simp only [momentHankel]
  rw [add_comm]

/-- Real cast of the integral moment matrix. -/
def realMomentHankel (N d : ℕ) (node value : Fin (N + 1) → ℤ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  (momentHankel N d node value).map (Int.castRingHom ℝ)

/-- Explicit interface to the paper argument: the reciprocal Stieltjes integral proves this
positive-definiteness statement when `N ≥ 2d + 1` and the node/value table comes from a
hypothetical counterexample. -/
def PaperPositiveDefinite (N d : ℕ) (node value : Fin (N + 1) → ℤ) : Prop :=
  (realMomentHankel N d node value).PosDef

/-- Integral quadratic value of the moment Hankel matrix. -/
def quadraticValue (N d : ℕ) (node value : Fin (N + 1) → ℤ)
    (c : Fin (d + 1) → ℤ) : ℤ :=
  dotProduct c (momentHankel N d node value *ᵥ c)

theorem quadraticValue_eq_doubleSum
    (N d : ℕ) (node value : Fin (N + 1) → ℤ) (c : Fin (d + 1) → ℤ) :
    quadraticValue N d node value c =
      ∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
        c i * clearedMoment N node value ((i : ℕ) + (j : ℕ)) * c j := by
  simp [quadraticValue, dotProduct, Matrix.mulVec, momentHankel, Finset.mul_sum, mul_assoc]

/-! ## Common-content amplification -/

/-- If one integer divides every cleared moment used by the truncated Hankel matrix, then it
divides every integral quadratic value of that matrix.  In applications the divisor may be
the node-only cofactor content, or the (usually larger) gcd of the actual output-dependent
moments. -/
theorem commonDivisor_dvd_quadraticValue
    (N d : ℕ) (node value : Fin (N + 1) → ℤ) (g : ℤ)
    (hdiv : ∀ r : ℕ, r ≤ 2 * d → g ∣ clearedMoment N node value r)
    (c : Fin (d + 1) → ℤ) :
    g ∣ quadraticValue N d node value c := by
  rw [quadraticValue_eq_doubleSum]
  apply Finset.dvd_sum
  intro i _
  apply Finset.dvd_sum
  intro j _
  have hij : (i : ℕ) + (j : ℕ) ≤ 2 * d := by
    have hi : (i : ℕ) ≤ d := Nat.le_of_lt_succ i.isLt
    have hj : (j : ℕ) ≤ d := Nat.le_of_lt_succ j.isLt
    omega
  obtain ⟨z, hz⟩ := hdiv ((i : ℕ) + (j : ℕ)) hij
  refine ⟨c i * z * c j, ?_⟩
  rw [hz]
  ring

/-- Entrywise common content contributes one copy from every determinant column. -/
theorem commonDivisor_pow_dvd_momentHankel_det
    (N d : ℕ) (node value : Fin (N + 1) → ℤ) (g : ℤ)
    (hdiv : ∀ r : ℕ, r ≤ 2 * d → g ∣ clearedMoment N node value r) :
    g ^ (d + 1) ∣ (momentHankel N d node value).det := by
  classical
  have hentry : ∀ i j : Fin (d + 1), g ∣ momentHankel N d node value i j := by
    intro i j
    apply hdiv
    have hi : (i : ℕ) ≤ d := Nat.le_of_lt_succ i.isLt
    have hj : (j : ℕ) ≤ d := Nat.le_of_lt_succ j.isLt
    omega
  have hprod : (∏ _j : Fin (d + 1), g) ∣ (momentHankel N d node value).det := by
    rw [Matrix.det_apply']
    apply Finset.dvd_sum
    intro σ _
    apply Dvd.dvd.mul_left
    exact Finset.prod_dvd_prod_of_dvd (fun _j : Fin (d + 1) ↦ g)
      (fun j ↦ momentHankel N d node value (σ j) j)
      (fun j _ ↦ hentry (σ j) j)
  simpa using hprod

theorem cast_quadraticValue
    (N d : ℕ) (node value : Fin (N + 1) → ℤ) (c : Fin (d + 1) → ℤ) :
    (quadraticValue N d node value c : ℝ) =
      dotProduct (fun i ↦ (c i : ℝ))
        (realMomentHankel N d node value *ᵥ fun i ↦ (c i : ℝ)) := by
  simp [quadraticValue, realMomentHankel, momentHankel, dotProduct, Matrix.mulVec,
    Finset.mul_sum]

/-- Positive definiteness makes every nonzero integral polynomial coefficient vector have a
positive integral quadratic value. -/
theorem quadraticValue_pos
    (N d : ℕ) (node value : Fin (N + 1) → ℤ)
    (hpos : PaperPositiveDefinite N d node value)
    (c : Fin (d + 1) → ℤ) (hc : c ≠ 0) :
    0 < quadraticValue N d node value c := by
  have hcR : (fun i ↦ (c i : ℝ)) ≠ 0 := by
    intro hzero
    apply hc
    funext i
    have hi : (c i : ℝ) = 0 := by simpa using congrFun hzero i
    exact_mod_cast hi
  have hp := hpos.dotProduct_mulVec_pos hcR
  have hp' : 0 < dotProduct (fun i ↦ (c i : ℝ))
      (realMomentHankel N d node value *ᵥ fun i ↦ (c i : ℝ)) := by
    simpa using hp
  rw [← cast_quadraticValue N d node value c] at hp'
  exact_mod_cast hp'

/-- Positive definiteness turns a positive common moment divisor into a strengthened lower
bound for every nonzero integral quadratic value. -/
theorem commonDivisor_le_quadraticValue
    (N d : ℕ) (node value : Fin (N + 1) → ℤ) (g : ℤ)
    (hg : 0 < g)
    (hdiv : ∀ r : ℕ, r ≤ 2 * d → g ∣ clearedMoment N node value r)
    (hpos : PaperPositiveDefinite N d node value)
    (c : Fin (d + 1) → ℤ) (hc : c ≠ 0) :
    g ≤ quadraticValue N d node value c := by
  obtain ⟨z, hz⟩ := commonDivisor_dvd_quadraticValue N d node value g hdiv c
  have hq : 0 < g * z := by
    rw [← hz]
    exact quadraticValue_pos N d node value hpos c hc
  have hzpos : 0 < z := by
    rcases (mul_pos_iff.mp hq) with h | h
    · exact h.2
    · exact (not_lt_of_ge hg.le h.1).elim
  have hzone : (1 : ℤ) ≤ z := by omega
  rw [hz]
  nlinarith

/-- Concrete node-LCM amplification of the quadratic floor. -/
theorem nodeCofactorContent_le_quadraticValue
    (N d : ℕ) (node value : Fin (N + 1) → ℤ)
    (hnode : Function.Injective node) (hdelta : 0 < vandermondeDelta N node)
    (hpos : PaperPositiveDefinite N d node value)
    (c : Fin (d + 1) → ℤ) (hc : c ≠ 0) :
    nodeCofactorContent N node ≤ quadraticValue N d node value c := by
  apply commonDivisor_le_quadraticValue N d node value (nodeCofactorContent N node)
    (nodeCofactorContent_pos N node hnode hdelta)
    (fun r _ ↦ nodeCofactorContent_dvd_clearedMoment N node value hnode r)
    hpos c hc

/-- The positive integral quadratic value has the unit floor. -/
theorem one_le_quadraticValue
    (N d : ℕ) (node value : Fin (N + 1) → ℤ)
    (hpos : PaperPositiveDefinite N d node value)
    (c : Fin (d + 1) → ℤ) (hc : c ≠ 0) :
    1 ≤ quadraticValue N d node value c := by
  have := quadraticValue_pos N d node value hpos c hc
  omega

/-- The determinant is a positive rational integer. -/
theorem momentHankel_det_pos
    (N d : ℕ) (node value : Fin (N + 1) → ℤ)
    (hpos : PaperPositiveDefinite N d node value) :
    0 < (momentHankel N d node value).det := by
  have hp := hpos.det_pos
  have hcast : (((momentHankel N d node value).det : ℤ) : ℝ) =
      (realMomentHankel N d node value).det := by
    simpa [realMomentHankel] using
      (Int.cast_det (R := ℝ) (momentHankel N d node value))
  rw [← hcast] at hp
  exact_mod_cast hp

/-- A positive common divisor of all used moments contributes its full matrix-size power to
the positive Hankel determinant. -/
theorem commonDivisor_pow_le_momentHankel_det
    (N d : ℕ) (node value : Fin (N + 1) → ℤ) (g : ℤ)
    (hg : 0 < g)
    (hdiv : ∀ r : ℕ, r ≤ 2 * d → g ∣ clearedMoment N node value r)
    (hpos : PaperPositiveDefinite N d node value) :
    g ^ (d + 1) ≤ (momentHankel N d node value).det := by
  obtain ⟨z, hz⟩ := commonDivisor_pow_dvd_momentHankel_det N d node value g hdiv
  have hgpow : 0 < g ^ (d + 1) := pow_pos hg _
  have hdet : 0 < g ^ (d + 1) * z := by
    rw [← hz]
    exact momentHankel_det_pos N d node value hpos
  have hzpos : 0 < z := by
    rcases (mul_pos_iff.mp hdet) with h | h
    · exact h.2
    · exact (not_lt_of_ge hgpow.le h.1).elim
  have hzone : (1 : ℤ) ≤ z := by omega
  rw [hz]
  nlinarith

/-- In particular, the integral Hankel determinant is at least one. -/
theorem one_le_momentHankel_det
    (N d : ℕ) (node value : Fin (N + 1) → ℤ)
    (hpos : PaperPositiveDefinite N d node value) :
    1 ≤ (momentHankel N d node value).det := by
  have := momentHankel_det_pos N d node value hpos
  omega

/-- Positive definiteness also makes the zeroth cleared moment positive. -/
theorem clearedMoment_zero_pos
    (N d : ℕ) (node value : Fin (N + 1) → ℤ)
    (hpos : PaperPositiveDefinite N d node value) :
    0 < clearedMoment N node value 0 := by
  have hp : 0 < realMomentHankel N d node value 0 0 := hpos.diag_pos
  have hp' : 0 < (clearedMoment N node value 0 : ℝ) := by
    simpa [realMomentHankel, momentHankel] using hp
  exact_mod_cast hp'

/-- The normalized squared mass represented by an integral coefficient vector. -/
def normalizedQuadraticValue
    (N d : ℕ) (node value : Fin (N + 1) → ℤ)
    (c : Fin (d + 1) → ℤ) : ℚ :=
  (quadraticValue N d node value c : ℚ) /
    (clearedMoment N node value 0 : ℚ)

/-- Output-sensitive lattice floor: after normalization by `k₀`, every nonzero integral
coefficient vector has mass at least `1 / k₀`. -/
theorem one_div_clearedMoment_zero_le_normalizedQuadraticValue
    (N d : ℕ) (node value : Fin (N + 1) → ℤ)
    (hpos : PaperPositiveDefinite N d node value)
    (c : Fin (d + 1) → ℤ) (hc : c ≠ 0) :
    (1 : ℚ) / (clearedMoment N node value 0 : ℚ) ≤
      normalizedQuadraticValue N d node value c := by
  have hk0Z := clearedMoment_zero_pos N d node value hpos
  have hk0Q : (0 : ℚ) < (clearedMoment N node value 0 : ℚ) := by
    exact_mod_cast hk0Z
  rw [normalizedQuadraticValue, div_le_div_iff_of_pos_right hk0Q]
  exact_mod_cast one_le_quadraticValue N d node value hpos c hc

/-- Common-content version of the normalized lattice floor.  Taking `g = 1` recovers the
unit bound above; taking the actual gcd of the used moments records output-sensitive Smith
mass without changing the normalized measure. -/
theorem commonDivisor_div_clearedMoment_zero_le_normalizedQuadraticValue
    (N d : ℕ) (node value : Fin (N + 1) → ℤ) (g : ℤ)
    (hg : 0 < g)
    (hdiv : ∀ r : ℕ, r ≤ 2 * d → g ∣ clearedMoment N node value r)
    (hpos : PaperPositiveDefinite N d node value)
    (c : Fin (d + 1) → ℤ) (hc : c ≠ 0) :
    (g : ℚ) / (clearedMoment N node value 0 : ℚ) ≤
      normalizedQuadraticValue N d node value c := by
  have hk0Z := clearedMoment_zero_pos N d node value hpos
  have hk0Q : (0 : ℚ) < (clearedMoment N node value 0 : ℚ) := by
    exact_mod_cast hk0Z
  rw [normalizedQuadraticValue, div_le_div_iff_of_pos_right hk0Q]
  exact_mod_cast commonDivisor_le_quadraticValue N d node value g hg hdiv hpos c hc

/-- Fully concrete normalized floor obtained from the node-only LCM cofactor content. -/
theorem nodeCofactorContent_div_clearedMoment_zero_le_normalizedQuadraticValue
    (N d : ℕ) (node value : Fin (N + 1) → ℤ)
    (hnode : Function.Injective node) (hdelta : 0 < vandermondeDelta N node)
    (hpos : PaperPositiveDefinite N d node value)
    (c : Fin (d + 1) → ℤ) (hc : c ≠ 0) :
    (nodeCofactorContent N node : ℚ) /
        (clearedMoment N node value 0 : ℚ) ≤
      normalizedQuadraticValue N d node value c := by
  exact commonDivisor_div_clearedMoment_zero_le_normalizedQuadraticValue
    N d node value (nodeCofactorContent N node)
    (nodeCofactorContent_pos N node hnode hdelta)
    (fun r _ ↦ nodeCofactorContent_dvd_clearedMoment N node value hnode r)
    hpos c hc

end

end ReciprocalMomentLatticeFinite
end LeanProofs.TwoBaseIntegerExponent
