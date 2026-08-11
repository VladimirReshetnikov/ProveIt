import PolynomialFormulas.LazardQuinticAlternateProjection
import PolynomialFormulas.LazardQuinticVieta

namespace LeanProofs.PolynomialFormulas.LazardQuintic

set_option autoImplicit false

section

variable {K : Type*} [Field K] [CharZero K]

/-- Lazard's first cyclic root-difference product `T'`. -/
def rootTPrime (x : Fin 5 → K) : K :=
  (x 0 - x 1) * (x 1 - x 2) * (x 2 - x 3) *
    (x 3 - x 4) * (x 4 - x 0)

/-- Lazard's second cyclic root-difference product `U'`. -/
def rootUPrime (x : Fin 5 → K) : K :=
  (x 0 - x 2) * (x 1 - x 3) * (x 2 - x 4) *
    (x 3 - x 0) * (x 4 - x 1)

omit [CharZero K] in
theorem root_sub_ne_zero {x : Fin 5 → K} (hx : Function.Injective x)
    {i j : Fin 5} (hij : i ≠ j) : x i - x j ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  exact hij (hx h)

omit [CharZero K] in
theorem rootTPrime_ne_zero {x : Fin 5 → K} (hx : Function.Injective x) :
    rootTPrime x ≠ 0 := by
  unfold rootTPrime
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (root_sub_ne_zero hx (by decide))
          (root_sub_ne_zero hx (by decide)))
        (root_sub_ne_zero hx (by decide)))
      (root_sub_ne_zero hx (by decide)))
    (root_sub_ne_zero hx (by decide))

omit [CharZero K] in
theorem rootUPrime_ne_zero {x : Fin 5 → K} (hx : Function.Injective x) :
    rootUPrime x ≠ 0 := by
  unfold rootUPrime
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (root_sub_ne_zero hx (by decide))
          (root_sub_ne_zero hx (by decide)))
        (root_sub_ne_zero hx (by decide)))
      (root_sub_ne_zero hx (by decide)))
    (root_sub_ne_zero hx (by decide))

/-- The ordered Vandermonde product, with the orientation `x i - x j`
for `i < j`. -/
def rootVandermondeDelta (x : Fin 5 → K) : K :=
  (x 0 - x 1) * (x 0 - x 2) * (x 0 - x 3) * (x 0 - x 4) *
    (x 1 - x 2) * (x 1 - x 3) * (x 1 - x 4) *
    (x 2 - x 3) * (x 2 - x 4) * (x 3 - x 4)

omit [CharZero K] in
/-- Lazard's product `T' U'` is the negative of the ordered Vandermonde
product.  The sign is immaterial for its role as a discriminant square
root, but recording it avoids an orientation ambiguity. -/
theorem rootTPrime_mul_rootUPrime_eq_neg_vandermondeDelta
    (x : Fin 5 → K) :
    rootTPrime x * rootUPrime x = -rootVandermondeDelta x := by
  simp only [rootTPrime, rootUPrime, rootVandermondeDelta]
  ring

omit [CharZero K] in
/-- Hence `(T' U')²` is exactly the root-discriminant product. -/
theorem rootTPrime_mul_rootUPrime_sq_eq_vandermondeDelta_sq
    (x : Fin 5 → K) :
    (rootTPrime x * rootUPrime x) ^ 2 =
      rootVandermondeDelta x ^ 2 := by
  rw [rootTPrime_mul_rootUPrime_eq_neg_vandermondeDelta]
  ring

omit [CharZero K] in
theorem rootVandermondeDelta_ne_zero
    {x : Fin 5 → K} (hx : Function.Injective x) :
    rootVandermondeDelta x ≠ 0 := by
  have hproduct : rootTPrime x * rootUPrime x ≠ 0 :=
    mul_ne_zero (rootTPrime_ne_zero hx) (rootUPrime_ne_zero hx)
  rw [rootTPrime_mul_rootUPrime_eq_neg_vandermondeDelta] at hproduct
  exact neg_ne_zero.mp hproduct

def rootT (omega : FifthRootOfUnity K) (x : Fin 5 → K) : K :=
  (omega.value - omega.value ^ 4) * rootTPrime x +
    (omega.value ^ 2 - omega.value ^ 3) * rootUPrime x

def rootU (omega : FifthRootOfUnity K) (x : Fin 5 → K) : K :=
  (omega.value ^ 2 - omega.value ^ 3) * rootTPrime x -
    (omega.value - omega.value ^ 4) * rootUPrime x

/-- The `U` convention used by the explicit formulas in Lazard's Figure 3
and by the reconstruction formulas on pp. 221--222.  It is the negative of
the `U = ψ(T)` printed earlier in the paper.  Keeping the two definitions
separate records the paper's sign discrepancy instead of silently changing
one of its formulas. -/
def rootFormulaU (omega : FifthRootOfUnity K) (x : Fin 5 → K) : K :=
  -rootU omega x

omit [CharZero K] in
@[simp] theorem rootFormulaU_eq_neg_rootU
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootFormulaU omega x = -rootU omega x := rfl

def fifthRootDiscriminantFactor (omega : FifthRootOfUnity K) : K :=
  omega.value + omega.value ^ 4 - omega.value ^ 2 - omega.value ^ 3

omit [CharZero K] in
private theorem omega_pow_six (omega : FifthRootOfUnity K) :
    omega.value ^ 6 = omega.value := by
  calc
    omega.value ^ 6 = omega.value ^ 5 * omega.value := by ring
    _ = omega.value := by rw [omega.primitive.pow_eq_one]; ring

omit [CharZero K] in
private theorem omega_pow_seven (omega : FifthRootOfUnity K) :
    omega.value ^ 7 = omega.value ^ 2 := by
  calc
    omega.value ^ 7 = omega.value ^ 5 * omega.value ^ 2 := by ring
    _ = omega.value ^ 2 := by rw [omega.primitive.pow_eq_one]; ring

omit [CharZero K] in
private theorem omega_pow_eight (omega : FifthRootOfUnity K) :
    omega.value ^ 8 = omega.value ^ 3 := by
  calc
    omega.value ^ 8 = omega.value ^ 5 * omega.value ^ 3 := by ring
    _ = omega.value ^ 3 := by rw [omega.primitive.pow_eq_one]; ring

omit [CharZero K] in
theorem fifthRoot_coeff_square_sum (omega : FifthRootOfUnity K) :
    (omega.value - omega.value ^ 4) ^ 2 +
        (omega.value ^ 2 - omega.value ^ 3) ^ 2 = -5 := by
  have hsum := omega.primitive.geom_sum_eq_zero (by norm_num : 1 < 5)
  norm_num [Finset.sum_range_succ] at hsum
  calc
    (omega.value - omega.value ^ 4) ^ 2 +
          (omega.value ^ 2 - omega.value ^ 3) ^ 2 =
        omega.value ^ 2 + omega.value ^ 4 + omega.value ^ 8 +
          omega.value ^ 6 - 4 * omega.value ^ 5 := by ring
    _ = omega.value ^ 2 + omega.value ^ 4 + omega.value ^ 3 +
          omega.value - 4 := by
      rw [omega_pow_eight omega, omega_pow_six omega,
        omega.primitive.pow_eq_one]
      norm_num
    _ = -5 := by linear_combination hsum

omit [CharZero K] in
/-- The standard projection denominator expressed through the two cyclic
root-difference products. -/
theorem rootT_sq_add_rootU_sq (omega : FifthRootOfUnity K)
    (x : Fin 5 → K) :
    rootT omega x ^ 2 + rootU omega x ^ 2 =
      -5 * (rootTPrime x ^ 2 + rootUPrime x ^ 2) := by
  calc
    rootT omega x ^ 2 + rootU omega x ^ 2 =
        ((omega.value - omega.value ^ 4) ^ 2 +
          (omega.value ^ 2 - omega.value ^ 3) ^ 2) *
          (rootTPrime x ^ 2 + rootUPrime x ^ 2) := by
      simp only [rootT, rootU]
      ring
    _ = -5 * (rootTPrime x ^ 2 + rootUPrime x ^ 2) := by
      rw [fifthRoot_coeff_square_sum omega]

omit [CharZero K] in
theorem rootT_sq_add_rootFormulaU_sq (omega : FifthRootOfUnity K)
    (x : Fin 5 → K) :
    rootT omega x ^ 2 + rootFormulaU omega x ^ 2 =
      -5 * (rootTPrime x ^ 2 + rootUPrime x ^ 2) := by
  simpa [rootFormulaU] using rootT_sq_add_rootU_sq omega x

omit [CharZero K] in
theorem fifthRootDiscriminantFactor_sq (omega : FifthRootOfUnity K) :
    fifthRootDiscriminantFactor omega ^ 2 = 5 := by
  have hsum := omega.primitive.geom_sum_eq_zero (by norm_num : 1 < 5)
  norm_num [Finset.sum_range_succ] at hsum
  unfold fifthRootDiscriminantFactor
  calc
    (omega.value + omega.value ^ 4 - omega.value ^ 2 -
          omega.value ^ 3) ^ 2 =
        omega.value ^ 2 + omega.value ^ 8 + omega.value ^ 4 +
          omega.value ^ 6 + 4 * omega.value ^ 5 -
          2 * (omega.value ^ 3 + omega.value ^ 4 +
            omega.value ^ 6 + omega.value ^ 7) := by ring
    _ = omega.value ^ 2 + omega.value ^ 3 + omega.value ^ 4 +
          omega.value + 4 -
          2 * (omega.value ^ 3 + omega.value ^ 4 +
            omega.value + omega.value ^ 2) := by
      rw [omega_pow_eight omega, omega_pow_six omega,
        omega_pow_seven omega, omega.primitive.pow_eq_one]
      norm_num
    _ = 5 := by linear_combination -hsum

theorem fifthRootDiscriminantFactor_ne_zero (omega : FifthRootOfUnity K) :
    fifthRootDiscriminantFactor omega ≠ 0 := by
  intro h
  have hsquare := fifthRootDiscriminantFactor_sq omega
  rw [h] at hsquare
  norm_num at hsquare

omit [CharZero K] in
private theorem fifthRoot_change_coeff_relation
    (omega : FifthRootOfUnity K) :
    (omega.value ^ 2 - omega.value ^ 3) ^ 2 +
        (omega.value - omega.value ^ 4) *
          (omega.value ^ 2 - omega.value ^ 3) -
        (omega.value - omega.value ^ 4) ^ 2 = 0 := by
  calc
    (omega.value ^ 2 - omega.value ^ 3) ^ 2 +
          (omega.value - omega.value ^ 4) *
            (omega.value ^ 2 - omega.value ^ 3) -
          (omega.value - omega.value ^ 4) ^ 2 =
        omega.value ^ 3 + omega.value ^ 7 - omega.value ^ 2 -
          omega.value ^ 8 := by ring
    _ = 0 := by
      rw [omega_pow_seven omega, omega_pow_eight omega]
      ring

omit [CharZero K] in
private theorem fifthRoot_change_mixed_relation
    (omega : FifthRootOfUnity K) :
    (omega.value ^ 2 - omega.value ^ 3) ^ 2 -
        (omega.value - omega.value ^ 4) ^ 2 -
        4 * (omega.value - omega.value ^ 4) *
          (omega.value ^ 2 - omega.value ^ 3) =
      5 * fifthRootDiscriminantFactor omega := by
  unfold fifthRootDiscriminantFactor
  calc
    (omega.value ^ 2 - omega.value ^ 3) ^ 2 -
          (omega.value - omega.value ^ 4) ^ 2 -
          4 * (omega.value - omega.value ^ 4) *
            (omega.value ^ 2 - omega.value ^ 3) =
        5 * omega.value ^ 4 + 5 * omega.value ^ 6 -
          omega.value ^ 2 - omega.value ^ 8 -
          4 * omega.value ^ 3 - 4 * omega.value ^ 7 := by ring
    _ = 5 * (omega.value + omega.value ^ 4 - omega.value ^ 2 -
          omega.value ^ 3) := by
      rw [omega_pow_six omega, omega_pow_seven omega,
        omega_pow_eight omega]
      ring

/-- The product of the two change-of-basis coefficients is the negative of
the discriminant coefficient.  This removes all occurrences of `omega` from
the root-side `F` and `G` reductions. -/
theorem fifthRoot_change_coeff_product
    (omega : FifthRootOfUnity K) :
    (omega.value - omega.value ^ 4) *
        (omega.value ^ 2 - omega.value ^ 3) =
      -fifthRootDiscriminantFactor omega := by
  have hzero := fifthRoot_change_coeff_relation omega
  have hmixed := fifthRoot_change_mixed_relation omega
  linear_combination
    (-1 / 5 : K) * hmixed + (1 / 5 : K) * hzero

omit [CharZero K] in
theorem root_alternateDenominator_identity
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    alternateDenominator (rootT omega x) (rootU omega x) =
      5 * rootTPrime x * rootUPrime x * fifthRootDiscriminantFactor omega := by
  have hzero := fifthRoot_change_coeff_relation omega
  have hmixed := fifthRoot_change_mixed_relation omega
  unfold alternateDenominator rootT rootU
  linear_combination
    (rootTPrime x ^ 2 - rootUPrime x ^ 2) * hzero +
      (rootTPrime x * rootUPrime x) * hmixed

theorem root_alternateDenominator_ne_zero
    (omega : FifthRootOfUnity K) {x : Fin 5 → K}
    (hx : Function.Injective x) :
    alternateDenominator (rootT omega x) (rootU omega x) ≠ 0 := by
  rw [root_alternateDenominator_identity]
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero (by norm_num) (rootTPrime_ne_zero hx))
      (rootUPrime_ne_zero hx))
    (fifthRootDiscriminantFactor_ne_zero omega)

theorem rootT_rootU_not_both_zero
    (omega : FifthRootOfUnity K) {x : Fin 5 → K}
    (hx : Function.Injective x) : rootT omega x ≠ 0 ∨ rootU omega x ≠ 0 := by
  by_contra h
  push Not at h
  have halt := root_alternateDenominator_ne_zero omega hx
  apply halt
  simp [alternateDenominator, h.1, h.2]

/-- Consequently the alternate four-by-four projection system is invertible
for every ordered tuple of distinct roots and every nonzero epsilon choice. -/
theorem root_alternateProjectionMatrix_det_ne_zero
    (omega : FifthRootOfUnity K) {x : Fin 5 → K}
    (hx : Function.Injective x) {epsilon : K} (hepsilon : epsilon ≠ 0) :
    (alternateProjectionMatrix epsilon (rootT omega x) (rootU omega x)).det ≠ 0 :=
  alternateProjectionMatrix_det_ne_zero _ _ _ hepsilon
    (root_alternateDenominator_ne_zero omega hx)

omit [CharZero K] in
theorem epsilonLinearFactor_zero_implies_cubic
    {a b c d e p q : K}
    (h1 : a + b + c + d + e = 0)
    (h2 : a*b + a*c + a*d + a*e + b*c + b*d + b*e + c*d + c*e + d*e = p)
    (h3 : a*b*c + a*b*d + a*b*e + a*c*d + a*c*e + a*d*e +
      b*c*d + b*c*e + b*d*e + c*d*e = -q)
    (hf : b - c - d + e = 0) :
    5 * a ^ 3 + 4 * p * a + 8 * q = 0 := by
  have hS : a + 2 * b + 2 * e = 0 := by
    linear_combination h1 + hf
  have hT : a + 2 * c + 2 * d = 0 := by
    linear_combination h1 - hf
  have hu : 4 * (b * e + c * d) - 4 * p - 3 * a ^ 2 = 0 := by
    linear_combination 4 * h2 - (2 * a + 2 * c + 2 * d) * hS - a * hT
  linear_combination 8 * h3 - a * hu -
    (2 * a * (a + 2 * c + 2 * d) - 2 * a ^ 2 + 4 * c * d) * hS -
    (-2 * a ^ 2 + 4 * b * e) * hT

def rootEpsilonProduct (x : Fin 5 → K) : K :=
  (x 1 - x 2 - x 3 + x 4) *
    (x 2 - x 3 - x 4 + x 0) *
    (x 3 - x 4 - x 0 + x 1) *
    (x 4 - x 0 - x 1 + x 2) *
    (x 0 - x 1 - x 2 + x 3)

def rootEpsilon (omega : FifthRootOfUnity K) (x : Fin 5 → K) : K :=
  fifthRootDiscriminantFactor omega * rootEpsilonProduct x

/-- The three root expressions that instantiate Lazard's quadratic stage. -/
def rootQuadraticTriple
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) : QuadraticTriple K :=
  ⟨rootEpsilon omega x, rootT omega x, rootFormulaU omega x⟩

/-- Root-side form of Lazard's `F` numerator. -/
theorem rootEpsilon_mul_rootT_sq_sub_rootU_sq
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootEpsilon omega x * (rootT omega x ^ 2 - rootU omega x ^ 2) =
      -5 * rootEpsilonProduct x *
        (rootTPrime x ^ 2 + 4 * rootTPrime x * rootUPrime x -
          rootUPrime x ^ 2) := by
  have hzero := fifthRoot_change_coeff_relation omega
  have hab := fifthRoot_change_coeff_product omega
  have hdiff :
      ((omega.value - omega.value ^ 4) * rootTPrime x +
          (omega.value ^ 2 - omega.value ^ 3) * rootUPrime x) ^ 2 -
        ((omega.value ^ 2 - omega.value ^ 3) * rootTPrime x -
          (omega.value - omega.value ^ 4) * rootUPrime x) ^ 2 =
      ((omega.value - omega.value ^ 4) *
          (omega.value ^ 2 - omega.value ^ 3)) *
        (rootTPrime x ^ 2 + 4 * rootTPrime x * rootUPrime x -
          rootUPrime x ^ 2) := by
    linear_combination
      -(rootTPrime x ^ 2 - rootUPrime x ^ 2) * hzero
  unfold rootEpsilon rootT rootU
  rw [hdiff, hab]
  have hsquare := fifthRootDiscriminantFactor_sq omega
  linear_combination
    -(rootEpsilonProduct x *
      (rootTPrime x ^ 2 + 4 * rootTPrime x * rootUPrime x -
        rootUPrime x ^ 2)) * hsquare

/-- The `F` identity is insensitive to the sign discrepancy in `U`. -/
theorem rootEpsilon_mul_rootT_sq_sub_rootFormulaU_sq
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootEpsilon omega x *
        (rootT omega x ^ 2 - rootFormulaU omega x ^ 2) =
      -5 * rootEpsilonProduct x *
        (rootTPrime x ^ 2 + 4 * rootTPrime x * rootUPrime x -
          rootUPrime x ^ 2) := by
  simpa [rootFormulaU] using
    rootEpsilon_mul_rootT_sq_sub_rootU_sq omega x

/-- Root-side form of Lazard's `G` numerator. -/
theorem rootEpsilon_mul_rootT_mul_rootU
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootEpsilon omega x * rootT omega x * rootU omega x =
      5 * rootEpsilonProduct x *
        (-rootTPrime x ^ 2 + rootTPrime x * rootUPrime x +
          rootUPrime x ^ 2) := by
  have hzero := fifthRoot_change_coeff_relation omega
  have hab := fifthRoot_change_coeff_product omega
  have hprod :
      ((omega.value - omega.value ^ 4) * rootTPrime x +
          (omega.value ^ 2 - omega.value ^ 3) * rootUPrime x) *
        ((omega.value ^ 2 - omega.value ^ 3) * rootTPrime x -
          (omega.value - omega.value ^ 4) * rootUPrime x) =
      ((omega.value - omega.value ^ 4) *
          (omega.value ^ 2 - omega.value ^ 3)) *
        (rootTPrime x ^ 2 - rootTPrime x * rootUPrime x -
          rootUPrime x ^ 2) := by
    linear_combination
      (rootTPrime x * rootUPrime x) * hzero
  unfold rootEpsilon rootT rootU
  calc
    fifthRootDiscriminantFactor omega * rootEpsilonProduct x *
          ((omega.value - omega.value ^ 4) * rootTPrime x +
            (omega.value ^ 2 - omega.value ^ 3) * rootUPrime x) *
          ((omega.value ^ 2 - omega.value ^ 3) * rootTPrime x -
            (omega.value - omega.value ^ 4) * rootUPrime x) =
        fifthRootDiscriminantFactor omega * rootEpsilonProduct x *
          (((omega.value - omega.value ^ 4) * rootTPrime x +
            (omega.value ^ 2 - omega.value ^ 3) * rootUPrime x) *
          ((omega.value ^ 2 - omega.value ^ 3) * rootTPrime x -
            (omega.value - omega.value ^ 4) * rootUPrime x)) := by ring
    _ = fifthRootDiscriminantFactor omega * rootEpsilonProduct x *
          (((omega.value - omega.value ^ 4) *
            (omega.value ^ 2 - omega.value ^ 3)) *
          (rootTPrime x ^ 2 - rootTPrime x * rootUPrime x -
            rootUPrime x ^ 2)) := by rw [hprod]
    _ = 5 * rootEpsilonProduct x *
          (-rootTPrime x ^ 2 + rootTPrime x * rootUPrime x +
            rootUPrime x ^ 2) := by
      rw [hab]
      have hsquare := fifthRootDiscriminantFactor_sq omega
      linear_combination
        -(rootEpsilonProduct x *
          (rootTPrime x ^ 2 - rootTPrime x * rootUPrime x -
            rootUPrime x ^ 2)) * hsquare

/-- With the `U` convention actually used by Figure 3 and the final
reconstruction formulas, the product has the advertised positive sign. -/
theorem rootEpsilon_mul_rootT_mul_rootFormulaU
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootEpsilon omega x * rootT omega x * rootFormulaU omega x =
      5 * rootEpsilonProduct x *
        (rootTPrime x ^ 2 - rootTPrime x * rootUPrime x -
          rootUPrime x ^ 2) := by
  rw [rootFormulaU, mul_neg]
  rw [rootEpsilon_mul_rootT_mul_rootU]
  ring

omit [CharZero K] in
theorem rootEpsilonProduct_ne_zero
    {x : Fin 5 → K} {p q : K}
    (h1 : fiveESymm1 x = 0) (h2 : fiveESymm2 x = p)
    (h3 : fiveESymm3 x = -q)
    (hcubic : ∀ k : Fin 5, 5 * x k ^ 3 + 4 * p * x k + 8 * q ≠ 0) :
    rootEpsilonProduct x ≠ 0 := by
  have h1' : x 0 + x 1 + x 2 + x 3 + x 4 = 0 := by
    simpa [fiveESymm1] using h1
  have h2' : x 0 * x 1 + x 0 * x 2 + x 0 * x 3 + x 0 * x 4 +
      x 1 * x 2 + x 1 * x 3 + x 1 * x 4 +
      x 2 * x 3 + x 2 * x 4 + x 3 * x 4 = p := by
    simpa [fiveESymm2] using h2
  have h3' : x 0 * x 1 * x 2 + x 0 * x 1 * x 3 + x 0 * x 1 * x 4 +
      x 0 * x 2 * x 3 + x 0 * x 2 * x 4 + x 0 * x 3 * x 4 +
      x 1 * x 2 * x 3 + x 1 * x 2 * x 4 + x 1 * x 3 * x 4 +
      x 2 * x 3 * x 4 = -q := by
    simpa [fiveESymm3] using h3
  have hf0 : x 1 - x 2 - x 3 + x 4 ≠ 0 := by
    intro hf
    apply hcubic 0
    exact epsilonLinearFactor_zero_implies_cubic h1' h2' h3' hf
  have hf1 : x 2 - x 3 - x 4 + x 0 ≠ 0 := by
    intro hf
    apply hcubic 1
    apply epsilonLinearFactor_zero_implies_cubic
        (a := x 1) (b := x 2) (c := x 3) (d := x 4) (e := x 0)
        (p := p) (q := q)
    · linear_combination h1'
    · linear_combination h2'
    · linear_combination h3'
    · exact hf
  have hf2 : x 3 - x 4 - x 0 + x 1 ≠ 0 := by
    intro hf
    apply hcubic 2
    apply epsilonLinearFactor_zero_implies_cubic
        (a := x 2) (b := x 3) (c := x 4) (d := x 0) (e := x 1)
        (p := p) (q := q)
    · linear_combination h1'
    · linear_combination h2'
    · linear_combination h3'
    · exact hf
  have hf3 : x 4 - x 0 - x 1 + x 2 ≠ 0 := by
    intro hf
    apply hcubic 3
    apply epsilonLinearFactor_zero_implies_cubic
        (a := x 3) (b := x 4) (c := x 0) (d := x 1) (e := x 2)
        (p := p) (q := q)
    · linear_combination h1'
    · linear_combination h2'
    · linear_combination h3'
    · exact hf
  have hf4 : x 0 - x 1 - x 2 + x 3 ≠ 0 := by
    intro hf
    apply hcubic 4
    apply epsilonLinearFactor_zero_implies_cubic
        (a := x 4) (b := x 0) (c := x 1) (d := x 2) (e := x 3)
        (p := p) (q := q)
    · linear_combination h1'
    · linear_combination h2'
    · linear_combination h3'
    · exact hf
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hf0 hf1) hf2) hf3) hf4

theorem rootEpsilon_ne_zero
    (omega : FifthRootOfUnity K) {x : Fin 5 → K} {p q : K}
    (h1 : fiveESymm1 x = 0) (h2 : fiveESymm2 x = p)
    (h3 : fiveESymm3 x = -q)
    (hcubic : ∀ k : Fin 5, 5 * x k ^ 3 + 4 * p * x k + 8 * q ≠ 0) :
    rootEpsilon omega x ≠ 0 := by
  exact mul_ne_zero (fifthRootDiscriminantFactor_ne_zero omega)
    (rootEpsilonProduct_ne_zero h1 h2 h3 hcubic)


end

end LeanProofs.PolynomialFormulas.LazardQuintic
