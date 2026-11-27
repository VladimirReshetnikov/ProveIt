import GRHArticle.SingularModuli.ClassPolynomialRootEnclosure

/-!
# Finite rational checks for the two quartic class-polynomial certificates
-/

namespace GRHArticle.SingularModuli

/-- Multiply the two quadratic factors of a monic quartic by pairing the roots. -/
def quarticCoefficients {A : Type*} (add mul : A → A → A) (neg : A → A)
    (one : A) (j : Fin 4 → A) : Fin 5 → A :=
  let s := add (j 0) (j 1)
  let t := add (j 2) (j 3)
  let p := mul (j 0) (j 1)
  let q := mul (j 2) (j 3)
  ![mul p q, neg (add (mul p t) (mul s q)), add (add p (mul s t)) q, neg (add s t), one]

def quartic55AnalyticCoefficientBox (n : Fin 5) : RationalComplexBox :=
  quarticCoefficients RationalComplexBox.add RationalComplexBox.mul RationalComplexBox.neg
    (RationalComplexBox.point 1 0) (fun i ↦ modularInvariantBox (quartic55QBox i)) n

def quartic68AnalyticCoefficientBox (n : Fin 5) : RationalComplexBox :=
  quarticCoefficients RationalComplexBox.add RationalComplexBox.mul RationalComplexBox.neg
    (RationalComplexBox.point 1 0) (fun i ↦ modularInvariantBox (quartic68QBox i)) n

/-- Every real number in this interval is within half a unit of `k`. -/
def RationalInterval.IsolatesInteger (A : RationalInterval) (k : ℤ) : Prop :=
  (k : ℚ) - 1 / 2 < A.lo ∧ A.hi < (k : ℚ) + 1 / 2

instance (A : RationalInterval) (k : ℤ) : Decidable (A.IsolatesInteger k) := by
  unfold RationalInterval.IsolatesInteger
  infer_instance

def quartic55PrintedCoefficient : Fin 5 → ℤ :=
  ![-18577989025032784359375, 172576736359017890625, -20948398473375, 13136684625, 1]

def quartic68PrintedCoefficient : Fin 5 → ℤ :=
  ![-2089297506304000000000000, -318507038720000000000, -75843692160000000, -178211040000, 1]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem quartic55_denominators_pos (i : Fin 4) :
    modularInvariantBoxDenominatorPositive (quartic55QBox i) := by
  fin_cases i <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem quartic68_denominators_pos (i : Fin 4) :
    modularInvariantBoxDenominatorPositive (quartic68QBox i) := by
  fin_cases i <;> decide +kernel

/-- The rational box encloses the actual modular invariant at each
reduced representative of discriminant -55. -/
theorem quartic55_modularInvariant_box_contains (i : Fin 4) :
    (modularInvariantBox (quartic55QBox i)).Contains
      (modularInvariant (quadraticPoint 55 (quartic55Form i).a (quartic55Form i).b)) := by
  have hm : quartic55Form i ∈ reducedForms 55 := by fin_cases i <;> decide +kernel
  exact modularInvariantBox_contains hm (quartic55QBox_contains i) (quartic55_denominators_pos i)

/-- The rational box encloses the actual modular invariant at each
reduced representative of discriminant -68. -/
theorem quartic68_modularInvariant_box_contains (i : Fin 4) :
    (modularInvariantBox (quartic68QBox i)).Contains
      (modularInvariant (quadraticPoint 68 (quartic68Form i).a (quartic68Form i).b)) := by
  have hm : quartic68Form i ∈ reducedForms 68 := by fin_cases i <;> decide +kernel
  exact modularInvariantBox_contains hm (quartic68QBox_contains i) (quartic68_denominators_pos i)

end GRHArticle.SingularModuli
