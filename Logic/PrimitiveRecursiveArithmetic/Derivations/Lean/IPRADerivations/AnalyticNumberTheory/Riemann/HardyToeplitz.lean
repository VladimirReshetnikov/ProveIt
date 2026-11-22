import IPRADerivations.AnalyticNumberTheory.Riemann.UniversalCriteria
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Imported from the packet `analytic-number-theory/riemann_ipra_formalization_2026-11-20`,
`HardyToeplitz.lean`: the namespace is placed under `LeanProofs.IPRA.AnalyticNumberTheory.Riemann`, the imports
are rewritten to the library, and axioms are audited in `Checks/Axioms.lean`. -/

/-! Finite Toeplitz contractions and their integer polarizations. -/
namespace LeanProofs.IPRA.AnalyticNumberTheory.Riemann.RiemannIPRA.HardyToeplitz
open LeanProofs.ConciseIPRA PacketLanguage Discrete
open scoped BigOperators

inductive Test where
  | impulse | polynomial | polarization

private def factE {ctx} (a : E ctx) : E ctx := call PrimeForms.factCode [a]
private def centreE {ctx} (i : E ctx) : E ctx := powE 2 i + 4
private def qE {ctx} (c : E ctx) : E ctx := 2*c
private def pE {ctx} (c : E ctx) : E ctx := (2*c-1)*c-1

/-- Positive and negative pieces of the integer T_k, for 0 ≤ k < m. -/
def coefficient (neg : Bool) : PR 8 := program ["d","H","u","v","i","m","N","k"] <|
  let c := centreE (v "i")
  let N := v "N"
  let m := v "m"
  let k := v "k"
  let a := call (Taylor.numerator neg) [v "d",v "H",v "u",v "v",c,k,N]
  N * powE (pE c) k * a * powE (qE c) (m-k) *
    divE (factE m) (factE k) * powE N (2*(m-k))

/-- The integer norm budget S. d indexes actual degree d+1. -/
def budget : PR 5 := program ["d","H","i","m","N"] <|
  let c := centreE (v "i")
  let d := v "d"+1
  let N := v "N"
  let m := v "m"
  let q := qE c
  let U := 1000*c*(1000*powE (d+1) 4*powE (v "H"+2) 2)*powE q 3
  let L := powE q m * factE m * powE N (2*m) * powE (factE N) c
  L * (N*U + m*9*(d+1)*powE (c+1) m)

private def lane {ctx} (w b h : E ctx) (slot : Nat) := digitE w b (4*h + E.num slot)
private def mag {ctx} (a b : E ctx) := (a-b)+(b-a)

/-- The positive/negative summands of the integer convolution output. -/
def outputSide (neg : Bool) : PR 10 := program ["d","H","u","v","i","m","N","w","b","row"] <|
  sumTo "col" (v "row"+1) <|
    let k := v "row" - v "col"
    let a := fun s => call (coefficient s) [v "d",v "H",v "u",v "v",v "i",v "m",v "N",k]
    let xp := lane (v "w") (v "b") (v "col") 0
    let xm := lane (v "w") (v "b") (v "col") 1
    a neg*xp + a (!neg)*xm

private abbrev ctx9 := ["d","H","u","v","i","m","N","w","b"]
private abbrev rows := "row" :: ctx9

private def z (s : Bool) : E rows := call (outputSide s)
  [v "d",v "H",v "u",v "v",v "i",v "m",v "N",v "w",v "b",v "row"]
private def term (s : Bool) : E rows := call (coefficient s)
  [v "d",v "H",v "u",v "v",v "i",v "m",v "N",v "row"]
private def component (slot : Nat) : E rows := lane (v "w") (v "b") (v "row") slot
private def squares (a b : E rows) : E ctx9 := sumTo "row" (v "m") (powE (mag a b) 2)
private def crossSide (s : Bool) : E ctx9 := sumTo "row" (v "m") <|
  z s * component 2 + z (!s) * component 3

/-- Arithmetic excess with actual m,N and a supplied radix and word. -/
def excess9 (mode : Test) : PR 9 := program ctx9 <|
  let S := call budget [v "d",v "H",v "i",v "m",v "N"]
  let B := powE S 2 * squares (component 0) (component 1)
  match mode with
  | .impulse => squares (term false) (term true) - powE S 2
  | .polynomial => squares (z false) (z true) - B
  | .polarization => 2*crossSide false - (2*crossSide true + B + squares (component 2) (component 3))

/-- The word doubles as a bound on the radix offset. Leading zero digits
allow a sufficiently large representative of every pair of integer vectors. -/
def matrix (mode : Test) : PR 8 := program ["d","H","u","v","i","h","t","w"] <|
  maxTo "j" (v "w"+1) (call (excess9 mode)
    [v "d",v "H",v "u",v "v",v "i",v "h"+1,v "t"+1,v "w",v "j"+2])

def statement (family : Family) (mode : Test) : Fm PTm 0 := family.close8 (matrix mode)
theorem family_reading (family : Family) (mode : Test) :
    naturalTerms.Holds (statement family mode) Fin.elim0 ↔
      family.allData (fun p => ∀ i h t w, value (matrix mode) (p.work i h t w) = 0) :=
  holds8 _ _

theorem scheduled (family : Family) (mode : Test) (g : PR 1) : Prf PRAAx []
    (Fm.iff (statement family mode) ((UniversalCriteria.block (statement family mode)).schedule g)) :=
  UniversalCriteria.scheduled (UniversalCriteria.eight family _) g

/-! Arithmetic reading of the compiled bound, coefficients, convolutions and tests. -/

private theorem factValue (e : Fin 1 → Nat) : value PrimeForms.factCode e = Taylor.fact (e 0) := by
  unfold PrimeForms.factCode
  rw [value_program]
  change overRange 1 _ _ = _
  simp only [Discrete.plus]
  change overRange 1 (fun i a => a*(i+1)) (e 0) = _
  generalize e 0 = n
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun a => a*(n+1)) ih

private theorem denFact {ctx} (a : E ctx) (e) :
    denote (factE a) e = Taylor.fact (denote a e) := factValue _

private theorem sideValue (neg : Bool) (e : Fin 7 → Nat) :
    value (Taylor.numerator neg) e = Taylor.sumSide ⟨e 0,e 1,e 2,e 3⟩ neg (e 4) (e 5) (e 6) := by
  apply Eq.trans _ (Taylor.numerator_reading ⟨e 0,e 1,e 2,e 3⟩ neg (e 4) (e 5) (e 6))
  apply congrArg (value _)
  funext ⟨i,h⟩
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => rfl
  | n+7 => omega

private theorem denSide {ctx} (neg : Bool) (d h u v c k N : E ctx) (e) :
    denote (call (Taylor.numerator neg) [d,h,u,v,c,k,N]) e =
    Taylor.sumSide ⟨denote d e,denote h e,denote u e,denote v e⟩ neg
      (denote c e) (denote k e) (denote N e) := sideValue neg _

def coeff (p : Data) (neg : Bool) (i m N k : Nat) : Nat :=
  let c := 2^i+4
  N*((2*c-1)*c-1)^k * Taylor.sumSide p neg c k N *
    (2*c)^(m-k) * (Taylor.fact m / Taylor.fact k) * N^(2*(m-k))

theorem coefficient_reading (neg : Bool) (e : Fin 8 → Nat) :
    value (coefficient neg) e = coeff ⟨e 0,e 1,e 2,e 3⟩ neg (e 4) (e 5) (e 6) (e 7) := by
  unfold coefficient
  rw [value_program]
  simp only [pE, qE, centreE, Discrete.times, Discrete.power, Discrete.plus, Discrete.minus,
    denote_divE, denFact, denSide]
  rfl

private theorem denCoeff {ctx} (neg : Bool) (d h u v i m N k : E ctx) (e) :
    denote (call (coefficient neg) [d,h,u,v,i,m,N,k]) e =
    coeff ⟨denote d e,denote h e,denote u e,denote v e⟩ neg
      (denote i e) (denote m e) (denote N e) (denote k e) := coefficient_reading neg _

def bound (d H i m N : Nat) : Nat :=
  let c := 2^i+4
  let q := 2*c
  let U := 1000*c*(1000*(d+1+1)^4*(H+2)^2)*q^3
  let L := q^m * Taylor.fact m * N^(2*m) * (Taylor.fact N)^c
  L*(N*U + m*9*(d+1+1)*(c+1)^m)

theorem budget_reading (e : Fin 5 → Nat) :
    value budget e = bound (e 0) (e 1) (e 2) (e 3) (e 4) := by
  unfold budget
  rw [value_program]
  simp only [qE, centreE, Discrete.times, Discrete.power, Discrete.plus,denFact]
  rfl

private theorem denBudget {ctx} (d h i m N : E ctx) (e) :
    denote (call budget [d,h,i,m,N]) e =
    bound (denote d e) (denote h e) (denote i e) (denote m e) (denote N e) := budget_reading _

def dig (w b h slot : Nat) := w / b^(4*h+slot) % b
private theorem denLane {ctx} (w b h : E ctx) (slot : Nat) (e) :
    denote (lane w b h slot) e = dig (denote w e) (denote b e) (denote h e) slot := by
  unfold lane digitE dig
  rw [denote_modE, denote_divE]
  change _ / denote (powE b _) e % _ = _
  rw [Discrete.power, Discrete.plus, Discrete.times]
  rfl

private theorem overSum (f : Nat → Nat) (n : Nat) :
    overRange 0 (fun i a => a+f i) n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp [overRange]
  | succ n ih => simpa [Finset.sum_range_succ,overRange] using congrArg (fun a => a+f n) ih

private theorem denSum {ctx} (s : String) (n : E ctx) (g : E (s::ctx)) (e) :
    denote (sumTo s n g) e = ∑ j ∈ Finset.range (denote n e), denote g (Fin.cases j e) :=
  overSum _ _

def rowSide (p : Data) (neg : Bool) (i m N w b row : Nat) : Nat :=
  ∑ j ∈ Finset.range (row+1),
    (coeff p neg i m N (row-j) * dig w b j 0 + coeff p (!neg) i m N (row-j) * dig w b j 1)

theorem output_reading (neg : Bool) (e : Fin 10 → Nat) :
    value (outputSide neg) e =
    rowSide ⟨e 0,e 1,e 2,e 3⟩ neg (e 4) (e 5) (e 6) (e 7) (e 8) (e 9) := by
  unfold outputSide
  rw [value_program]
  simp only [denSum, Discrete.plus, Discrete.minus, Discrete.times, denCoeff, denLane]
  rfl

private theorem denOutput {ctx} (s : Bool) (d H u v i m N w b h : E ctx) (e) :
    denote (call (outputSide s) [d,H,u,v,i,m,N,w,b,h]) e =
    rowSide ⟨denote d e,denote H e,denote u e,denote v e⟩ s (denote i e)
      (denote m e) (denote N e) (denote w e) (denote b e) (denote h e) := output_reading s _

/-- An executable, digitwise reading of each row of the test. The integer
y=Mx in the polarization identity is represented by the difference of rowSide outputs. -/
def check (mode : Test) (p : Data) (i m N w b : Nat) : Prop :=
  let S := bound p.degreeOffset p.height i m N
  let D := dig w b
  let Z := fun s => rowSide p s i m N w b
  let A := fun s => coeff p s i m N
  let absDiff := fun a b : Nat => (a-b)+(b-a)
  let B := S^2*(∑ j ∈ Finset.range m, (absDiff (D j 0) (D j 1))^2)
  match mode with
  | .impulse => (∑ j ∈ Finset.range m, (absDiff (A false j) (A true j))^2) ≤ S^2
  | .polynomial => (∑ j ∈ Finset.range m, (absDiff (Z false j) (Z true j))^2) ≤ B
  | .polarization =>
    2*(∑ j ∈ Finset.range m, (Z false j*D j 2 + Z true j*D j 3)) ≤
    2*(∑ j ∈ Finset.range m, (Z true j*D j 2 + Z false j*D j 3)) +
    B + ∑ j ∈ Finset.range m, (absDiff (D j 2) (D j 3))^2

theorem excess_reading (mode : Test) (e : Fin 9 → Nat) :
    value (excess9 mode) e = 0 ↔
    check mode ⟨e 0,e 1,e 2,e 3⟩ (e 4) (e 5) (e 6) (e 7) (e 8) := by
  cases mode <;> unfold excess9 <;> rw [value_program] <;>
    simp only [squares, mag, crossSide, component, term, z, denOutput, denCoeff, denSum,
      denLane, denBudget, Discrete.power, Discrete.times, Discrete.plus, Discrete.minus,
      Nat.sub_eq_zero_iff_le] <;> rfl

private theorem maxZero (f : Nat → Nat) (n : Nat) :
    overRange 0 (fun i a => max a (f i)) n = 0 ↔ ∀ i < n, f i = 0 := by
  induction n with
  | zero => simp [overRange]
  | succ n ih =>
    change max (overRange 0 (fun i a => max a (f i)) n) (f n) = 0 ↔ _
    constructor
    · intro H i hi
      have : overRange 0 (fun i a => max a (f i)) n = 0 ∧ f n = 0 := by omega
      obtain rfl | hlt := eq_or_lt_of_le (Nat.le_of_lt_succ hi)
      · exact this.2
      · exact ih.mp this.1 _ hlt
    · intro H
      have h0 := ih.mpr (fun i hi => H i (by omega))
      have h1 := H n (by omega)
      simp [h0,h1]

private theorem denMaxZero {ctx} (s : String) (n : E ctx) (g : E (s::ctx)) (e) :
    denote (maxTo s n g) e = 0 ↔ ∀ j < denote n e, denote g (Fin.cases j e) = 0 := maxZero _ _

private theorem denExcess {ctx} (mode : Test) (d H u v i m N w b : E ctx) (e) :
    denote (call (excess9 mode) [d,H,u,v,i,m,N,w,b]) e = 0 ↔
    check mode ⟨denote d e,denote H e,denote u e,denote v e⟩ (denote i e)
      (denote m e) (denote N e) (denote w e) (denote b e) := excess_reading mode _

theorem matrix_check (mode : Test) (p : Data) (i h t w : Nat) :
    value (matrix mode) (p.work i h t w) = 0 ↔
    ∀ j < w+1, check mode p i (h+1) (t+1) w (j+2) := by
  unfold matrix
  rw [value_program]
  simp only [denMaxZero, denExcess, Discrete.plus]
  rfl

theorem statement_check (family : Family) (mode : Test) :
    naturalTerms.Holds (statement family mode) Fin.elim0 ↔
      family.allData (fun p => ∀ i h t w j, j < w+1 → check mode p i (h+1) (t+1) w (j+2)) := by
  rw [family_reading]
  apply family.lift_iff
  intro p
  simp only [matrix_check]

/-- Native arithmetic lemma. Completion of squares is valid even for
integer threshold b < 0; neither an eigenvalue theorem nor division occurs. -/
theorem polarization_iff {ι : Type*} (s : Finset ι) (z : ι → ℤ) (b : ℤ) :
    (∑ i ∈ s, (z i)^2) ≤ b ↔
      ∀ y : ι → ℤ, 2*(∑ i ∈ s, y i*z i) ≤ b + ∑ i ∈ s, (y i)^2 := by
  constructor
  · intro hb y
    have hpoint : ∀ i ∈ s, 2*(y i * z i) ≤ (z i)^2 + (y i)^2 := by
      intro i _
      nlinarith [sq_nonneg (y i - z i)]
    have h := Finset.sum_le_sum hpoint
    rw [← Finset.mul_sum, Finset.sum_add_distrib] at h
    linarith
  · intro h
    have hh := h z
    simp only [← sq] at hh
    omega

theorem contraction_iff_block {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (M : (κ → ℤ) → ι → ℤ) (S : ℤ) :
    (∀ x : κ → ℤ, (∑ i ∈ s, (M x i)^2) ≤ S^2*(∑ j ∈ t, (x j)^2)) ↔
    ∀ x : κ → ℤ, ∀ y : ι → ℤ, 2*(∑ i ∈ s, y i*M x i) ≤
      S^2*(∑ j ∈ t, (x j)^2) + ∑ i ∈ s, (y i)^2 := by
  exact forall_congr' fun x => polarization_iff s (M x) _

/-! A fourth criterion uses shifted leading principal determinants. -/
private abbrev gramCtx := ["d","H","u","v","i","m","N","a","b"]
private abbrev gramRows := "row" :: gramCtx

private def matrixEntry (s : Bool) (column : E gramRows) : E gramRows :=
  leB column (v "row") * call (coefficient s)
    [v "d",v "H",v "u",v "v",v "i",v "m",v "N",v "row"-column]

/-- Positive/negative components of (MᵀM)_{a,b}. -/
def gramSide (neg : Bool) : PR 9 := program gramCtx <|
  sumTo "row" (v "m") <|
    matrixEntry false (v "a") * matrixEntry neg (v "b") +
    matrixEntry true (v "a") * matrixEntry (!neg) (v "b")

/-- Signed components of I+k(S²I−MᵀM). -/
def shiftedSide (neg : Bool) : PR 10 := program ["d","H","u","v","i","m","N","k","a","b"] <|
  let gram := call (gramSide (!neg))
    [v "d",v "H",v "u",v "v",v "i",v "m",v "N",v "a",v "b"]
  let diag := eqB (v "a") (v "b") *
    (1+v "k"*powE (call budget [v "d",v "H",v "i",v "m",v "N"]) 2)
  (if neg then 0 else diag) + v "k"*gram

/-- A digit permutation is stored in base h+1. -/
def permBit : PR 2 := program ["h","perm"] <|
  allTo "a" (v "h") <|
    leB (digitE (v "perm") (v "h"+1) (v "a") + 1) (v "h") *
    allTo "b" (v "a") (eqB (eqB (digitE (v "perm") (v "h"+1) (v "a"))
      (digitE (v "perm") (v "h"+1) (v "b"))) 0)

def inversions : PR 2 := program ["h","perm"] <|
  sumTo "a" (v "h") <| sumTo "b" (v "a") <|
    leB (digitE (v "perm") (v "h"+1) (v "a")+1) (digitE (v "perm") (v "h"+1) (v "b"))

/-- Leibniz formula expanded over the signs of the h integer entries. -/
def determinantSide (neg : Bool) : PR 9 := program ["d","H","u","v","i","m","N","k","h"] <|
  sumTo "perm" (powE (v "h"+1) (v "h")) <|
    call permBit [v "h",v "perm"] * sumTo "mask" (powE 2 (v "h")) (
      let parity := modE (call inversions [v "h",v "perm"] +
        sumTo "a" (v "h") (digitE (v "mask") 2 (v "a"))) 2
      eqB parity (if neg then 1 else 0) * prodTo "a" (v "h") (
        let b := digitE (v "perm") (v "h"+1) (v "a")
        let entry := fun s => call (shiftedSide s)
          [v "d",v "H",v "u",v "v",v "i",v "m",v "N",v "k",v "a",b]
        iteE (digitE (v "mask") 2 (v "a")) (entry true) (entry false)))

/-- Every leading principal determinant of the indicated shifted matrix is positive. -/
def leadingMatrix : PR 8 := program ["d","H","u","v","i","length","precision","k"] <|
  maxTo "j" (v "length"+1) <|
    let side : Bool → E ["j","d","H","u","v","i","length","precision","k"] := fun s => call (determinantSide s)
      [v "d",v "H",v "u",v "v",v "i",v "length"+1,v "precision"+1,v "k",v "j"+1]
    (side true+1)-side false

def leadingStatement (family : Family) : Fm PTm 0 := family.close8 leadingMatrix

theorem leading_scheduled (family : Family) (g : PR 1) : Prf PRAAx []
    (Fm.iff (leadingStatement family) ((UniversalCriteria.block (leadingStatement family)).schedule g)) :=
  UniversalCriteria.scheduled (UniversalCriteria.eight family _) g

/-- Over integers, shifts classify nonnegative quadratic forms by strict
positivity. x=0 is excluded in the strict test. -/
theorem nonneg_iff_all_shifts (a b : ℤ) (hb : 0 < b) :
    0 ≤ a ↔ ∀ k : ℕ, 0 < b+(k:ℤ)*a := by
  constructor
  · intro ha k
    have := mul_nonneg (Nat.cast_nonneg (α := ℤ) k) ha
    omega
  · intro hs
    by_cases ha : 0 ≤ a
    · exact ha
    · have h := hs ((b+1).toNat)
      rw [Int.toNat_of_nonneg (by omega)] at h
      have hb1 : 0 ≤ b+1 := by omega
      have ha1 : 0 ≤ -a-1 := by omega
      nlinarith [mul_nonneg hb1 ha1]

/-- Clearing all fixed denominators reduces removing the precision
allowance to choosing precision J+1. -/
theorem remove_allowance (A B J : Nat) (h : ∀ n, (n+1)*A ≤ (n+1)*B + J) : A ≤ B := by
  by_cases H : A ≤ B
  · exact H
  · have h1 := h J
    have h2 := Nat.mul_le_mul_left (J+1) (show B+1 ≤ A by omega)
    rw [Nat.mul_add,Nat.mul_one] at h2
    omega

/-- Algebraic finite-difference substitute for the derivative estimate. -/
theorem monomial_increment (a b : ℚ) (ha : 0 ≤ a) (hab : a ≤ b) (k : Nat) :
    b^(k+1)-a^(k+1) ≤ ((k:ℚ)+1)*b^k*(b-a) := by
  have hb : 0 ≤ b := ha.trans hab
  induction k with
  | zero => simp
  | succ k ih =>
    have bound1 := mul_le_mul_of_nonneg_left ih hb
    have bound2 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hab (k+1)) (sub_nonneg.mpr hab)
    push_cast
    rw [pow_succ b (k+1),pow_succ a (k+1)]
    simp only [pow_succ b k] at *
    linarith only [add_le_add bound1 bound2]

end LeanProofs.IPRA.AnalyticNumberTheory.Riemann.RiemannIPRA.HardyToeplitz
