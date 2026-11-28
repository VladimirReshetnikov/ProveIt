import Lib.DiscreteSeries.Rigidity.RepresentationsAndCasimirs
import Lib.GLn.SchurModule.Basic
import Lib.General.Algebra.MultivariatePolynomials
import Lib.Weil.Fock.Basic

/-!
# Fock space oscillator actions, joint harmonics and Fischer decomposition

This file treats polynomials in the variables of `T : New.FockDualPair`, indexed by rows `r : R` and
columns `c : C`. It defines the oscillator action `New.FockDualPair.oscRows` of `gl R` on the rows.
It also defines matched parameters and joint harmonics for the theta correspondence of
`U(ε) × U(ε')`, and proves that these notions are symmetric under `New.FockDualPair.swap`. A
Fischer-type analysis of orthogonal complements in bounded degree gives criteria for the Laplacians
to vanish.

## Main definitions and results

* `New.FockDualPair`, `New.FockDualPair.swap`: the data of the dual pair, and the data with
  `globalSign` negated and rows and columns exchanged.
* `New.FockDualPair.oscRows`: the action of `gl R` on the rows. The action of `gl C` on the columns
  is `oscRows` of `swap`, and its matrix units are given by `New.FockDualPair.swap_oscRows_E`.
* `New.FockDualPair.IsMatchedPair`, `New.IsMatch`: when the parameters `l = 2λ` and `l' = 2λ'`
  correspond.
* `New.FockDualPair.IsTermwiseHarmonic`, `New.IsJointHarmonic`: termwise harmonic polynomials, and
  joint harmonics that are highest for the lowest `K`-types `l.lowestKType` and `l'.lowestKType`.
  The signs `ε` and `ε'` are carried by the types of `l` and `l'`.
* `New.Fischer.fockLaplacian_eq_zero`, `New.Fischer.isLaplaceHarmonic_of_isKHighest`: criteria for
  the Laplacians `New.FockDualPair.fockLaplacian` to vanish.

Notions from other files:
* `New.HCParam.HasGap`: `l.HasGap h` says that the entries of `l = 2λ` are distinct and congruent to
  `n − 1` mod 2, where `n` is their number, and `|λ_i − λ_j| ≥ h` whenever `ε_i ≠ ε_j`.
* `New.HCParam.IsKHighest`: `x` is a `K`-highest vector of weight `ν`: each `E a a` acts on it by
  `ν a`, and it is killed by the compact raising operators, the `E a b` with `ε a = ε b` and
  `l b < l a`. The second condition alone is `New.GlModule.IsCompactPrimitive`.
* `New.HCParam.lowestKType`: for a parameter `l = 2λ`, the integer vector `λ + ρ − 2ρ_c`, which is
  the highest weight of the lowest `K`-type.
* `New.fockPairing`: the bilinear form `⟨P, Q⟩ = P(∂)Q(0)` on polynomials, for which monomials are
  orthogonal and `⟨x^d, x^d⟩ = d!`.

## Relation to the literature

Known; see `Lib.DiscreteSeries.Theta.LocalCorrespondence` for sources.
-/

noncomputable section

namespace New

/-!
## Oscillator actions, matched parameters and joint harmonics

`New.Fock.glOp η a b` is `raiseOp η a * lowerOp η b`, and `New.Fock.raiseOp η a` and
`New.Fock.lowerOp η a` are `X a` and `∂ a` if `η a = 1`, and `-∂ a` and `X a` otherwise.
-/

section OscillatorDefs

open Matrix Fintype Fock MvPolynomial Finset GlModule

variable {R C ι : Type} [DecidableEq R] [Fintype C] [DecidableEq C] [Fintype ι]

/-- The raising operators of the Fock model for the signs `η` commute: `raiseOp η a` is
multiplication by `X a` if `η a = 1` and `-∂ a` otherwise. -/
theorem Fock.raiseOp_comm (η : R → ℤˣ) (a b : R) (P : MvPolynomial R ℂ) :
    raiseOp η a (raiseOp η b P) = raiseOp η b (raiseOp η a P) := by
  rcases eq_or_ne a b with rfl | hab
  · rfl
  -- For `a ≠ b`, each of `X a`, `∂ a` commutes with each of `X b`, `∂ b`.
  by_cases ha : η a = 1 <;> by_cases hb : η b = 1 <;>
    simp [raiseOp, ha, hb, hab, hab.symm, mul_left_comm, pderiv_comm a]

/-- The lowering operators of the Fock model for the signs `η` commute: `lowerOp η a` is `∂ a` if
`η a = 1` and multiplication by `X a` otherwise. -/
theorem Fock.lowerOp_comm (η : R → ℤˣ) (a b : R) (P : MvPolynomial R ℂ) :
    lowerOp η a (lowerOp η b P) = lowerOp η b (lowerOp η a P) := by
  rcases eq_or_ne a b with rfl | hab
  · rfl
  -- For `a ≠ b`, each of `X a`, `∂ a` commutes with each of `X b`, `∂ b`.
  by_cases ha : η a = 1 <;> by_cases hb : η b = 1 <;>
    simp [lowerOp, ha, hb, hab, hab.symm, mul_left_comm, pderiv_comm a]

/-- The commutator of the lowering operator `lowerOp η a` (`∂ a` or `X a`, by the sign `η a`) with
the raising operator `raiseOp η b` (`X b` or `-∂ b`) is the identity if `a = b`, and zero if not. -/
theorem Fock.lowerOp_raiseOp (η : R → ℤˣ) (a b : R) (P : MvPolynomial R ℂ) :
    lowerOp η a (raiseOp η b P) = raiseOp η b (lowerOp η a P) + if a = b then P else 0 := by
  rcases eq_or_ne a b with rfl | hab
  · -- This is Leibniz's rule `∂ (X * P) = X * ∂ P + P`, whatever the sign of `a`.
    by_cases ha : η a = 1 <;> simp [raiseOp, lowerOp, ha, add_comm]
  -- Operators in different variables commute.
  by_cases ha : η a = 1 <;> by_cases hb : η b = 1 <;>
    simp [raiseOp, lowerOp, ha, hb, hab, hab.symm, mul_left_comm, pderiv_comm a]

/-- The canonical commutation relations of the Fock model for the signs `η`: raising operators
commute, lowering operators commute, and the commutator of `lowerOp η a` with `raiseOp η b` is
`δ_ab`. -/
theorem Fock.canonical_commutation (η : R → ℤˣ) (a b : R) (P : MvPolynomial R ℂ) :
    raiseOp η a (raiseOp η b P) = raiseOp η b (raiseOp η a P) ∧
      lowerOp η a (lowerOp η b P) = lowerOp η b (lowerOp η a P) ∧
      lowerOp η a (raiseOp η b P) = raiseOp η b (lowerOp η a P) + if a = b then P else 0 :=
  ⟨raiseOp_comm η a b P, lowerOp_comm η a b P, lowerOp_raiseOp η a b P⟩

/-! ### Dual pair data and signs of the variables -/

/-- The sign `σ * ε r * ε' c` of the variable in row `r` and column `c`, where `i = (r, c)`. -/
def pairSign (σ : ℤˣ) (ε : R → ℤˣ) (ε' : C → ℤˣ) (i : R × C) : ℤˣ := σ * ε i.1 * ε' i.2

/-- The data of a dual pair in Fock space for the signs `ε`, `ε'`: a sign `σ` (`globalSign`), two
integers `γ` (`rowShift`) and `γ'` (`columnShift`), and a bijection from `R × C` to the index set
`ι` of the variables. -/
structure FockDualPair (ε : R → ℤˣ) (ε' : C → ℤˣ) (ι : Sort*) where
  /-- The sign `σ`, a factor of the sign `σ * ε r * ε' c` of each variable. -/
  globalSign : ℤˣ
  /-- The constant `γ` added to the diagonal matrix units of the row action `oscRows`. -/
  rowShift : ℤ
  /-- The constant `γ'` added to the diagonal matrix units of the column action. -/
  columnShift : ℤ
  /-- The bijection that names the variable of row `r` and column `c`. -/
  varEquiv : R × C ≃ ι

/-- The dual pair data with sign `σ = 1`, integers `γ` and `γ' + card R`, and variables indexed by
`R × C` itself. Then `E a b` acts on the rows by `∑ c, raiseOp (a, c) * lowerOp (b, c) + γ δ_ab` and
on the columns by `-∑ r, raiseOp (r, b) * lowerOp (r, a) + γ' δ_ab`. -/
abbrev FockDualPair.std [Fintype R]
    (ε : R → ℤˣ) (ε' : C → ℤˣ) (γ γ' : ℤ) : FockDualPair ε ε' (R × C) where
  globalSign := 1
  rowShift := γ
  columnShift := γ' + Fintype.card R
  varEquiv := Equiv.refl (R × C)

variable [Fintype R]

variable {ε : R → ℤˣ} {ε' : C → ℤˣ} (T : FockDualPair ε ε' ι) (l : HCParam ε) (l' : HCParam ε')
  (Φ : MvPolynomial ι ℂ)

namespace FockDualPair

/-- The data with rows and columns exchanged: the sign `-σ`, the integers `γ'` and `γ` in this
order, and the variable of `(c, r)` named as that of `(r, c)`. -/
abbrev swap : FockDualPair ε' ε ι where
  globalSign := -T.globalSign
  rowShift := T.columnShift
  columnShift := T.rowShift
  varEquiv := (Equiv.prodComm C R).trans T.varEquiv

omit [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C] [Fintype ι] in
theorem swap_swap : T.swap.swap = T := by
  simp only [swap, neg_neg]
  rfl

/-- The sign `σ * ε r * ε' c` of the variable in row `r` and column `c`. -/
abbrev varSign : R × C → ℤˣ := pairSign T.globalSign ε ε'

/-- The signs of the variables as a function on `ι`: the variable `T.varEquiv (r, c)` has the sign
`σ * ε r * ε' c`. -/
@[simp]
abbrev indexSign : ι → ℤˣ := T.varSign ∘ T.varEquiv.symm

/-! ### Vacuum weight, the row action, Laplacians and polarisation -/

/-- The weight of the vacuum (the constant polynomial `1`) at a row of sign `s` for the action
`New.FockDualPair.oscRows`: `γ` minus the number of columns `c` with `σ * s * ε' c ≠ 1`. Each such
column contributes `-∂ (X * 1) = -1` to `E r r 1`. -/
def vacuumWeight (s : ℤˣ) : ℤ := T.rowShift - #{c : C | T.globalSign * s * ε' c ≠ 1}

/-- The entry in row `r` of the lowest `K`-type for `l = 2λ`, minus the weight of the vacuum on a
row of sign `ε r`. -/
abbrev relWeight (r : R) : ℤ := l.lowestKType r - T.vacuumWeight (ε r)

/-- The integer `l r - 2γ + card C`; for `l = 2λ` it is twice the centred parameter
`λ r - γ + card C / 2`. -/
@[simp]
abbrev centredParam (r : R) : ℤ := l r - 2 * T.rowShift + Fintype.card C

section

omit [Fintype ι]

/-- The operators `glOp η i j = raiseOp η i * lowerOp η j` satisfy the commutation rule
`[E i j, E k m] = δ_jk E i m - δ_im E k j` of the matrix units. Here `raiseOp η i` and `lowerOp η i`
are `X i` and `∂ i` if the sign `η i` is `1`, and `-∂ i` and `X i` otherwise. -/
theorem _root_.New.Fock.glOp_commutator [DecidableEq ι] (η : ι → ℤˣ) (i j k m : ι) :
    glOp η i j * glOp η k m - glOp η k m * glOp η i j =
      (if j = k then glOp η i m else 0) - if i = m then glOp η k j else 0 := by
  refine LinearMap.ext fun P ↦ ?_
  -- Move the raising operators to the left; the terms of degree four then cancel.
  have h_order (p q r s : ι) : glOp η p q (glOp η r s P) =
      raiseOp η p (raiseOp η r (lowerOp η q (lowerOp η s P))) +
        if q = r then glOp η p s P else 0 := by
    simp [glOp, lowerOp_raiseOp, apply_ite (raiseOp η p)]
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, h_order, h_order,
    raiseOp_comm η i k, lowerOp_comm η j m, add_sub_add_left_eq_sub]
  simp [DFunLike.ite_apply, eq_comm]

/-- Reversing all signs exchanges raising and lowering operators up to sign, so
`glOp (-η) i j = raiseOp (-η) i * lowerOp (-η) j` is `∓ lowerOp η i * raiseOp η j`, with the minus
sign when `η i = η j`. Here `raiseOp η i` and `lowerOp η i` are `X i` and `∂ i` if `η i = 1`, and
`-∂ i` and `X i` otherwise. -/
theorem _root_.New.Fock.glOp_neg (η : ι → ℤˣ) (i j : ι) :
    glOp (-η) i j = (if η i = η j then -1 else 1 : ℂ) • (lowerOp η i * raiseOp η j) := by
  -- In each of the four cases of signs both sides are the same product of `X` and `∂`.
  rcases Int.units_eq_one_or (η i) with hi | hi <;>
    rcases Int.units_eq_one_or (η j) with hj | hj <;>
    simp [raiseOp, lowerOp, hi, hj, glOp]

/-- The operator by which the matrix unit `E a b` of `gl R` acts on the rows of the variables
`varEquiv (r, c)`: it is `s • ∑ c, glOp η (varEquiv (a, c)) (varEquiv (b, c)) + γ δ_ab`, where
`s = 1` if `ε a = ε b` and `s = σ` otherwise. -/
def oscRowsUnit (a b : R) : Module.End ℂ (MvPolynomial ι ℂ) :=
  (if ε a = ε b then 1 else T.globalSign : ℂ) •
      ∑ c : C, glOp T.indexSign (T.varEquiv (a, c)) (T.varEquiv (b, c)) +
    if a = b then ↑T.rowShift else 0

omit [Fintype R] in
/-- The sums over the columns `x` of the operators `glOp` between the variables `(a, x)` and
`(b, x)` satisfy the commutation rule of the matrix units `E a b` of `gl R`. Here `T.varEquiv` names
the variables, `T.indexSign` gives their signs, and `glOp η i j` raises in `i` after lowering in
`j`. -/
theorem sum_glOp_commutator (a b c d : R) :
    (∑ x : C, glOp T.indexSign (T.varEquiv (a, x)) (T.varEquiv (b, x))) *
          ∑ x : C, glOp T.indexSign (T.varEquiv (c, x)) (T.varEquiv (d, x)) -
        (∑ x : C, glOp T.indexSign (T.varEquiv (c, x)) (T.varEquiv (d, x))) *
          ∑ x : C, glOp T.indexSign (T.varEquiv (a, x)) (T.varEquiv (b, x)) =
      (if b = c then ∑ x : C, glOp T.indexSign (T.varEquiv (a, x)) (T.varEquiv (d, x)) else 0) -
        if a = d then ∑ x : C, glOp T.indexSign (T.varEquiv (c, x)) (T.varEquiv (b, x)) else 0 := by
  classical
  rw [Fintype.sum_mul_sum, Fintype.sum_mul_sum, sum_comm]
  simp only [← sum_sub_distrib, glOp_commutator]
  -- Only the pairs of equal columns contribute.
  simp [ite_and]

end

/-- For a sign `σ`, the factor that is `1` if `s = t` and `σ` if not is multiplicative along three
signs `s`, `t`, `u`. -/
theorem _root_.New.ite_units_eq_mul_ite_units_eq (σ s t u : ℤˣ) :
    (if s = t then 1 else σ : ℂ) * (if t = u then 1 else σ : ℂ) =
      (if s = u then 1 else σ : ℂ) := by
  -- There are only two signs, so this is a check of cases.
  rcases Int.units_eq_one_or σ with rfl | rfl <;> rcases Int.units_eq_one_or s with rfl | rfl <;>
    rcases Int.units_eq_one_or t with rfl | rfl <;> rcases Int.units_eq_one_or u with rfl | rfl <;>
    simp

omit [Fintype R] [Fintype ι] in
/-- The operators `oscRowsUnit a b`, by which the matrix units of `gl R` act on the rows, satisfy
the commutation rule `[E a b, E c d] = δ_bc E a d - δ_ad E c b`. -/
theorem oscRowsUnit_commutator (a b c d : R) :
    T.oscRowsUnit a b * T.oscRowsUnit c d - T.oscRowsUnit c d * T.oscRowsUnit a b =
      (if b = c then T.oscRowsUnit a d else 0) - if a = d then T.oscRowsUnit c b else 0 := by
  -- The sums over the columns satisfy the rule, the signs multiply as the rule needs, and the
  -- scalar terms are central.
  let sign (p q : R) : ℂ := if ε p = ε q then 1 else T.globalSign
  let rowSum (p q : R) : Module.End ℂ (MvPolynomial ι ℂ) :=
    ∑ x : C, glOp T.indexSign (T.varEquiv (p, x)) (T.varEquiv (q, x))
  have h_unit (p q : R) :
      T.oscRowsUnit p q = sign p q • rowSum p q + (if p = q then (T.rowShift : ℂ) else 0) • 1 := by
    simp [oscRowsUnit, sign, rowSum, Int.cast_smul_eq_zsmul]
  have h_sign_self (p : R) : sign p p = 1 := ite_eq_left rfl
  have h_sign (p q r : R) : sign p q * sign q r = sign p r :=
    ite_units_eq_mul_ite_units_eq T.globalSign (ε p) (ε q) (ε r)
  have h_central : T.oscRowsUnit a b * T.oscRowsUnit c d - T.oscRowsUnit c d * T.oscRowsUnit a b =
      (sign a b * sign c d) • (rowSum a b * rowSum c d - rowSum c d * rowSum a b) := by
    simp only [h_unit, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    module
  rw [h_central, T.sum_glOp_commutator, h_unit, h_unit]
  by_cases hbc : b = c <;> by_cases had : a = d <;>
    simp [rowSum, hbc, had, h_sign, h_sign_self, smul_sub, eq_comm, mul_comm (sign d b)]

/-- The commutation rule `[x E a b, y E c d] = x y (δ_bc E a d - δ_ad E c b)` for multiples of two
matrix units in `Matrix R R ℂ`. -/
theorem _root_.New.single_mul_single_sub_single_mul_single (a b c d : R) (x y : ℂ) :
    Matrix.single a b x * Matrix.single c d y - Matrix.single c d y * Matrix.single a b x =
      (if b = c then Matrix.single a d (x * y) else 0) -
        if a = d then Matrix.single c b (x * y) else 0 := by
  by_cases hbc : b = c <;> by_cases had : a = d <;>
    simp [hbc, had, Ne.symm, mul_comm y x]

/-- The oscillator action of `gl R` on the rows of the variables `varEquiv (r, c)`: the linear
map that sends the matrix unit `E a b` to `oscRowsUnit a b`. For `σ = -1` its noncompact part
changes sign. -/
def oscRows : GlModule R (MvPolynomial ι ℂ) where
  ρ := liftLinear ℂ fun a b : R ↦ LinearMap.id.smulRight (T.oscRowsUnit a b)
  map_bracket X Y := by
    -- Both sides are additive in `X` and in `Y`, so it suffices to treat multiples of matrix units.
    induction X using Matrix.induction_on' with
    | h_zero => simp
    | h_add X X' hX hX' => simp only [add_mul, mul_add, map_add, add_sub_add_comm, hX, hX']
    | h_std_basis a b x =>
      induction Y using Matrix.induction_on' with
      | h_zero => simp
      | h_add Y Y' hY hY' => simp only [add_mul, mul_add, map_add, add_sub_add_comm, hY, hY']
      | h_std_basis c d y =>
        have h_commutator :
            (x • T.oscRowsUnit a b) * (y • T.oscRowsUnit c d) -
                (y • T.oscRowsUnit c d) * (x • T.oscRowsUnit a b) =
              (if b = c then (x * y) • T.oscRowsUnit a d else 0) -
                if a = d then (x * y) • T.oscRowsUnit c b else 0 := by
          rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm y x, ← smul_sub,
            oscRowsUnit_commutator, smul_sub, smul_ite_zero, smul_ite_zero]
        rw [single_mul_single_sub_single_mul_single, map_sub, apply_ite (liftLinear ℂ _),
          apply_ite (liftLinear ℂ _)]
        simpa using h_commutator.symm

section

omit [Fintype ι]

theorem oscRows_apply (X : Matrix R R ℂ) :
    T.oscRows X = ∑ a : R, ∑ b : R, X a b • T.oscRowsUnit a b := by
  simp [oscRows, liftLinear_apply]

theorem oscRows_E (a b : R) : T.oscRows.E a b = T.oscRowsUnit a b := by
  simp [oscRows, E]

/-- The operator `∑ c, glOp (a, c) (b, c)` over the columns `c` where `(a, c)` has sign `-1`. For
`ε a ≠ ε b` it is the Laplacian `-∑ c, ∂_{a c} ∂_{b c}`: up to the factor `σ`, the part of the
matrix unit `E a b` of `New.FockDualPair.oscRows` that lowers the degree. -/
def fockLaplacian (a b : R) : Module.End ℂ (MvPolynomial ι ℂ) :=
  ∑ c : C with T.varSign (a, c) = -1, glOp T.indexSign (T.varEquiv (a, c)) (T.varEquiv (b, c))

/-- The polarisation `∑ c, X_{a c} * ∂Φ/∂X_{b c}` of the polynomial `Φ`, summed over the columns `c`
where the variable `(b, c)` has sign `s`. -/
def polarisation (a b : R) (s : ℤˣ) : MvPolynomial ι ℂ :=
  ∑ c : C with T.varSign (b, c) = s, X (T.varEquiv (a, c)) * pderiv (T.varEquiv (b, c)) Φ

/-! ### Matching parameters and joint harmonics -/

/-- The row `r` is matched with the column `c`: with `n = card R`, `n' = card C` and
`a = l r - 2γ + n'`, one has `a = -(l' c - 2γ' + n)` and `|n - n'| < σ * ε r * ε' c * a`. -/
abbrev IsMatchedPair (r : R) (c : C) : Prop :=
  T.centredParam l r = -T.swap.centredParam l' c ∧
    |(Fintype.card R - Fintype.card C : ℤ)| < T.varSign (r, c) * T.centredParam l r

/-- `∂_{a c} ∂_{b c} Φ = 0` whenever `ε a ≠ ε b`. This says that no monomial of `Φ` contains two
variables of one column `c` from rows of opposite signs. -/
def IsTermwiseHarmonic : Prop :=
  ∀ (a b : R) (c : C), ε a ≠ ε b → pderiv (T.varEquiv (a, c)) (pderiv (T.varEquiv (b, c)) Φ) = 0

/-- `Φ` is killed by the Laplacians of the rows: for `ε a ≠ ε b`, the sum of `∂_{a c} ∂_{b c} Φ`
over the columns `c` where the variable `(a, c)` has sign `-1` is zero. -/
def IsLaplaceHarmonic : Prop := ∀ a b : R, ε a ≠ ε b → T.fockLaplacian a b Φ = 0

/-- `Φ` is not zero, killed by the compact raising operators of the columns (in the order of `l'`),
`K`-highest of weight `l.lowestKType` for the action on the rows, and killed by the Laplacians of
both sides. The last condition is weaker than `New.FockDualPair.IsTermwiseHarmonic` for both sides;
uniqueness is proved in this wider class, as Howe's argument needs it there. -/
structure IsPreJointHarmonic : Prop where
  /-- `Φ` is not zero. -/
  ne_zero : Φ ≠ 0
  /-- The compact raising operators of the column action, in the order of `l'`, kill `Φ`. -/
  isCompactPrimitive_cols : T.swap.oscRows.IsCompactPrimitive l' Φ
  /-- The Laplacians of the rows kill `Φ`. -/
  isLaplaceHarmonic : T.IsLaplaceHarmonic Φ
  /-- `Φ` is `K`-highest for the row action, with the lowest `K`-type of `l` as weight. -/
  isKHighest_rows : l.IsKHighest T.oscRows l.lowestKType Φ
  /-- The Laplacians of the columns kill `Φ`. -/
  isLaplaceHarmonic_swap : T.swap.IsLaplaceHarmonic Φ

/-- `Φ` is not zero, termwise harmonic for both sides, and `K`-highest of weight `ν` for the action
on the rows and of weight `ν'` for the action on the columns. -/
structure IsJointHighest (ν : R → ℤ) (ν' : C → ℤ) : Prop where
  /-- `Φ` is not zero. -/
  ne_zero : Φ ≠ 0
  /-- `Φ` is `K`-highest of weight `ν'` for the column action, in the order of `l'`. -/
  isKHighest_cols : l'.IsKHighest T.swap.oscRows ν' Φ
  /-- No monomial of `Φ` contains two variables of one column from rows of opposite signs. -/
  isTermwiseHarmonic : T.IsTermwiseHarmonic Φ
  /-- `Φ` is `K`-highest of weight `ν` for the row action, in the order of `l`. -/
  isKHighest_rows : l.IsKHighest T.oscRows ν Φ
  /-- No monomial of `Φ` contains two variables of one row from columns of opposite signs. -/
  isTermwiseHarmonic_swap : T.swap.IsTermwiseHarmonic Φ

omit [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C] in
theorem swap_indexSign : T.swap.indexSign = -T.indexSign := by
  ext i
  simp [pairSign, mul_right_comm T.globalSign]

/-- For a dual pair `T` in Fock space, with sign `σ`, integers `γ` and `γ'`, and variables
`varEquiv (r, c)` indexed by rows `r : R` and columns `c : C`, the matrix unit `E a b` of `gl C`
acts on the columns by `s • (-∑ r, lowerOp η (varEquiv (r, a)) * raiseOp η (varEquiv (r, b))) + γ'
δ_ab`, where `s = 1` if `ε' a = ε' b` and `s = σ` otherwise. This column action is `T.swap.oscRows`,
the row action of the swapped pair, whose sign is `-σ`. Here `η` gives the signs of the variables,
`raiseOp η i` and `lowerOp η i` are `X i` and `∂ i` if `η i = 1` and `-∂ i` and `X i` otherwise, and
the integer `γ'` of the pair acts as a scalar. -/
theorem swap_oscRows_E (a b : C) :
    T.swap.oscRows.E a b =
      (if ε' a = ε' b then 1 else T.globalSign : ℂ) •
          -∑ r : R, lowerOp T.indexSign (T.varEquiv (r, a)) * raiseOp T.indexSign
            (T.varEquiv (r, b)) +
        if a = b then ↑T.columnShift else 0 := by
  -- Two variables of one row have equal signs exactly when their columns do; `glOp_neg` then
  -- gives each term of the sum.
  have h_sign (r : R) : T.indexSign (T.varEquiv (r, a)) = T.indexSign (T.varEquiv (r, b)) ↔ ε' a =
    ε' b := by
    simp [pairSign]
  have h_sum : ∑ r : R, glOp T.swap.indexSign (T.swap.varEquiv (a, r)) (T.swap.varEquiv (b, r)) =
      (if ε' a = ε' b then -1 else 1 : ℂ) •
        ∑ r : R, lowerOp T.indexSign (T.varEquiv (r, a)) * raiseOp T.indexSign
          (T.varEquiv (r, b)) := by
    simp only [swap_indexSign, glOp_neg, Equiv.trans_apply, Equiv.prodComm_apply, Prod.swap_prod_mk,
      h_sign, smul_sum]
  rw [oscRows_E, oscRowsUnit, h_sum]
  by_cases hab : ε' a = ε' b <;> simp [hab]

end

end FockDualPair

export FockDualPair (vacuumWeight oscRowsUnit oscRows oscRows_E fockLaplacian polarisation
  IsMatchedPair IsTermwiseHarmonic swap_oscRows_E)

/-- The parameters `l = 2λ`, `l' = 2λ'` match. With `n = card R` and `n' = card C`, both have gap
`500 (n + n')³`. Put `ξ r = λ r - γ + n' / 2` and `ξ' c = λ' c - γ' + n / 2`; a pair `(r, c)` is
matched if `ξ r = -ξ' c` and `σ * ε r * ε' c * ξ r > |n - n'| / 2`. Each row is matched or has
`|ξ r| < (n - n') / 2`, and each column is matched or has `|ξ' c| < (n' - n) / 2`. So the matched
entries are the common ones and the others form the block; `New.isBlockRule_iff_isMatch` proves that
this is the block rule. -/
structure IsMatch : Prop where
  /-- The row parameter `l` has gap `500 (n + n')³`, where `n = card R` and `n' = card C`. -/
  hasGap_row : l.HasGap (500 * (Fintype.card R + Fintype.card C) ^ 3)
  /-- The column parameter `l'` has the same gap `500 (n' + n)³`. -/
  hasGap_column : l'.HasGap (500 * (Fintype.card C + Fintype.card R) ^ 3)
  /-- Every row `r` is matched with a column, or `|l r - 2γ + n'| < n - n'`. -/
  left (r : R) :
    (∃ c : C, T.IsMatchedPair l l' r c) ∨ |T.centredParam l r| < Fintype.card R - Fintype.card C
  /-- Every column `c` is matched with a row, or `|l' c - 2γ' + n| < n' - n`. -/
  right (c : C) :
    (∃ r : R, T.IsMatchedPair l l' r c) ∨
      |T.swap.centredParam l' c| < Fintype.card C - Fintype.card R

/-- `Φ` is a joint harmonic: `l` and `l'` match, and `Φ ≠ 0` is `K`-highest for the row and column
actions, of the weights of the two lowest `K`-types, and satisfies
`New.FockDualPair.IsTermwiseHarmonic` for `T` and for `T.swap`. -/
structure IsJointHarmonic : Prop extends IsMatch T l l' where
  /-- `Φ` is nonzero, termwise harmonic for both sides, and highest of weight `l.lowestKType` for
  the action on the rows and of weight `l'.lowestKType` for the action on the columns. -/
  isJointHighest : T.IsJointHighest l l' Φ l.lowestKType l'.lowestKType

end OscillatorDefs

/-!
## Swap symmetry, Laplacians and Fischer decomposition in Fock space

On polynomials `⟪P, Q⟫` is the Fischer inner product `fockPairing (conj P) Q`, for which `X i` is
adjoint to `∂_i`. For it, `New.Fischer.perpInDegree j G` is the orthogonal complement of `G` in
degree at most `j`.

* `New.Fischer.oscRows_E_eq_polarisation_sub`: the compact matrix units, expressed by polarisations
  and the vacuum weight `New.FockDualPair.vacuumWeight`.
-/

section FischerDecomposition

open MvPolynomial Finset InnerProductSpace Fock Submodule Int Complex ComplexOrder Pi

section

variable {R C : Type} {ι : Type _} [Fintype R] [Fintype C]
  {ε : R → ℤˣ} {ε' : C → ℤˣ} {T : FockDualPair (R := R) (C := C) ε ε' ι}

/-- If row `r` is matched with column `c` for `T`, then `c` is matched with `r` for `T.swap`, the
data with rows and columns exchanged and the sign `σ` negated. -/
theorem FockDualPair.IsMatchedPair.swap {l' : HCParam ε'} {l : HCParam ε} {r : R} {c : C}
    (hrc : T.IsMatchedPair l l' r c) : T.swap.IsMatchedPair l' l c r := by
  obtain ⟨h_param, h_large⟩ := hrc
  -- Both the sign of the variable and the centred parameter change sign.
  have h_sign : (T.swap.varSign (c, r) : ℤ) = -T.varSign (r, c) := by
    simp [pairSign, mul_right_comm]
  have h_neg : T.swap.centredParam l' c = -T.centredParam l r := by rw [h_param, neg_neg]
  exact ⟨by rwa [T.swap_swap], by rwa [abs_sub_comm, h_sign, h_neg, neg_mul_neg]⟩

/-- The matching of parameters is symmetric: if `l` and `l'` match for `T`, then `l'` and `l` match
for `T.swap`, the data with rows and columns exchanged and the sign `σ` negated. -/
theorem IsMatch.swap {l' : HCParam ε'} {l : HCParam ε} (hm : IsMatch T l l') :
    IsMatch T.swap l' l where
  hasGap_row := hm.hasGap_column
  hasGap_column := hm.hasGap_row
  left c := (hm.right c).imp_left fun ⟨r, hrc⟩ ↦ ⟨r, hrc.swap⟩
  right r := by simpa only [T.swap_swap] using (hm.left r).imp_left fun ⟨c, hrc⟩ ↦ ⟨c, hrc.swap⟩

variable [DecidableEq R] [DecidableEq C]

/-- Let `P ≠ 0` be termwise harmonic for both sides, and `K`-highest of weight `ν` for the rows and
of weight `ν'` for the columns of `T`. Then it is so for `T.swap`, with the parameters `l`, `l'`
and the weights `ν`, `ν'` exchanged. -/
theorem FockDualPair.IsJointHighest.swap [Fintype ι]
    {l' : HCParam ε'} {l : HCParam ε} {P : MvPolynomial ι ℂ}
    {ν : R → ℤ} {ν' : C → ℤ} (hP : T.IsJointHighest l l' P ν ν') :
    T.swap.IsJointHighest l' l P ν' ν where
  ne_zero := hP.ne_zero
  isKHighest_cols := by simpa only [T.swap_swap] using hP.isKHighest_rows
  isTermwiseHarmonic := hP.isTermwiseHarmonic_swap
  isKHighest_rows := hP.isKHighest_cols
  isTermwiseHarmonic_swap := by simpa only [T.swap_swap] using hP.isTermwiseHarmonic

/-- Let `T` be a dual pair in Fock space with sign `σ`. A joint harmonic `P` of `T` for `l`, `l'` is
a joint harmonic of `T.swap` for `l'`, `l`, where `T.swap` exchanges rows and columns, replaces `σ`
by `-σ` and swaps `γ`, `γ'`. Here a joint harmonic for matching parameters is a nonzero polynomial
that is `K`-highest of the lowest `K`-type weights for the row and column actions, and that has no
monomial with two variables of one column from rows of opposite signs, or of one row from columns of
opposite signs. -/
theorem IsJointHarmonic.swap [Fintype ι] {l' : HCParam ε'} {l : HCParam ε} {P : MvPolynomial ι ℂ}
    (hP : IsJointHarmonic T l l' P) : IsJointHarmonic T.swap l' l P :=
  ⟨hP.toIsMatch.swap, hP.isJointHighest.swap⟩

namespace Fischer

/-- For rows `a`, `b` of equal sign, the matrix unit `E a b` of the row action sends `P` to the
polarisation `∑ X_ac ∂_bc P` over the columns `c` where `(b, c)` has sign `1`, minus `∑ X_bc ∂_ac P`
over those where it has sign `-1`, plus `T.vacuumWeight (ε a)` (the weight by which `E a a` acts on
the constant `1`) times `P` if `a = b`. -/
theorem oscRows_E_eq_polarisation_sub {a b : R} {P : MvPolynomial ι ℂ} (hab : ε a = ε b) :
    T.oscRows.E a b P =
      T.polarisation P a b 1 - T.polarisation P b a (-1) +
        (if a = b then (T.vacuumWeight (ε a) : ℂ) else 0) • P := by
  classical
  -- A column of sign `1` gives `X_a ∂_b` and one of sign `-1` gives `-∂_a X_b = -X_b ∂_a - δ_ab`.
  have h_sign (c : C) : T.varSign (a, c) = T.varSign (b, c) := by simp [pairSign, hab]
  have h_term (c : C) : glOp T.indexSign (T.varEquiv (a, c)) (T.varEquiv (b, c)) P =
      if T.varSign (b, c) = 1 then X (T.varEquiv (a, c)) * pderiv (T.varEquiv (b, c)) P
      else -(X (T.varEquiv (b, c)) * pderiv (T.varEquiv (a, c)) P) - if a = b then P else 0 := by
    split_ifs with h h_eq <;>
      simp [glOp, raiseOp, lowerOp, *]; ring
  simp [oscRows_E, oscRowsUnit, hab, h_term, h_sign, sum_ite, polarisation, vacuumWeight,
    pairSign, units_ne_iff_eq_neg, sum_sub_distrib, DFunLike.ite_apply]
  split_ifs <;> simp [Algebra.smul_def] <;> ring

/-- The inner product `⟪P, Q⟫ = fockPairing (conj P) Q` on polynomials, the Fischer inner product,
makes them a normed group. -/
scoped instance : NormedAddCommGroup (MvPolynomial ι ℂ) :=
  Core.toNormedAddCommGroup
    (cd :=
      ⟨⟨⟨(fockPairing ℂ <| map (starRingEnd ℂ) ·)⟩,
          -- conjugate symmetry
          by simp [map_fockPairing, fockPairing_comm, map_leftInverse conj_conj _],
          -- `0 ≤ re ⟪P, P⟫`
          by
            simp
            grind [fockPairing_star_self_pos, zero_re, pos_iff],
          -- additive and conjugate linear in the first variable
          by simp, by
            simp [← C_mul']
            simp [C_mul']⟩,
        -- definite
        by grind [fockPairing_star_self_pos, inner]⟩)

scoped instance : InnerProductSpace ℂ (MvPolynomial ι ℂ) := .ofCore _

/-- For the Fischer inner product on complex polynomials, multiplication by `X b` is adjoint to the
partial derivative `pderiv b`, on either side of the inner product. -/
@[scoped simp]
theorem inner_X_mul {b : ι} {P Q : MvPolynomial ι ℂ} :
    ⟪X b * P, Q⟫_ℂ = ⟪P, pderiv b Q⟫_ℂ ∧ ⟪P, X b * Q⟫_ℂ = ⟪pderiv b P, Q⟫_ℂ := by
  simp [inner, fockPairing_mul_X, mul_comm (X b), fockPairing_comm (map _ _), pderiv_map]

/-! ### Degree filtration and vanishing of the Laplacians -/

/-- For an integer `j`, the space of complex polynomials of total degree at most `j` in variables
indexed by `ι`. -/
def polyDegreeLE (j : ℤ) : Submodule ℂ (MvPolynomial ι ℂ) :=
  restrictSupport ℂ {d : ι →₀ ℕ | d.degree ≤ j}

variable [Fintype ι] in
instance {j : ℤ} : Module.Finite ℂ (polyDegreeLE (ι := ι) j) :=
  finiteDimensional_of_le (S₂ := restrictTotalDegree ι ℂ j.toNat)
    (restrictSupport_mono ℂ fun _ ↦ toNat_le_toNat)

/-- Multiplication by a variable raises the bound on the degree by one. -/
theorem X_mul_mem_polyDegreeLE {c : ι} {k m : ℤ} {Q : MvPolynomial ι ℂ} (hQ : Q ∈ polyDegreeLE k)
    (h_le : k + 1 ≤ m) : X c * Q ∈ polyDegreeLE m := by
  simp_all [polyDegreeLE, mem_restrictSupport_iff, Set.subset_def]
  grind [Finsupp.degree_single]

/-- A partial derivative lowers the bound on the degree by one. -/
theorem pderiv_mem_polyDegreeLE {c : ι} {k m : ℤ} {Q : MvPolynomial ι ℂ} (hQ : Q ∈ polyDegreeLE k)
    (h_le : k - 1 ≤ m) : pderiv c Q ∈ polyDegreeLE m := by
  simp_all [polyDegreeLE, mem_restrictSupport_iff, Set.subset_def, coeff_pderiv]
  grind [Finsupp.degree_single]

/-- If `P` has degree at most `j`, then `glOp η a b P` has degree at most every `i` with
`j + η a ≤ i + η b`. -/
theorem glOp_mem_polyDegreeLE {a : ι} {η : ι → ℤˣ} {i j : ℤ} {b : ι} {P : MvPolynomial ι ℂ}
    (hP : P ∈ polyDegreeLE j) (h_deg : j + η a ≤ i + η b) : glOp η a b P ∈ polyDegreeLE i := by
  -- `raiseOp η c` changes the degree by `η c` and `lowerOp η c` by `-η c`.
  have h_lower : lowerOp η b P ∈ polyDegreeLE (j - η b) := by
    obtain hb | hb := units_eq_one_or (η b) <;>
      simp [lowerOp, hb, pderiv_mem_polyDegreeLE hP, X_mul_mem_polyDegreeLE hP]
  obtain ha | ha := units_eq_one_or (η a) <;> simp only [ha, Units.val_one, Units.val_neg] at h_deg
  · simpa [glOp, raiseOp, ha] using X_mul_mem_polyDegreeLE (c := a) (m := i) h_lower (by lia)
  · simpa [glOp, raiseOp, ha] using pderiv_mem_polyDegreeLE (c := a) (m := i) h_lower (by lia)

/-- The polynomials of degree at most `j` that are orthogonal, for the Fischer inner product, to
all elements of `G` of degree at most `j`. -/
abbrev perpInDegree (j : ℤ) (G : Submodule ℂ (MvPolynomial ι ℂ)) : Submodule ℂ (MvPolynomial ι ℂ) :=
  (polyDegreeLE (ι := ι) j ⊓ G)ᗮ ⊓ polyDegreeLE j

/-- A polynomial of degree at most `j` that lies in `N` and is orthogonal to the elements of `N` of
degree at most `j` is zero. -/
theorem eq_zero_of_mem_perpInDegree {N : Submodule ℂ (MvPolynomial ι ℂ)} {j : ℤ}
    {P : MvPolynomial ι ℂ} (hP : P ∈ perpInDegree j N) (hN : P ∈ N) : P = 0 := by
  exact inner_self_eq_zero.1 (hP.1 P ⟨hP.2, hN⟩)

/-- The inductive step in Fischer's argument. Let `G` contain all polynomials of degree
less than `j`, let `P` have degree at most `j` and be orthogonal to the part of `G` of degree at
most `j`, and let `ε a ≠ ε b`. Let `Q = fockLaplacian a b P`, the sum of the `-∂_ac ∂_bc P` over
the columns `c` where `(a, c)` has sign `-1`. If `Q ∈ G` implies `E b a Q ∈ G` for the row action,
then `Q = 0`. -/
theorem fockLaplacian_eq_zero {a : R} {G : Submodule ℂ (MvPolynomial ι ℂ)} {j : ℤ} {b : R}
    {P Q : MvPolynomial ι ℂ} (ih : ∀ k : ℤ, k < j → polyDegreeLE k ≤ G)
    (hP : P ∈ perpInDegree j G) (hab : ε a ≠ ε b) (hQ : Q = T.fockLaplacian a b P)
    (hG : Q ∈ G → T.oscRows.E b a Q ∈ G) : Q = 0 := by
  -- The matrix unit `E b a` sends `Q` to `± ∑ c, A c` (with `A` as below). This sum lies in `G`
  -- and has degree at most `j`, so it is orthogonal to `P`; and `⟪Q, Q⟫ = -∑ c, ⟪A c, P⟫`.
  let A (c : C) : MvPolynomial ι ℂ := glOp T.indexSign (T.varEquiv (b, c)) (T.varEquiv (a, c)) Q
  obtain ⟨hP_perp, hP_deg⟩ := hP
  have hQ_sum :
      Q = ∑ c with T.varSign (a, c) = -1,
        glOp T.indexSign (T.varEquiv (a, c)) (T.varEquiv (b, c)) P :=
    hQ.trans (LinearMap.sum_apply ..)
  have h_sign (c : C) : T.varSign (b, c) = -T.varSign (a, c) := by
    simp [pairSign, (units_ne_iff_eq_neg.1 hab.symm)]
  have h_η (r : R) (c : C) : T.indexSign (T.varEquiv (r, c)) = T.varSign (r, c) := by simp
  have hQ_deg : Q ∈ polyDegreeLE (j - 2) := by
    rw [hQ_sum]
    exact sum_mem fun c hc ↦ glOp_mem_polyDegreeLE hP_deg (by grind [Units.val_neg, Units.val_one])
  have hA_deg (c : C) : A c ∈ polyDegreeLE j :=
    glOp_mem_polyDegreeLE hQ_deg (by grind [units_natAbs])
  -- The sum lies in `G`, since `Q ∈ G` by its degree and `E b a Q = σ • ∑ c, A c`.
  have hA_sum : ∑ c, A c ∈ G := by
    rw [← smul_mem_iff G (s := (T.globalSign : ℂ)) (by simp)]
    simpa [A, oscRows_E, oscRowsUnit, Ne.symm hab, ne_of_apply_ne ε hab.symm,
      -FockDualPair.indexSign]
      using hG (ih (j - 2) (by lia) hQ_deg)
  have h_term (c : C) :
      (if T.varSign (a, c) = -1 then ⟪Q, glOp T.indexSign (T.varEquiv (a, c)) (T.varEquiv (b, c))
        P⟫_ℂ
        else 0) = -⟪A c, P⟫_ℂ := by
    split_ifs with hc
    · -- Here the two operators are `-∂ ∂` and `X * X`, and `X` is adjoint to `∂`.
      simp [A, glOp, h_sign, hc, raiseOp, lowerOp]
    · -- Here `A c` is `-∂ ∂ Q`, of degree at most `j - 4`, so it lies in `G`.
      have hA_low : A c ∈ polyDegreeLE (j - 4) := glOp_mem_polyDegreeLE hQ_deg
        (by grind [Units.val_neg, Units.val_one, units_eq_one_or (T.varSign (a, c))])
      rw [hP_perp _ ⟨hA_deg c, ih _ (by lia) hA_low⟩, neg_zero]
  rw [← inner_self_eq_zero (𝕜 := ℂ)]
  calc ⟪Q, Q⟫_ℂ
      = ⟪Q, ∑ c with T.varSign (a, c) = -1,
          glOp T.indexSign (T.varEquiv (a, c)) (T.varEquiv (b, c)) P⟫_ℂ := by rw [← hQ_sum]
    _ = ∑ c, -⟪A c, P⟫_ℂ := by rw [inner_sum, sum_filter, sum_congr rfl fun c _ ↦ h_term c]
    _ = 0 := by
        rw [sum_neg_distrib, ← sum_inner, hP_perp _ ⟨sum_mem fun c _ ↦ hA_deg c, hA_sum⟩, neg_zero]

/-- Let `P` be `K`-highest of weight `ν` for the action `T.oscRows` on rows: each `E r r` acts on it
by `ν r`, and the compact raising operators of `l` kill it. Suppose that no nonzero Laplacian
`T.fockLaplacian a b P` with `ε a ≠ ε b` is `K`-highest of weight
`ν + Pi.single a 1 - Pi.single b 1`. Then `P` is row harmonic: all these Laplacians are zero. The
reason is that they form a tensor operator, so an extremal nonzero one would be highest. -/
theorem isLaplaceHarmonic_of_isKHighest {ν : R → ℤ} {l : HCParam ε} {P : MvPolynomial ι ℂ}
    (hP : l.IsKHighest T.oscRows ν P)
    (h_zero : ∀ a b : R, ε a ≠ ε b →
      l.IsKHighest T.oscRows (ν + single a 1 - single b 1) (T.fockLaplacian a b P) →
      T.fockLaplacian a b P = 0) :
    T.IsLaplaceHarmonic P := by
  classical
  -- The compact `E x z` act on the family `T.fockLaplacian a b` as on matrix units, by the
  -- canonical commutation relations.
  have h_comm (x z a b : R) (h : ε x = ε z) :
      T.oscRows.E x z (T.fockLaplacian a b P) = T.fockLaplacian a b (T.oscRows.E x z P) +
        (if z = a then T.fockLaplacian x b P else 0) -
          if b = x then T.fockLaplacian a z P else 0 := by
    simp +contextual [oscRows_E, oscRowsUnit, fockLaplacian, pairSign, h, glOp, raiseOp_comm,
      lowerOp_comm, lowerOp_raiseOp, -zsmul_eq_mul, apply_ite (raiseOp ..),
      apply_ite (lowerOp ..), sum_comm (t := univ), ite_and, sum_add_distrib, DFunLike.ite_apply]
    abel
  -- Induction on `l b - l a`.
  suffices h_all : ∀ p : R × R, ε p.1 ≠ ε p.2 → T.fockLaplacian p.1 p.2 P = 0 from
    fun a b ↦ h_all (a, b)
  refine Finite.int_weight_induction (fun p ↦ l p.2 - l p.1) fun ⟨a, b⟩ ih hab ↦ ?_
  replace ih (a' b' : R) (h : l b' - l a' < l b - l a) (h_ne : ε a' ≠ ε b') :
      T.fockLaplacian a' b' P = 0 :=
    ih (a', b') h h_ne
  obtain ⟨h_weight, h_raise⟩ := hP
  -- A raising `E x z` kills `P`, and its commutator with `T.fockLaplacian a b` involves only
  -- `T.fockLaplacian x b` with `l a < l x` and `T.fockLaplacian a z` with `l z < l b`. So
  -- `T.fockLaplacian a b P` is a highest vector.
  refine h_zero a b hab ⟨fun x ↦ ?_, fun x z hxz h_lt ↦ ?_⟩
  · rw [h_comm x x a b rfl, h_weight]
    simp only [map_smul, Pi.add_apply, Pi.sub_apply, single_apply, eq_comm (a := b)]
    split_ifs <;> simp_all [add_smul, sub_smul]
  · rw [h_comm x z a b hxz, h_raise x z hxz h_lt]
    grind

/-- Let `ε a = ε b`. If the compact matrix unit `E b a` of the row action maps `N` into `G`, then
`E a b` maps `perpInDegree j G` (the orthogonal complement of `G` in degree at most `j`) into
`perpInDegree j N`. -/
theorem mapsTo_perpInDegree {a : R} {N G : Submodule ℂ (MvPolynomial ι ℂ)} {j : ℤ} {b : R}
    (hab : ε a = ε b) (hN : N ≤ G.comap (T.oscRows.E b a)) :
    Set.MapsTo (T.oscRows.E a b) (perpInDegree j G) (perpInDegree j N) := by
  -- For `ε a = ε b` the matrix units preserve the degree, and `E b a` is adjoint to `E a b`.
  have h_deg {a b : R} {z : MvPolynomial ι ℂ} (hab : ε a = ε b) (hz : z ∈ polyDegreeLE j) :
      T.oscRows.E a b z ∈ polyDegreeLE j := by
    have h_sum : ∑ c, glOp T.indexSign (T.varEquiv (a, c)) (T.varEquiv (b, c)) z ∈ polyDegreeLE j :=
      sum_mem fun c _ ↦ glOp_mem_polyDegreeLE hz (by simp [pairSign, hab])
    simp [oscRows_E, oscRowsUnit, hab, ← cast_smul_eq_zsmul ℂ, DFunLike.ite_apply,
      -FockDualPair.indexSign]
    grind [smul_mem, add_mem]
  have h_adj (y z : MvPolynomial ι ℂ) : ⟪z, T.oscRows.E a b y⟫_ℂ = ⟪T.oscRows.E b a z, y⟫_ℂ := by
    obtain rfl | h_ne := eq_or_ne a b <;>
      simp [oscRows_E_eq_polarisation_sub, polarisation, *, Ne.symm, mul_comm, pairSign]
  intro y ⟨hy_perp, hy_deg⟩
  refine ⟨fun z ⟨hz_deg, hz_mem⟩ ↦ ?_, h_deg hab hy_deg⟩
  rw [h_adj, hy_perp _ ⟨h_deg hab.symm hz_deg, hN hz_mem⟩]

end Fischer

end

end FischerDecomposition

end New

end
