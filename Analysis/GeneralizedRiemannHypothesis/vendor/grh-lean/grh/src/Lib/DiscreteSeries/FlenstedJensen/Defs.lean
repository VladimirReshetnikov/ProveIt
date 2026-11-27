import Lib.DiscreteSeries.Haar.CayleyChart

/-!
# Harish-Chandra parameters, c_λ, deg_λ, e_λ and holomorphic discrete series

This file collects the definitions behind the discrete series of `G = New.USign ε`. A Harish-Chandra
parameter `λ` is stored as the integer vector `l = 2λ`, and the root `e_i - e_j` is positive when
`l j < l i`. The file proves elementary identities for `ρ`, `λ + ρ` and `Λ = λ + ρ - 2ρ_c`, and for
the gap condition. It then sets up Borel matrices, weights and holomorphic functions of weight `u`
for the holomorphic discrete series.

## Main definitions and results

* `New.HCParam.HasGap`, `New.HCParam.HasLargeGap`: `λ` is regular, each `λ i` lies in
  `(n - 1) / 2 + ℤ`, and entries of `λ` with opposite signs `ε` are far apart, at least by the gap.
* `New.paramAddRho`, `New.HCParam.lowestKType`, `New.HCParam.casimirValue`, `New.weylDimensionPoly`:
  `λ + ρ`, `λ + ρ - 2ρ_c`, `|λ|² - |ρ|²` and the product of the positive roots at `λ` divided by
  `∏_{i < n} i!`.
* `New.weightMinors`, `New.HCParam.flenstedJensen`, `New.HCParam.dsCoeff`: a product of principal
  minors (`New.principalMinor`), Flensted-Jensen's integral of such products over `K`, and the
  function `c_λ` that it defines.
* `New.HCParam.formalDegree`, `New.HCParam.dsKernel`: `deg_λ = (∫ |c_λ|²)⁻¹` for the measure
  `New.haarU`, and `e_λ = deg_λ * conj c_λ`.
* `New.IsPosFirstOrder`, `New.IsKDominant`, `New.HasHolGap`: the indices of sign `1` come first; a
  weight does not increase within a block; a weight jumps up by at least `γ` from the first block to
  the second.
* `New.IsHolOfWeight`: a function on a product of copies of the group extends analytically to the
  products `h * b`, `b` invertible triangular, transforming under `b` by the character of weight
  `u`; an optional second sign vector restricts `h` and `b` to block diagonal matrices.

Notions from other files:
* `New.USign`: for a vector of signs `ε`, the unitary group `U(J)` of the diagonal matrix
  `J = New.signMatrix ε` with entries `ε i`.
* `New.principalMinor`: the determinant of the square submatrix on the indices with a given
  property.
* `New.haarU`: a measure on `U(J)` obtained from Lebesgue measure by a Cayley chart; a Haar measure
  for a hermitian involution `J`.

## Relation to the literature

The definitions are part of three known results, each treated in another file:
* Flensted-Jensen's function as the coefficient of the lowest K-type of a discrete series, in
  `Lib.DiscreteSeries.FlenstedJensen.PsiKTypes`;
* the lowest K-type and the Casimir value determine a discrete series coefficient, in
  `Lib.DiscreteSeries.Rigidity.HighestVectorsAndFiltration`;
* the highest coefficient of a holomorphic discrete series and its reproducing property, in
  `Lib.DiscreteSeries.Holomorphic.HighestVectorExtension`.
-/

noncomputable section

/-!
## Harish-Chandra parameters, discrete series coefficients, formal degrees

* `New.maxCompactU`, `New.haarK`: the subgroup `K = G ∩ U(n)` and its Haar measure of mass one.
-/

section DiscreteSeriesDefs

open Matrix MeasureTheory Finset Fintype Equiv Int ComplexConjugate Norms.Operator

namespace New

variable {n : Type} [Fintype n] [DecidableEq n] (ε : n → ℤˣ) (l : n → ℤ) (J g : Matrix n n ℂ)

/-! ### The Lie algebra and the exponential map -/

/-- The Lie algebra of `U(J)`: the real vector space of complex matrices `X` with
`Xᴴ * J + J * X = 0`. -/
def unitaryLie : Submodule ℝ (Matrix n n ℂ) where
  carrier := {X : Matrix n n ℂ | Xᴴ * J + J * X = 0}
  add_mem' := by grind [conjTranspose_add, add_mul, mul_add]
  zero_mem' := by simp
  smul_mem' := by simp_all [star_trivial, ← smul_add]

/-- For `X` with `Xᴴ * J + J * X = 0`, the matrix exponential of `X` as an element of the group
`U(J)`. -/
@[simps! coe_val]
def expU {J : Matrix n n ℂ} (X : unitaryLie J) : U J where
  val := X.1.isUnit_exp.unit
  property := by
    -- Exponentiate the relation `J * X = -Xᴴ * J`.
    have h_semiconj : SemiconjBy J X.1 (-X.1ᴴ) :=
      (eq_neg_of_add_eq_zero_right X.2).trans (neg_mul X.1ᴴ J).symm
    -- `using!`: the two sides differ in the topology instance under which `exp` is taken.
    simpa [U, ← exp_conjTranspose] using! h_semiconj.exp_neg_mul_mul_exp_eq_self

/-! ### Parameters and weights -/

/-- The product over all integers `t` of the principal minor of `g` on `{i | t ≤ l i}`, each factor
with `t ≤ 0` divided by `det g`. For invertible `g` almost all factors are `1`. For a dominant
weight `l` it is the coefficient of a highest vector of weight `l`. -/
def weightMinors : ℂ := ∏ᶠ t : ℤ, principalMinor g (fun i ↦ t ≤ l i) / if t ≤ 0 then g.det else 1

/-- The gap `500 n³ + A`, where `n` is the number of indices. -/
abbrev gapThreshold (n : Type*) [Fintype n] (A : ℕ) : ℕ := 500 * Fintype.card n ^ 3 + A

/-- The vector with i-th entry #{j : r(i,j), l_j < l_i} − #{j : r(i,j), l_i < l_j}: the sum of
those roots e_i − e_j selected by r that are positive for l, when r is symmetric. -/
def twoRho (r : n → n → Prop) [DecidableRel r] (i : n) : ℤ :=
  (#{j : n | r i j ∧ l j < l i} - #{j : n | r i j ∧ l i < l j} : ℤ)

/-- The integer vector with entries (l_i + 2ρ_i)/2 rounded down, ρ the half sum of roots
positive for l; it is λ+ρ for a parameter l = 2λ. -/
def paramAddRho (i : n) : ℤ := (l i + twoRho l ⊤ i) / 2

/-- The product of `λ i - λ j` over the pairs with `λ j < λ i`, divided by `∏_{i < card n} i!`, for
`l = 2λ`. -/
def weylDimensionPoly : ℝ :=
  (∏ i : n, ∏ j : n with l j < l i, (l i - l j : ℝ) / 2) /
    ∏ i ∈ Finset.range (Fintype.card n), ↑i.factorial

/-! ### The compact subgroup -/

/-- The subgroup U(diag ε)∩U(n) of U(diag ε), consisting of the elements that are unitary
matrices. -/
def maxCompactU : Subgroup (U (signMatrix ε)) := (U 1).subgroupOf (U (signMatrix ε))

instance : CompactSpace (maxCompactU ε) :=
  ((isClosed_U _).isClosedEmbedding_subtypeVal.restrictPreimage _).compactSpace (Y := U 1)

/-- The Haar measure of total mass one on the compact group K=U(diag ε)∩U(n). -/
def haarK : Measure (maxCompactU ε) := Measure.haarMeasure ⊤

/-! ### Block diagonal parts, parameters and discrete series coefficients -/

/-- The continuous linear map that keeps the entries `(i, j)` of a matrix with `r i j` and puts `0`
elsewhere. -/
@[simp]
def entryMask (r : n → n → Prop) [DecidableRel r] : Matrix n n ℂ →L[ℂ] Matrix n n ℂ :=
  LinearMap.toContinuousLinearMap
    ({ toFun Z := Matrix.of fun i j ↦ if r i j then Z i j else 0
       map_add' := by aesop
       map_smul' := by aesop } : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)

/-- For signs ε, the continuous linear map that keeps the entries (i, j) of a matrix with ε_i=ε_j
and puts zero elsewhere. -/
def blockDiagPart : Matrix n n ℂ →L[ℂ] Matrix n n ℂ := entryMask fun i j ↦ ε i = ε j

/-- Integer vectors indexed by n, attached to the signs ε; they serve as doubled Harish-Chandra
parameters l = 2λ and as integral weights of U(diag ε). -/
abbrev HCParam {n : Type*} (_ : n → ℤˣ) : Type _ := n → ℤ

/-- The integer vector l, regarded as a doubled parameter or weight for the signs ε. -/
abbrev toHCParam : HCParam ε := l

namespace HCParam

variable {ε : n → ℤˣ} (l : HCParam ε) (g z : Matrix n n ℂ)

/-- The same integer vector l, regarded for the signs all equal to 1, that is for the compact
group U(n). -/
abbrev compactForm : HCParam (1 : n → ℤˣ) := toHCParam 1 l

/-- The integral ∫_K |m_l(k)|² dk over K = U(diag ε)∩U(n) with total mass one, where
m_l = `New.weightMinors l` is the product of principal minors of weight l. -/
abbrev kTypeNormSq : ℝ := ∫ k : maxCompactU ε, ‖weightMinors l k.val‖ ^ 2 ∂haarK ε

/-- The vector `l = 2λ` is a parameter of gap `h`: its entries are distinct and congruent to
`card n - 1` mod 2, and `|λ i - λ j| ≥ h` whenever `ε i ≠ ε j`. -/
class HasGap (h : outParam ℕ) where
  /-- The entries of `l = 2λ` are distinct. -/
  injective : Function.Injective l
  /-- Each entry of `l` has the parity of `card n - 1`, that is, `λ i ∈ (card n - 1) / 2 + ℤ`. -/
  parity (i : n) : Even (l i + Fintype.card n - 1)
  /-- Entries of `λ` with different signs `ε` are at least `h` apart. -/
  gap (i j : n) : ε i ≠ ε j → 2 * h ≤ |l i - l j|

/-- The vector `l = 2λ` is a parameter for the signs `ε` with gap `500 n³ + A`. -/
abbrev HasLargeGap (A : ℕ) : Prop := l.HasGap (gapThreshold n A)

/-- The integer vector `paramAddRho l - 2ρ_c`, where `2ρ_c` is the sum of the compact roots
(`ε i = ε j`) that are positive for `l`. For a parameter `l = 2λ` it is `Λ = λ + ρ - 2ρ_c`, the
highest weight of the lowest K-type. -/
def lowestKType : HCParam ε := fun i ↦ paramAddRho l i - twoRho l (fun i j ↦ ε i = ε j) i

/-- For l = 2λ, the real number κ_λ = |λ|² − |ρ|², ρ the half sum of the roots positive for l. -/
def casimirValue : ℝ := ∑ i : n, (l i ^ 2 - twoRho l ⊤ i ^ 2 : ℝ) / 4

/-- Flensted-Jensen's integral ∫_K m_Λ(gk) conj(m_Λ(k)) / m_{−λ−ρ}(kᴴzk) dk divided by
∫_K |m_Λ|², for l = 2λ, Λ = λ+ρ−2ρ_c and m_w = `New.weightMinors w`. For a parameter l the
factor 1 / ∫_K |m_Λ|² is, by Schur's relations, the dimension of the K-type Λ. -/
def flenstedJensen : ℂ :=
  (∫ k : maxCompactU ε, weightMinors l.lowestKType (g * k.val) *
      conj (weightMinors l.lowestKType k.val) /
      weightMinors (-paramAddRho l) ((k.val : Matrix n n ℂ)ᴴ * z * k.val) ∂haarK ε) /
    l.lowestKType.kTypeNormSq

/-- The function c_λ(g) = Ξ(a, a⁻¹g) of a complex matrix g, with a the block diagonal part of g
and Ξ the normalised integral `New.HCParam.flenstedJensen`. On U(diag ε), for a parameter with a
gap, every splitting g = pzqᴴ with p, q block diagonal and z accretive gives the same value
(`New.dsCoeff_eq_integral_of_eq_mul_mul_conjTranspose`). -/
def dsCoeff : ℂ := l.flenstedJensen (blockDiagPart ε g) ((blockDiagPart ε g)⁻¹ * g)

/-- For signs ε and l=2λ, the reciprocal of the integral of |c_λ|² over U(diag ε) for the
measure `New.haarU`, which is the `volume` of that group. -/
def formalDegree : ℝ := (∫ g : USign ε, ‖l.dsCoeff g‖ ^ 2)⁻¹

/-- The complex function on U(diag ε) given by deg_λ times the complex conjugate of c_λ(g), for
l=2λ. -/
def dsKernel (g : USign ε) : ℂ := l.formalDegree * conj (l.dsCoeff g)

end HCParam

export HCParam (kTypeNormSq HasGap lowestKType flenstedJensen dsCoeff formalDegree dsKernel)

namespace Exchange

variable {α β : Type*} [Fintype α] [Fintype β] (a : α → ℤˣ) {b : β → ℤˣ}

/-! ### Counting negative signs -/

/-- The number of indices `i` with sign `a i = -1`. It is additive over `a ⊕ᵥ b`, the sign vector
`Sum.elim a b` on `α ⊕ β` (`New.Exchange.negCount_sumElim`). -/
@[local simp]
def negCount : ℕ := Fintype.card {x // a x = -1}

lemma negCount_neg_add : negCount (-a) + negCount a = Fintype.card α := by
  simp [← units_ne_iff_eq_neg, card_subtype_le]

@[simp]
lemma negCount_sumElim : negCount (a ⊕ᵥ b) = negCount a + negCount b :=
  (card_congr subtypeSum).trans card_sum

lemma negCount_one : negCount (1 : α → ℤˣ) = 0 := by simp

lemma negCount_neg_one : negCount (-1 : α → ℤˣ) = Fintype.card α := by simp

@[simp]
lemma negCount_one_and_neg_one :
    negCount (1 : α → ℤˣ) = 0 ∧ negCount (-1 : α → ℤˣ) = Fintype.card α :=
  ⟨negCount_one, negCount_neg_one⟩

/-- Sign vectors on index types of the same size with equally many negative signs (`negCount`, the
number of entries `-1`) differ by a bijection of the indices. -/
lemma _root_.New.exists_equiv_comp_eq_of_negCount_eq {a : α → ℤˣ}
    (h_card : Fintype.card α = Fintype.card β)
    (h_neg : negCount a = negCount b) : ∃ e : α ≃ β, b ∘ e = a := by
  -- The fibres over `-1` have equal size by `h_neg`; by `h_card`, so have their complements.
  have h_pos : negCount (-a) = negCount (-b) := by grind [negCount_neg_add]
  have h_fiber (c : ℤˣ) : card {x // a x = c} = card {x // b x = c} := by
    rcases Int.units_eq_one_or c with rfl | rfl
    · simpa [negCount] using h_pos
    · simpa [negCount] using h_neg
  exact ⟨ofFiberEquiv fun c ↦ equivOfCardEq (h_fiber c), funext (ofFiberEquiv_map _)⟩

end Exchange

end New

end DiscreteSeriesDefs

/-!
## Arithmetic of ρ, λ + ρ, Λ and the gap condition

Elementary facts about `ρ`, and, for a Harish-Chandra parameter `l = 2λ` with signs `ε i = ±1`
(`New.HCParam.HasGap`: distinct entries `≡ n - 1` mod 2, and `|l i - l j| ≥ 2h` whenever
`ε i ≠ ε j`), about `λ + ρ` and `Λ = New.HCParam.lowestKType l`.
-/

section RhoArithmetic

open Finset Fintype

namespace New

variable {n : Type} [Fintype n] {ε : n → ℤˣ} {l : HCParam ε} {h h' : ℕ}

/-- Every entry of `New.twoRho l r`, a difference of two numbers of indices, has absolute value at
most the number of all indices. -/
theorem abs_twoRho_le (r : n → n → Prop) [DecidableRel r] (i : n) (l : n → ℤ) :
    |twoRho l r i| ≤ Fintype.card n := by
  grind [twoRho, card_le_univ]

/-- The vector `New.twoRho l r`, whose `i`-th entry counts the `j` related to `i` by `r` with
`l j < l i` minus those with `l i < l j`, changes sign with `l`. -/
theorem twoRho_neg (r : n → n → Prop) [DecidableRel r] (i : n) (l : n → ℤ) :
    twoRho (-l) r i = -twoRho l r i := by
  simp [twoRho]

/-- For injective `l`, the number of indices `j` with `l j < l i`, plus the number of those with
`l i < l j`, plus one for `i` itself, is the number of all indices. -/
theorem card_lt_add_card_gt_add_one {l : n → ℤ} (hl : l.Injective) (i : n) :
    #{j : n | l j < l i} + #{j : n | l i < l j} + 1 = Fintype.card n := by
  classical
  set below : Finset n := {j | l j < l i}
  set above : Finset n := {j | l i < l j}
  have h_disj : Disjoint below above := disjoint_filter.mpr fun j _ h_lt h_gt ↦ lt_asymm h_lt h_gt
  have h_not : i ∉ below ∪ above := by simp [below, above]
  have h_univ : insert i (below ∪ above) = univ := by grind [hl.eq_iff]
  rw [← card_union_of_disjoint h_disj, ← card_insert_of_notMem h_not, h_univ, card_univ]

/-- `2(λ + ρ) = l + 2ρ`, where `2ρ = New.twoRho l ⊤` is the sum of the roots positive for `l`: for a
parameter `l = 2λ` of some gap (distinct entries congruent to `n - 1` mod 2) the division by 2 in
`New.paramAddRho l` is exact. -/
theorem two_mul_paramAddRho (hg : l.HasGap h) (i : n) :
    2 * paramAddRho l i = l i + twoRho l ⊤ i := by
  -- The counts below and above `i` add up to `n - 1`, which has the parity of `l i`.
  have h_even : Even (l i + twoRho l ⊤ i) := by
    simp only [twoRho, Pi.top_apply, Prop.top_eq_true, true_and]
    grind [card_lt_add_card_gt_add_one hg.injective i, hg.parity i]
  rw [paramAddRho, Int.mul_ediv_cancel' h_even.two_dvd]

/-- For a parameter `l = 2λ` of some gap `h` (distinct entries congruent to `n - 1` mod 2, those at
indices with different signs `ε` at least `2h` apart), twice
`Λ = New.HCParam.lowestKType l` is `l + 2ρ_n - 2ρ_c`. Here `ρ_n` and `ρ_c` are the half sums of
the roots `e_i - e_j` with `l j < l i` and with `ε i ≠ ε j`, respectively `ε i = ε j`, and
`New.twoRho l r` is the sum of those roots for the relation `r`. -/
@[local grind .]
theorem two_mul_lowestKType (hg : l.HasGap h) (i : n) :
    2 * l.lowestKType i =
      l i + twoRho l (fun a b : n ↦ ε a ≠ ε b) i - twoRho l (fun a b : n ↦ ε a = ε b) i := by
  -- `twoRho` of all roots is the sum of its parts with different and with equal signs.
  have h_count (p : n → Prop) [DecidablePred p] :
      #{j : n | p j} = #{j : n | ε i ≠ ε j ∧ p j} + #{j : n | ε i = ε j ∧ p j} := by
    rw [← card_filter_add_card_filter_not (s := {j | p j}) (fun j ↦ ε i ≠ ε j)]
    simp [filter_filter, and_comm]
  have h_split : twoRho l ⊤ i =
      twoRho l (fun a b : n ↦ ε a ≠ ε b) i + twoRho l (fun a b : n ↦ ε a = ε b) i := by
    -- Apply `h_count` to the indices below and to those above `i`.
    simp only [twoRho, Pi.top_apply, Prop.top_eq_true, true_and]
    grind
  rw [lowestKType, mul_sub, two_mul_paramAddRho hg, h_split]
  ring

/-- If `l = 2λ` is a parameter of gap `h` for the signs `ε` (distinct entries congruent to `n - 1`
mod 2, those at indices with different signs at least `2h` apart) and `|l a| ≤ L` for all `a`,
then every entry of `Λ = New.HCParam.lowestKType l`, the vector `λ + ρ - 2ρ_c`, satisfies
`|Λ a| ≤ L + n`, where `n` is the number of indices. -/
theorem abs_lowestKType_le (hg : l.HasGap h) {L : ℕ} (hL : ∀ a : n, |l a| ≤ L) (a : n) :
    |l.lowestKType a| ≤ ↑(L + Fintype.card n) := by
  -- Twice `|Λ a|` is at most `|l a|` plus two terms `|twoRho l r a| ≤ n`.
  have h_two : 2 * l.lowestKType a = l a + twoRho l (fun a b : n ↦ ε a ≠ ε b) a -
      twoRho l (fun a b : n ↦ ε a = ε b) a := two_mul_lowestKType hg a
  have h_ne : |twoRho l (fun a b : n ↦ ε a ≠ ε b) a| ≤ Fintype.card n := abs_twoRho_le _ a l
  have h_eq : |twoRho l (fun a b : n ↦ ε a = ε b) a| ≤ Fintype.card n := abs_twoRho_le _ a l
  grind [hL a]

theorem HCParam.HasGap.mono (hg : l.HasGap h) (h_le : h' ≤ h) : l.HasGap h' :=
  { hg with gap i j h_ne := by linarith [hg.gap i j h_ne] }

/-- If l = 2λ is a parameter of gap h for the signs ε (distinct entries congruent to n − 1 mod 2,
those at indices with different signs at least 2h apart), then `l.compactForm`, the same vector
for the constant signs +1 (that is, for the compact group U(n)), is a parameter of gap h as
well. -/
theorem HCParam.HasGap.signs_one (hg : l.HasGap h) : l.compactForm.HasGap h :=
  { hg with gap := by simp }

theorem HCParam.HasGap.neg (hg : l.HasGap h) : (-l).HasGap h where
  injective := neg_injective.comp hg.injective
  parity i := by grind [hg.parity i, Pi.neg_apply]
  gap i j h_ne := by simpa [abs_sub_comm, neg_add_eq_sub] using hg.gap i j h_ne

@[simp]
theorem lowestKType_neg (hg : l.HasGap h) : (-l).lowestKType = -l.lowestKType := by
  funext i
  -- Compare `2Λ = l + 2ρ_n - 2ρ_c` for `l` and for `-l`.
  grind [two_mul_lowestKType hg i, two_mul_lowestKType hg.neg i, twoRho_neg, Pi.neg_apply]

end New

end RhoArithmetic

/-!
## Borel matrices, K-dominance and holomorphic functions of weight u

An integer vector `o`, usually injective, orders the indices; weights are integer vectors.

* `New.IsBorelMatrix`, `New.diagChar`, `New.blockDiagAlg`, `New.diagTorus`: the matrices of the
  Borel subgroup for `o`, their characters, the algebra of block diagonal matrices and the map
  from tuples in the circle to diagonal elements of the group.
-/

namespace New

open Matrix Norms.L2Operator

variable {n Φ : Type} [Fintype n] [DecidableEq n] (ε : n → ℤˣ) (o w : n → ℤ) (b : Matrix n n ℂ)
  [Fintype Φ] (u : Φ → n → ℤ)

/-- For an integer vector w and a complex square matrix b, the product over i of the diagonal
entries b_ii raised to the power w_i. -/
def diagChar : ℂ := ∏ i : n, b i i ^ w i

/-- The matrix b is invertible and block upper triangular for o: b_ij = 0 whenever o_j < o_i. For
injective o it is upper triangular in the order given by o. -/
def IsBorelMatrix : Prop := b.BlockTriangular o ∧ b.det ≠ 0

/-- The weight w is K-dominant for the order o: w_j ≤ w_i whenever ε_i = ε_j and o_i < o_j. -/
def IsKDominant : Prop := ∀ i j : n, ε i = ε j → o i < o j → w j ≤ w i

/-- The order o has distinct values and puts every index of sign +1 before every index of sign
−1. -/
def IsPosFirstOrder : Prop := o.Injective ∧ ∀ i j : n, ε i = 1 → ε j = -1 → o i < o j

/-- The condition on signs ε, integer vector w and natural number γ that w_i + γ ≤ w_j whenever
ε_i = +1 and ε_j = −1. -/
def HasHolGap (γ : ℕ) : Prop := ∀ i j : n, ε i = 1 → ε j = -1 → w i + γ ≤ w j

/-- The algebra of complex matrices commuting with diag(ε), that is the block diagonal matrices
for the signs ε. -/
def blockDiagAlg : Subalgebra ℂ (Matrix n n ℂ) := Subalgebra.centralizer ℂ {signMatrix ε}

/-- F on U(diag ε)^Φ is holomorphic of weight u: some function F' of tuples of matrices is analytic
at all products hb, with F'(hb) = ∏_τ `New.diagChar` (u τ) (b τ) · F(h). Here h is in the group, b
is invertible and o-triangular, and both commute with diag(ε'), which is no condition for the
default ε' = 1. -/
def IsHolOfWeight (F : (Φ → USign ε) → ℂ) (ε' : n → ℤˣ := 1) : Prop :=
  ∃ F' : (Φ → Matrix n n ℂ) → ℂ, ∀ (h : Φ → USign ε) (b : Φ → Matrix n n ℂ),
    (∀ τ : Φ, IsBorelMatrix o (b τ)) →
    (∀ τ : Φ, ↑(h τ : USign ε) ∈ blockDiagAlg ε' ∧ b τ ∈ blockDiagAlg ε') →
    letI z (τ : Φ) := h τ * b τ
    AnalyticAt ℂ F' z ∧ F' z = (∏ τ : Φ, diagChar (u τ) (b τ)) * F h

/-- For signs ε, weight w and matrix b, the quotient m_{w+c}(b)/m_c(b) of products of
principal minors m = `New.weightMinors`, where c_i = 2∑|w_j| if ε_i = +1 and c_i = 0 otherwise. -/
def holMinors : ℂ :=
  letI c (i : n) := if ε i = 1 then 2 * ∑ j : n, |w j| else 0
  weightMinors (fun i ↦ w i + c i) b / weightMinors c b

/-- For weights u_τ and a tuple h in U(diag ε)^Φ, the product over τ of the quotients of minors
`New.holMinors` of weight u_τ at h_τ. -/
def holMinorsPi (h : Φ → USign ε) : ℂ := ∏ τ : Φ, holMinors ε (u τ) (h τ)

/-- For a tuple t of complex numbers of modulus one, the diagonal matrix diag(t) as an element
of U(diag ε). -/
def diagTorus (t : n → Circle) : USign ε :=
  ⟨IsUnit.unit (a := diagonal fun i ↦ t i) (by simp [Pi.isUnit_iff]),
    by simp [U, signMatrix, field, ← Circle.coe_inv_eq_conj]⟩

end New

end
