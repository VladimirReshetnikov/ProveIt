import ExponentialIdentities.TwoBaseIntegerExponent.MixedExponentSemigroup
import ExponentialIdentities.TwoBaseIntegerExponent.RowBlockUnitDivisibility
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Mixed-determinant bridge to row-block unit divisibility

The report's mixed integer matrix has entries `left row ^ u * right row ^ v`.
After grouping columns by `u` at the prime two, or by `v` at the prime
three, its entries are exactly a rank-one structural prime power times a
block-scaled consecutive-power unit matrix.  This file records that exact
algebraic identification and transfers the additive tropical-plus-unit
divisors back through the column permutation.

The endpoint theorems deliberately take the finite fiber data as explicit
hypotheses: a column permutation, ordered block labels, block sizes, and a
degree-preserving equivalence of each fiber with `Fin (s k)`.  Constructing
those certificates for the globally first `N` mixed exponents is a separate
finite combinatorial problem.

For later use, the file also gives a finite, noncomputable model obtained by
sorting the `(N + 1) × (N + 1)` exponent box and restricting to its first
`N` entries.  The resulting weights are strictly increasing.  No claim is
made here that this prefix has already been identified with a separately
defined global enumeration of the mixed semigroup.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Matrix

/-! ## A finite sorted-box model for mixed exponent columns -/

noncomputable section

/-- The standard enumeration of the exponent box `{0, ..., N}²`. -/
def mixedExponentBoxPair (N : ℕ) :
    Fin ((N + 1) * (N + 1)) → ℕ × ℕ :=
  fun j ↦
    let uv := finProdFinEquiv.symm j
    ((uv.1 : ℕ), (uv.2 : ℕ))

theorem mixedExponentBoxPair_injective (N : ℕ) :
    Function.Injective (mixedExponentBoxPair N) := by
  intro i j hij
  dsimp [mixedExponentBoxPair] at hij
  apply finProdFinEquiv.symm.injective
  apply Prod.ext
  · exact Fin.ext (congrArg Prod.fst hij)
  · exact Fin.ext (congrArg Prod.snd hij)

/-- There is room for `N` columns in the `(N + 1) × (N + 1)` box. -/
theorem le_mixedExponentBox_card (N : ℕ) :
    N ≤ (N + 1) * (N + 1) := by
  nlinarith [Nat.zero_le N]

/-- The exponent box reordered by increasing mixed weight. -/
def sortedMixedExponentBoxPair (N : ℕ) :
    Fin ((N + 1) * (N + 1)) → ℕ × ℕ :=
  mixedExponentBoxPair N ∘
    Tuple.sort (mixedExponent ∘ mixedExponentBoxPair N)

/-- Irrationality of the mixed slope upgrades sortedness of the finite box
from monotonicity to strict monotonicity. -/
theorem sortedMixedExponentBoxPair_weight_strictMono (N : ℕ) :
    StrictMono (mixedExponent ∘ sortedMixedExponentBoxPair N) := by
  have hmono : Monotone
      ((mixedExponent ∘ mixedExponentBoxPair N) ∘
        Tuple.sort (mixedExponent ∘ mixedExponentBoxPair N)) :=
    Tuple.monotone_sort (mixedExponent ∘ mixedExponentBoxPair N)
  have hinj : Function.Injective
      ((mixedExponent ∘ mixedExponentBoxPair N) ∘
        Tuple.sort (mixedExponent ∘ mixedExponentBoxPair N)) :=
    (mixedExponent_injective.comp (mixedExponentBoxPair_injective N)).comp
      (Tuple.sort (mixedExponent ∘ mixedExponentBoxPair N)).injective
  exact hmono.strictMono_of_injective hinj

/-- The first `N` entries of the sorted `(N + 1) × (N + 1)` exponent box. -/
def sortedMixedExponentBoxPrefix (N : ℕ) : Fin N → ℕ × ℕ :=
  sortedMixedExponentBoxPair N ∘
    Fin.castLE (le_mixedExponentBox_card N)

theorem sortedMixedExponentBoxPrefix_weight_strictMono (N : ℕ) :
    StrictMono (mixedExponent ∘ sortedMixedExponentBoxPrefix N) := by
  exact (sortedMixedExponentBoxPair_weight_strictMono N).comp
    (Fin.strictMono_castLE (le_mixedExponentBox_card N))

end

/-! ## Exact matrix identifications after grouping columns -/

/-- The integer mixed-power matrix with column exponent pair `(u, v)`. -/
def mixedIntegerPowerMatrix
    {N : ℕ} (left right : Fin N → ℤ) (ab : Fin N → ℕ × ℕ) :
    Matrix (Fin N) (Fin N) ℤ :=
  fun row col ↦ left row ^ (ab col).1 * right row ^ (ab col).2

/-- After a column permutation presents each exponent pair as
`(value (b col), degree col)`, the dyadic mixed matrix is exactly the
rank-one matrix whose unit part has row scale `M ^ (row * value block)`. -/
theorem submatrix_mixedIntegerPowerMatrix_eq_two_rankOnePowerMatrix
    {N : ℕ} {o : Type*}
    (depth : Fin N → ℕ) (M : ℤ) (q : Fin N → ℤ)
    (ab : Fin N → ℕ × ℕ) (rho : Equiv.Perm (Fin N))
    (b : Fin N → o) (value : o → ℕ) (degree : Fin N → ℕ)
    (hab : ∀ col, ab (rho col) = (value (b col), degree col)) :
    (mixedIntegerPowerMatrix
        (fun row ↦ (2 : ℤ) ^ depth row * M ^ (row : ℕ)) q ab).submatrix id rho =
      rankOnePowerMatrix 2 depth b value
        (fiberScaledConsecutivePowerMatrix b degree
          (fun k row ↦ M ^ ((row : ℕ) * value k))
          (fun _ row ↦ q row)) := by
  ext row col
  simp only [Matrix.submatrix_apply, mixedIntegerPowerMatrix, id_eq,
    hab col, rankOnePowerMatrix_apply, fiberScaledConsecutivePowerMatrix]
  rw [mul_pow, pow_mul]
  ring

/-- The symmetric triadic identification, now grouping the columns by
their second exponent and using the first exponent as local degree. -/
theorem submatrix_mixedIntegerPowerMatrix_eq_three_rankOnePowerMatrix
    {N : ℕ} {o : Type*}
    (depth : Fin N → ℕ) (A : ℤ) (r : Fin N → ℤ)
    (ab : Fin N → ℕ × ℕ) (rho : Equiv.Perm (Fin N))
    (b : Fin N → o) (value : o → ℕ) (degree : Fin N → ℕ)
    (hab : ∀ col, ab (rho col) = (degree col, value (b col))) :
    (mixedIntegerPowerMatrix r
        (fun row ↦ (3 : ℤ) ^ depth row * A ^ (row : ℕ)) ab).submatrix id rho =
      rankOnePowerMatrix 3 depth b value
        (fiberScaledConsecutivePowerMatrix b degree
          (fun k row ↦ A ^ ((row : ℕ) * value k))
          (fun _ row ↦ r row)) := by
  ext row col
  simp only [Matrix.submatrix_apply, mixedIntegerPowerMatrix, id_eq,
    hab col, rankOnePowerMatrix_apply, fiberScaledConsecutivePowerMatrix]
  rw [mul_pow, pow_mul]
  ring

/-- Divisibility of a determinant is unchanged when the columns are
permuted. -/
theorem dvd_det_of_dvd_det_columnPermute
    {N : ℕ} (d : ℤ) (B : Matrix (Fin N) (Fin N) ℤ)
    (rho : Equiv.Perm (Fin N))
    (h : d ∣ (B.submatrix id rho).det) : d ∣ B.det := by
  rw [Matrix.det_permute'] at h
  rcases Int.units_eq_one_or (Equiv.Perm.sign rho) with hs | hs
  · simpa [hs] using h
  · simpa [hs] using h

/-! ## Additive tropical minimum plus unit-ordering gain -/

/-- Dyadic additive divisor for a raw mixed integer matrix.  The hypotheses
`e` and `hdegree` say exactly that, after `rho`, every fixed-`u` fiber has
local degrees `0, ..., s u - 1`. -/
theorem two_pow_minCost_add_rowBlockOrderingExponent_dvd_det_mixedIntegerPowerMatrix
    {N : ℕ} {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    {depth : Fin N → ℕ} (M : ℤ) (q : Fin N → ℤ)
    (ab : Fin N → ℕ × ℕ) (rho : Equiv.Perm (Fin N))
    (b : Fin N → o) {value : o → ℕ}
    (s : o → ℕ) (e : ∀ k : o, {i : Fin N // b i = k} ≃ Fin (s k))
    (degree : Fin N → ℕ)
    (hab : ∀ col, ab (rho col) = (value (b col), degree col))
    (hdegree : ∀ (k : o) (j : Fin (s k)),
      degree ((e k).symm j).1 = (j : ℕ))
    (z : Fin N → ℕ) (hq : ∀ row, q row = 2 * (z row : ℤ) + 1)
    (hdepth : StrictAnti depth) (hb : Monotone b) (hvalue : Monotone value) :
    (2 : ℤ) ^
        (rankOneAssignmentCost depth (value ∘ b) (Equiv.refl _) +
          rowBlockOrderingExponent s twoUnitOrderingWeight) ∣
      (mixedIntegerPowerMatrix
        (fun row ↦ (2 : ℤ) ^ depth row * M ^ (row : ℕ)) q ab).det := by
  let D := mixedIntegerPowerMatrix
    (fun row ↦ (2 : ℤ) ^ depth row * M ^ (row : ℕ)) q ab
  apply dvd_det_of_dvd_det_columnPermute _ D rho
  rw [submatrix_mixedIntegerPowerMatrix_eq_two_rankOnePowerMatrix
    depth M q ab rho b value degree hab]
  rw [show (fun _ row ↦ q row) =
      (fun (_ : o) row ↦ 2 * (z row : ℤ) + 1) by
        funext k row
        exact hq row]
  exact two_pow_minCost_add_rowBlockOrderingExponent_dvd_det_rankOnePowerMatrix
    b s e degree hdegree
      (fun k row ↦ M ^ ((row : ℕ) * value k))
      (fun _ row ↦ z row) hdepth hb hvalue

/-- Triadic additive divisor for a raw mixed integer matrix.  After `rho`,
the fixed-`v` fibers have consecutive first-coordinate degrees. -/
theorem three_pow_minCost_add_rowBlockOrderingExponent_dvd_det_mixedIntegerPowerMatrix
    {N : ℕ} {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    {depth : Fin N → ℕ} (A : ℤ) (r : Fin N → ℤ)
    (ab : Fin N → ℕ × ℕ) (rho : Equiv.Perm (Fin N))
    (b : Fin N → o) {value : o → ℕ}
    (s : o → ℕ) (e : ∀ k : o, {i : Fin N // b i = k} ≃ Fin (s k))
    (degree : Fin N → ℕ)
    (hab : ∀ col, ab (rho col) = (degree col, value (b col)))
    (hdegree : ∀ (k : o) (j : Fin (s k)),
      degree ((e k).symm j).1 = (j : ℕ))
    (z : Fin N → ℕ) (residue : Fin N → Fin 2)
    (hr : ∀ row,
      r row = 3 * (z row : ℤ) + ((residue row : ℕ) : ℤ) + 1)
    (hdepth : StrictAnti depth) (hb : Monotone b) (hvalue : Monotone value) :
    (3 : ℤ) ^
        (rankOneAssignmentCost depth (value ∘ b) (Equiv.refl _) +
          rowBlockOrderingExponent s threeUnitOrderingWeight) ∣
      (mixedIntegerPowerMatrix r
        (fun row ↦ (3 : ℤ) ^ depth row * A ^ (row : ℕ)) ab).det := by
  let D := mixedIntegerPowerMatrix r
    (fun row ↦ (3 : ℤ) ^ depth row * A ^ (row : ℕ)) ab
  apply dvd_det_of_dvd_det_columnPermute _ D rho
  rw [submatrix_mixedIntegerPowerMatrix_eq_three_rankOnePowerMatrix
    depth A r ab rho b value degree hab]
  rw [show (fun _ row ↦ r row) =
      (fun (_ : o) row ↦
        3 * (z row : ℤ) + ((residue row : ℕ) : ℤ) + 1) by
        funext k row
        exact hr row]
  exact three_pow_minCost_add_rowBlockOrderingExponent_dvd_det_rankOnePowerMatrix
    b s e degree hdegree
      (fun k row ↦ A ^ ((row : ℕ) * value k))
      (fun _ row ↦ z row) (fun _ row ↦ residue row) hdepth hb hvalue

end LeanProofs.TwoBaseIntegerExponent
