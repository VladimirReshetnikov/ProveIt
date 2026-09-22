import Surreal.Surcomplex.PowerSeries
import Surreal.HahnSeries.BinomialRoots

/-!
# Binomial series at actual surcomplex infinitesimals

For an ordinary complex exponent, the formal binomial series at an actual
infinitesimal is a strong sum with standard part one. Exponent addition
and natural powers have their formal meanings. Positive integer roots
are unique among all actual values infinitesimally close to one. The
construction includes zero increments. No global power operation, choice
of roots away from one, or topological convergence is asserted.
-/

universe u v

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- The ordinary-complex binomial series evaluated at an actual infinitesimal. -/
def binomialPower (x : Surcomplex.{u}) (hx : IsInfinitesimal x) (r : ℂ) :
    Surcomplex.{u} :=
  powerSeriesEvaluation x hx (PowerSeries.binomialSeries ℂ r)

/-- The displayed binomial terms satisfy both strong summability conditions. -/
theorem stronglySummable_binomialTerms (x : Surcomplex.{u}) (hx : IsInfinitesimal x)
    (r : ℂ) : StronglySummable (fun n : ℕ => ofComplex (Ring.choose r n) * x ^ n) :=
  stronglySummable_coeff_mul_powers x hx (fun n => Ring.choose r n)

/-- Binomial evaluation is exactly the strong sum of the usual coefficient-times-power terms. -/
theorem binomialPower_eq_strongSum (x : Surcomplex.{u}) (hx : IsInfinitesimal x)
    (r : ℂ) : binomialPower x hx r =
      strongSum (fun n : ℕ => ofComplex (Ring.choose r n) * x ^ n)
        (stronglySummable_binomialTerms x hx r) := by
  simpa only [binomialPower, PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one] using
    powerSeriesEvaluation_eq_strongSum x hx (PowerSeries.binomialSeries ℂ r)

/-- Every binomial value is finite. -/
theorem isFinite_binomialPower (x : Surcomplex.{u}) (hx : IsInfinitesimal x) (r : ℂ) :
    IsFinite (binomialPower x hx r) :=
  isFinite_powerSeriesEvaluation x hx _

@[simp] theorem standardPart_binomialPower (x : Surcomplex.{u}) (hx : IsInfinitesimal x)
    (r : ℂ) : standardPart (binomialPower x hx r) = 1 := by
  rw [binomialPower, standardPart_powerSeriesEvaluation, PowerSeries.binomialSeries_constantCoeff]

/-- The binomial value belongs to the actual infinitesimal neighborhood of one. -/
theorem isInfinitesimal_binomialPower_sub_one (x : Surcomplex.{u})
    (hx : IsInfinitesimal x) (r : ℂ) : IsInfinitesimal (binomialPower x hx r - 1) := by
  have h := (isInfinitesimal_powerSeriesEvaluation_iff x hx
    (PowerSeries.binomialSeries ℂ r - 1)).mpr (by simp)
  simpa only [map_sub, map_one, binomialPower] using h

/-- Exponent addition multiplies the actual binomial values. -/
theorem binomialPower_add (x : Surcomplex.{u}) (hx : IsInfinitesimal x) (r s : ℂ) :
    binomialPower x hx (r + s) = binomialPower x hx r * binomialPower x hx s := by
  simp only [binomialPower, PowerSeries.binomialSeries_add, map_mul]

@[simp] theorem binomialPower_nat (x : Surcomplex.{u}) (hx : IsInfinitesimal x) (n : ℕ) :
    binomialPower x hx (n : ℂ) = (1 + x) ^ n := by
  simp only [binomialPower, PowerSeries.binomialSeries_nat, map_pow, map_add, map_one,
    powerSeriesEvaluation_X]

@[simp] theorem binomialPower_zero (x : Surcomplex.{u}) (hx : IsInfinitesimal x) :
    binomialPower x hx (0 : ℂ) = 1 := by
  simpa only [Nat.cast_zero, pow_zero] using binomialPower_nat x hx 0

@[simp] theorem binomialPower_one (x : Surcomplex.{u}) (hx : IsInfinitesimal x) :
    binomialPower x hx (1 : ℂ) = 1 + x := by
  simpa only [Nat.cast_one, pow_one] using binomialPower_nat x hx 1

@[simp] theorem binomialPower_zero_input (r : ℂ) :
    binomialPower (0 : Surcomplex.{u}) ⟨SignSequence.infinitesimal_zero, SignSequence.infinitesimal_zero⟩ r = 1 := by
  simp only [binomialPower, powerSeriesEvaluation_zero, PowerSeries.binomialSeries_constantCoeff,
    map_one]

/-- Finite powers multiply the ordinary formal exponent. -/
theorem binomialPower_pow (x : Surcomplex.{u}) (hx : IsInfinitesimal x) (r : ℂ) (n : ℕ) :
    binomialPower x hx r ^ n = binomialPower x hx ((n : ℂ) * r) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Nat.cast_add, Nat.cast_one, add_mul, one_mul, binomialPower_add]

theorem binomialPower_ne_zero (x : Surcomplex.{u}) (hx : IsInfinitesimal x) (r : ℂ) :
    binomialPower x hx r ≠ 0 := by
  apply left_ne_zero_of_mul_eq_one (b := binomialPower x hx (-r))
  rw [← binomialPower_add, _root_.add_neg_cancel, binomialPower_zero]

/-- Negating the exponent gives the multiplicative inverse near one. -/
theorem binomialPower_neg (x : Surcomplex.{u}) (hx : IsInfinitesimal x) (r : ℂ) :
    binomialPower x hx (-r) = (binomialPower x hx r)⁻¹ := by
  apply mul_left_cancel₀ (binomialPower_ne_zero x hx r)
  rw [← binomialPower_add, _root_.add_neg_cancel, binomialPower_zero,
    mul_inv_cancel₀ (binomialPower_ne_zero x hx r)]

/-- The reciprocal positive-integer exponent supplies a root of the actual perturbation. -/
theorem binomialPower_rat_root (x : Surcomplex.{u}) (hx : IsInfinitesimal x)
    (m : ℕ) (hm : m ≠ 0) : binomialPower x hx (1 / (m : ℂ)) ^ m = 1 + x := by
  rw [binomialPower_pow, mul_one_div_cancel (Nat.cast_ne_zero.mpr hm), binomialPower_one]

theorem binomialPower_half_sq (x : Surcomplex.{u}) (hx : IsInfinitesimal x) :
    binomialPower x hx (1 / 2 : ℂ) ^ 2 = 1 + x :=
  binomialPower_rat_root x hx 2 (by decide)

section Workspace

variable {Γ : Type v} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Small.{u} Γ]

/-- Binomial values agree with their evaluation in every small complex Hahn workspace. -/
theorem binomialPower_hahnEmbedding (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (y : _root_.HahnSeries Γ ℂ) (hy : 0 < y.orderTop) (r : ℂ) :
    binomialPower (hahnEmbedding e he y) ((isInfinitesimal_hahnEmbedding_iff e he y).mpr hy) r =
      hahnEmbedding e he (Surreal.HahnSeries.binomialPower y hy r) :=
  powerSeriesEvaluation_hahnEmbedding e he y hy _

end Workspace

/-- Positive natural powers are injective on all actual values infinitesimally close to one. -/
theorem pow_injective_near_one (m : ℕ) (hm : m ≠ 0) :
    Set.InjOn (fun y : Surcomplex.{u} => y ^ m) {y | IsInfinitesimal (y - 1)} := by
  intro y hy z hz hpow
  change IsInfinitesimal (y - 1) at hy
  change IsInfinitesimal (z - 1) at hz
  let F : Bool → Surcomplex.{u} := fun b => cond b z y
  let Γ := familyWorkspaceExponents F
  let e : Γ →+ SignSequence.{u} := Γ.subtype.toAddMonoidHom
  have he : StrictMono e := fun _ _ h => h
  let Y := familyHahnPreimage F false
  let Z := familyHahnPreimage F true
  have hY : hahnEmbedding e he Y = y := familyWorkspaceEmbedding_preimage F false
  have hZ : hahnEmbedding e he Z = z := familyWorkspaceEmbedding_preimage F true
  have hYo : 0 < (Y - 1).orderTop := by
    apply (isInfinitesimal_hahnEmbedding_iff e he (Y - 1)).mp
    simpa only [map_sub, map_one, hY] using hy
  have hZo : 0 < (Z - 1).orderTop := by
    apply (isInfinitesimal_hahnEmbedding_iff e he (Z - 1)).mp
    simpa only [map_sub, map_one, hZ] using hz
  have hp : Y ^ m = Z ^ m := by
    apply hahnEmbedding_injective e he
    simpa only [map_pow, hY, hZ] using hpow
  have hYZ := Surreal.HahnSeries.pow_injective_near_one m hm hYo hZo hp
  exact hY.symm.trans ((congrArg (hahnEmbedding e he) hYZ).trans hZ)

/-- The binomial root is the unique actual root infinitesimally close to one. -/
theorem binomialPower_rat_root_unique (x : Surcomplex.{u}) (hx : IsInfinitesimal x)
    (m : ℕ) (hm : m ≠ 0) (y : Surcomplex.{u}) (hy : IsInfinitesimal (y - 1))
    (hpow : y ^ m = 1 + x) : y = binomialPower x hx (1 / (m : ℂ)) :=
  pow_injective_near_one m hm hy (isInfinitesimal_binomialPower_sub_one x hx _)
    (hpow.trans (binomialPower_rat_root x hx m hm).symm)

theorem exists_unique_root_near_one (x : Surcomplex.{u}) (hx : IsInfinitesimal x)
    (m : ℕ) (hm : m ≠ 0) :
    ∃! y : Surcomplex.{u}, y ^ m = 1 + x ∧ IsInfinitesimal (y - 1) := by
  refine ⟨binomialPower x hx (1 / (m : ℂ)),
    ⟨binomialPower_rat_root x hx m hm, isInfinitesimal_binomialPower_sub_one x hx _⟩, ?_⟩
  intro y hy
  exact binomialPower_rat_root_unique x hx m hm y hy.2 hy.1

end

end Surreal.Surcomplex
