import GowersSzemeredi.Proofs16AllScaleCoverTransfer
import GowersSzemeredi.Proofs16SinglePieceGlobal
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.Degree.Monomial
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Data.Finset.DenselyOrdered
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Factorial.NatCast
import Mathlib.GroupTheory.CosetCover
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic

/-! Power lower bounds for the single-piece width pipeline.

The scale conditions of the single-piece route ask that certain nested
widths exceed fixed targets. Every width in the pipeline is a power of the
input above an explicit threshold:
* `coverWidth E t L = ⌈L^E⌉` is at least `L^E`;
* one unused-coordinate step `liftLastW w t L = √(w(t/2)⌈L/8⌉ − 1) − 1` turns
  `L^a` into `L^(a/4)`, above `max(8L₀ + 8, 6^(4/a))`.

The thresholds are `exp(O(1/a))`, so their logarithms are polynomial in
`1/a`, which is what the final budget needs.
* `WidthPowerLB`, `coverWidth_powerLB`, `liftLastW_powerLB`,
  `WidthPowerLB.min`, `WidthPowerLB.mono_exponent`.

The 14 declarations of this module that the final route does not use are in
`Proofs18WidthPowerBoundsSide`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Pointwise power lower bounds compose by multiplying their exponents. -/
theorem rpow_le_comp {x y z a b : Real} (hx : 0 ≤ x) (hb : 0 ≤ b)
    (hxy : x ^ a ≤ y) (hyz : y ^ b ≤ z) : x ^ (a * b) ≤ z := by
  rw [Real.rpow_mul hx]
  exact (Real.rpow_le_rpow (Real.rpow_nonneg hx _) hxy hb).trans hyz

/-- `w L ≥ L^a` for every `L ≥ L₀`. -/
def WidthPowerLB (w : Nat → Nat) (a L0 : Real) : Prop :=
  ∀ L : Nat, L0 ≤ L → (L : Real) ^ a ≤ w L

theorem coverWidth_powerLB (E : Real → Real) (t : Real) (hE : 0 ≤ E (t / 2)) :
    WidthPowerLB (coverWidth E t) (E (t / 2)) 0 := by
  intro L _
  unfold coverWidth
  rw [max_eq_right hE]
  exact Nat.le_ceil _

/-- The key estimate: `√(n − 1) − 1 ≥ x` when `n ≥ x⁴/8` and `x ≥ 6`. -/
theorem nat_sqrt_pred_pred_ge {n : Nat} {x : Real} (hx : 6 ≤ x)
    (hn : x ^ 4 / 8 ≤ n) : x ≤ ((Nat.sqrt (n - 1) - 1 : Nat) : Real) := by
  set k := ⌈x⌉₊
  have hxk : x ≤ k := Nat.le_ceil x
  have hk2 : (k : Real) ≤ x + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hx2 : 36 ≤ x ^ 2 := by nlinarith
  have hx4' : 36 * x ^ 2 ≤ x ^ 4 := by nlinarith
  have hn1 : 1 ≤ n := by
    have : (1 : Real) ≤ n := by nlinarith
    exact_mod_cast this
  have hsq : (k + 1) ^ 2 ≤ n - 1 := by
    have hreal : ((k + 1 : Nat) : Real) ^ 2 ≤ (n : Real) - 1 := by
      push_cast
      have hk0 : (0 : Real) ≤ (k : Real) + 1 := by positivity
      have hkx : ((k : Real) + 1) ^ 2 ≤ (x + 2) ^ 2 :=
        pow_le_pow_left₀ hk0 (by linarith) 2
      nlinarith
    have : ((k + 1) ^ 2 : Nat) ≤ ((n - 1 : Nat) : Real) := by
      push_cast [Nat.cast_sub hn1]
      exact_mod_cast hreal
    exact_mod_cast this
  have hroot : k + 1 ≤ Nat.sqrt (n - 1) := Nat.le_sqrt.mpr (by nlinarith [hsq])
  have hfinal : k ≤ Nat.sqrt (n - 1) - 1 := by omega
  exact hxk.trans (by exact_mod_cast hfinal)

/-- A power lower bound for the slice width survives the square-root localization.
The same bound also supplies the elementary size condition `2 ≤ L`. -/
theorem localization_width_bounds {x f : Real} {L : Nat} (hx : 1 ≤ x) (hf : 0 ≤ f)
    (h6 : 6 ≤ x ^ (f / 8)) (hL : x ^ f ≤ L) :
    2 ≤ L ∧ x ^ (f / 8) ≤ ((Nat.sqrt (L - 1) - 1 : Nat) : Real) := by
  have hfull : x ^ (f / 8) ≤ x ^ f :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  refine ⟨by exact_mod_cast (show (2 : Real) ≤ L by linarith), ?_⟩
  apply nat_sqrt_pred_pred_ge h6
  have hpow4 : (x ^ (f / 8)) ^ 4 = x ^ (f / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans hx)]
    congr 1
    norm_num
    ring
  rw [hpow4]
  exact ((div_le_self (Real.rpow_nonneg (zero_le_one.trans hx) _) (by norm_num)).trans
    (Real.rpow_le_rpow_of_exponent_le hx (by linarith))).trans hL

/-- **Composition**: powers multiply above the pulled-back threshold. -/
theorem WidthPowerLB.comp {w v : Nat → Nat} {a b L0 L1 : Real}
    (hw : WidthPowerLB w a L0) (hv : WidthPowerLB v b L1) (ha : 0 < a) (hb : 0 ≤ b)
    (hL0 : 1 ≤ L0) (hL1 : 0 ≤ L1) :
    WidthPowerLB (fun L => v (w L)) (a * b) (max L0 (L1 ^ (1 / a))) := by
  intro L hL
  have hL0' : L0 ≤ L := (le_max_left _ _).trans hL
  have hL1' : L1 ^ (1 / a) ≤ L := (le_max_right _ _).trans hL
  have hLpos : (0 : Real) ≤ L := by linarith
  have hwL := hw L hL0'
  have hLa : L1 ≤ (L : Real) ^ a := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hL1 _) hL1' ha.le
    rwa [← Real.rpow_mul hL1, show 1 / a * a = 1 by field_simp, Real.rpow_one] at h
  have hvw := hv (w L) (hLa.trans hwL)
  exact rpow_le_comp hLpos hb hwL hvw

end LeanProofs.GowersSzemeredi
