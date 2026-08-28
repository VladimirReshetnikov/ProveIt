import FabiusFunction.IntegerZeroLocalFactorization
import FabiusFunction.Existence
import FabiusFunction.LeadingJet
import Mathlib.Analysis.Analytic.Order

/-!
# Complex analytic order of the integer zeros

The denominator-cleared identities in `IntegerZeroLocalFactorization` expose
the local power of the zero without using division.  This module packages the
remaining analytic layer.  It first transfers entire-ness from the Fourier
transform of an existing Fabius solution to the standalone sinc product.  It
then divides by the nonvanishing center denominator, producing an analytic
local cofactor whose value at zero is nonzero because the canonical odd tail
is evaluated at a half-integer.

Consequently every nonzero integer `m` is a complex zero of exact analytic
order `padicValNat 2 m.natAbs + 1`.  The lower complex derivatives vanish and
the derivative at that order is nonzero.

* `rvachevFourierProduct_differentiable` — the standalone sinc product is
  entire.
* `rvachevFourierProduct_nat_div_two_ne_zero_of_odd` — an odd half-integer is
  not a zero of the product.
* `integerZeroLocalCofactor` — the total local quotient used near a nonzero
  integer center.
* `rvachevFourierProduct_int_add_eq_pow_mul_cofactor` — the divided local
  factorization away from its removable denominator.
* `rvachevFourierProduct_int_add_eventuallyEq_pow_mul_cofactor` — the same
  factorization as an equality of germs at the local origin.
* `rvachevFourierProduct_int_eventuallyEq_sub_pow_mul_cofactor` — the centered
  germ in the original complex coordinate.
* `integerZeroLocalCofactor_analyticAt_of_add_ne`,
  `integerZeroLocalCofactor_analyticAt`, and
  `integerZeroLocalCofactor_zero` — analyticity and its exact central value.
* `integerZeroLocalCofactor_zero_ne` — the cofactor is a local analytic unit.
* `analyticOrderAt_rvachevFourierProduct_int` — the exact complex zero order.
* `iteratedDeriv_rvachevFourierProduct_int_eq_zero_of_lt` and
  `iteratedDeriv_rvachevFourierProduct_int_add_order` — the lower-jet
  vanishing and every higher jet in terms of the analytic cofactor.
* `iteratedDeriv_rvachevFourierProduct_int` — the exact first nonzero
  derivative; the nonvanishing theorem is retained as a convenience
  corollary.
-/

set_option autoImplicit false

open scoped BigOperators
open Filter Finset Topology

namespace Fabius

noncomputable section

/-- The standalone Rvachev sinc product is entire.  This is transferred from
the already-proved entire Fourier transform of any Fabius solution, whose
existence is supplied by `existsUnique_fabius`. -/
theorem rvachevFourierProduct_differentiable :
    Differentiable ℂ rvachevFourierProduct := by
  obtain ⟨F, hF, _⟩ := existsUnique_fabius
  have heq : rvachevFourier F = rvachevFourierProduct := by
    funext z
    exact rvachevFourier_eq_product F hF z
  rw [← heq]
  exact rvachevFourier_differentiable_analytic F hF

/-- The sinc product does not vanish at a positive half-integer with odd
numerator. -/
theorem rvachevFourierProduct_nat_div_two_ne_zero_of_odd
    {q : ℕ} (hq : Odd q) :
    rvachevFourierProduct ((q : ℂ) / 2) ≠ 0 := by
  intro hzero
  rcases (rvachevFourierProduct_eq_zero_iff ((q : ℂ) / 2)).mp hzero with
    ⟨r, _, heq⟩
  have heqC : (q : ℂ) = 2 * (r : ℂ) := by
    calc
      (q : ℂ) = 2 * ((q : ℂ) / 2) := by ring
      _ = 2 * (r : ℂ) := by rw [heq]
  have heqZ : (q : ℤ) = 2 * r := by
    exact_mod_cast heqC
  have hdvdZ : (2 : ℤ) ∣ (q : ℤ) := ⟨r, heqZ⟩
  have hdvdN : 2 ∣ q := by exact_mod_cast hdvdZ
  exact (Nat.not_even_iff_odd.mpr hq) (even_iff_two_dvd.mpr hdvdN)

/-- The analytic cofactor in the local coordinate at an integer center.

It is intentionally defined as a total quotient.  When `m ≠ 0`, its
denominator is nonzero near `w = 0`; the corresponding factorization theorem
below supplies the local equality with the sinc product. -/
noncomputable def integerZeroLocalCofactor (m : ℤ) (w : ℂ) : ℂ :=
  let d := padicValNat 2 m.natAbs + 1
  let q := Nat.divMaxPow m.natAbs 2
  (-(∏ h ∈ range d,
      complexSinc ((Real.pi : ℂ) * w / (2 : ℂ) ^ h)) *
      rvachevFourierProduct
        ((q : ℂ) / 2 + (Int.sign m : ℂ) * w / (2 : ℂ) ^ d)) /
    ((m : ℂ) + w) ^ d

/-- Away from the removable denominator `m + w = 0`, the total integer-center
identity is exactly `Φ(m+w) = w^d U_m(w)`. -/
theorem rvachevFourierProduct_int_add_eq_pow_mul_cofactor
    (m : ℤ) (hm : m ≠ 0) (w : ℂ) (hw : (m : ℂ) + w ≠ 0) :
    rvachevFourierProduct ((m : ℂ) + w) =
      w ^ (padicValNat 2 m.natAbs + 1) * integerZeroLocalCofactor m w := by
  let d := padicValNat 2 m.natAbs + 1
  let q := Nat.divMaxPow m.natAbs 2
  let P : ℂ := ∏ h ∈ range d,
    complexSinc ((Real.pi : ℂ) * w / (2 : ℂ) ^ h)
  let T : ℂ := rvachevFourierProduct
    ((q : ℂ) / 2 + (Int.sign m : ℂ) * w / (2 : ℂ) ^ d)
  have hfactor := rvachevFourierProduct_int_add_factorization m hm w
  change (((m : ℂ) + w) ^ d) *
      rvachevFourierProduct ((m : ℂ) + w) = -w ^ d * P * T at hfactor
  change rvachevFourierProduct ((m : ℂ) + w) =
    w ^ d * (-P * T / ((m : ℂ) + w) ^ d)
  have hden : ((m : ℂ) + w) ^ d ≠ 0 := pow_ne_zero d hw
  rw [show w ^ d * (-P * T / ((m : ℂ) + w) ^ d) =
      (w ^ d * (-P * T)) / ((m : ℂ) + w) ^ d by ring]
  apply (eq_div_iff hden).2
  calc
    rvachevFourierProduct ((m : ℂ) + w) * ((m : ℂ) + w) ^ d =
        ((m : ℂ) + w) ^ d *
          rvachevFourierProduct ((m : ℂ) + w) := by ring
    _ = -w ^ d * P * T := hfactor
    _ = w ^ d * (-P * T) := by ring

/-- The divided integer-center factorization holds throughout a whole
neighborhood of the local origin.  This is the reusable germ-level form:
the exceptional totalized denominator lies away from `w = 0`. -/
theorem rvachevFourierProduct_int_add_eventuallyEq_pow_mul_cofactor
    (m : ℤ) (hm : m ≠ 0) :
    (fun w : ℂ => rvachevFourierProduct ((m : ℂ) + w)) =ᶠ[nhds 0]
      fun w => w ^ (padicValNat 2 m.natAbs + 1) *
        integerZeroLocalCofactor m w := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hden : ∀ᶠ w : ℂ in nhds 0, (m : ℂ) + w ≠ 0 := by
    have hc : ContinuousAt (fun w : ℂ => (m : ℂ) + w) 0 := by fun_prop
    exact hc.eventually_ne (by simpa using hmC)
  exact hden.mono fun w hw =>
    rvachevFourierProduct_int_add_eq_pow_mul_cofactor m hm w hw

/-- **Centered integer-zero germ.**  In the original complex coordinate,
the sinc product is locally `(z-m)^d` times the translated analytic cofactor.
This is a reusable input for analytic order, all higher jets, and reciprocal
pole calculations. -/
theorem rvachevFourierProduct_int_eventuallyEq_sub_pow_mul_cofactor
    (m : ℤ) (hm : m ≠ 0) :
    rvachevFourierProduct =ᶠ[nhds (m : ℂ)]
      fun z => (z - (m : ℂ)) ^ (padicValNat 2 m.natAbs + 1) *
        integerZeroLocalCofactor m (z - (m : ℂ)) := by
  have hcoord : Tendsto (fun z : ℂ => z - (m : ℂ))
      (nhds (m : ℂ)) (nhds 0) := by
    have hcontinuous : ContinuousAt (fun z : ℂ => z - (m : ℂ)) (m : ℂ) :=
      continuousAt_id.sub continuousAt_const
    change Tendsto (fun z : ℂ => z - (m : ℂ))
      (nhds (m : ℂ)) (nhds ((m : ℂ) - (m : ℂ))) at hcontinuous
    simpa only [sub_self] using hcontinuous
  have hcomp :=
    (rvachevFourierProduct_int_add_eventuallyEq_pow_mul_cofactor m hm).comp_tendsto
      hcoord
  filter_upwards [hcomp] with z hz
  have hcenter : (m : ℂ) + (z - (m : ℂ)) = z := by ring
  simpa only [Function.comp_apply, hcenter] using hz

/-- The local cofactor is analytic away from the totalized denominator point
`w = -m`.  No parity or nonzero hypothesis
on the integer parameter is needed. -/
theorem integerZeroLocalCofactor_analyticAt_of_add_ne
    (m : ℤ) {w₀ : ℂ} (hden0 : (m : ℂ) + w₀ ≠ 0) :
    AnalyticAt ℂ (integerZeroLocalCofactor m) w₀ := by
  let d := padicValNat 2 m.natAbs + 1
  let q := Nat.divMaxPow m.natAbs 2
  have hprefix : AnalyticAt ℂ
      (fun w : ℂ => ∏ h ∈ range d,
        complexSinc ((Real.pi : ℂ) * w / (2 : ℂ) ^ h)) w₀ := by
    apply Finset.analyticAt_fun_prod
    intro h hh
    have hinner : AnalyticAt ℂ
        (fun w : ℂ => (Real.pi : ℂ) * w / (2 : ℂ) ^ h) w₀ := by
      fun_prop
    exact (complexSinc_differentiable.analyticAt _).comp hinner
  have htail : AnalyticAt ℂ
      (fun w : ℂ => rvachevFourierProduct
        ((q : ℂ) / 2 + (Int.sign m : ℂ) * w / (2 : ℂ) ^ d)) w₀ := by
    have hinner : AnalyticAt ℂ
        (fun w : ℂ =>
          (q : ℂ) / 2 + (Int.sign m : ℂ) * w / (2 : ℂ) ^ d) w₀ := by
      fun_prop
    exact (rvachevFourierProduct_differentiable.analyticAt _).comp hinner
  have hden : AnalyticAt ℂ (fun w : ℂ => ((m : ℂ) + w) ^ d) w₀ := by
    fun_prop
  have hdenPow : ((m : ℂ) + w₀) ^ d ≠ 0 := pow_ne_zero d hden0
  change AnalyticAt ℂ
    (fun w : ℂ =>
      (-(∏ h ∈ range d,
          complexSinc ((Real.pi : ℂ) * w / (2 : ℂ) ^ h)) *
        rvachevFourierProduct
          ((q : ℂ) / 2 + (Int.sign m : ℂ) * w / (2 : ℂ) ^ d)) /
        ((m : ℂ) + w) ^ d) w₀
  exact (hprefix.neg.mul htail).div hden hdenPow

/-- The local cofactor is analytic at the origin for every nonzero integer
center. -/
theorem integerZeroLocalCofactor_analyticAt (m : ℤ) (hm : m ≠ 0) :
    AnalyticAt ℂ (integerZeroLocalCofactor m) 0 := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  exact integerZeroLocalCofactor_analyticAt_of_add_ne m (by simpa using hmC)

/-- Exact value of the totalized cofactor at the integer center.  For
`m = 0` this is only a division-by-zero identity; its analytic-unit
interpretation begins with the nonzero-center theorem below. -/
theorem integerZeroLocalCofactor_zero (m : ℤ) :
    integerZeroLocalCofactor m 0 =
      -rvachevFourierProduct
          (((Nat.divMaxPow m.natAbs 2 : ℕ) : ℂ) / 2) /
        (m : ℂ) ^ (padicValNat 2 m.natAbs + 1) := by
  simp [integerZeroLocalCofactor, complexSinc]

/-- At a nonzero integer center the local analytic cofactor does not vanish
at zero. -/
theorem integerZeroLocalCofactor_zero_ne (m : ℤ) (hm : m ≠ 0) :
    integerZeroLocalCofactor m 0 ≠ 0 := by
  have habs : m.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hm
  have hodd : Odd (Nat.divMaxPow m.natAbs 2) :=
    Nat.not_even_iff_odd.mp
      (mt Even.two_dvd (Nat.not_dvd_divMaxPow (by norm_num) habs))
  have htail : rvachevFourierProduct
      (((Nat.divMaxPow m.natAbs 2 : ℕ) : ℂ) / 2) ≠ 0 :=
    rvachevFourierProduct_nat_div_two_ne_zero_of_odd hodd
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  rw [integerZeroLocalCofactor_zero]
  exact div_ne_zero (neg_ne_zero.mpr htail)
    (pow_ne_zero (padicValNat 2 m.natAbs + 1) hmC)

/-- **Exact complex zero order.**  Every nonzero integer `m` is a zero of the
standalone sinc product of analytic order `v₂(|m|)+1`. -/
theorem analyticOrderAt_rvachevFourierProduct_int
    (m : ℤ) (hm : m ≠ 0) :
    analyticOrderAt rvachevFourierProduct (m : ℂ) =
      padicValNat 2 m.natAbs + 1 := by
  let U : ℂ → ℂ := fun z => integerZeroLocalCofactor m (z - (m : ℂ))
  have hproduct : AnalyticAt ℂ rvachevFourierProduct (m : ℂ) :=
    rvachevFourierProduct_differentiable.analyticAt (m : ℂ)
  apply hproduct.analyticOrderAt_eq_natCast.mpr
  refine ⟨U, ?_, ?_, ?_⟩
  · have hinner : AnalyticAt ℂ (fun z : ℂ => z - (m : ℂ)) (m : ℂ) := by
      fun_prop
    simpa only [U] using
      (integerZeroLocalCofactor_analyticAt m hm).fun_comp_of_eq hinner (by ring)
  · simpa only [U, sub_self] using integerZeroLocalCofactor_zero_ne m hm
  · filter_upwards [
      rvachevFourierProduct_int_eventuallyEq_sub_pow_mul_cofactor m hm]
      with z hz
    simpa only [U, smul_eq_mul] using hz

/-- All complex derivatives below the exact integer-zero order vanish. -/
theorem iteratedDeriv_rvachevFourierProduct_int_eq_zero_of_lt
    (m : ℤ) (hm : m ≠ 0) {j : ℕ}
    (hj : j < padicValNat 2 m.natAbs + 1) :
    iteratedDeriv j rvachevFourierProduct (m : ℂ) = 0 := by
  have hjet :=
    (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
      (rvachevFourierProduct_differentiable.analyticAt (m : ℂ))).mp
      (analyticOrderAt_rvachevFourierProduct_int m hm)
  exact hjet.1 j hj

/-- **Every higher complex jet at an integer zero.**  If
`d = v₂(|m|)+1`, then the `(d+r)`-th derivative is the division-free
binomial-factorial multiple of the `r`-th derivative of the analytic local
cofactor.  The leading-jet formula below is the case `r = 0`. -/
theorem iteratedDeriv_rvachevFourierProduct_int_add_order
    (m : ℤ) (hm : m ≠ 0) (r : ℕ) :
    iteratedDeriv (padicValNat 2 m.natAbs + 1 + r)
        rvachevFourierProduct (m : ℂ) =
      ((padicValNat 2 m.natAbs + 1 + r).choose
          (padicValNat 2 m.natAbs + 1) : ℂ) *
        ((padicValNat 2 m.natAbs + 1).factorial : ℂ) *
          iteratedDeriv r (integerZeroLocalCofactor m) 0 := by
  let d := padicValNat 2 m.natAbs + 1
  change iteratedDeriv (d + r) rvachevFourierProduct (m : ℂ) =
    ((d + r).choose d : ℂ) * (d.factorial : ℂ) *
      iteratedDeriv r (integerZeroLocalCofactor m) 0
  have hfactor :
      (fun w : ℂ => rvachevFourierProduct ((m : ℂ) + w)) =ᶠ[nhds 0]
        fun w => w ^ d * integerZeroLocalCofactor m w := by
    simpa only [d] using
      rvachevFourierProduct_int_add_eventuallyEq_pow_mul_cofactor m hm
  have hlocal :=
    iteratedDeriv_eq_choose_factorial_mul_of_eventuallyEq_pow_mul
      d r hfactor (integerZeroLocalCofactor_analyticAt m hm).contDiffAt
  have hshift := congrFun
    (iteratedDeriv_comp_const_add (d + r) rvachevFourierProduct (m : ℂ))
    (0 : ℂ)
  calc
    iteratedDeriv (d + r) rvachevFourierProduct (m : ℂ) =
        iteratedDeriv (d + r)
          (fun w : ℂ => rvachevFourierProduct ((m : ℂ) + w)) 0 := by
      simpa only [add_zero] using hshift.symm
    _ = ((d + r).choose d : ℂ) * (d.factorial : ℂ) *
        iteratedDeriv r (integerZeroLocalCofactor m) 0 := hlocal

/-- **Exact leading complex jet.**  At every nonzero integer center, the
first nonzero derivative is the odd-tail value times the explicit factorial
and scale factor. -/
theorem iteratedDeriv_rvachevFourierProduct_int
    (m : ℤ) (hm : m ≠ 0) :
    iteratedDeriv (padicValNat 2 m.natAbs + 1)
        rvachevFourierProduct (m : ℂ) =
      -((padicValNat 2 m.natAbs + 1).factorial : ℂ) *
          rvachevFourierProduct
            (((Nat.divMaxPow m.natAbs 2 : ℕ) : ℂ) / 2) /
        (m : ℂ) ^ (padicValNat 2 m.natAbs + 1) := by
  let d := padicValNat 2 m.natAbs + 1
  let q := Nat.divMaxPow m.natAbs 2
  change iteratedDeriv d rvachevFourierProduct (m : ℂ) =
    -(d.factorial : ℂ) * rvachevFourierProduct ((q : ℂ) / 2) /
      (m : ℂ) ^ d
  calc
    iteratedDeriv d rvachevFourierProduct (m : ℂ) =
        (d.factorial : ℂ) * integerZeroLocalCofactor m 0 := by
      simpa only [d, add_zero, Nat.choose_self, Nat.cast_one, one_mul,
        iteratedDeriv_zero] using
        iteratedDeriv_rvachevFourierProduct_int_add_order m hm 0
    _ = -(d.factorial : ℂ) * rvachevFourierProduct ((q : ℂ) / 2) /
        (m : ℂ) ^ d := by
      rw [integerZeroLocalCofactor_zero]
      ring

/-- The complex derivative at the exact integer-zero order is nonzero. -/
theorem iteratedDeriv_rvachevFourierProduct_int_ne_zero
    (m : ℤ) (hm : m ≠ 0) :
    iteratedDeriv (padicValNat 2 m.natAbs + 1)
      rvachevFourierProduct (m : ℂ) ≠ 0 := by
  have hjet :=
    (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
      (rvachevFourierProduct_differentiable.analyticAt (m : ℂ))).mp
      (analyticOrderAt_rvachevFourierProduct_int m hm)
  exact hjet.2

end

end Fabius
