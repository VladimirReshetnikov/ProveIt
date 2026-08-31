import FabiusFunction.GeometricUniformLaw
import Mathlib.MeasureTheory.Group.Convolution

/-!
# The fixed dyadic two-section law

At the normalized geometric ratios `1 / 2` and `1 / 4`, separating the
uniform coordinates into their even and odd subsequences gives the exact
pointwise decomposition

`Y_(1/2) = (2 / 3) Y_(1/4)^even + (1 / 3) Y_(1/4)^odd`.

The two reindexed coordinate processes are independent copies of the original
product process.  Consequently the same identity holds as a product-map law,
and hence as a convolution of the two scaled quarter-ratio laws.  This file
only treats this fixed normalized two-section identity; it does not assert a
general ratio or general multisection theorem.
-/

open Filter Set MeasureTheory ProbabilityTheory Topology
open scoped BigOperators unitInterval

namespace Fabius
namespace ProbabilityRepresentation

set_option autoImplicit false
noncomputable section

/-! ## Even and odd coordinate processes -/

/-- The subsequence of the even-numbered uniform coordinates. -/
def evenCoordinates (omega : SampleSpace) : SampleSpace :=
  fun n => omega (2 * n)

/-- The subsequence of the odd-numbered uniform coordinates. -/
def oddCoordinates (omega : SampleSpace) : SampleSpace :=
  fun n => omega (2 * n + 1)

private lemma measurable_evenCoordinates : Measurable evenCoordinates := by
  exact measurable_pi_lambda _ fun n => measurable_pi_apply (2 * n)

private lemma measurable_oddCoordinates : Measurable oddCoordinates := by
  exact measurable_pi_lambda _ fun n => measurable_pi_apply (2 * n + 1)

private lemma uniformProduct_map_evenCoordinates :
    uniformProduct.map evenCoordinates = uniformProduct := by
  change
    (Measure.infinitePi
      (fun _ : Nat => (volume : Measure (Set.Icc (0 : Real) 1)))).map
        (fun omega n => omega (2 * n)) =
      Measure.infinitePi
        (fun _ : Nat => (volume : Measure (Set.Icc (0 : Real) 1)))
  rw [Measure.map_infinitePi_infinitePi_of_inj
    (mul_right_injective₀ (by omega : (2 : Nat) ≠ 0))]

private lemma uniformProduct_map_oddCoordinates :
    uniformProduct.map oddCoordinates = uniformProduct := by
  change
    (Measure.infinitePi
      (fun _ : Nat => (volume : Measure (Set.Icc (0 : Real) 1)))).map
        (fun omega n => omega (2 * n + 1)) =
      Measure.infinitePi
        (fun _ : Nat => (volume : Measure (Set.Icc (0 : Real) 1)))
  have hinj : Function.Injective (fun n : Nat => 2 * n + 1) := by
    intro m n hmn
    exact Nat.mul_left_cancel (by omega : 0 < 2) (Nat.add_right_cancel hmn)
  rw [Measure.map_infinitePi_infinitePi_of_inj hinj]

private lemma independent_even_odd_coordinates :
    IndepFun evenCoordinates oddCoordinates uniformProduct := by
  change IndepFun
    (fun omega n => omega (2 * n))
    (fun omega n => omega (2 * n + 1)) uniformProduct
  apply IndepFun.process_indepFun_process
    (fun n => measurable_pi_apply (2 * n))
    (fun n => measurable_pi_apply (2 * n + 1))
  intro s t
  let se : Finset Nat := s.image fun n => 2 * n
  let so : Finset Nat := t.image fun n => 2 * n + 1
  have hdisj : Disjoint se so := by
    rw [Finset.disjoint_left]
    intro n hnse hnso
    rcases Finset.mem_image.mp hnse with ⟨i, _hi, hin⟩
    rcases Finset.mem_image.mp hnso with ⟨j, _hj, hjn⟩
    omega
  have hfin := iIndepFun.indepFun_finset se so hdisj
    independent_uniform_coordinates (fun n => measurable_pi_apply n)
  let reindexEven :
      ((i : se) → Set.Icc (0 : Real) 1) →
        ((i : s) → Set.Icc (0 : Real) 1) :=
    fun z i => z ⟨2 * i, Finset.mem_image.mpr ⟨i, i.property, rfl⟩⟩
  let reindexOdd :
      ((i : so) → Set.Icc (0 : Real) 1) →
        ((i : t) → Set.Icc (0 : Real) 1) :=
    fun z i => z ⟨2 * i + 1, Finset.mem_image.mpr ⟨i, i.property, rfl⟩⟩
  have hcomp := hfin.comp
    (by fun_prop : Measurable reindexEven)
    (by fun_prop : Measurable reindexOdd)
  simpa only [Function.comp_def, reindexEven, reindexOdd, se, so] using hcomp

private lemma uniformProduct_map_even_oddCoordinates :
    uniformProduct.map (fun omega : SampleSpace =>
      (evenCoordinates omega, oddCoordinates omega)) =
        uniformProduct.prod uniformProduct := by
  have h := independent_even_odd_coordinates.map_prod_eq_prod_map_map
    measurable_evenCoordinates.aemeasurable
    measurable_oddCoordinates.aemeasurable
  rwa [uniformProduct_map_evenCoordinates,
    uniformProduct_map_oddCoordinates] at h

/-! ## The fixed two-section identity -/

/-- Splitting a normalized ratio-`1 / 2` geometric uniform series into its
even and odd coordinates gives two scaled normalized ratio-`1 / 4` series. -/
theorem geometricUniformSeries_one_half_multisection (omega : SampleSpace) :
    geometricUniformSeries (1 / 2 : Real) omega =
      (2 / 3 : Real) *
          geometricUniformSeries (1 / 4 : Real) (evenCoordinates omega) +
        (1 / 3 : Real) *
          geometricUniformSeries (1 / 4 : Real) (oddCoordinates omega) := by
  let f : Nat → Real := fun n =>
    (omega n : Real) • geometricUniformWeight (1 / 2 : Real) n
  have hs : Summable f := by
    simpa only [f] using
      (summable_weightedUniformSeries_terms
        (summable_norm_geometricUniformWeight
          (by norm_num : |(1 / 2 : Real)| < 1)) omega)
  have heven : Summable (fun n : Nat => f (2 * n)) :=
    hs.comp_injective
      (mul_right_injective₀ (by omega : (2 : Nat) ≠ 0))
  have hodd : Summable (fun n : Nat => f (2 * n + 1)) :=
    hs.comp_injective ((add_left_injective 1).comp
      (mul_right_injective₀ (by omega : (2 : Nat) ≠ 0)))
  have heven_term (n : Nat) :
      f (2 * n) =
        (2 / 3 : Real) *
          ((evenCoordinates omega n : Real) •
            geometricUniformWeight (1 / 4 : Real) n) := by
    simp only [f, evenCoordinates, geometricUniformWeight, smul_eq_mul]
    rw [pow_mul]
    norm_num
    ring
  have hodd_term (n : Nat) :
      f (2 * n + 1) =
        (1 / 3 : Real) *
          ((oddCoordinates omega n : Real) •
            geometricUniformWeight (1 / 4 : Real) n) := by
    simp only [f, oddCoordinates, geometricUniformWeight, smul_eq_mul]
    rw [pow_succ, pow_mul]
    norm_num
    ring
  calc
    geometricUniformSeries (1 / 2 : Real) omega = ∑' n : Nat, f n := rfl
    _ = (∑' n : Nat, f (2 * n)) + ∑' n : Nat, f (2 * n + 1) :=
      (tsum_even_add_odd heven hodd).symm
    _ = (∑' n : Nat, (2 / 3 : Real) *
          ((evenCoordinates omega n : Real) •
            geometricUniformWeight (1 / 4 : Real) n)) +
        ∑' n : Nat, (1 / 3 : Real) *
          ((oddCoordinates omega n : Real) •
            geometricUniformWeight (1 / 4 : Real) n) := by
      rw [tsum_congr heven_term, tsum_congr hodd_term]
    _ = (2 / 3 : Real) *
          geometricUniformSeries (1 / 4 : Real) (evenCoordinates omega) +
        (1 / 3 : Real) *
          geometricUniformSeries (1 / 4 : Real) (oddCoordinates omega) := by
      rw [tsum_mul_left, tsum_mul_left]
      rfl

/-- The normalized ratio-`1 / 2` law is the image of two independent copies
of the normalized ratio-`1 / 4` law under the fixed affine sum map. -/
theorem geometricUniformDistribution_one_half_multisection :
    geometricUniformDistribution (1 / 2 : Real) =
      ((geometricUniformDistribution (1 / 4 : Real)).prod
        (geometricUniformDistribution (1 / 4 : Real))).map
          (fun p => (2 / 3 : Real) * p.1 + (1 / 3 : Real) * p.2) := by
  have hquarter : Measurable (geometricUniformSeries (1 / 4 : Real)) :=
    measurable_geometricUniformSeries
      (by norm_num : |(1 / 4 : Real)| < 1)
  have hjoint :
      uniformProduct.map (fun omega : SampleSpace =>
        (geometricUniformSeries (1 / 4 : Real) (evenCoordinates omega),
          geometricUniformSeries (1 / 4 : Real) (oddCoordinates omega))) =
        (geometricUniformDistribution (1 / 4 : Real)).prod
          (geometricUniformDistribution (1 / 4 : Real)) := by
    calc
      uniformProduct.map (fun omega : SampleSpace =>
          (geometricUniformSeries (1 / 4 : Real) (evenCoordinates omega),
            geometricUniformSeries (1 / 4 : Real) (oddCoordinates omega))) =
          (uniformProduct.map (fun omega : SampleSpace =>
            (evenCoordinates omega, oddCoordinates omega))).map
              (Prod.map (geometricUniformSeries (1 / 4 : Real))
                (geometricUniformSeries (1 / 4 : Real))) := by
        rw [Measure.map_map (hquarter.prodMap hquarter)
          (measurable_evenCoordinates.prodMk measurable_oddCoordinates)]
        rfl
      _ = (uniformProduct.prod uniformProduct).map
            (Prod.map (geometricUniformSeries (1 / 4 : Real))
              (geometricUniformSeries (1 / 4 : Real))) := by
        rw [uniformProduct_map_even_oddCoordinates]
      _ = (geometricUniformDistribution (1 / 4 : Real)).prod
            (geometricUniformDistribution (1 / 4 : Real)) := by
        rw [← Measure.map_prod_map uniformProduct uniformProduct hquarter hquarter]
        rfl
  change uniformProduct.map (geometricUniformSeries (1 / 2 : Real)) = _
  let pair : SampleSpace → Real × Real := fun omega =>
    (geometricUniformSeries (1 / 4 : Real) (evenCoordinates omega),
      geometricUniformSeries (1 / 4 : Real) (oddCoordinates omega))
  let combine : Real × Real → Real := fun p =>
    (2 / 3 : Real) * p.1 + (1 / 3 : Real) * p.2
  have hpair : Measurable pair :=
    (hquarter.comp measurable_evenCoordinates).prodMk
      (hquarter.comp measurable_oddCoordinates)
  calc
    uniformProduct.map (geometricUniformSeries (1 / 2 : Real)) =
        uniformProduct.map (combine ∘ pair) := by
      apply Measure.map_congr
      filter_upwards with omega
      exact geometricUniformSeries_one_half_multisection omega
    _ = (uniformProduct.map pair).map combine := by
      simpa only using
        (Measure.map_map (μ := uniformProduct) (f := pair) (g := combine)
          (by fun_prop) hpair).symm
    _ = _ := by
      rw [show uniformProduct.map pair =
          (geometricUniformDistribution (1 / 4 : Real)).prod
            (geometricUniformDistribution (1 / 4 : Real)) by
        simpa only [pair] using hjoint]

/-- Equivalently, the normalized ratio-`1 / 2` law is the convolution of the
`2 / 3` and `1 / 3` pushforwards of the normalized ratio-`1 / 4` law. -/
theorem geometricUniformDistribution_one_half_conv_one_quarter :
    geometricUniformDistribution (1 / 2 : Real) =
      (geometricUniformDistribution (1 / 4 : Real)).map
          (fun x => (2 / 3 : Real) * x) ∗
        (geometricUniformDistribution (1 / 4 : Real)).map
          (fun x => (1 / 3 : Real) * x) := by
  letI : IsProbabilityMeasure
      (geometricUniformDistribution (1 / 4 : Real)) :=
    geometricUniformDistribution_isProbabilityMeasure
      (by norm_num : |(1 / 4 : Real)| < 1)
  rw [geometricUniformDistribution_one_half_multisection]
  unfold Measure.conv
  rw [Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

end

end ProbabilityRepresentation
end Fabius
