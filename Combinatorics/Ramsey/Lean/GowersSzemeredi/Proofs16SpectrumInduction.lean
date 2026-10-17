import GowersSzemeredi.Proofs16CubeDensity
import GowersSzemeredi.Proofs14Product
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Nat.Dist
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.RingTheory.Coprime.Lemmas

/-! The large-spectrum relation satisfies the size and product-property
inputs of the preceding-dimensional Theorem 16.2, uniformly in the domain.

`Theorem162At.restrict_spectrum` is in `Proofs16SpectrumInductionSide`, outside
the final route. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem section16_large_spectrum_card {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (h : Point N k) {delta : Real} (hd : 0 < delta) :
    ((section16LargeSpectrum B h delta).card : Real) ≤ delta ^ (-(2 : Int)) := by
  let f := higherCubeCorrelation (section16PointIndicator B) h
  let K := section16LargeSpectrum B h delta
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hf (x : ZMod N) : ‖f x‖ ≤ (N : Real) ^ k := by
    dsimp only [f]
    rw [section16_cube_correlation_eq_fibreCount]
    simp only [domainFibreCountFunction, Complex.norm_natCast]
    have hc := countWhere_le_card (fun y : Point N k =>
      ∀ e, appendCoordinate (AxisCube.vertex (y, h) e) x ∈ B)
    rw [section16_cube_fibre_card]
    exact_mod_cast (by simpa [Point, ZMod.card] using hc)
  have hl : (K.card : Real) * (delta * (N : Real) ^ (k + 1)) ^ 2 ≤
      ∑ r : ZMod N, ‖fourier f r‖ ^ 2 := by
    calc
      _ = ∑ _r ∈ K, (delta * (N : Real) ^ (k + 1)) ^ 2 := by simp
      _ ≤ ∑ r ∈ K, ‖fourier f r‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro r hr
        exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr ((Finset.mem_filter.mp hr).2)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => sq_nonneg _)
  have hu : (∑ r : ZMod N, ‖fourier f r‖ ^ 2) ≤ ((N : Real) ^ (k + 1)) ^ 2 := by
    rw [identity_2_3_holds]
    calc
      _ ≤ (N : Real) * ∑ _x : ZMod N, ((N : Real) ^ k) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hN.le
        exact Finset.sum_le_sum (fun x _ =>
          (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hf x))
      _ = _ := by simp [pow_succ]; ring
  have hb : (K.card : Real) * delta ^ 2 ≤ 1 := by
    apply (mul_le_mul_iff_left₀ (show 0 < ((N : Real) ^ (k + 1)) ^ 2 by positivity)).mp
    calc
      _ = (K.card : Real) * (delta * (N : Real) ^ (k + 1)) ^ 2 := by ring
      _ ≤ ((N : Real) ^ (k + 1)) ^ 2 := hl.trans hu
      _ = _ := by ring
  rw [zpow_neg, zpow_ofNat]
  simpa only [one_div] using (le_div_iff₀ (sq_pos_of_pos hd)).mpr hb

theorem section16_spectrum_relation_card {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) {delta : Real} (hd : 0 < delta) :
    ((section16SpectrumRelation B delta).card : Real) ≤
      delta ^ (-(2 : Int)) * (N : Real) ^ k := by
  have hc : (section16SpectrumRelation B delta).card =
      ∑ h : Point N k, (section16LargeSpectrum B h delta).card := by
    simp only [section16SpectrumRelation, Finset.card_eq_sum_ones, Finset.sum_filter,
      Fintype.sum_prod_type]
    simp
  rw [hc, Nat.cast_sum]
  calc
    _ ≤ ∑ _h : Point N k, delta ^ (-(2 : Int)) :=
      Finset.sum_le_sum (fun h _ => section16_large_spectrum_card B h hd)
    _ = _ := by simp [Point, ZMod.card, mul_comm]

theorem section16_spectrum_relation_product {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) {delta : Real} (hd : 0 < delta) :
    RelationProductProperty delta (section16SpectrumRelation B delta) := by
  intro C phi hgraph
  apply lemma_14_3_holds N k delta (section16PointIndicator B) C phi hd
    (fun x => by simp only [section16PointIndicator]; split_ifs <;> simp)
  intro h hh
  have hm := hgraph h hh
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hm).2).2

end LeanProofs.GowersSzemeredi
