import GowersSzemeredi.Proofs16SlabCommonBaseGeometry
import GowersSzemeredi.Proofs16SpectrumInduction
import GowersSzemeredi.Proofs16GlobalFiniteCover

/-! The actual Section 16 spectrum of a slab is independent of the cube
sidelength. It is one fixed finite set, with the existing Parseval budget. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem section16_slab_cube_fibre_card {N k : Nat} [NeZero N]
    (A : Finset (ZMod N)) (h : Point N k) (x : ZMod N) :
    ((section16CubeMultifunctionDomain (lastProductSet Finset.univ A) h).fibre x).card =
      if x ∈ A then N ^ k else 0 := by
  classical
  rw [section16_cube_fibre_card]
  simp only [lastProductSet, Finset.mem_filter, Finset.mem_univ, true_and,
    section16Last_appendCoordinate]
  by_cases hx : x ∈ A <;> simp [hx, countWhere, Point, ZMod.card]

theorem section16_slab_cube_correlation {N k : Nat} [NeZero N]
    (A : Finset (ZMod N)) (h : Point N k) :
    higherCubeCorrelation
      (section16PointIndicator (lastProductSet Finset.univ A)) h =
      fun x => (N : Complex) ^ k * indicator A x := by
  classical
  rw [section16_cube_correlation_eq_fibreCount]
  funext x
  rw [domainFibreCountFunction, section16_slab_cube_fibre_card]
  by_cases hx : x ∈ A <;> simp [hx, indicator]

theorem section16_slab_large_spectrum_eq {N k : Nat} [NeZero N]
    (A : Finset (ZMod N)) (h h' : Point N k) (delta : Real) :
    section16LargeSpectrum (lastProductSet Finset.univ A) h delta =
      section16LargeSpectrum (lastProductSet Finset.univ A) h' delta := by
  simp only [section16LargeSpectrum, section16_slab_cube_correlation]

theorem section16_slab_spectrum_relation {N k : Nat} [NeZero N]
    (A : Finset (ZMod N)) (delta : Real) :
    section16SpectrumRelation (lastProductSet (Finset.univ : Finset (Point N k)) A) delta =
      Finset.univ ×ˢ section16LargeSpectrum (lastProductSet Finset.univ A) (0 : Point N k) delta := by
  classical
  ext z
  simp only [section16SpectrumRelation, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_product]
  rw [section16_slab_large_spectrum_eq A z.1 0 delta]

/-- One finite frequency set covers every sidelength, without invoking the
preceding-dimensional structural theorem. This is a cardinality statement;
the required multiply-linear cover still needs its parameter comparison. -/
theorem section16_slab_spectrum_global_values {N k : Nat} [NeZero N]
    (A : Finset (ZMod N)) {delta : Real} (hd : 0 < delta) :
    ∃ K : Finset (ZMod N), (K.card : Real) ≤ delta ^ (-(2 : Int)) ∧
      section16SpectrumRelation (lastProductSet (Finset.univ : Finset (Point N k)) A) delta =
        Finset.univ ×ˢ K := by
  exact ⟨section16LargeSpectrum (lastProductSet Finset.univ A) (0 : Point N k) delta,
    section16_large_spectrum_card _ _ hd, section16_slab_spectrum_relation A delta⟩

/-- The entire slab spectrum satisfies the exact common-base cover budget;
no restriction of the sidelength set or structural induction is needed. -/
theorem section16_slab_spectrum_multiplyLinear {N k : Nat} [NeZero N]
    (A : Finset (ZMod N)) {delta theta1 : Real}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (ht : 0 < theta1) (ht1 : theta1 ≤ 1) :
    MultiplyLinear delta (section16T delta theta1 k)
      (section16SpectrumRelation (lastProductSet (Finset.univ : Finset (Point N k)) A) delta) := by
  classical
  obtain ⟨K, hK, heq⟩ := section16_slab_spectrum_global_values (k := k) A hd
  have hS : 1 ≤ multipleS (theta1 / 8) delta k :=
    one_le_multipleS k (by positivity) (by linarith) hd hd1
  have hbudget : delta ^ (-(2 : Int)) ≤ section16T delta theta1 k := by
    unfold section16T
    exact le_mul_of_one_le_right (by positivity) hS
  apply multiplyLinear_of_global_values _ K ?_ hd hd1
    (section16T_one_le k hd hd1 ht ht1) (hK.trans hbudget)
  intro z hz
  rw [heq] at hz
  exact (Finset.mem_product.mp hz).2

end LeanProofs.GowersSzemeredi
