import Surreal.Algebra.IdealReconstructionFormulas
import Surreal.HahnSeries.MultiplierFormulas

/-!
# Native internal reconstruction from any ideal formula

The arbitrary-ideal-predicate extension following `odg:def:cor:internal`.
The graph is on two fraction pairs, and recovers the actual Hahn coefficient,
not an abstract isomorphic copy. All bound variables range over the full
coefficient pullback.
-/

namespace Surreal.HahnSeries
open _root_.HahnSeries FirstOrder FirstOrder.Language
noncomputable section

variable {Γ K O : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field K] [CommRing O]
variable (i : O →+* K)
local notation "A" => coefficientRestrictedSubring (Γ := Γ) i
local notation "ι" => coefficientRestrictedHahnInclusion (Γ := Γ) i

private theorem ideal_representative (x : K⟦Γ⟧) (hx : PurelyInfiniteSeries x) :
    ∃ y : A, ι y = x := ⟨purelyInfiniteRestricted i x hx, rfl⟩

section Predicate
variable (P : coefficientRestrictedSubring (Γ := Γ) i → Prop)
  (htest : ∀ x : coefficientRestrictedSubring (Γ := Γ) i,
    P x ↔ x.val ∈ purelyInfiniteIdeal (Γ := Γ) (R := K))
include P htest

private theorem predicate_ambient_test (x : A) : P x ↔ PurelyInfiniteSeries (ι x) := by
  change P x ↔ PurelyInfiniteSeries x.val.val
  rw [purelyInfiniteSeries_iff]
  exact htest x

/-- Any correct ideal predicate reconstructs exactly the support ring on fraction pairs. -/
theorem predicate_multiplier_iff (a b : A) :
    PredicateIdealReconstruction.Mult P a b ↔
      b ≠ 0 ∧ ι a / ι b ∈ nonpositiveSupportSubring Γ K := by
  rw [PredicateIdealReconstruction.mult_iff P ι (coefficientRestrictedHahnInclusion_injective i)
    PurelyInfiniteSeries (predicate_ambient_test i P htest) (ideal_representative (Γ := Γ) i)]
  exact and_congr Iff.rfl (purelyInfiniteMultiplier_iff (Γ := Γ) (K := K) _)

/-- The two-sided multiplier condition reconstructs precisely the embedded coefficients. -/
theorem predicate_coefficient_iff (a b : A) :
    PredicateIdealReconstruction.Coeff P a b ↔
      b ≠ 0 ∧ ∃ c : K, ι a / ι b = C c :=
  PredicateIdealReconstruction.coeff_iff P ι (coefficientRestrictedHahnInclusion_injective i)
    PurelyInfiniteSeries (fun x => ∃ c : K, x = C c)
    (predicate_ambient_test i P htest) (ideal_representative (Γ := Γ) i)
    (coefficient_iff_multiplier_and_inverse (Γ := Γ) (K := K)) a b

/-- The four-coordinate graph extracts the actual coefficient at exponent zero. -/
theorem predicate_reconstructionGraph_iff (a b c d : A) :
    PredicateIdealReconstruction.Graph P a b c d ↔ b ≠ 0 ∧ d ≠ 0 ∧
      ι a / ι b ∈ nonpositiveSupportSubring Γ K ∧
      ι c / ι d = C ((ι a / ι b).coeff 0) := by
  rw [PredicateIdealReconstruction.graph_iff P ι (coefficientRestrictedHahnInclusion_injective i)
    PurelyInfiniteSeries (fun x => ∃ c : K, x = C c)
    (predicate_ambient_test i P htest) (ideal_representative (Γ := Γ) i)
    (coefficient_iff_multiplier_and_inverse (Γ := Γ) (K := K))]
  constructor
  · rintro ⟨hb, hd, hm, ⟨e, he⟩, hi⟩
    have hs := (purelyInfiniteMultiplier_iff (Γ := Γ) (K := K) _).mp hm
    have hc := (coefficientGraph_iff (Γ := Γ) (K := K) ⟨ι a / ι b, hs⟩ e).mp (by rwa [← he])
    exact ⟨hb, hd, hs, he.trans (congrArg C hc)⟩
  · rintro ⟨hb, hd, hs, he⟩
    refine ⟨hb, hd, (purelyInfiniteMultiplier_iff (Γ := Γ) (K := K) _).mpr hs, ⟨_, he⟩, ?_⟩
    rw [he]
    exact (coefficientGraph_iff (Γ := Γ) (K := K) ⟨ι a / ι b, hs⟩ _).mpr rfl

/-- All support-ring elements, including every coefficient, have valid fraction representatives. -/
theorem predicate_reconstruction_covers_support [Nontrivial Γ]
    (f : nonpositiveSupportSubring Γ K) :
    ∃ a b : A, b ≠ 0 ∧ f.val = ι a / ι b ∧ PredicateIdealReconstruction.Mult P a b := by
  obtain ⟨g, hg⟩ := exists_lt (0 : Γ)
  obtain ⟨a, b, hb, _, _, hf⟩ := nonpositiveSupport_fraction_of_monomial i g hg f
  exact ⟨a, b, hb, hf, (predicate_multiplier_iff i P htest a b).mpr ⟨hb, hf ▸ f.property⟩⟩

/-- Every represented support-ring input has a coefficient output represented in the original ring. -/
theorem predicate_reconstructionGraph_total [Nontrivial Γ] (a b : A)
    (hm : PredicateIdealReconstruction.Mult P a b) :
    ∃ c d : A, PredicateIdealReconstruction.Graph P a b c d := by
  obtain ⟨hb, hs⟩ := (predicate_multiplier_iff i P htest a b).mp hm
  obtain ⟨c, d, hd, he, _⟩ := predicate_reconstruction_covers_support i P htest
    (nonpositiveConstants ((ι a / ι b).coeff 0))
  exact ⟨c, d, (predicate_reconstructionGraph_iff i P htest a b c d).mpr
    ⟨hb, hd, hs, he.symm⟩⟩

/-- The reconstructed output is unique as a fraction, without requiring unique representatives. -/
theorem predicate_reconstructionGraph_singleValued (a b c d c' d' : A)
    (h : PredicateIdealReconstruction.Graph P a b c d)
    (h' : PredicateIdealReconstruction.Graph P a b c' d') : ι c / ι d = ι c' / ι d' :=
  ((predicate_reconstructionGraph_iff i P htest a b c d).mp h).2.2.2.trans
    ((predicate_reconstructionGraph_iff i P htest a b c' d').mp h').2.2.2.symm

end Predicate

local instance reconstructionNativeStructure : FirstOrder.Ring.CompatibleRing A :=
  FirstOrder.Ring.compatibleRingOfRing A

variable (φ : Language.ring.Formula (Fin 1))
  (hφ : ∀ x : coefficientRestrictedSubring (Γ := Γ) i,
    φ.Realize (fun _ => x) ↔ x.val ∈ purelyInfiniteIdeal (Γ := Γ) (R := K))
include φ hφ

/-- Exact native satisfaction for the support-ring reconstruction formula. -/
theorem native_reconstruction_mult_iff (a : Fin 2 → A) :
    (IdealReconstructionFormulas.multFormula φ).Realize a ↔
      a 1 ≠ 0 ∧ ι (a 0) / ι (a 1) ∈ nonpositiveSupportSubring Γ K :=
  (IdealReconstructionFormulas.realize_multFormula φ a).trans
    (predicate_multiplier_iff i _ hφ (a 0) (a 1))

/-- Exact native satisfaction for the embedded coefficient-field formula. -/
theorem native_reconstruction_coeff_iff (a : Fin 2 → A) :
    (IdealReconstructionFormulas.coeffFormula φ).Realize a ↔
      a 1 ≠ 0 ∧ ∃ c : K, ι (a 0) / ι (a 1) = C c :=
  (IdealReconstructionFormulas.realize_coeffFormula φ a).trans
    (predicate_coefficient_iff i _ hφ (a 0) (a 1))

/-- Exact native satisfaction for the graph on two fraction representatives. -/
theorem native_reconstruction_graph_iff (a : Fin 4 → A) :
    (IdealReconstructionFormulas.graphFormula φ).Realize a ↔ a 1 ≠ 0 ∧ a 3 ≠ 0 ∧
      ι (a 0) / ι (a 1) ∈ nonpositiveSupportSubring Γ K ∧
      ι (a 2) / ι (a 3) = C ((ι (a 0) / ι (a 1)).coeff 0) :=
  (IdealReconstructionFormulas.realize_graphFormula φ a).trans
    (predicate_reconstructionGraph_iff i _ hφ (a 0) (a 1) (a 2) (a 3))

/-- Every ambient coefficient is represented when the exponent group is nontrivial. -/
theorem native_reconstruction_covers_coefficients [Nontrivial Γ] (c : K) :
    ∃ a b : A, ι a / ι b = C c ∧
      (IdealReconstructionFormulas.coeffFormula φ).Realize ![a, b] := by
  obtain ⟨a, b, hb, he, _⟩ := predicate_reconstruction_covers_support i
    (fun x => φ.Realize (fun _ => x)) hφ (nonpositiveConstants c)
  exact ⟨a, b, he.symm, (native_reconstruction_coeff_iff i φ hφ ![a, b]).mpr
    ⟨hb, c, he.symm⟩⟩

/-- The native graph has an output for every represented support-ring input. -/
theorem native_reconstruction_graph_total [Nontrivial Γ] (a : Fin 2 → A)
    (hm : (IdealReconstructionFormulas.multFormula φ).Realize a) :
    ∃ c d : A, (IdealReconstructionFormulas.graphFormula φ).Realize ![a 0, a 1, c, d] := by
  obtain ⟨c, d, hg⟩ := predicate_reconstructionGraph_total i
    (fun x => φ.Realize (fun _ => x)) hφ (a 0) (a 1)
    ((IdealReconstructionFormulas.realize_multFormula φ a).mp hm)
  exact ⟨c, d, (IdealReconstructionFormulas.realize_graphFormula φ _).mpr hg⟩

/-- The support-ring representatives are parameter-free definable in the original ring. -/
theorem reconstruction_support_definable : (∅ : Set A).Definable Language.ring
    {a : Fin 2 → A | a 1 ≠ 0 ∧ ι (a 0) / ι (a 1) ∈ nonpositiveSupportSubring Γ K} := by
  apply Set.empty_definable_iff.mpr
  refine ⟨IdealReconstructionFormulas.multFormula φ, ?_⟩
  ext a
  exact (native_reconstruction_mult_iff i φ hφ a).symm

/-- The embedded coefficient representatives are parameter-free definable. -/
theorem reconstruction_coefficients_definable : (∅ : Set A).Definable Language.ring
    {a : Fin 2 → A | a 1 ≠ 0 ∧ ∃ c : K, ι (a 0) / ι (a 1) = C c} := by
  apply Set.empty_definable_iff.mpr
  refine ⟨IdealReconstructionFormulas.coeffFormula φ, ?_⟩
  ext a
  exact (native_reconstruction_coeff_iff i φ hφ a).symm

/-- The graph on two fraction pairs is parameter-free definable. -/
theorem reconstruction_graph_definable : (∅ : Set A).Definable Language.ring
    {a : Fin 4 → A | a 1 ≠ 0 ∧ a 3 ≠ 0 ∧
      ι (a 0) / ι (a 1) ∈ nonpositiveSupportSubring Γ K ∧
      ι (a 2) / ι (a 3) = C ((ι (a 0) / ι (a 1)).coeff 0)} := by
  apply Set.empty_definable_iff.mpr
  refine ⟨IdealReconstructionFormulas.graphFormula φ, ?_⟩
  ext a
  exact (native_reconstruction_graph_iff i φ hφ a).symm

end
end Surreal.HahnSeries
