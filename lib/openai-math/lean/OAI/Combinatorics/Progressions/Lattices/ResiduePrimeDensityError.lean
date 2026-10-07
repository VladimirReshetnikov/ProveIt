/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.FiniteProductCellMean
import OAI.Combinatorics.Progressions.Estimates.ProductReferenceFiber
import OAI.Combinatorics.Progressions.Estimates.UniformRestrictedMean
import OAI.Combinatorics.Progressions.Lattices.CoprimeResiduePhysicalStability
import OAI.Combinatorics.Progressions.Polynomial.FiniteMarginalLowDegree

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_prime_coordinate_integer_anchor {ι σ : Type*} [DecidableEq ι]
    (q : ι → ℕ) [∀ i, NeZero (q i)]
    (hcop : Pairwise (fun i j => (q i).Coprime (q j)))
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    ∃ u : σ → ℤ, ∀ i ∈ I, (fun j => (u j : ZMod (q i))) = x i := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp⟩
  | @insert i I hi ih =>
    obtain ⟨v, hv⟩ := ih
    have hc : (q i).Coprime (∏ k ∈ I, q k) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro k hk
      apply hcop
      intro heq
      exact hi (heq ▸ hk)
    have hu : ∀ j : σ, ∃ u : ℤ,
        u ≡ ((x i j).val : ℤ) [ZMOD (q i : ℤ)] ∧ u ≡ v j [ZMOD ((∏ k ∈ I, q k : ℕ) : ℤ)] := by
      intro j
      exact exists_integer_coprime_residues hc (x i j).val (v j)
    choose u hu using hu
    refine ⟨u, ?_⟩
    intro k hk
    rcases Finset.mem_insert.mp hk with hki | hk
    · subst k
      funext j
      have h := (ZMod.intCast_eq_intCast_iff (u j) ((x i j).val : ℤ) (q i)).mpr (hu j).1
      simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using h
    · funext j
      have hd : (q k : ℤ) ∣ ((∏ l ∈ I, q l : ℕ) : ℤ) := by
        exact_mod_cast Finset.dvd_prod_of_mem q hk
      have h := (ZMod.intCast_eq_intCast_iff (u j) (v j) (q k)).mpr ((hu j).2.of_dvd hd)
      exact h.trans (congrFun (hv k hk) j)

theorem primeCoordinateCell_eq_integer_anchor {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ) (I : Finset ι)
    (x : ∀ i, σ → ZMod (q i)) (u : σ → ℤ)
    (hu : ∀ i ∈ I, (fun j => (u j : ZMod (q i))) = x i) :
    primeCoordinateCell lo N q I x =
      primeCoordinateCell lo N q I (fun i j => (u j : ZMod (q i))) := by
  ext z
  simp only [mem_primeCoordinateCell]
  constructor
  · rintro ⟨hz, hx⟩
    exact ⟨hz, fun i hi => (hx i hi).trans (hu i hi).symm⟩
  · rintro ⟨hz, hx⟩
    exact ⟨hz, fun i hi => (hx i hi).trans (hu i hi)⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def primeCoordinateMassRatio {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ) [∀ i, NeZero (q i)]
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) : ℝ :=
  ((primeCoordinateCell lo N q I x).card : ℝ) / (translatedIntegerBox lo N).card /
    productFiberMass (FiniteProbabilityWeights.pi (primeCoordinateReference (σ := σ) q)).weight I x

theorem primeCoordinate_weighted_fiber {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ)
    (hbox : (translatedIntegerBox lo N).Nonempty) (q : ι → ℕ) [∀ i, NeZero (q i)]
    (f : (σ → ℤ) → ℝ) (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    (FiniteProbabilityWeights.uniformFinset (translatedIntegerBox lo N) hbox).mean
      (fun z => f z.val * productFiberIndicator I x (primeCoordinateObservation q z.val)) =
      ((primeCoordinateCell lo N q I x).card : ℝ) / (translatedIntegerBox lo N).card *
        (𝔼 z : primeCoordinateCell lo N q I x, f z.val) := by
  classical
  let P : (σ → ℤ) → Prop := fun z => ∀ i ∈ I, (fun j => (z j : ZMod (q i))) = x i
  have hcell : primeCoordinateCell lo N q I x = (translatedIntegerBox lo N).filter P := by
    ext z
    simp only [mem_primeCoordinateCell, Finset.mem_filter, P]
  rw [hcell]
  calc
    _ = (FiniteProbabilityWeights.uniformFinset (translatedIntegerBox lo N) hbox).mean
        (fun z => if P z.val then f z.val else 0) := by
      congr 1
      funext z
      have ho : primeCoordinateObservation q z.val =
          (fun i j => (z.val j : ZMod (q i))) := rfl
      rw [ho]
      by_cases hp : P z.val
      · change (∀ i ∈ I, (fun j => (z.val j : ZMod (q i))) = x i) at hp
        dsimp only [productFiberIndicator, P]
        rw [ite_eq_left hp, ite_eq_left hp, mul_one]
      · change ¬ (∀ i ∈ I, (fun j => (z.val j : ZMod (q i))) = x i) at hp
        dsimp only [productFiberIndicator, P]
        rw [ite_eq_right hp, ite_eq_right hp, mul_zero]
    _ = _ := uniformFinset_restricted_mean (translatedIntegerBox lo N) hbox P f

theorem primeCoordinateDensity_conditional {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ)
    (hbox : (translatedIntegerBox lo N).Nonempty) (q : ι → ℕ) [∀ i, NeZero (q i)]
    (f : (σ → ℤ) → ℝ) (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    productConditionalMean (primeCoordinateReference (σ := σ) q) I
      (primeCoordinateDensity lo N hbox q f) x =
      primeCoordinateMassRatio lo N q I x * (𝔼 z : primeCoordinateCell lo N q I x, f z.val) := by
  unfold primeCoordinateDensity
  rw [observedProductDensity_conditional _ (primeCoordinateReference_weight_pos q)]
  rw [primeCoordinate_weighted_fiber lo N hbox q f I x]
  unfold primeCoordinateMassRatio
  ring

theorem primeCoordinateReference_fiber {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (q : ι → ℕ) [∀ i, NeZero (q i)]
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    productFiberMass (FiniteProbabilityWeights.pi (primeCoordinateReference (σ := σ) q)).weight I x =
      (((∏ i ∈ I, q i : ℕ) : ℝ) ^ Fintype.card σ)⁻¹ := by
  change productFiberMass (FiniteProbabilityWeights.pi
    (fun i => FiniteProbabilityWeights.uniform (σ → ZMod (q i)))).weight I x = _
  rw [productFiberMass_uniform]
  simp only [Fintype.card_fun, ZMod.card, Nat.cast_pow, Nat.cast_prod,
    Finset.prod_inv_distrib, Finset.prod_pow]

theorem primeCoordinateMassRatio_eq_count {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ) [∀ i, NeZero (q i)]
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    primeCoordinateMassRatio lo N q I x =
      ((∏ i ∈ I, q i : ℕ) : ℝ) ^ Fintype.card σ *
        (primeCoordinateCell lo N q I x).card / (translatedIntegerBox lo N).card := by
  rw [primeCoordinateMassRatio, primeCoordinateReference_fiber, div_inv_eq_mul]
  ring

theorem primeCoordinateDensity_conditional_one {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ)
    (hbox : (translatedIntegerBox lo N).Nonempty) (q : ι → ℕ) [∀ i, NeZero (q i)]
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    productConditionalMean (primeCoordinateReference (σ := σ) q) I
      (primeCoordinateDensity lo N hbox q (fun _ => 1)) x = primeCoordinateMassRatio lo N q I x := by
  classical
  rw [primeCoordinateDensity_conditional]
  by_cases hne : (primeCoordinateCell lo N q I x).Nonempty
  · let : Nonempty (primeCoordinateCell lo N q I x) := hne.to_subtype
    rw [Fintype.expect_const, mul_one]
  · have hempty : primeCoordinateCell lo N q I x = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [primeCoordinateMassRatio, hempty, Finset.card_empty, Nat.cast_zero, zero_div, zero_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem primeCoordinateCell_card_residue {ι σ : Type*} [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ)
    (hcop : Pairwise (fun i j => (q i).Coprime (q j))) (I : Finset ι)
    (x : ∀ i, σ → ZMod (q i)) (u : σ → ℤ)
    (hu : ∀ i ∈ I, (fun j => (u j : ZMod (q i))) = x i) :
    (primeCoordinateCell lo N q I x).card =
      rectangularResidueCount lo (fun j => lo j + N j) (fun _ => ((∏ i ∈ I, q i : ℕ) : ℤ)) u := by
  rw [primeCoordinateCell_eq_integer_anchor lo N q I x u hu]
  have hc := Fintype.card_congr (primeCoordinateCellEquiv lo N q hcop I u)
  rw [Fintype.card_coe] at hc
  exact hc.trans (rectangularResidueCount_eq_card _ _ _ _).symm

theorem primeCoordinateMassRatio_close {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (hN : ∀ j, 0 < N j)
    (q : ι → ℕ) [∀ i, NeZero (q i)]
    (hcop : Pairwise (fun i j => (q i).Coprime (q j))) (I : Finset ι)
    (x : ∀ i, σ → ZMod (q i))
    (hsmall : (∑ j, ((∏ i ∈ I, q i : ℕ) : ℝ) / N j) ≤ 1 / 2) :
    |primeCoordinateMassRatio lo N q I x - 1| ≤
      2 * ∑ j, ((∏ i ∈ I, q i : ℕ) : ℝ) / N j := by
  obtain ⟨u, hu⟩ := exists_prime_coordinate_integer_anchor q hcop I x
  have hM : 0 < ∏ i ∈ I, q i := Finset.prod_pos (fun i _ => Nat.pos_of_ne_zero (NeZero.ne (q i)))
  have herr := rectangularResidueCount_relative_error lo (fun j => lo j + N j)
    (fun _ => ((∏ i ∈ I, q i : ℕ) : ℤ)) u
    (fun j => by have hj := hN j; omega) (fun _ => Nat.cast_pos.mpr hM)
    (by simpa only [add_sub_cancel_left, Int.cast_natCast] using hsmall)
  have hcell := primeCoordinateCell_card_residue lo N q hcop I x u hu
  have hvolume : integerRectangleVolume lo (fun j => lo j + N j) =
      ((translatedIntegerBox lo N).card : ℝ) := by
    simp only [integerRectangleVolume, add_sub_cancel_left, Int.cast_natCast,
      translatedIntegerBox, card_translateSupport, card_integerBox, Nat.cast_prod]
  rw [hvolume, ← hcell] at herr
  simp only [Finset.prod_const, Finset.card_univ, add_sub_cancel_left, Int.cast_natCast] at herr
  have hV : (0 : ℝ) < (translatedIntegerBox lo N).card := by
    simp only [translatedIntegerBox, card_translateSupport, card_integerBox, Nat.cast_prod]
    exact Finset.prod_pos (fun j _ => Nat.cast_pos.mpr (hN j))
  rw [primeCoordinateMassRatio_eq_count]
  calc
    _ = |((∏ i ∈ I, q i : ℕ) : ℝ) ^ Fintype.card σ * (primeCoordinateCell lo N q I x).card -
        (translatedIntegerBox lo N).card| / (translatedIntegerBox lo N).card := by
      rw [← abs_of_pos hV, ← abs_div]
      congr 1
      rw [abs_of_pos hV]
      field_simp
    _ ≤ _ := (div_le_iff₀ hV).mpr herr

theorem primeCoordinateDensity_productMarginalsClose {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (hN : ∀ j, 0 < N j)
    (hbox : (translatedIntegerBox lo N).Nonempty) (q : ι → ℕ) [∀ i, NeZero (q i)]
    (hcop : Pairwise (fun i j => (q i).Coprime (q j))) (r : ℕ) (η : ℝ)
    (hsmall : ∀ I : Finset ι, I.card ≤ r → (∑ j, ((∏ i ∈ I, q i : ℕ) : ℝ) / N j) ≤ 1 / 2)
    (herror : ∀ I : Finset ι, I.card ≤ r → 2 * (∑ j, ((∏ i ∈ I, q i : ℕ) : ℝ) / N j) ≤ η) :
    ProductMarginalsClose (primeCoordinateReference (σ := σ) q)
      (primeCoordinateDensity lo N hbox q (fun _ => 1)) η r := by
  intro I hI x _
  rw [primeCoordinateDensity_conditional_one]
  exact (primeCoordinateMassRatio_close lo N hN q hcop I x (hsmall I hI)).trans (herror I hI)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def residuePrimeCoordinateLaw {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] : FiniteProbabilityWeights (∀ i, σ → ZMod (q i)) := by
  let := hne
  exact (FiniteProbabilityWeights.uniform
    (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a)).fiberLaw
      (fun z => primeCoordinateObservation q (fun j => (z j).val))

noncomputable def residuePrimeCoordinateDensity {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (f : (σ → ℤ) → ℝ) : (∀ i, σ → ZMod (q i)) → ℝ := by
  let := hne
  exact observedProductDensity (primeCoordinateReference (σ := σ) q)
    (FiniteProbabilityWeights.uniform
      (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (fun z => primeCoordinateObservation q (fun j => (z j).val)) (fun z => f (fun j => (z j).val))

noncomputable def residuePrimeCoordinateMassRatio {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (q : ι → ℕ) [∀ i, NeZero (q i)] (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) : ℝ :=
  (Fintype.card (ResiduePrimeCoordinateCell lo N M a q I x) : ℝ) /
    Fintype.card (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a) /
    productFiberMass (FiniteProbabilityWeights.pi (primeCoordinateReference (σ := σ) q)).weight I x

theorem residuePrimeCoordinateDensity_conditional {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (f : (σ → ℤ) → ℝ)
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    productConditionalMean (primeCoordinateReference (σ := σ) q) I
      (residuePrimeCoordinateDensity lo N M a hne q f) x =
      residuePrimeCoordinateMassRatio lo N M a q I x *
        (𝔼 z : ResiduePrimeCoordinateCell lo N M a q I x, f (fun j => (z.val j).val)) := by
  let := hne
  exact uniform_observedProductDensity_conditional
    (Ω := IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a)
    (primeCoordinateReference (σ := σ) q)
    (primeCoordinateReference_weight_pos q)
    (fun z => primeCoordinateObservation q (fun j => (z j).val)) (fun z => f (fun j => (z j).val)) I x

theorem residuePrimeCoordinateMassRatio_eq_count {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (q : ι → ℕ) [∀ i, NeZero (q i)] (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    residuePrimeCoordinateMassRatio lo N M a q I x =
      ((∏ i ∈ I, q i : ℕ) : ℝ) ^ Fintype.card σ *
        Fintype.card (ResiduePrimeCoordinateCell lo N M a q I x) /
        Fintype.card (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a) := by
  rw [residuePrimeCoordinateMassRatio, primeCoordinateReference_fiber, div_inv_eq_mul]
  ring

theorem residuePrimeCoordinateDensity_conditional_one {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    productConditionalMean (primeCoordinateReference (σ := σ) q) I
      (residuePrimeCoordinateDensity lo N M a hne q (fun _ => 1)) x =
      residuePrimeCoordinateMassRatio lo N M a q I x := by
  classical
  rw [residuePrimeCoordinateDensity_conditional]
  by_cases hc : Nonempty (ResiduePrimeCoordinateCell lo N M a q I x)
  · let := hc
    rw [Fintype.expect_const, mul_one]
  · have hempty : IsEmpty (ResiduePrimeCoordinateCell lo N M a q I x) := not_nonempty_iff.mp hc
    let := hempty
    simp only [residuePrimeCoordinateMassRatio, Fintype.card_of_isEmpty, Nat.cast_zero,
      zero_div, zero_mul]

theorem residuePrimeCoordinateDensity_one {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (x : ∀ i, σ → ZMod (q i)) :
    residuePrimeCoordinateDensity lo N M a hne q (fun _ => 1) x =
      (residuePrimeCoordinateLaw lo N M a hne q).weight x /
        (FiniteProbabilityWeights.pi (primeCoordinateReference (σ := σ) q)).weight x := rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem primeCoordinateMean_re {ι σ : Type*} [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ)
    (q : ι → ℕ) (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    (primeCoordinateMean f lo N q I x).re = 𝔼 z : primeCoordinateCell lo N q I x, (f z.val).re := by
  simp only [primeCoordinateMean, Fintype.expect_eq_sum_div_card, Complex.div_natCast_re, Complex.re_sum]

theorem primeCoordinateRealMean_bound {ι σ : Type*} [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (f : (σ → ℤ) → ℝ) (lo : σ → ℤ) (N : σ → ℕ)
    (q : ι → ℕ) (I : Finset ι) (x : ∀ i, σ → ZMod (q i))
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ z ∈ translatedIntegerBox lo N, |f z| ≤ C) :
    |𝔼 z : primeCoordinateCell lo N q I x, f z.val| ≤ C := by
  classical
  by_cases hne : (primeCoordinateCell lo N q I x).Nonempty
  · let : Nonempty (primeCoordinateCell lo N q I x) := hne.to_subtype
    rw [← FiniteProbabilityWeights.uniform_mean]
    apply FiniteProbabilityWeights.abs_mean_le_on_support
    intro z _
    exact hf z.val ((mem_primeCoordinateCell lo N q I x z.val).mp z.property).1
  · have hempty : primeCoordinateCell lo N q I x = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [hempty, Fintype.expect_eq_sum_div_card, Fintype.card_coe, Finset.card_empty,
      Nat.cast_zero, div_zero, abs_zero]
    exact hC

theorem primeCoordinateDensity_conditional_error {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (hN : ∀ j, 0 < N j)
    (hbox : (translatedIntegerBox lo N).Nonempty) (q : ι → ℕ) [∀ i, NeZero (q i)]
    (hcop : Pairwise (fun i j => (q i).Coprime (q j)))
    (f : (σ → ℤ) → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ z ∈ translatedIntegerBox lo N, |f z| ≤ C)
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i))
    (hsmall : (∑ j, ((∏ i ∈ I, q i : ℕ) : ℝ) / N j) ≤ 1 / 2) :
    |productConditionalMean (primeCoordinateReference (σ := σ) q) I
      (primeCoordinateDensity lo N hbox q f) x - (𝔼 z : primeCoordinateCell lo N q I x, f z.val)| ≤
      (2 * ∑ j, ((∏ i ∈ I, q i : ℕ) : ℝ) / N j) * C := by
  rw [primeCoordinateDensity_conditional]
  rw [← sub_one_mul, abs_mul]
  exact mul_le_mul (primeCoordinateMassRatio_close lo N hN q hcop I x hsmall)
    (primeCoordinateRealMean_bound f lo N q I x C hC hf) (abs_nonneg _) (by positivity)

theorem primeCoordinateDensity_sectionMarginalsClose {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (hN : ∀ j, 0 < N j)
    (hbox : (translatedIntegerBox lo N).Nonempty) (q : ι → ℕ) [∀ i, NeZero (q i)]
    (hcop : Pairwise (fun i j => (q i).Coprime (q j))) (r : ℕ) (η : ℝ)
    (hsmall : ∀ I : Finset ι, I.card ≤ r → (∑ j, ((∏ i ∈ I, q i : ℕ) : ℝ) / N j) ≤ 1 / 2)
    (herror : ∀ I : Finset ι, I.card ≤ r → 2 * (∑ j, ((∏ i ∈ I, q i : ℕ) : ℝ) / N j) ≤ η)
    (T A : Finset ι) (hAT : A ⊆ T) (hAr : A.card ≤ r) (z : ∀ i, σ → ZMod (q i)) :
    ProductMarginalsClose (primeCoordinateReference (σ := σ) q)
      (productSectionAverage (primeCoordinateReference (σ := σ) q) T A z
        (primeCoordinateDensity lo N hbox q (fun _ => 1))) η (r - A.card) := by
  apply ProductMarginalsClose.section (primeCoordinateReference (σ := σ) q)
    (primeCoordinateDensity_productMarginalsClose lo N hN hbox q hcop r η hsmall herror)
    T A hAT hAr z
  exact (Finset.prod_pos (fun i _ => primeCoordinateReference_weight_pos q i (z i))).ne'

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def normalizedResiduePrimeDensity {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (f : (σ → ℤ) → ℝ) (scale : ℝ)
    (x : ∀ i, σ → ZMod (q i)) : ℝ :=
  scale⁻¹ * residuePrimeCoordinateDensity lo N M a hne q f x

theorem normalizedResiduePrimeDensity_low_degree {ι σ : Type*} [Fintype ι] [LinearOrder ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (moduli : ι → ℕ) [∀ i, NeZero (moduli i)] (f : (σ → ℤ) → ℝ)
    (hf : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ f z ∧ f z ≤ 1)
    (scale : ℝ) (hscale : 0 < scale) {cap η P : ℝ} (hcap : 0 ≤ cap) (hinv : scale⁻¹ ≤ cap)
    {k r q : ℕ} (hkr : k ≤ r) (hq : 2 ≤ q) (heven : Even q) (hη : 0 ≤ η)
    (hrP : (r : ℝ) ≤ P) (hlog : Real.log (2 + cap) ≤ P)
    (hPq : P ≤ (q : ℝ)) (hqP : (q : ℝ) ≤ P + 2)
    (hsmall : η ≤ (1 / 2) * (((2 : ℝ) ^ (r + 1) * (2 + (Fintype.card ι : ℝ)) ^ r * (2 + cap)) ^ q)⁻¹)
    (hclose : ProductMarginalsClose (primeCoordinateReference (σ := σ) moduli)
      (residuePrimeCoordinateDensity lo N M a hne moduli (fun _ => 1)) η (r * (q + 1)))
    (hbound : ProductBoundedMarginals (primeCoordinateReference (σ := σ) moduli)
      (normalizedResiduePrimeDensity lo N M a hne moduli f scale) 1 r) :
    Real.sqrt (productANOVAEnergy (primeCoordinateReference (σ := σ) moduli)
      (Finset.univ.powersetCard k) (normalizedResiduePrimeDensity lo N M a hne moduli f scale)) ≤
      (16 * (P + 2)) ^ (2 * k) := by
  let := hne
  apply normalizedObservedDensity_low_degree (primeCoordinateReference (σ := σ) moduli)
    (FiniteProbabilityWeights.uniform
      (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (fun z => primeCoordinateObservation moduli (fun j => (z j).val))
    (fun z => f (fun j => (z j).val)) _ scale hscale hcap hinv hkr hq heven hη
    hrP hlog hPq hqP hsmall hclose hbound
  intro z
  apply hf
  apply (mem_translatedIntegerBox lo N _).mpr
  intro j
  exact Finset.mem_Ico.mp ((Finset.mem_filter.mp (z j).property).1)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
  (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a))
  (q : ι → ℕ) [∀ i, NeZero (q i)]

theorem residuePrimeCoordinateMassRatio_close_of_marginals {eta : ℝ} {A : ℕ}
    (hclose : ProductMarginalsClose (primeCoordinateReference (σ := σ) q)
      (residuePrimeCoordinateDensity lo N M a hne q (fun _ => 1)) eta A)
    (K : Finset ι) (hK : K.card ≤ A) (base : ∀ i, σ → ZMod (q i)) :
    |residuePrimeCoordinateMassRatio lo N M a q K base - 1| ≤ eta := by
  have h := hclose K hK base
    (Finset.prod_pos (fun i _ => primeCoordinateReference_weight_pos q i (base i))).ne'
  rwa [residuePrimeCoordinateDensity_conditional_one] at h

theorem residuePrimeCoordinateCell_nonempty_of_marginals {eta : ℝ} {A : ℕ}
    (hclose : ProductMarginalsClose (primeCoordinateReference (σ := σ) q)
      (residuePrimeCoordinateDensity lo N M a hne q (fun _ => 1)) eta A)
    (heta : eta < 1) (K : Finset ι) (hK : K.card ≤ A) (base : ∀ i, σ → ZMod (q i)) :
    Nonempty (ResiduePrimeCoordinateCell lo N M a q K base) := by
  classical
  by_contra hempty
  let : IsEmpty (ResiduePrimeCoordinateCell lo N M a q K base) := not_nonempty_iff.mp hempty
  have h := residuePrimeCoordinateMassRatio_close_of_marginals lo N M a hne q hclose K hK base
  simp only [residuePrimeCoordinateMassRatio, Fintype.card_of_isEmpty, Nat.cast_zero,
    zero_div, zero_sub, abs_neg, abs_one] at h
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem residuePrimeCoordinateMassRatio_affine {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hM : 0 < M) (hcop : ∀ i, M.Coprime (q i))
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    residuePrimeCoordinateMassRatio lo N M a q I
      (fun i => affineResidueCoordinateEquiv M (q i) a (hcop i) (x i)) =
    primeCoordinateMassRatio (fun j => residueIndexLower (lo j) M (a j))
      (fun j => residueIndexLength (lo j) (lo j + N j) M (a j)) q I x := by
  have hc := Fintype.card_congr (residuePrimeCoordinateCellEquiv lo N M a q hM hcop I x)
  have hb := Fintype.card_congr (integerResidueBoxEquiv lo (fun j => lo j + N j)
    (fun _ => (M : ℤ)) a (fun _ => Nat.cast_pos.mpr hM))
  rw [Fintype.card_coe] at hc hb
  rw [residuePrimeCoordinateMassRatio_eq_count, primeCoordinateMassRatio_eq_count, ← hc, ← hb]

theorem residuePrimeCoordinateMassRatio_close {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hM : 0 < M) (hcop : ∀ i, M.Coprime (q i))
    (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i))
    (hsmall : (∑ j, ((∏ i ∈ I, q i : ℕ) : ℝ) /
      residueIndexLength (lo j) (lo j + N j) M (a j)) ≤ 1 / 2) :
    |residuePrimeCoordinateMassRatio lo N M a q I x - 1| ≤
      2 * ∑ j, ((∏ i ∈ I, q i : ℕ) : ℝ) /
        residueIndexLength (lo j) (lo j + N j) M (a j) := by
  let inv : ∀ i, σ → ZMod (q i) :=
    fun i => (affineResidueCoordinateEquiv M (q i) a (hcop i)).symm (x i)
  have hx : (fun i => affineResidueCoordinateEquiv M (q i) a (hcop i) (inv i)) = x := by
    funext i
    exact Equiv.apply_symm_apply _ _
  have hlength := integerResidueBox_lengths_pos lo (fun j => lo j + N j)
    (fun _ => (M : ℤ)) a (fun _ => Nat.cast_pos.mpr hM) hne
  rw [← hx, residuePrimeCoordinateMassRatio_affine lo N M a q hM hcop I inv]
  exact primeCoordinateMassRatio_close _ _ hlength q hpair I inv hsmall

theorem residuePrimeCoordinateCell_nonempty_of_small {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hM : 0 < M) (hcop : ∀ i, M.Coprime (q i))
    (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i))
    (hsmall : (∑ j, ((∏ i ∈ I, q i : ℕ) : ℝ) /
      residueIndexLength (lo j) (lo j + N j) M (a j)) < 1 / 2) :
    Nonempty (ResiduePrimeCoordinateCell lo N M a q I x) := by
  classical
  by_contra hc
  let : IsEmpty (ResiduePrimeCoordinateCell lo N M a q I x) := not_nonempty_iff.mp hc
  have he := residuePrimeCoordinateMassRatio_close lo N M a hne q hM hcop hpair I x hsmall.le
  simp only [residuePrimeCoordinateMassRatio, Fintype.card_of_isEmpty, Nat.cast_zero,
    zero_div, zero_sub, abs_neg, abs_one] at he
  linarith

theorem residuePrimeCoordinateDensity_productMarginalsClose {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hM : 0 < M) (hcop : ∀ i, M.Coprime (q i))
    (hpair : Pairwise (fun i j => (q i).Coprime (q j))) (r : ℕ) (η : ℝ)
    (hsmall : ∀ I : Finset ι, I.card ≤ r → (∑ j, ((∏ i ∈ I, q i : ℕ) : ℝ) /
      residueIndexLength (lo j) (lo j + N j) M (a j)) ≤ 1 / 2)
    (herror : ∀ I : Finset ι, I.card ≤ r → 2 * (∑ j, ((∏ i ∈ I, q i : ℕ) : ℝ) /
      residueIndexLength (lo j) (lo j + N j) M (a j)) ≤ η) :
    ProductMarginalsClose (primeCoordinateReference (σ := σ) q)
      (residuePrimeCoordinateDensity lo N M a hne q (fun _ => 1)) η r := by
  intro I hI x _
  rw [residuePrimeCoordinateDensity_conditional_one]
  exact (residuePrimeCoordinateMassRatio_close lo N M a hne q hM hcop hpair I x
    (hsmall I hI)).trans (herror I hI)

theorem residuePrimeCoordinateDensity_sectionMarginalsClose {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hM : 0 < M) (hcop : ∀ i, M.Coprime (q i))
    (hpair : Pairwise (fun i j => (q i).Coprime (q j))) (r : ℕ) (η : ℝ)
    (hsmall : ∀ I : Finset ι, I.card ≤ r → (∑ j, ((∏ i ∈ I, q i : ℕ) : ℝ) /
      residueIndexLength (lo j) (lo j + N j) M (a j)) ≤ 1 / 2)
    (herror : ∀ I : Finset ι, I.card ≤ r → 2 * (∑ j, ((∏ i ∈ I, q i : ℕ) : ℝ) /
      residueIndexLength (lo j) (lo j + N j) M (a j)) ≤ η)
    (T A : Finset ι) (hAT : A ⊆ T) (hAr : A.card ≤ r) (z : ∀ i, σ → ZMod (q i)) :
    ProductMarginalsClose (primeCoordinateReference (σ := σ) q)
      (productSectionAverage (primeCoordinateReference (σ := σ) q) T A z
        (residuePrimeCoordinateDensity lo N M a hne q (fun _ => 1))) η (r - A.card) := by
  apply ProductMarginalsClose.section (primeCoordinateReference (σ := σ) q)
    (residuePrimeCoordinateDensity_productMarginalsClose lo N M a hne q hM hcop hpair r η hsmall herror)
    T A hAT hAr z
  exact (Finset.prod_pos (fun i _ => primeCoordinateReference_weight_pos q i (z i))).ne'

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem residuePrimeCoordinateMean_re {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ)
    (M : ℕ) (a : σ → ℤ) (q : ι → ℕ) (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    (residuePrimeCoordinateMean f lo N M a q I x).re =
      𝔼 z : ResiduePrimeCoordinateCell lo N M a q I x, (f (fun j => (z.val j).val)).re := by
  simp only [residuePrimeCoordinateMean, Fintype.expect_eq_sum_div_card,
    Complex.div_natCast_re, Complex.re_sum]
  congr 3 <;> exact Subsingleton.elim _ _

theorem residuePrimeCoordinateRealMean_bound {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (f : (σ → ℤ) → ℝ) (lo : σ → ℤ) (N : σ → ℕ)
    (M : ℕ) (a : σ → ℤ) (q : ι → ℕ) (I : Finset ι) (x : ∀ i, σ → ZMod (q i))
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ z ∈ translatedIntegerBox lo N, |f z| ≤ C) :
    |𝔼 z : ResiduePrimeCoordinateCell lo N M a q I x, f (fun j => (z.val j).val)| ≤ C := by
  classical
  by_cases hne : Nonempty (ResiduePrimeCoordinateCell lo N M a q I x)
  · let := hne
    rw [← FiniteProbabilityWeights.uniform_mean]
    apply FiniteProbabilityWeights.abs_mean_le_on_support
    intro z _
    apply hf
    apply (mem_translatedIntegerBox lo N _).mpr
    intro j
    exact Finset.mem_Ico.mp ((Finset.mem_filter.mp (z.val j).property).1)
  · let : IsEmpty (ResiduePrimeCoordinateCell lo N M a q I x) := not_nonempty_iff.mp hne
    simp only [Fintype.expect_eq_sum_div_card, Fintype.card_of_isEmpty, Nat.cast_zero,
      div_zero, abs_zero]
    exact hC

theorem residuePrimeCoordinateDensity_conditional_error {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hM : 0 < M) (hcop : ∀ i, M.Coprime (q i))
    (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (f : (σ → ℤ) → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ z ∈ translatedIntegerBox lo N, |f z| ≤ C)
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i))
    (hsmall : (∑ j, ((∏ i ∈ I, q i : ℕ) : ℝ) /
      residueIndexLength (lo j) (lo j + N j) M (a j)) ≤ 1 / 2) :
    |productConditionalMean (primeCoordinateReference (σ := σ) q) I
      (residuePrimeCoordinateDensity lo N M a hne q f) x -
        (𝔼 z : ResiduePrimeCoordinateCell lo N M a q I x, f (fun j => (z.val j).val))| ≤
      (2 * ∑ j, ((∏ i ∈ I, q i : ℕ) : ℝ) /
        residueIndexLength (lo j) (lo j + N j) M (a j)) * C := by
  rw [residuePrimeCoordinateDensity_conditional, ← sub_one_mul, abs_mul]
  exact mul_le_mul (residuePrimeCoordinateMassRatio_close lo N M a hne q hM hcop hpair I x hsmall)
    (residuePrimeCoordinateRealMean_bound f lo N M a q I x C hC hf) (abs_nonneg _) (by positivity)

end Erdos3

end

end OAI
