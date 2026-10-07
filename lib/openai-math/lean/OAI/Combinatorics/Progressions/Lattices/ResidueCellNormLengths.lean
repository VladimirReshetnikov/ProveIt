import OAI.Combinatorics.Progressions.Estimates.StableReferenceMean
import OAI.Combinatorics.Progressions.Lattices.AffineResidueAccuracy
import OAI.Combinatorics.Progressions.Polynomial.CappedSectionLowDegree

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι σ : Type*} [Fintype ι] [LinearOrder ι] [Fintype σ] [DecidableEq σ]
  (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
  (hne : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
  (moduli : ι → ℕ) [∀ i, NeZero (moduli i)]
  (f : (σ → ℤ) → ℝ) (hf : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ f z ∧ f z ≤ 1)

include hf

theorem residuePrimeDensity_scaled_section_low_degree {scale cap η P : ℝ}
    (hscale : 0 < scale) (hcap : 0 ≤ cap) (hinv : scale⁻¹ ≤ cap)
    {r q k : ℕ} (hq : 2 ≤ q) (heven : Even q) (A : Finset ι)
    (hAr : A.card ≤ r) (hk : k ≤ r - A.card) (z : ∀ i, σ → ZMod (moduli i))
    (hη : 0 ≤ η) (hrP : (r : ℝ) ≤ P) (hlog : Real.log (2 + cap) ≤ P)
    (hPq : P ≤ (q : ℝ)) (hqP : (q : ℝ) ≤ P + 2)
    (hsmall : η ≤ (1 / 2) * (((2 : ℝ) ^ (r + 1) * (2 + (Fintype.card ι : ℝ)) ^ r * (2 + cap)) ^ q)⁻¹)
    (hclose : ProductMarginalsClose (primeCoordinateReference (σ := σ) moduli)
      (residuePrimeCoordinateDensity lo N M a hne moduli (fun _ => 1)) η (r * (q + 1)))
    (hbound : ProductBoundedMarginals (primeCoordinateReference (σ := σ) moduli)
      (normalizedResiduePrimeDensity lo N M a hne moduli f scale) 1 r) :
    Real.sqrt (productANOVAEnergy (primeCoordinateReference (σ := σ) moduli) (Finset.univ.powersetCard k)
      (fun y => scale⁻¹ * productSectionAverage (primeCoordinateReference (σ := σ) moduli) A A z
        (residuePrimeCoordinateDensity lo N M a hne moduli f) y)) ≤ (16 * (P + 2)) ^ (2 * k) := by
  let := hne
  have hphys : ∀ z : IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a,
      0 ≤ f (fun j => (z j).val) ∧ f (fun j => (z j).val) ≤ 1 := by
    intro z
    apply hf
    apply (mem_translatedIntegerBox lo N _).mpr
    intro j
    exact Finset.mem_Ico.mp ((Finset.mem_filter.mp (z j).property).1)
  exact observedProductDensity_scaled_section_low_degree (primeCoordinateReference (σ := σ) moduli)
    (FiniteProbabilityWeights.uniform (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (fun z => primeCoordinateObservation moduli (fun j => (z j).val)) (fun z => f (fun j => (z j).val))
    hphys hscale hcap hinv hq heven A A le_rfl hAr hk z
    (Finset.prod_pos (fun i _ => primeCoordinateReference_weight_pos moduli i (z i))).ne'
    hη hrP hlog hPq hqP hsmall hclose hbound

theorem residuePrimeDensity_scaled_section_norm {scale cap η : ℝ}
    (hscale : 0 < scale) (hinv : scale⁻¹ ≤ cap) (A : Finset ι) (z : ∀ i, σ → ZMod (moduli i))
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (D : Finset (Finset ι)) {b : ℕ}
    (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose (primeCoordinateReference (σ := σ) moduli)
      (residuePrimeCoordinateDensity lo N M a hne moduli (fun _ => 1)) η (2 * b + A.card))
    (herr : 2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ 1) :
    Real.sqrt (productANOVAEnergy (primeCoordinateReference (σ := σ) moduli) D
      (fun y => scale⁻¹ * productSectionAverage (primeCoordinateReference (σ := σ) moduli) A A z
        (residuePrimeCoordinateDensity lo N M a hne moduli f) y)) ≤ 3 * cap := by
  let := hne
  have hphys : ∀ z : IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a,
      0 ≤ f (fun j => (z j).val) ∧ f (fun j => (z j).val) ≤ 1 := by
    intro z
    apply hf
    apply (mem_translatedIntegerBox lo N _).mpr
    intro j
    exact Finset.mem_Ico.mp ((Finset.mem_filter.mp (z j).property).1)
  exact observedProductDensity_scaled_section_norm (primeCoordinateReference (σ := σ) moduli)
    (FiniteProbabilityWeights.uniform (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (fun z => primeCoordinateObservation moduli (fun j => (z j).val)) (fun z => f (fun j => (z j).val))
    hphys hscale hinv A A le_rfl z
    (Finset.prod_pos (fun i _ => primeCoordinateReference_weight_pos moduli i (z i))).ne'
    hη0 hη1 D hcard hclose herr

theorem residuePrimeDensity_section_norm_le_three (A : Finset ι) (z : ∀ i, σ → ZMod (moduli i))
    {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (D : Finset (Finset ι)) {b : ℕ}
    (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose (primeCoordinateReference (σ := σ) moduli)
      (residuePrimeCoordinateDensity lo N M a hne moduli (fun _ => 1)) η (2 * b + A.card))
    (herr : 2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ 1) :
    Real.sqrt (productANOVAEnergy (primeCoordinateReference (σ := σ) moduli) D
      (productSectionAverage (primeCoordinateReference (σ := σ) moduli) A A z
        (residuePrimeCoordinateDensity lo N M a hne moduli f))) ≤ 3 := by
  let := hne
  have hphys : ∀ z : IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a,
      0 ≤ f (fun j => (z j).val) ∧ f (fun j => (z j).val) ≤ 1 := by
    intro z
    apply hf
    apply (mem_translatedIntegerBox lo N _).mpr
    intro j
    exact Finset.mem_Ico.mp ((Finset.mem_filter.mp (z j).property).1)
  exact observedProductDensity_section_norm_le_three (primeCoordinateReference (σ := σ) moduli)
    (FiniteProbabilityWeights.uniform (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (fun z => primeCoordinateObservation moduli (fun j => (z j).val)) (fun z => f (fun j => (z j).val))
    hphys A A le_rfl z
    (Finset.prod_pos (fun i _ => primeCoordinateReference_weight_pos moduli i (z i))).ne'
    hη0 hη1 D hcard hclose herr

end Erdos3

end

section

namespace Erdos3

theorem productSectionAverage_empty_fixed {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))
    (z : ∀ i, X i) (f : (∀ i, X i) → ℝ) : productSectionAverage μ ∅ ∅ z f = f := by
  funext x
  have hm (u v : ∀ i, X i) : productCoordinateMix (∅ : Finset ι) u v = v := by
    funext i
    simp [productCoordinateMix]
  simp only [productSectionAverage, hm]
  exact (FiniteProbabilityWeights.pi μ).mean_const _

theorem residuePrimeDensity_norm_le_three {ι σ : Type*}
    [Fintype ι] [LinearOrder ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (f : (σ → ℤ) → ℝ)
    (hf : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ f z ∧ f z ≤ 1)
    {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (D : Finset (Finset ι)) {b : ℕ}
    (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose (primeCoordinateReference (σ := σ) q)
      (residuePrimeCoordinateDensity lo N M a hne q (fun _ => 1)) η (2 * b))
    (herr : 2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ 1) :
    Real.sqrt (productANOVAEnergy (primeCoordinateReference (σ := σ) q) D
      (residuePrimeCoordinateDensity lo N M a hne q f)) ≤ 3 := by
  have h := residuePrimeDensity_section_norm_le_three lo N M a hne q f hf ∅ (fun _ _ => 0)
    hη0 hη1 D hcard (by simpa only [Finset.card_empty, add_zero] using hclose) herr
  rw [productSectionAverage_empty_fixed] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem residuePrimeCoordinateMassRatio_nonneg {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (q : ι → ℕ) [∀ i, NeZero (q i)] (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    0 ≤ residuePrimeCoordinateMassRatio lo N M a q I x := by
  rw [residuePrimeCoordinateMassRatio_eq_count]
  positivity

theorem residuePrimeCoordinateMassRatio_outside {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (K : Finset ι) (base : ∀ i, σ → ZMod (q i))
    (u : ResiduePrimeCoordinateCell lo N M a q K base)
    (S : Finset {i // i ∉ K}) (x : ∀ i, σ → ZMod (q i)) (hx : ∀ i ∈ K, x i = base i) :
    residuePrimeCoordinateMassRatio lo N M a q (K ∪ S.image Subtype.val) x =
      residuePrimeCoordinateMassRatio lo N M a q K base *
        residuePrimeCoordinateMassRatio lo N (M.lcm (∏ i ∈ K, q i)) (fun j => (u.val j).val)
          (fun i : {i // i ∉ K} => q i.val) S (fun i => x i.val) := by
  classical
  have hdis : Disjoint K (S.image Subtype.val) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨j, _, heq⟩ := Finset.mem_image.mp hj
    exact j.property (heq ▸ hi)
  have hprod : (∏ i ∈ K ∪ S.image Subtype.val, q i) =
      (∏ i ∈ K, q i) * (∏ i ∈ S, q i.val) := by
    rw [Finset.prod_union hdis, Finset.prod_image]
    intro i _ j _ hij
    exact Subtype.ext hij
  have hc := Fintype.card_congr (residuePrimeCoordinateOutsideEquiv lo N M a q hpair K base u S x hx)
  have hb := Fintype.card_congr (residuePrimeCoordinateCell_lcmEquiv lo N M a q hpair K base u)
  let : Nonempty (ResiduePrimeCoordinateCell lo N M a q K base) := ⟨u⟩
  let : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a) := ⟨u.val⟩
  have hK : (Fintype.card (ResiduePrimeCoordinateCell lo N M a q K base) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := ResiduePrimeCoordinateCell lo N M a q K base)
  have hB : (Fintype.card (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a)
  rw [residuePrimeCoordinateMassRatio_eq_count, residuePrimeCoordinateMassRatio_eq_count,
    residuePrimeCoordinateMassRatio_eq_count, hprod, Nat.cast_mul, mul_pow, hc, ← hb]
  field_simp

theorem residuePrimeCoordinateDensity_conditional_outside {ι σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (K : Finset ι) (base : ∀ i, σ → ZMod (q i))
    (u : ResiduePrimeCoordinateCell lo N M a q K base)
    (f : (σ → ℤ) → ℝ) (S : Finset {i // i ∉ K})
    (x : ∀ i, σ → ZMod (q i)) (hx : ∀ i ∈ K, x i = base i) :
    productConditionalMean (primeCoordinateReference (σ := σ) q) (K ∪ S.image Subtype.val)
      (residuePrimeCoordinateDensity lo N M a hne q f) x =
      residuePrimeCoordinateMassRatio lo N M a q K base *
        productConditionalMean (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val)) S
          (residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i)) (fun j => (u.val j).val)
            (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
            (fun i : {i // i ∉ K} => q i.val) f) (fun i => x i.val) := by
  have hm := Fintype.expect_equiv (residuePrimeCoordinateOutsideEquiv lo N M a q hpair K base u S x hx)
    (fun z => f (fun j => (z.val j).val)) (fun z => f (fun j => (z.val j).val)) (fun _ => rfl)
  rw [residuePrimeCoordinateDensity_conditional, residuePrimeCoordinateDensity_conditional,
    residuePrimeCoordinateMassRatio_outside lo N M a q hpair K base u S x hx, hm, mul_assoc]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem retained_residue_marginals_of_lengths {ι σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    [∀ i, NeZero (q i)] (hM : 0 < M) (hpair : Pairwise (fun i k => (q i).Coprime (q k)))
    (K : Finset ι) (base : ∀ i, σ → ZMod (q i)) (hcop : ∀ i ∉ K, M.Coprime (q i))
    (u : ResiduePrimeCoordinateCell lo N M a q K base)
    (R : ℕ) (B C D η : ℝ) (hB : 0 ≤ B) (hη : η ≤ 1) (herror : Real.exp (-D) ≤ η)
    (hmoduli : ∀ i ∉ K, (q i : ℝ) ≤ Real.exp B)
    (hdim : (Fintype.card σ : ℝ) ≤ Real.exp C)
    (hlength : ∀ k, Real.exp (B * R + D + C + 1) ≤
      (residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val) : ℝ)) :
    ProductMarginalsClose (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val))
      (residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i)) (fun k => (u.val k).val)
        (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
        (fun i : {i // i ∉ K} => q i.val) (fun _ => 1)) η R ∧
    ∀ S : Finset {i // i ∉ K}, S.card ≤ R →
      2 * (∑ k, ((∏ i ∈ S, q i.val : ℕ) : ℝ) /
        residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val)) ≤ η := by
  have hQ : 0 < M.lcm (∏ i ∈ K, q i) :=
    Nat.pos_of_ne_zero (Nat.lcm_ne_zero hM.ne'
      (Finset.prod_pos (fun i _ => Nat.pos_of_ne_zero (NeZero.ne (q i)))).ne')
  have hQcop : ∀ i : {i // i ∉ K}, (M.lcm (∏ k ∈ K, q k)).Coprime (q i.val) :=
    fun i => selectedCombined_coprime_outside q hpair M K hcop i.val i.property
  have hpair' : Pairwise (fun i k : {i // i ∉ K} => (q i.val).Coprime (q k.val)) :=
    fun i k hik => hpair (fun heq => hik (Subtype.ext heq))
  have hne := residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u
  have hmods := fun i : {i // i ∉ K} => hmoduli i.val i.property
  refine ⟨?_, ?_⟩
  · exact residuePrimeDensity_close_of_lengths (ι := {i // i ∉ K}) (σ := σ)
      lo N (M.lcm (∏ i ∈ K, q i)) (fun k => (u.val k).val) hne
      (fun i : {i // i ∉ K} => q i.val) hQ hQcop hpair'
      R B C D η hB hη herror hmods hdim hlength
  · intro S hS
    exact (primeCoordinate_error_le_exp (fun i : {i // i ∉ K} => q i.val)
      (fun k => residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val))
      R B C D hB hmods hdim hlength S hS).trans herror

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def residueCellOutsideDensity {ι σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    [∀ i, NeZero (q i)] (K : Finset ι) (base : ∀ i, σ → ZMod (q i))
    (u : ResiduePrimeCoordinateCell lo N M a q K base) (f : (σ → ℤ) → ℝ) :
    (∀ i : {i // i ∉ K}, σ → ZMod (q i.val)) → ℝ :=
  observedProductDensity (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val))
    (@FiniteProbabilityWeights.uniform (ResiduePrimeCoordinateCell lo N M a q K base) _ ⟨u⟩)
    (fun z => primeCoordinateObservation (fun i : {i // i ∉ K} => q i.val) (fun k => (z.val k).val))
    (fun z => f (fun k => (z.val k).val))

theorem residueCellOutsideDensity_lcm {ι σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    [∀ i, NeZero (q i)] (hpair : Pairwise (fun i k => (q i).Coprime (q k)))
    (K : Finset ι) (base : ∀ i, σ → ZMod (q i))
    (u : ResiduePrimeCoordinateCell lo N M a q K base) (f : (σ → ℤ) → ℝ) :
    residueCellOutsideDensity lo N M a q K base u f =
      residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i)) (fun k => (u.val k).val)
        (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
        (fun i : {i // i ∉ K} => q i.val) f := by
  let : Nonempty (ResiduePrimeCoordinateCell lo N M a q K base) := ⟨u⟩
  let := residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u
  exact uniform_observedProductDensity_source_equiv
    (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val))
    (residuePrimeCoordinateCell_lcmEquiv lo N M a q hpair K base u)
    (fun z => primeCoordinateObservation (fun i : {i // i ∉ K} => q i.val) (fun k => (z k).val))
    (fun z => f (fun k => (z k).val))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem PrimeRefinementUpperBound.reference_density_upper {ι σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
    [∀ i, NeZero (q i)] {r : ℕ} {level ε δ : ℝ} {K : Finset ι}
    {base : ∀ i, σ → ZMod (q i)}
    (hupper : PrimeRefinementUpperBound h g lo N M a q r level ε δ K base)
    (hM : 0 < M) (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (hcop : ∀ i ∉ K, M.Coprime (q i))
    (u : ResiduePrimeCoordinateCell lo N M a q K base)
    (C : ℝ) (hC : 0 ≤ C) (hh : ∀ z ∈ translatedIntegerBox lo N, |(h z).re| ≤ C)
    (S : Finset {i // i ∉ K}) (hS : S.card ≤ r)
    (x : ∀ i : {i // i ∉ K}, σ → ZMod (q i.val))
    (hsmall : (∑ j, ((∏ i ∈ S, q i.val : ℕ) : ℝ) /
      residueIndexLength (lo j) (lo j + N j) (M.lcm (∏ i ∈ K, q i)) ((u.val j).val)) < 1 / 2) :
    productConditionalMean (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val)) S
      (residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i)) (fun j => (u.val j).val)
        (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
        (fun i : {i // i ∉ K} => q i.val) (fun z => (h z).re)) x ≤
      level * (residuePrimeCoordinateMean g lo N M a q K base).re + ε + level * δ +
        (2 * ∑ j, ((∏ i ∈ S, q i.val : ℕ) : ℝ) /
          residueIndexLength (lo j) (lo j + N j) (M.lcm (∏ i ∈ K, q i)) ((u.val j).val)) * C := by
  have hQ : 0 < M.lcm (∏ i ∈ K, q i) :=
    Nat.pos_of_ne_zero (Nat.lcm_ne_zero hM.ne'
      (Finset.prod_pos (fun i _ => Nat.pos_of_ne_zero (NeZero.ne (q i)))).ne')
  have hQcop : ∀ i : {i // i ∉ K}, (M.lcm (∏ k ∈ K, q k)).Coprime (q i.val) :=
    fun i => selectedCombined_coprime_outside q hpair M K hcop i.val i.property
  have hpair' : Pairwise (fun i j : {i // i ∉ K} => (q i.val).Coprime (q j.val)) :=
    fun i j hij => hpair (fun heq => hij (Subtype.ext heq))
  have hbase := residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u
  have hne := residuePrimeCoordinateCell_nonempty_of_small lo N (M.lcm (∏ i ∈ K, q i))
    (fun j => (u.val j).val) hbase (fun i : {i // i ∉ K} => q i.val) hQ hQcop hpair' S x hsmall
  have hu := hupper.outside hpair u S hS x hne
  have he := residuePrimeCoordinateDensity_conditional_error lo N (M.lcm (∏ i ∈ K, q i))
    (fun j => (u.val j).val) hbase (fun i : {i // i ∉ K} => q i.val) hQ hQcop hpair'
    (fun z => (h z).re) C hC hh S x hsmall.le
  rw [← residuePrimeCoordinateMean_re] at he
  have he' := (abs_le.mp he).2
  linarith

theorem PrimeRefinementUpperBound.reference_conditioned_upper {ι σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
    [∀ i, NeZero (q i)] {r : ℕ} {level ε δ : ℝ} {K : Finset ι}
    {base : ∀ i, σ → ZMod (q i)}
    (hupper : PrimeRefinementUpperBound h g lo N M a q r level ε δ K base)
    (hM : 0 < M) (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (hcop : ∀ i ∉ K, M.Coprime (q i))
    (u : ResiduePrimeCoordinateCell lo N M a q K base)
    (C : ℝ) (hC : 0 ≤ C) (hh : ∀ z ∈ translatedIntegerBox lo N, |(h z).re| ≤ C)
    (S : Finset {i // i ∉ K}) (hS : S.card ≤ r)
    (x : ∀ i, σ → ZMod (q i)) (hx : ∀ i ∈ K, x i = base i)
    (hsmall : (∑ j, ((∏ i ∈ S, q i.val : ℕ) : ℝ) /
      residueIndexLength (lo j) (lo j + N j) (M.lcm (∏ i ∈ K, q i)) ((u.val j).val)) < 1 / 2) :
    productConditionalMean (primeCoordinateReference (σ := σ) q) (K ∪ S.image Subtype.val)
      (residuePrimeCoordinateDensity lo N M a ⟨u.val⟩ q (fun z => (h z).re)) x ≤
      residuePrimeCoordinateMassRatio lo N M a q K base *
        (level * (residuePrimeCoordinateMean g lo N M a q K base).re + ε + level * δ +
          (2 * ∑ j, ((∏ i ∈ S, q i.val : ℕ) : ℝ) /
            residueIndexLength (lo j) (lo j + N j) (M.lcm (∏ i ∈ K, q i)) ((u.val j).val)) * C) := by
  rw [residuePrimeCoordinateDensity_conditional_outside lo N M a ⟨u.val⟩ q hpair K base u
    (fun z => (h z).re) S x hx]
  exact mul_le_mul_of_nonneg_left
    (hupper.reference_density_upper hM hpair hcop u C hC hh S hS (fun i => x i.val) hsmall)
    (residuePrimeCoordinateMassRatio_nonneg lo N M a q K base)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem residueCellOutsideDensity_norm_of_lengths {ι σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ) [∀ i, NeZero (q i)]
    (hM : 0 < M) (hpair : Pairwise (fun i k => (q i).Coprime (q k)))
    (K : Finset ι) (base : ∀ i, σ → ZMod (q i)) (hcop : ∀ i ∉ K, M.Coprime (q i))
    (u : ResiduePrimeCoordinateCell lo N M a q K base) (f : (σ → ℤ) → ℝ)
    (hf : ∀ z : ResiduePrimeCoordinateCell lo N M a q K base,
      0 ≤ f (fun k => (z.val k).val) ∧ f (fun k => (z.val k).val) ≤ 1)
    (B : ℕ) (P modLog dimLog : ℝ) (hP : 0 ≤ P) (hmodLog : 0 ≤ modLog)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hmoduli : ∀ i ∉ K, (q i : ℝ) ≤ Real.exp modLog)
    (hdim : (Fintype.card σ : ℝ) ≤ Real.exp dimLog)
    (hlength : ∀ k, Real.exp (modLog * (2 * B : ℕ) + affineComparisonAccuracyLog B P 0 0 + dimLog + 1) ≤
      (residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val) : ℝ)) :
    Real.sqrt (productANOVAEnergy (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val))
      (lowDegreeCoordinateSets {i // i ∉ K} B) (residueCellOutsideDensity lo N M a q K base u f)) ≤ 3 := by
  let η := affineComparisonAccuracy B P 0 0
  let μ := primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val)
  let p := @FiniteProbabilityWeights.uniform (ResiduePrimeCoordinateCell lo N M a q K base) _ ⟨u⟩
  let F := fun z : ResiduePrimeCoordinateCell lo N M a q K base =>
    primeCoordinateObservation (fun i : {i // i ∉ K} => q i.val) (fun k => (z.val k).val)
  have he := affineComparisonAccuracy_bounds (level := 1) (L := 0) (T := 0) B hP (by norm_num) (by norm_num) (by norm_num)
  have hcount' : (Fintype.card {i // i ∉ K} : ℝ) ≤ Real.exp P :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hcount
  have hgram : 2 * η * ((lowDegreeCoordinateSets {i // i ∉ K} B).card : ℝ) ^ 2 *
      (4 : ℝ) ^ B * (1 + η) ^ 2 ≤ 1 := by
    simpa only [neg_zero, Real.exp_zero] using
      affineComparisonAccuracy_gram (ι := {i // i ∉ K}) (L := 0) (T := 0) B hP (by norm_num) (by norm_num) hcount'
  have hbase0 := retained_residue_marginals_of_lengths (ι := ι) (σ := σ)
    lo N M a q hM hpair K base hcop u (2 * B) modLog dimLog (affineComparisonAccuracyLog B P 0 0) η
  have herror : Real.exp (-affineComparisonAccuracyLog B P 0 0) ≤ η := by
    unfold η affineComparisonAccuracy
    exact le_rfl
  have hbase := (hbase0 hmodLog he.2.1.le herror hmoduli hdim hlength).1
  have hclose : ProductMarginalsClose μ (residueCellOutsideDensity lo N M a q K base u (fun _ => 1)) η (2 * B) := by
    rw [residueCellOutsideDensity_lcm lo N M a q hpair K base u]
    exact hbase
  change ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (2 * B) at hclose
  have hz : (FiniteProbabilityWeights.pi μ).weight (fun _ _ => 0) ≠ 0 :=
    (Finset.prod_pos (fun i _ => primeCoordinateReference_weight_pos (fun i : {i // i ∉ K} => q i.val) i (fun _ => 0))).ne'
  have hn := observedProductDensity_section_norm_le_three μ p F (fun z => f (fun k => (z.val k).val)) hf
    ∅ ∅ (Finset.Subset.refl ∅) (fun _ _ => 0) hz he.1.le he.2.1.le
    (lowDegreeCoordinateSets {i // i ∉ K} B) (fun S hS => (mem_lowDegreeCoordinateSets _ _ S).mp hS)
    (by simpa only [Finset.card_empty, add_zero] using hclose) hgram
  rw [productSectionAverage_empty_fixed] at hn
  exact hn

end Erdos3

end

end OAI
