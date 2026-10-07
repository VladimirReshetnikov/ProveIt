/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Dynamics.InitialConditioningBudget
import OAI.Combinatorics.Progressions.Geometry.OutsideProductTransport
import OAI.Combinatorics.Progressions.Lattices.ResidueCellNormLengths
import OAI.Combinatorics.Progressions.Lattices.RetainedPhysicalCRT

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)]
    (hpair : Pairwise (fun i k => (q i).Coprime (q k)))
    (K : Finset ι) (base : ∀ i, σ → ZMod (q i))
    (u : ResiduePrimeCoordinateCell lo N M a q K base)

include hpair u

theorem residuePrimeCoordinateDensity_fixed (f : (σ → ℤ) → ℝ)
    (x : ∀ i, σ → ZMod (q i)) (hx : ∀ i ∈ K, x i = base i) :
    residuePrimeCoordinateDensity lo N M a hne q f x =
      residuePrimeCoordinateMassRatio lo N M a q K base *
        residueCellOutsideDensity lo N M a q K base u f (fun i => x i.val) := by
  have hcover : K ∪ (Finset.univ : Finset {i // i ∉ K}).image Subtype.val = Finset.univ := by
    ext i
    by_cases hi : i ∈ K
    · simp [hi]
    · simp only [Finset.mem_union, hi, false_or, Finset.mem_image, Finset.mem_univ, iff_true]
      exact ⟨⟨i, hi⟩, trivial, rfl⟩
  have h := residuePrimeCoordinateDensity_conditional_outside lo N M a hne q hpair K base u f
    (Finset.univ : Finset {i // i ∉ K}) x hx
  rw [hcover, productConditionalMean_univ, productConditionalMean_univ] at h
  rw [residueCellOutsideDensity_lcm lo N M a q hpair K base u f]
  exact h

theorem residuePrimeCoordinateDensity_section (f : (σ → ℤ) → ℝ) (x : ∀ i, σ → ZMod (q i)) :
    productSectionAverage (primeCoordinateReference (σ := σ) q) K K base
      (residuePrimeCoordinateDensity lo N M a hne q f) x =
      residuePrimeCoordinateMassRatio lo N M a q K base *
        residueCellOutsideDensity lo N M a q K base u f (fun i => x i.val) := by
  have hx : ∀ i ∈ K, productCoordinateMix K base x i = base i := by
    intro i hi
    simp only [productCoordinateMix, hi, ite_true]
  have hout : (fun i : {i // i ∉ K} => productCoordinateMix K base x i.val) = (fun i : {i // i ∉ K} => x i.val) := by
    funext i
    simp only [productCoordinateMix, i.property, ite_false]
  rw [productSectionAverage_eq_conditionalMean _ K K (Finset.Subset.refl K)]
  simp only [Finset.union_compl, productConditionalMean_univ]
  rw [residuePrimeCoordinateDensity_fixed lo N M a hne q hpair K base u f _ hx, hout]

omit hne hpair in
theorem residuePrimeCoordinateMassRatio_pos : 0 < residuePrimeCoordinateMassRatio lo N M a q K base := by
  let : Nonempty (ResiduePrimeCoordinateCell lo N M a q K base) := ⟨u⟩
  let : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a) := ⟨u.val⟩
  have hp : 0 < ∏ i ∈ K, q i := Finset.prod_pos (fun i _ => Nat.pos_of_ne_zero (NeZero.ne (q i)))
  rw [residuePrimeCoordinateMassRatio_eq_count]
  positivity

theorem residuePrimeCoordinateDensity_normalized_section (f : (σ → ℤ) → ℝ)
    (x : ∀ i, σ → ZMod (q i)) :
    (residuePrimeCoordinateMassRatio lo N M a q K base)⁻¹ *
      productSectionAverage (primeCoordinateReference (σ := σ) q) K K base
        (residuePrimeCoordinateDensity lo N M a hne q f) x =
      residueCellOutsideDensity lo N M a q K base u f (fun i => x i.val) := by
  rw [residuePrimeCoordinateDensity_section lo N M a hne q hpair K base u f x,
    ← mul_assoc, inv_mul_cancel₀ (residuePrimeCoordinateMassRatio_pos lo N M a q K base u).ne', one_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem residuePrimeCoordinateMassRatio_le_prime_product {ι σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ) [∀ i, NeZero (q i)]
    (K : Finset ι) (base : ∀ i, σ → ZMod (q i))
    (u : ResiduePrimeCoordinateCell lo N M a q K base) :
    residuePrimeCoordinateMassRatio lo N M a q K base ≤ ((∏ i ∈ K, q i : ℕ) : ℝ) ^ Fintype.card σ := by
  let : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a) := ⟨u.val⟩
  have hB : (0 : ℝ) < Fintype.card (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a) := by
    exact_mod_cast Fintype.card_pos
  have hcard : (Fintype.card (ResiduePrimeCoordinateCell lo N M a q K base) : ℝ) ≤
      Fintype.card (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a) :=
    Nat.cast_le.mpr (Fintype.card_subtype_le _)
  have hratio : (Fintype.card (ResiduePrimeCoordinateCell lo N M a q K base) : ℝ) /
      Fintype.card (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a) ≤ 1 := by
    apply (div_le_iff₀ hB).mpr
    simpa only [one_mul] using hcard
  rw [residuePrimeCoordinateMassRatio_eq_count, mul_div_assoc]
  exact mul_le_of_le_one_right (by positivity) hratio

theorem residuePrimeCoordinateMassRatio_le_exp {ι σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ) [∀ i, NeZero (q i)]
    (K : Finset ι) (base : ∀ i, σ → ZMod (q i))
    (u : ResiduePrimeCoordinateCell lo N M a q K base) (modLog : ℝ)
    (hmoduli : ∀ i, (q i : ℝ) ≤ Real.exp modLog) :
    residuePrimeCoordinateMassRatio lo N M a q K base ≤
      Real.exp ((K.card : ℝ) * Fintype.card σ * modLog) := by
  have hprod := primeCoordinateProduct_le_exp q K modLog hmoduli
  calc
    _ ≤ ((∏ i ∈ K, q i : ℕ) : ℝ) ^ Fintype.card σ :=
      residuePrimeCoordinateMassRatio_le_prime_product lo N M a q K base u
    _ ≤ (Real.exp (modLog * K.card)) ^ Fintype.card σ :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hprod _
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem residuePrimeCoordinateDensity_section_norm {ι σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hpair : Pairwise (fun i k => (q i).Coprime (q k)))
    (K : Finset ι) (base : ∀ i, σ → ZMod (q i))
    (u : ResiduePrimeCoordinateCell lo N M a q K base) (f : (σ → ℤ) → ℝ) (B : ℕ) :
    Real.sqrt (productANOVAEnergy (primeCoordinateReference (σ := σ) q) (lowDegreeCoordinateSets ι B)
      (productSectionAverage (primeCoordinateReference (σ := σ) q) K K base
        (residuePrimeCoordinateDensity lo N M a hne q f))) =
      residuePrimeCoordinateMassRatio lo N M a q K base *
        Real.sqrt (productANOVAEnergy (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val))
          (lowDegreeCoordinateSets {i // i ∉ K} B) (residueCellOutsideDensity lo N M a q K base u f)) := by
  have hs := funext (residuePrimeCoordinateDensity_section lo N M a hne q hpair K base u f)
  rw [hs, sqrt_productANOVAEnergy_smul,
    productANOVAEnergy_outside (primeCoordinateReference (σ := σ) q) K base B,
    abs_of_nonneg (residuePrimeCoordinateMassRatio_pos lo N M a q K base u).le]
  rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem residueSectionPairing_core {ι σ τ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
    (loX : σ → ℤ) (NX : σ → ℕ) (MX : ℕ) (aX : σ → ℤ)
    (hneX : Nonempty (IntegerResidueBox loX (fun k => loX k + NX k) (fun _ => (MX : ℤ)) aX))
    (loY : τ → ℤ) (NY : τ → ℕ) (MY : ℕ) (aY : τ → ℤ)
    (hneY : Nonempty (IntegerResidueBox loY (fun k => loY k + NY k) (fun _ => (MY : ℤ)) aY))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hpair : Pairwise (fun i k => (q i).Coprime (q k)))
    (K : Finset ι) (baseX : ∀ i, σ → ZMod (q i)) (baseY : ∀ i, τ → ZMod (q i))
    (uX : ResiduePrimeCoordinateCell loX NX MX aX q K baseX)
    (uY : ResiduePrimeCoordinateCell loY NY MY aY q K baseY)
    (c : ∀ i, FiniteProbabilityCoupling (primeCoordinateReference (σ := σ) q i) (primeCoordinateReference (σ := τ) q i))
    (w : (σ → ℤ) → ℝ) (f : (τ → ℤ) → ℝ) (B : ℕ) :
    productTruncatedPairing c (conditioningCoreSupports K B)
      (productSectionAverage (primeCoordinateReference (σ := σ) q) K K baseX (residuePrimeCoordinateDensity loX NX MX aX hneX q w))
      (productSectionAverage (primeCoordinateReference (σ := τ) q) K K baseY (residuePrimeCoordinateDensity loY NY MY aY hneY q f)) =
      residuePrimeCoordinateMassRatio loX NX MX aX q K baseX * residuePrimeCoordinateMassRatio loY NY MY aY q K baseY *
        productTruncatedPairing (fun i : {i // i ∉ K} => c i.val)
          (lowDegreeCoordinateSets {i // i ∉ K} (B - K.card))
          (residueCellOutsideDensity loX NX MX aX q K baseX uX w)
          (residueCellOutsideDensity loY NY MY aY q K baseY uY f) := by
  have hx := funext (residuePrimeCoordinateDensity_section loX NX MX aX hneX q hpair K baseX uX w)
  have hy := funext (residuePrimeCoordinateDensity_section loY NY MY aY hneY q hpair K baseY uY f)
  rw [hx, hy, productTruncatedPairing_smul, productTruncatedPairing_outside_core c K baseX baseY B]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem residue_initial_conditioning_shell {ι σ τ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
    (loX : σ → ℤ) (NX : σ → ℕ) (MX : ℕ) (aX : σ → ℤ)
    (hneX : Nonempty (IntegerResidueBox loX (fun k => loX k + NX k) (fun _ => (MX : ℤ)) aX))
    (loY : τ → ℤ) (NY : τ → ℕ) (MY : ℕ) (aY : τ → ℤ)
    (hneY : Nonempty (IntegerResidueBox loY (fun k => loY k + NY k) (fun _ => (MY : ℤ)) aY))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hpair : Pairwise (fun i k => (q i).Coprime (q k)))
    (K : Finset ι) (baseX : ∀ i, σ → ZMod (q i)) (baseY : ∀ i, τ → ZMod (q i))
    (uX : ResiduePrimeCoordinateCell loX NX MX aX q K baseX)
    (uY : ResiduePrimeCoordinateCell loY NY MY aY q K baseY)
    (kernel : ∀ i, (σ → ZMod (q i)) → FiniteProbabilityWeights (τ → ZMod (q i)))
    (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (f : (τ → ZMod (q i)) → ℝ), (primeCoordinateReference (σ := τ) q i).mean f = 0 →
      (primeCoordinateReference (σ := σ) q i).mean (fun x => (kernel i x).mean f ^ 2) ≤
        C i * (primeCoordinateReference (σ := τ) q i).mean (fun y => f y ^ 2))
    (hmean : ∀ i (f : (τ → ZMod (q i)) → ℝ),
      (primeCoordinateReference (σ := σ) q i).mean (fun x => (kernel i x).mean f) =
        (primeCoordinateReference (σ := τ) q i).mean f)
    (w : (σ → ℤ) → ℝ) (f : (τ → ℤ) → ℝ) (B : ℕ) (hKB : K.card ≤ B)
    {κ sourceNorm siteNorm : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hcap : ∀ i ∉ K, C i ≤ κ ^ 2)
    (hsourceNorm : Real.sqrt (productANOVAEnergy
      (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val))
      (lowDegreeCoordinateSets {i // i ∉ K} B) (residueCellOutsideDensity loX NX MX aX q K baseX uX w)) ≤ sourceNorm)
    (hsiteNorm : Real.sqrt (productANOVAEnergy
      (primeCoordinateReference (σ := τ) (fun i : {i // i ∉ K} => q i.val))
      (lowDegreeCoordinateSets {i // i ∉ K} B) (residueCellOutsideDensity loY NY MY aY q K baseY uY f)) ≤ siteNorm) :
    let c := fun i => FiniteProbabilityCoupling.ofKernel (primeCoordinateReference (σ := σ) q i)
      (primeCoordinateReference (σ := τ) q i) (kernel i) (hmean i)
    |productAtomTruncatedPairing c (lowDegreeCoordinateSets ι B) K baseX baseY
        (residuePrimeCoordinateDensity loX NX MX aX hneX q w) (residuePrimeCoordinateDensity loY NY MY aY hneY q f) -
      productCouplingAtomMass c K baseX baseY *
        (residuePrimeCoordinateMassRatio loX NX MX aX q K baseX * residuePrimeCoordinateMassRatio loY NY MY aY q K baseY *
          productTruncatedPairing (fun i : {i // i ∉ K} => c i.val)
            (lowDegreeCoordinateSets {i // i ∉ K} (B - K.card))
            (residueCellOutsideDensity loX NX MX aX q K baseX uX w)
            (residueCellOutsideDensity loY NY MY aY q K baseY uY f))| ≤
      (2 : ℝ) ^ K.card * (κ ^ (B - K.card) *
        (residuePrimeCoordinateMassRatio loX NX MX aX q K baseX * sourceNorm) *
        (residuePrimeCoordinateMassRatio loY NY MY aY q K baseY * siteNorm)) := by
  let μ := primeCoordinateReference (σ := σ) q
  let ν := primeCoordinateReference (σ := τ) q
  let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (kernel i) (hmean i)
  have hx : Real.sqrt (productANOVAEnergy μ (lowDegreeCoordinateSets ι B)
      (productSectionAverage μ K K baseX (residuePrimeCoordinateDensity loX NX MX aX hneX q w))) ≤
      residuePrimeCoordinateMassRatio loX NX MX aX q K baseX * sourceNorm := by
    rw [residuePrimeCoordinateDensity_section_norm loX NX MX aX hneX q hpair K baseX uX w B]
    exact mul_le_mul_of_nonneg_left hsourceNorm (residuePrimeCoordinateMassRatio_pos loX NX MX aX q K baseX uX).le
  have hy : Real.sqrt (productANOVAEnergy ν (lowDegreeCoordinateSets ι B)
      (productSectionAverage ν K K baseY (residuePrimeCoordinateDensity loY NY MY aY hneY q f))) ≤
      residuePrimeCoordinateMassRatio loY NY MY aY q K baseY * siteNorm := by
    rw [residuePrimeCoordinateDensity_section_norm loY NY MY aY hneY q hpair K baseY uY f B]
    exact mul_le_mul_of_nonneg_left hsiteNorm (residuePrimeCoordinateMassRatio_pos loY NY MY aY q K baseY uY).le
  have hshell := productKernel_conditioning_shell_of_truncated μ ν kernel C hC hbound hmean K B hKB
    hκ0 hκ1 hcap baseX baseY
    (residuePrimeCoordinateDensity loX NX MX aX hneX q w) (residuePrimeCoordinateDensity loY NY MY aY hneY q f) hx hy
  change |productAtomTruncatedPairing c (lowDegreeCoordinateSets ι B) K baseX baseY
      (residuePrimeCoordinateDensity loX NX MX aX hneX q w) (residuePrimeCoordinateDensity loY NY MY aY hneY q f) -
    productCouplingAtomMass c K baseX baseY * productTruncatedPairing c (conditioningCoreSupports K B)
      (productSectionAverage μ K K baseX (residuePrimeCoordinateDensity loX NX MX aX hneX q w))
      (productSectionAverage ν K K baseY (residuePrimeCoordinateDensity loY NY MY aY hneY q f))| ≤ _ at hshell
  rw [residueSectionPairing_core loX NX MX aX hneX loY NY MY aY hneY q hpair K baseX baseY uX uY c w f B] at hshell
  exact hshell

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem residue_initial_conditioning_shell_of_lengths {ι σ τ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
    (loX : σ → ℤ) (NX : σ → ℕ) (MX : ℕ) (aX : σ → ℤ)
    (hneX : Nonempty (IntegerResidueBox loX (fun k => loX k + NX k) (fun _ => (MX : ℤ)) aX))
    (loY : τ → ℤ) (NY : τ → ℕ) (MY : ℕ) (aY : τ → ℤ)
    (hneY : Nonempty (IntegerResidueBox loY (fun k => loY k + NY k) (fun _ => (MY : ℤ)) aY))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hpair : Pairwise (fun i k => (q i).Coprime (q k)))
    (K : Finset ι) (baseX : ∀ i, σ → ZMod (q i)) (baseY : ∀ i, τ → ZMod (q i))
    (uX : ResiduePrimeCoordinateCell loX NX MX aX q K baseX)
    (uY : ResiduePrimeCoordinateCell loY NY MY aY q K baseY)
    (kernel : ∀ i, (σ → ZMod (q i)) → FiniteProbabilityWeights (τ → ZMod (q i)))
    (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (f : (τ → ZMod (q i)) → ℝ), (primeCoordinateReference (σ := τ) q i).mean f = 0 →
      (primeCoordinateReference (σ := σ) q i).mean (fun x => (kernel i x).mean f ^ 2) ≤
        C i * (primeCoordinateReference (σ := τ) q i).mean (fun y => f y ^ 2))
    (hmean : ∀ i (f : (τ → ZMod (q i)) → ℝ),
      (primeCoordinateReference (σ := σ) q i).mean (fun x => (kernel i x).mean f) =
        (primeCoordinateReference (σ := τ) q i).mean f)
    (w : (σ → ℤ) → ℝ) (f : (τ → ℤ) → ℝ) (B : ℕ) (hKB : K.card ≤ B)
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hcap : ∀ i ∉ K, C i ≤ κ ^ 2)
    (hMX : 0 < MX) (hMY : 0 < MY)
    (hcopX : ∀ i ∉ K, MX.Coprime (q i)) (hcopY : ∀ i ∉ K, MY.Coprime (q i))
    (hw : ∀ z : ResiduePrimeCoordinateCell loX NX MX aX q K baseX,
      0 ≤ w (fun k => (z.val k).val) ∧ w (fun k => (z.val k).val) ≤ 1)
    (hf : ∀ z : ResiduePrimeCoordinateCell loY NY MY aY q K baseY,
      0 ≤ f (fun k => (z.val k).val) ∧ f (fun k => (z.val k).val) ≤ 1)
    (P modLog dimX dimY : ℝ) (hP : 0 ≤ P) (hmodLog : 0 ≤ modLog)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hmoduli : ∀ i ∉ K, (q i : ℝ) ≤ Real.exp modLog)
    (hdimX : (Fintype.card σ : ℝ) ≤ Real.exp dimX) (hdimY : (Fintype.card τ : ℝ) ≤ Real.exp dimY)
    (hlengthX : ∀ k, Real.exp (modLog * (2 * B : ℕ) + affineComparisonAccuracyLog B P 0 0 + dimX + 1) ≤
      (residueIndexLength (loX k) (loX k + NX k) (MX.lcm (∏ i ∈ K, q i)) ((uX.val k).val) : ℝ))
    (hlengthY : ∀ k, Real.exp (modLog * (2 * B : ℕ) + affineComparisonAccuracyLog B P 0 0 + dimY + 1) ≤
      (residueIndexLength (loY k) (loY k + NY k) (MY.lcm (∏ i ∈ K, q i)) ((uY.val k).val) : ℝ)) :
    let c := fun i => FiniteProbabilityCoupling.ofKernel (primeCoordinateReference (σ := σ) q i)
      (primeCoordinateReference (σ := τ) q i) (kernel i) (hmean i)
    |productAtomTruncatedPairing c (lowDegreeCoordinateSets ι B) K baseX baseY
        (residuePrimeCoordinateDensity loX NX MX aX hneX q w) (residuePrimeCoordinateDensity loY NY MY aY hneY q f) -
      productCouplingAtomMass c K baseX baseY *
        (residuePrimeCoordinateMassRatio loX NX MX aX q K baseX * residuePrimeCoordinateMassRatio loY NY MY aY q K baseY *
          productTruncatedPairing (fun i : {i // i ∉ K} => c i.val)
            (lowDegreeCoordinateSets {i // i ∉ K} (B - K.card))
            (residueCellOutsideDensity loX NX MX aX q K baseX uX w)
            (residueCellOutsideDensity loY NY MY aY q K baseY uY f))| ≤
      (2 : ℝ) ^ K.card * (κ ^ (B - K.card) *
        (residuePrimeCoordinateMassRatio loX NX MX aX q K baseX * 3) *
        (residuePrimeCoordinateMassRatio loY NY MY aY q K baseY * 3)) := by
  have hx := residueCellOutsideDensity_norm_of_lengths (ι := ι) (σ := σ)
    loX NX MX aX q hMX hpair K baseX hcopX uX w hw B P modLog dimX hP hmodLog hcount hmoduli hdimX hlengthX
  have hy := residueCellOutsideDensity_norm_of_lengths (ι := ι) (σ := τ)
    loY NY MY aY q hMY hpair K baseY hcopY uY f hf B P modLog dimY hP hmodLog hcount hmoduli hdimY hlengthY
  exact residue_initial_conditioning_shell loX NX MX aX hneX loY NY MY aY hneY q hpair K baseX baseY uX uY
    kernel C hC hbound hmean w f B hKB hκ0 hκ1 hcap hx hy

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem residue_initial_conditioning_shell_small {ι σ τ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
    (loX : σ → ℤ) (NX : σ → ℕ) (MX : ℕ) (aX : σ → ℤ)
    (hneX : Nonempty (IntegerResidueBox loX (fun k => loX k + NX k) (fun _ => (MX : ℤ)) aX))
    (loY : τ → ℤ) (NY : τ → ℕ) (MY : ℕ) (aY : τ → ℤ)
    (hneY : Nonempty (IntegerResidueBox loY (fun k => loY k + NY k) (fun _ => (MY : ℤ)) aY))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hpair : Pairwise (fun i k => (q i).Coprime (q k)))
    (K : Finset ι) (baseX : ∀ i, σ → ZMod (q i)) (baseY : ∀ i, τ → ZMod (q i))
    (uX : ResiduePrimeCoordinateCell loX NX MX aX q K baseX)
    (uY : ResiduePrimeCoordinateCell loY NY MY aY q K baseY)
    (kernel : ∀ i, (σ → ZMod (q i)) → FiniteProbabilityWeights (τ → ZMod (q i)))
    (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (f : (τ → ZMod (q i)) → ℝ), (primeCoordinateReference (σ := τ) q i).mean f = 0 →
      (primeCoordinateReference (σ := σ) q i).mean (fun x => (kernel i x).mean f ^ 2) ≤
        C i * (primeCoordinateReference (σ := τ) q i).mean (fun y => f y ^ 2))
    (hmean : ∀ i (f : (τ → ZMod (q i)) → ℝ),
      (primeCoordinateReference (σ := σ) q i).mean (fun x => (kernel i x).mean f) =
        (primeCoordinateReference (σ := τ) q i).mean f)
    (w : (σ → ℤ) → ℝ) (f : (τ → ℤ) → ℝ) (B : ℕ)
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2) (hcap : ∀ i ∉ K, C i ≤ κ ^ 2)
    (hMX : 0 < MX) (hMY : 0 < MY)
    (hcopX : ∀ i ∉ K, MX.Coprime (q i)) (hcopY : ∀ i ∉ K, MY.Coprime (q i))
    (hw : ∀ z : ResiduePrimeCoordinateCell loX NX MX aX q K baseX,
      0 ≤ w (fun k => (z.val k).val) ∧ w (fun k => (z.val k).val) ≤ 1)
    (hf : ∀ z : ResiduePrimeCoordinateCell loY NY MY aY q K baseY,
      0 ≤ f (fun k => (z.val k).val) ∧ f (fun k => (z.val k).val) ≤ 1)
    (P modLog dimX dimY : ℝ) (hP : 0 ≤ P) (hmodLog : 0 ≤ modLog)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hmoduli : ∀ i, (q i : ℝ) ≤ Real.exp modLog)
    (hdimX : (Fintype.card σ : ℝ) ≤ Real.exp dimX) (hdimY : (Fintype.card τ : ℝ) ≤ Real.exp dimY)
    (hlengthX : ∀ k, Real.exp (modLog * (2 * B : ℕ) + affineComparisonAccuracyLog B P 0 0 + dimX + 1) ≤
      (residueIndexLength (loX k) (loX k + NX k) (MX.lcm (∏ i ∈ K, q i)) ((uX.val k).val) : ℝ))
    (hlengthY : ∀ k, Real.exp (modLog * (2 * B : ℕ) + affineComparisonAccuracyLog B P 0 0 + dimY + 1) ≤
      (residueIndexLength (loY k) (loY k + NY k) (MY.lcm (∏ i ∈ K, q i)) ((uY.val k).val) : ℝ))
    (shell : ℝ) (hshell : 0 < shell)
    (hB : K.card + CyclicCrootSisask.spectralIterations shell
      ((K.card : ℝ) * ((Fintype.card σ : ℝ) * modLog + (Fintype.card τ : ℝ) * modLog + 1) + 4) ≤ B) :
    let c := fun i => FiniteProbabilityCoupling.ofKernel (primeCoordinateReference (σ := σ) q i)
      (primeCoordinateReference (σ := τ) q i) (kernel i) (hmean i)
    |productAtomTruncatedPairing c (lowDegreeCoordinateSets ι B) K baseX baseY
        (residuePrimeCoordinateDensity loX NX MX aX hneX q w) (residuePrimeCoordinateDensity loY NY MY aY hneY q f) -
      productCouplingAtomMass c K baseX baseY *
        (residuePrimeCoordinateMassRatio loX NX MX aX q K baseX * residuePrimeCoordinateMassRatio loY NY MY aY q K baseY *
          productTruncatedPairing (fun i : {i // i ∉ K} => c i.val)
            (lowDegreeCoordinateSets {i // i ∉ K} (B - K.card))
            (residueCellOutsideDensity loX NX MX aX q K baseX uX w)
            (residueCellOutsideDensity loY NY MY aY q K baseY uY f))| ≤ shell / 16 := by
  have hsmallX : residuePrimeCoordinateMassRatio loX NX MX aX q K baseX ≤
      Real.exp ((K.card : ℝ) * ((Fintype.card σ : ℝ) * modLog)) := by
    simpa only [mul_assoc] using residuePrimeCoordinateMassRatio_le_exp loX NX MX aX q K baseX uX modLog hmoduli
  have hsmallY : residuePrimeCoordinateMassRatio loY NY MY aY q K baseY ≤
      Real.exp ((K.card : ℝ) * ((Fintype.card τ : ℝ) * modLog)) := by
    simpa only [mul_assoc] using residuePrimeCoordinateMassRatio_le_exp loY NY MY aY q K baseY uY modLog hmoduli
  have hbudget := initial_conditioning_error_small K.card B
    (residuePrimeCoordinateMassRatio_pos loX NX MX aX q K baseX uX).le
    (residuePrimeCoordinateMassRatio_pos loY NY MY aY q K baseY uY).le
    hsmallX hsmallY hκ0 hκhalf hshell hB
  have hresult := residue_initial_conditioning_shell_of_lengths
    loX NX MX aX hneX loY NY MY aY hneY q hpair K baseX baseY uX uY kernel C hC hbound hmean
    w f B (by omega) hκ0 (by linarith) hcap hMX hMY hcopX hcopY hw hf P modLog dimX dimY hP hmodLog
    hcount (fun i _ => hmoduli i) hdimX hdimY hlengthX hlengthY
  exact hresult.trans hbudget

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem affine_period_initial_conditioning_shell_small {ι J σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype J] [Fintype σ]
    (loX : (Option J × σ) → ℤ) (NX : (Option J × σ) → ℕ) (MX : ℕ) (aX : (Option J × σ) → ℤ)
    (hneX : Nonempty (IntegerResidueBox loX (fun k => loX k + NX k) (fun _ => (MX : ℤ)) aX))
    (loY : σ → ℤ) (NY : σ → ℕ) (MY : ℕ) (aY : σ → ℤ)
    (hneY : Nonempty (IntegerResidueBox loY (fun k => loY k + NY k) (fun _ => (MY : ℤ)) aY))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hpair : Pairwise (fun i k => (q i).Coprime (q k)))
    (K : Finset ι) (baseX : ∀ i, (Option J × σ) → ZMod (q i)) (baseY : ∀ i, σ → ZMod (q i))
    (uX : ResiduePrimeCoordinateCell loX NX MX aX q K baseX)
    (uY : ResiduePrimeCoordinateCell loY NY MY aY q K baseY)
    (D : ℕ) (a : J → ℤ) (hDcop : ∀ i ∉ K, D.Coprime (q i))
    (prime power : ι → ℕ) (hprime : ∀ i, (prime i).Prime)
    (hpower : ∀ i, q i = prime i ^ power i) (hJ : 2 ≤ Fintype.card J)
    (w : ((Option J × σ) → ℤ) → ℝ) (f : (σ → ℤ) → ℝ) (B : ℕ)
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2) (hlarge : ∀ i ∉ K, (prime i : ℝ)⁻¹ ≤ κ)
    (hMX : 0 < MX) (hMY : 0 < MY)
    (hcopX : ∀ i ∉ K, MX.Coprime (q i)) (hcopY : ∀ i ∉ K, MY.Coprime (q i))
    (hw : ∀ z : ResiduePrimeCoordinateCell loX NX MX aX q K baseX,
      0 ≤ w (fun k => (z.val k).val) ∧ w (fun k => (z.val k).val) ≤ 1)
    (hf : ∀ z : ResiduePrimeCoordinateCell loY NY MY aY q K baseY,
      0 ≤ f (fun k => (z.val k).val) ∧ f (fun k => (z.val k).val) ≤ 1)
    (P modLog dimX dimY : ℝ) (hP : 0 ≤ P) (hmodLog : 0 ≤ modLog)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hmoduli : ∀ i, (q i : ℝ) ≤ Real.exp modLog)
    (hdimX : (Fintype.card (Option J × σ) : ℝ) ≤ Real.exp dimX) (hdimY : (Fintype.card σ : ℝ) ≤ Real.exp dimY)
    (hlengthX : ∀ k, Real.exp (modLog * (2 * B : ℕ) + affineComparisonAccuracyLog B P 0 0 + dimX + 1) ≤
      (residueIndexLength (loX k) (loX k + NX k) (MX.lcm (∏ i ∈ K, q i)) ((uX.val k).val) : ℝ))
    (hlengthY : ∀ k, Real.exp (modLog * (2 * B : ℕ) + affineComparisonAccuracyLog B P 0 0 + dimY + 1) ≤
      (residueIndexLength (loY k) (loY k + NY k) (MY.lcm (∏ i ∈ K, q i)) ((uY.val k).val) : ℝ))
    (shell : ℝ) (hshell : 0 < shell)
    (hB : K.card + CyclicCrootSisask.spectralIterations shell
      ((K.card : ℝ) * ((Fintype.card (Option J × σ) : ℝ) * modLog + (Fintype.card σ : ℝ) * modLog + 1) + 4) ≤ B) :
    let c := affinePeriodProductCoupling (σ := σ) q D a
    |productAtomTruncatedPairing c (lowDegreeCoordinateSets ι B) K baseX baseY
        (residuePrimeCoordinateDensity loX NX MX aX hneX q w) (residuePrimeCoordinateDensity loY NY MY aY hneY q f) -
      productCouplingAtomMass c K baseX baseY *
        (residuePrimeCoordinateMassRatio loX NX MX aX q K baseX * residuePrimeCoordinateMassRatio loY NY MY aY q K baseY *
          affineResidueTruncatedPairing (J := J) (σ := σ) (fun i : {i // i ∉ K} => q i.val)
            (lowDegreeCoordinateSets {i // i ∉ K} (B - K.card))
            (residueCellOutsideDensity loX NX MX aX q K baseX uX w)
            (residueCellOutsideDensity loY NY MY aY q K baseY uY f))| ≤ shell / 16 := by
  let kernel := fun i => affineSampleParameterKernel (I := σ) (affinePeriodParameterLaw (q := q i) D a)
  let C := fun i => if i ∈ K then (1 : ℝ) else κ ^ 2
  have hC (i : ι) : 0 ≤ C i := by
    dsimp only [C]
    split_ifs <;> positivity
  have hbound := affinePeriodParameterKernel_centered_sq (σ := σ) q D a K prime power
    hprime hpower hDcop hκ0 hJ hlarge
  have hmean := fun i => affineSampleParameterKernel_preserves_mean (I := σ)
    (affinePeriodParameterLaw (q := q i) D a)
  have hcap (i : ι) (hi : i ∉ K) : C i ≤ κ ^ 2 := by simp only [C, ite_eq_right hi, le_refl]
  have hresult := residue_initial_conditioning_shell_small
    loX NX MX aX hneX loY NY MY aY hneY q hpair K baseX baseY uX uY
    kernel C hC hbound hmean w f B hκ0 hκhalf hcap hMX hMY hcopX hcopY hw hf
    P modLog dimX dimY hP hmodLog hcount hmoduli hdimX hdimY hlengthX hlengthY shell hshell hB
  change
    |productAtomTruncatedPairing (affinePeriodProductCoupling (σ := σ) q D a) (lowDegreeCoordinateSets ι B) K baseX baseY
        (residuePrimeCoordinateDensity loX NX MX aX hneX q w) (residuePrimeCoordinateDensity loY NY MY aY hneY q f) -
      productCouplingAtomMass (affinePeriodProductCoupling (σ := σ) q D a) K baseX baseY *
        (residuePrimeCoordinateMassRatio loX NX MX aX q K baseX * residuePrimeCoordinateMassRatio loY NY MY aY q K baseY *
          productTruncatedPairing (fun i : {i // i ∉ K} => affinePeriodProductCoupling (σ := σ) q D a i.val)
            (lowDegreeCoordinateSets {i // i ∉ K} (B - K.card))
            (residueCellOutsideDensity loX NX MX aX q K baseX uX w)
            (residueCellOutsideDensity loY NY MY aY q K baseY uY f))| ≤ shell / 16 at hresult
  rw [affinePeriodProductCoupling_outside q D a K hDcop] at hresult
  exact hresult

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem affine_masked_initial_conditioning_shell_small {ι J σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype J] [Fintype σ]
    (loX : (Option J × σ) → ℤ) (NX : (Option J × σ) → ℕ) (MX : ℕ) (aX : (Option J × σ) → ℤ)
    (hneX : Nonempty (IntegerResidueBox loX (fun k => loX k + NX k) (fun _ => (MX : ℤ)) aX))
    (loY : σ → ℤ) (NY : σ → ℕ) (MY : ℕ) (aY : σ → ℤ)
    (hneY : Nonempty (IntegerResidueBox loY (fun k => loY k + NY k) (fun _ => (MY : ℤ)) aY))
    (q : ι → ℕ) [∀ i, NeZero (q i)]
    (K : Finset ι) (baseX : ∀ i, (Option J × σ) → ZMod (q i)) (baseY : ∀ i, σ → ZMod (q i))
    (uX : ResiduePrimeCoordinateCell loX NX MX aX q K baseX)
    (uY : ResiduePrimeCoordinateCell loY NY MY aY q K baseY)
    (D : ℕ) (a : J → ℤ)
    (prime power : ι → ℕ) (hprime : ∀ i, (prime i).Prime)
    (hpower : ∀ i, q i = prime i ^ power i) (hinj : Function.Injective prime) (hJ : 2 ≤ Fintype.card J)
    (w : ((Option J × σ) → ℤ) → ℝ) (f : (σ → ℤ) → ℝ) (B : ℕ)
    (hMX : 0 < MX) (hMY : 0 < MY)
    (hw : ∀ z : ResiduePrimeCoordinateCell loX NX MX aX q K baseX,
      0 ≤ w (fun k => (z.val k).val) ∧ w (fun k => (z.val k).val) ≤ 1)
    (hf : ∀ z : ResiduePrimeCoordinateCell loY NY MY aY q K baseY,
      0 ≤ f (fun k => (z.val k).val) ∧ f (fun k => (z.val k).val) ≤ 1)
    (P modLog dimX dimY : ℝ) (hP : 0 ≤ P) (hmodLog : 0 ≤ modLog)
    (ξ : ℝ) (hξ : 0 < ξ) (hmask : affineSamplerPrimeMask prime ξ P MX MY D ⊆ K)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hmoduli : ∀ i, (q i : ℝ) ≤ Real.exp modLog)
    (hdimX : (Fintype.card (Option J × σ) : ℝ) ≤ Real.exp dimX) (hdimY : (Fintype.card σ : ℝ) ≤ Real.exp dimY)
    (hlengthX : ∀ k, Real.exp (modLog * (2 * B : ℕ) + affineComparisonAccuracyLog B P 0 0 + dimX + 1) ≤
      (residueIndexLength (loX k) (loX k + NX k) (MX.lcm (∏ i ∈ K, q i)) ((uX.val k).val) : ℝ))
    (hlengthY : ∀ k, Real.exp (modLog * (2 * B : ℕ) + affineComparisonAccuracyLog B P 0 0 + dimY + 1) ≤
      (residueIndexLength (loY k) (loY k + NY k) (MY.lcm (∏ i ∈ K, q i)) ((uY.val k).val) : ℝ))
    (shell : ℝ) (hshell : 0 < shell)
    (hB : K.card + CyclicCrootSisask.spectralIterations shell
      ((K.card : ℝ) * ((Fintype.card (Option J × σ) : ℝ) * modLog + (Fintype.card σ : ℝ) * modLog + 1) + 4) ≤ B) :
    let c := affinePeriodProductCoupling (σ := σ) q D a
    |productAtomTruncatedPairing c (lowDegreeCoordinateSets ι B) K baseX baseY
        (residuePrimeCoordinateDensity loX NX MX aX hneX q w) (residuePrimeCoordinateDensity loY NY MY aY hneY q f) -
      productCouplingAtomMass c K baseX baseY *
        (residuePrimeCoordinateMassRatio loX NX MX aX q K baseX * residuePrimeCoordinateMassRatio loY NY MY aY q K baseY *
          affineResidueTruncatedPairing (J := J) (σ := σ) (fun i : {i // i ∉ K} => q i.val)
            (lowDegreeCoordinateSets {i // i ∉ K} (B - K.card))
            (residueCellOutsideDensity loX NX MX aX q K baseX uX w)
            (residueCellOutsideDensity loY NY MY aY q K baseY uY f))| ≤ shell / 16 := by
  have hpair : Pairwise (fun i k => (q i).Coprime (q k)) := by
    intro i k hik
    rw [hpower i, hpower k]
    exact selectedPrimePowers_pairwise_coprime prime power hprime hinj hik
  have houtside := affineSamplerPrimeMask_outside prime power hprime hP K hmask
  have hcopX (i : ι) (hi : i ∉ K) : MX.Coprime (q i) := by
    rw [hpower i]
    exact (houtside i hi).1
  have hcopY (i : ι) (hi : i ∉ K) : MY.Coprime (q i) := by
    rw [hpower i]
    exact (houtside i hi).2.1
  have hDcop (i : ι) (hi : i ∉ K) : D.Coprime (q i) := by
    rw [hpower i]
    exact (houtside i hi).2.2.1
  have hlarge (i : ι) (hi : i ∉ K) : (prime i : ℝ)⁻¹ ≤ affineComparisonContraction ξ P :=
    (houtside i hi).2.2.2
  have hκ := affineComparisonContraction_bounds hξ hP
  exact affine_period_initial_conditioning_shell_small
    loX NX MX aX hneX loY NY MY aY hneY q hpair K baseX baseY uX uY
    D a hDcop prime power hprime hpower hJ w f B hκ.1.le hκ.2.1 hlarge
    hMX hMY hcopX hcopY hw hf P modLog dimX dimY hP hmodLog hcount hmoduli
    hdimX hdimY hlengthX hlengthY shell hshell hB

end Erdos3

end

end OAI
