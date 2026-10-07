import Mathlib.Data.ZMod.QuotientRing
import OAI.Combinatorics.Progressions.Lattices.BoundedPrimeDepthBudget
import OAI.Combinatorics.Progressions.Lattices.ResidueSliceUpperFailure

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι σ : Type*} (q : ι → ℕ) (I : Finset ι)
  (hpair : Pairwise (fun i j => (q i).Coprime (q j)))

noncomputable def selectedPrimeCRT :
    ZMod (∏ i : I, q i.val) ≃+* (∀ i : I, ZMod (q i.val)) :=
  ZMod.prodEquivPi (fun i : I => q i.val)
    (fun i j hij => hpair (by intro h; exact hij (Subtype.ext h)))

noncomputable def primeCoordinatesMod (m : ℕ) (hd : m ∣ ∏ i : I, q i.val) :
    (∀ i, σ → ZMod (q i)) →+ (σ → ZMod m) where
  toFun x k := (ZMod.castHom hd (ZMod m))
    ((selectedPrimeCRT q I hpair).symm (fun i : I => x i.val k))
  map_zero' := by
    ext k
    change (ZMod.castHom hd (ZMod m)) ((selectedPrimeCRT q I hpair).symm 0) = 0
    rw [map_zero, map_zero]
  map_add' := by
    intro x y
    ext k
    change (ZMod.castHom hd (ZMod m)) ((selectedPrimeCRT q I hpair).symm
      ((fun i : I => x i.val k) + (fun i : I => y i.val k))) = _
    rw [map_add, map_add]
    rfl

theorem primeCoordinatesMod_agree (m : ℕ) (hd : m ∣ ∏ i : I, q i.val)
    (x y : ∀ i, σ → ZMod (q i)) (hxy : ∀ i ∈ I, x i = y i) :
    primeCoordinatesMod q I hpair m hd x = primeCoordinatesMod q I hpair m hd y := by
  ext k
  change (ZMod.castHom hd (ZMod m)) ((selectedPrimeCRT q I hpair).symm (fun i : I => x i.val k)) =
    (ZMod.castHom hd (ZMod m)) ((selectedPrimeCRT q I hpair).symm (fun i : I => y i.val k))
  congr 2
  funext i
  exact congrFun (hxy i.val i.property) k

theorem primeCoordinatesMod_integer (m : ℕ) (hd : m ∣ ∏ i : I, q i.val) (u : σ → ℤ) :
    primeCoordinatesMod q I hpair m hd (primeCoordinateObservation q u) = (fun k => (u k : ZMod m)) := by
  ext k
  change (ZMod.castHom hd (ZMod m))
    ((selectedPrimeCRT q I hpair).symm (u k : ∀ i : I, ZMod (q i.val))) = _
  rw [map_intCast, map_intCast]

theorem primeCoordinatesMod_surjective (m : ℕ) [NeZero m] (hd : m ∣ ∏ i : I, q i.val) :
    Function.Surjective (primeCoordinatesMod (σ := σ) q I hpair m hd) := by
  intro y
  refine ⟨primeCoordinateObservation q (fun k => ((y k).val : ℤ)), ?_⟩
  rw [primeCoordinatesMod_integer]
  funext k
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def coarseResidueIndicator {ι σ : Type*}
    (q : ι → ℕ) (I : Finset ι) (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (m : ℕ) (hd : m ∣ ∏ i : I, q i.val) (r : σ → ZMod m) (x : ∀ i, σ → ZMod (q i)) : ℝ :=
  if primeCoordinatesMod q I hpair m hd x = r then 1 else 0

section

variable {ι σ : Type*} (q : ι → ℕ) (I : Finset ι)
  (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
  (m : ℕ) (hd : m ∣ ∏ i : I, q i.val) (r : σ → ZMod m)

theorem coarseResidueIndicator_depends :
    ProductDependsOn I (coarseResidueIndicator q I hpair m hd r) := by
  intro x y hxy
  unfold coarseResidueIndicator
  rw [primeCoordinatesMod_agree q I hpair m hd x y hxy]

theorem coarseResidueIndicator_abs (x : ∀ i, σ → ZMod (q i)) :
    |coarseResidueIndicator q I hpair m hd r x| = coarseResidueIndicator q I hpair m hd r x := by
  unfold coarseResidueIndicator
  split_ifs <;> norm_num

theorem coarseResidueIndicator_integer (u : σ → ℤ) :
    coarseResidueIndicator q I hpair m hd r (primeCoordinateObservation q u) =
      if (fun k => (u k : ZMod m)) = r then (1 : ℝ) else 0 := by
  simp only [coarseResidueIndicator, primeCoordinatesMod_integer]

end

theorem primeCoordinateReference_uniform {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (q : ι → ℕ) [∀ i, NeZero (q i)] :
    FiniteProbabilityWeights.pi (primeCoordinateReference (σ := σ) q) =
      FiniteProbabilityWeights.uniform (∀ i, σ → ZMod (q i)) := by
  apply FiniteProbabilityWeights.eq_of_weight_eq
  intro x
  change (∏ i, (Fintype.card (σ → ZMod (q i)) : ℝ)⁻¹) =
    (Fintype.card (∀ i, σ → ZMod (q i)) : ℝ)⁻¹
  rw [Fintype.card_pi, Nat.cast_prod, Finset.prod_inv_distrib]

theorem coarseResidueIndicator_mean {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (q : ι → ℕ) [∀ i, NeZero (q i)] (I : Finset ι)
    (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (m : ℕ) [NeZero m] (hd : m ∣ ∏ i : I, q i.val) (r : σ → ZMod m) :
    (FiniteProbabilityWeights.pi (primeCoordinateReference (σ := σ) q)).mean
      (coarseResidueIndicator q I hpair m hd r) = ((m : ℝ) ^ Fintype.card σ)⁻¹ := by
  rw [primeCoordinateReference_uniform]
  have h := uniform_mean_surjective_hom_fiber (primeCoordinatesMod (σ := σ) q I hpair m hd)
    (primeCoordinatesMod_surjective q I hpair m hd) r
  convert h using 1
  · congr 1
  · simp only [Fintype.card_fun, ZMod.card, Nat.cast_pow]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def residueTruncationCap (ι : Type*) [Fintype ι] [DecidableEq ι]
    (b : ℕ) (eta : ℝ) : ℝ :=
  ((lowDegreeCoordinateSets ι b).card : ℝ) * (2 : ℝ) ^ b * (1 + eta)

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
  (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a))
  (q : ι → ℕ) [∀ i, NeZero (q i)]

noncomputable def residuePhysicalTruncation (b : ℕ) (f : (σ → ℤ) → ℝ) (u : σ → ℤ) : ℝ :=
  productANOVATruncation (primeCoordinateReference (σ := σ) q) (lowDegreeCoordinateSets ι b)
    (residuePrimeCoordinateDensity lo N M a hne q f) (primeCoordinateObservation q u)

def ResiduePhysicalTruncationControl (b : ℕ) (f : (σ → ℤ) → ℝ) (eta : ℝ) : Prop :=
  let low := residuePhysicalTruncation lo N M a hne q b f
  let cap := residueTruncationCap ι b eta
  (𝔼 z : IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a,
    low (fun k => (z k).val) ^ 2) ≤ 2 + 3 * eta * cap ^ 2 ∧
  (𝔼 z : IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a,
    (f (fun k => (z k).val) - low (fun k => (z k).val)) ^ 2) ≤ 1 + eta * cap ^ 2 ∧
  ∀ (I : Finset ι), I.card ≤ b → ∀ test : (∀ i, σ → ZMod (q i)) → ℝ, ProductDependsOn I test →
    |𝔼 z : IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a,
      (f (fun k => (z k).val) - low (fun k => (z k).val)) *
        test (primeCoordinateObservation q (fun k => (z k).val))| ≤
      eta * cap * (FiniteProbabilityWeights.pi (primeCoordinateReference (σ := σ) q)).mean
        (fun x => |test x|)

theorem residuePhysicalTruncation_control (b : ℕ) (f : (σ → ℤ) → ℝ)
    (hf : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ f z ∧ f z ≤ 1) {eta : ℝ} (heta : 0 ≤ eta)
    (hclose : ProductMarginalsClose (primeCoordinateReference (σ := σ) q)
      (residuePrimeCoordinateDensity lo N M a hne q (fun _ => 1)) eta (2 * b)) :
    ResiduePhysicalTruncationControl lo N M a hne q b f eta := by
  let := hne
  let p := FiniteProbabilityWeights.uniform
    (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a)
  let F := fun z : IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a =>
    primeCoordinateObservation q (fun k => (z k).val)
  let w := fun z : IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a =>
    f (fun k => (z k).val)
  have hw (z) : 0 ≤ w z ∧ w z ≤ 1 := by
    apply hf
    apply (mem_translatedIntegerBox lo N _).mpr
    intro k
    exact Finset.mem_Ico.mp ((Finset.mem_filter.mp (z k).property).1)
  have h := observed_unit_truncation_control (primeCoordinateReference (σ := σ) q) p F
    (primeCoordinateReference_weight_pos q) (fun _ _ => 0) w hw (lowDegreeCoordinateSets ι b)
    heta (fun S hS => (mem_lowDegreeCoordinateSets ι b S).mp hS) hclose
  dsimp only [ResiduePhysicalTruncationControl]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [residuePhysicalTruncation, residueTruncationCap, residuePrimeCoordinateDensity,
      p, F, w, FiniteProbabilityWeights.uniform_mean] using h.1
  · simpa only [residuePhysicalTruncation, residueTruncationCap, residuePrimeCoordinateDensity,
      p, F, w, FiniteProbabilityWeights.uniform_mean] using h.2.1
  · intro I hI test htest
    have ht := h.2.2 I hI
      (fun S hS => (mem_lowDegreeCoordinateSets ι b S).mpr ((Finset.card_le_card hS).trans hI)) test htest
    simpa only [residuePhysicalTruncation, residueTruncationCap, residuePrimeCoordinateDensity,
      p, F, w, FiniteProbabilityWeights.uniform_mean] using ht

theorem residuePhysicalTruncation_control_of_lengths (b : ℕ) (f : (σ → ℤ) → ℝ)
    (hf : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ f z ∧ f z ≤ 1)
    (hM : 0 < M) (hcop : ∀ i, M.Coprime (q i)) (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (modLog dimLog accLog eta : ℝ) (hmodLog : 0 ≤ modLog) (heta : eta ≤ 1)
    (hacc : Real.exp (-accLog) ≤ eta) (hmoduli : ∀ i, (q i : ℝ) ≤ Real.exp modLog)
    (hdim : (Fintype.card σ : ℝ) ≤ Real.exp dimLog)
    (hlength : ∀ k, Real.exp (modLog * (2 * b : ℕ) + accLog + dimLog + 1) ≤
      (residueIndexLength (lo k) (lo k + N k) M (a k) : ℝ)) :
    ResiduePhysicalTruncationControl lo N M a hne q b f eta := by
  have hclose := residuePrimeDensity_close_of_lengths lo N M a hne q hM hcop hpair
    (2 * b) modLog dimLog accLog eta hmodLog heta hacc hmoduli hdim hlength
  exact residuePhysicalTruncation_control lo N M a hne q b f hf ((Real.exp_pos _).le.trans hacc) hclose

theorem residuePhysicalTruncation_atom_error {b : ℕ} {f : (σ → ℤ) → ℝ} {eta : ℝ}
    (h : ResiduePhysicalTruncationControl lo N M a hne q b f eta)
    (I : Finset ι) (hI : I.card ≤ b) (base : ∀ i, σ → ZMod (q i)) :
    |𝔼 z : IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a,
      (f (fun k => (z k).val) - residuePhysicalTruncation lo N M a hne q b f (fun k => (z k).val)) *
        productFiberIndicator I base (primeCoordinateObservation q (fun k => (z k).val))| ≤
      eta * residueTruncationCap ι b eta * (((∏ i ∈ I, q i : ℕ) : ℝ) ^ Fintype.card σ)⁻¹ := by
  have ht := h.2.2 I hI (productFiberIndicator I base) (productFiberIndicator_depends I base)
  have hind : (fun x => |productFiberIndicator I base x|) = productFiberIndicator I base := by
    funext x
    unfold productFiberIndicator
    split_ifs <;> norm_num
  rw [hind] at ht
  change _ ≤ eta * residueTruncationCap ι b eta *
    productFiberMass (FiniteProbabilityWeights.pi (primeCoordinateReference (σ := σ) q)).weight I base at ht
  rw [primeCoordinateReference_fiber] at ht
  exact ht

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem residuePhysicalTruncation_modulus_error {ι σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)]
    (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    {b : ℕ} {f : (σ → ℤ) → ℝ} {eta : ℝ}
    (h : ResiduePhysicalTruncationControl lo N M a hne q b f eta)
    (I : Finset ι) (hI : I.card ≤ b) (m : ℕ) [NeZero m]
    (hd : m ∣ ∏ i ∈ I, q i) (r : σ → ZMod m) :
    |𝔼 z : IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a,
      (f (fun k => (z k).val) - residuePhysicalTruncation lo N M a hne q b f (fun k => (z k).val)) *
        (if (fun k => ((z k).val : ZMod m)) = r then (1 : ℝ) else 0)| ≤
      eta * residueTruncationCap ι b eta * ((m : ℝ) ^ Fintype.card σ)⁻¹ := by
  have hd' : m ∣ ∏ i : I, q i.val := by simpa only [Finset.prod_coe_sort] using hd
  have ht := h.2.2 I hI (coarseResidueIndicator q I hpair m hd' r)
    (coarseResidueIndicator_depends q I hpair m hd' r)
  simp_rw [coarseResidueIndicator_integer, coarseResidueIndicator_abs] at ht
  rw [coarseResidueIndicator_mean] at ht
  convert ht using 1
  congr 3
  funext z
  split_ifs <;> rfl

theorem residuePhysicalTruncation_small_modulus_error {ι σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a))
    (prime power : ι → ℕ) [∀ i, NeZero (prime i ^ power i)]
    (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime)
    {b : ℕ} {f : (σ → ℤ) → ℝ} {eta : ℝ}
    (h : ResiduePhysicalTruncationControl lo N M a hne (fun i => prime i ^ power i) b f eta)
    (m : ℕ) [NeZero m] (hm : m ∣ ∏ i, prime i ^ power i) (hmb : m ≤ 2 ^ b)
    (r : σ → ZMod m) :
    |𝔼 z : IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a,
      (f (fun k => (z k).val) - residuePhysicalTruncation lo N M a hne
        (fun i => prime i ^ power i) b f (fun k => (z k).val)) *
        (if (fun k => ((z k).val : ZMod m)) = r then (1 : ℝ) else 0)| ≤
      eta * residueTruncationCap ι b eta * ((m : ℝ) ^ Fintype.card σ)⁻¹ := by
  exact residuePhysicalTruncation_modulus_error lo N M a hne (fun i => prime i ^ power i)
    (selectedPrimePowers_pairwise_coprime prime power hprime hinj) h (periodPrimeCoordinates prime m)
    (periodPrimeCoordinates_card_le_of_le_pow prime hprime hinj (Nat.pos_of_ne_zero (NeZero.ne m)) hmb)
    m (periodPrimeCoordinates_modulus_dvd_product prime power hprime m hm) r

end Erdos3

end

section

namespace Erdos3

open scoped Classical

variable {ι I : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]

theorem residuePrimeCoordinateDensity_congr_on_box
    (lo : I → ℤ) (N : I → ℕ) (M : ℕ) (a : I → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun i => lo i + N i) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (f g : (I → ℤ) → ℝ)
    (hfg : ∀ z ∈ translatedIntegerBox lo N, f z = g z) :
    residuePrimeCoordinateDensity lo N M a hne q f =
      residuePrimeCoordinateDensity lo N M a hne q g := by
  have heq : (fun z : IntegerResidueBox lo (fun i => lo i + N i) (fun _ => (M : ℤ)) a =>
      f (fun i => (z i).val)) = (fun z => g (fun i => (z i).val)) := by
    funext z
    apply hfg
    apply (mem_translatedIntegerBox lo N _).mpr
    intro i
    exact Finset.mem_Ico.mp (Finset.mem_filter.mp (z i).property).1
  unfold residuePrimeCoordinateDensity
  dsimp only
  rw [heq]

theorem residuePhysicalTruncation_congr_on_box
    (lo : I → ℤ) (N : I → ℕ) (M : ℕ) (a : I → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun i => lo i + N i) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (b : ℕ) (f g : (I → ℤ) → ℝ)
    (hfg : ∀ z ∈ translatedIntegerBox lo N, f z = g z) :
    residuePhysicalTruncation lo N M a hne q b f =
      residuePhysicalTruncation lo N M a hne q b g := by
  funext x
  unfold residuePhysicalTruncation
  rw [residuePrimeCoordinateDensity_congr_on_box lo N M a hne q f g hfg]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem boundedPrimePhysicalTruncation_modulus_error {σ : Type*} [Fintype σ] [DecidableEq σ]
    (Q : ℕ) (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a))
    {b : ℕ} {f : (σ → ℤ) → ℝ} {eta : ℝ} (hQb : Q ≤ 2 ^ b)
    (h : ResiduePhysicalTruncationControl lo N M a hne (boundedPrimePower Q) b f eta)
    (m : ℕ) [NeZero m] (hmQ : m ≤ Q) (r : σ → ZMod m) :
    |𝔼 z : IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a,
      (f (fun k => (z k).val) - residuePhysicalTruncation lo N M a hne
        (boundedPrimePower Q) b f (fun k => (z k).val)) *
        (if (fun k => ((z k).val : ZMod m)) = r then (1 : ℝ) else 0)| ≤
      eta * residueTruncationCap (BoundedPrime Q) b eta * ((m : ℝ) ^ Fintype.card σ)⁻¹ := by
  let : ∀ i : BoundedPrime Q, NeZero (boundedPrime Q i ^ boundedPrimeExponent Q i) :=
    fun i => ⟨(boundedPrimePower_pos Q i).ne'⟩
  exact residuePhysicalTruncation_small_modulus_error lo N M a hne
    (boundedPrime Q) (boundedPrimeExponent Q) (boundedPrime_prime Q) (boundedPrime_injective Q) h m
    (boundedPrimeProduct_captures (Nat.pos_of_ne_zero (NeZero.ne m)) hmQ) (hmQ.trans hQb) r

end Erdos3

end

end OAI
