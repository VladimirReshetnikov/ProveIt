/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Probability.ObservedProductDensity

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)]

theorem productMean_reindex (μ : ∀ i, FiniteProbabilityWeights (X i))
    (e : J ≃ I) (g : (∀ j, X (e j)) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => g (fun j => x (e j))) =
      (FiniteProbabilityWeights.pi (fun j => μ (e j))).mean g := by
  classical
  apply Fintype.sum_equiv (Equiv.piCongrLeft X e).symm
  intro x
  change (∏ i, (μ i).weight (x i)) * g (fun j => x (e j)) =
    (∏ j, (μ (e j)).weight (x (e j))) * g (fun j => x (e j))
  rw [e.prod_comp (fun i => (μ i).weight (x i))]

theorem productComplexMean_reindex (μ : ∀ i, FiniteProbabilityWeights (X i))
    (e : J ≃ I) (g : (∀ j, X (e j)) → ℂ) :
    (FiniteProbabilityWeights.pi μ).complexMean (fun x => g (fun j => x (e j))) =
      (FiniteProbabilityWeights.pi (fun j => μ (e j))).complexMean g := by
  classical
  apply Fintype.sum_equiv (Equiv.piCongrLeft X e).symm
  intro x
  change ((∏ i, (μ i).weight (x i) : ℝ) : ℂ) * g (fun j => x (e j)) =
    ((∏ j, (μ (e j)).weight (x (e j)) : ℝ) : ℂ) * g (fun j => x (e j))
  rw [e.prod_comp (fun i => (μ i).weight (x i))]

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [DecidableEq I] {X : I → Type*}

def productSubtypePoint (S : Finset I) (z : ∀ i : S, X i) (base : ∀ i, X i) : ∀ i, X i :=
  fun i => if h : i ∈ S then z ⟨i, h⟩ else base i

theorem productSubtypePoint_apply_mem (S : Finset I) (z : ∀ i : S, X i)
    (base : ∀ i, X i) (i : S) : productSubtypePoint S z base i = z i := by
  simp only [productSubtypePoint, dite_eq_left i.property]

theorem productSubtypePoint_restrict (S : Finset I) (x base : ∀ i, X i) :
    productSubtypePoint S (fun i => x i) base = productCoordinateMix S x base := by
  funext i
  by_cases hi : i ∈ S <;> simp [productSubtypePoint, productCoordinateMix, hi]

theorem ProductDependsOn.subtypePoint {S : Finset I} {f : (∀ i, X i) → ℝ}
    (hf : ProductDependsOn S f) (x base : ∀ i, X i) :
    f (productSubtypePoint S (fun i => x i) base) = f x := by
  apply hf
  intro i hi
  exact productSubtypePoint_apply_mem S (fun j => x j) base ⟨i, hi⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]

omit [Fintype ι] [∀ i, Fintype (X i)] in
theorem productFiberIndicator_subtype (I : Finset ι) (a : ∀ i : I, X i)
    (base x : ∀ i, X i) :
    productFiberIndicator I (productSubtypePoint I a base) x =
      if (fun i : I => x i) = a then 1 else 0 := by
  have he : (∀ i ∈ I, x i = productSubtypePoint I a base i) ↔
      (fun i : I => x i) = a := by
    constructor
    · intro h
      funext i
      exact (h i i.property).trans (productSubtypePoint_apply_mem I a base i)
    · intro h i hi
      exact (congrFun h ⟨i, hi⟩).trans (productSubtypePoint_apply_mem I a base ⟨i, hi⟩).symm
  simp only [productFiberIndicator, he]

omit [Fintype ι] in
theorem productFiberIndicator_sum_subtype (I : Finset ι) (base x : ∀ i, X i) :
    (∑ a : ∀ i : I, X i, productFiberIndicator I (productSubtypePoint I a base) x) = 1 := by
  simp [productFiberIndicator_subtype]

omit [Fintype ι] in
theorem productFiberIndicator_partition (I : Finset ι) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    (∑ a : ∀ i : I, X i, productFiberIndicator I (productSubtypePoint I a base) x * f x) = f x := by
  rw [← Finset.sum_mul, productFiberIndicator_sum_subtype, one_mul]

theorem productFiberMass_sum_subtype (w : (∀ i, X i) → ℝ) (I : Finset ι)
    (base : ∀ i, X i) :
    (∑ a : ∀ i : I, X i, productFiberMass w I (productSubtypePoint I a base)) = ∑ x, w x := by
  unfold productFiberMass
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, productFiberIndicator_sum_subtype, mul_one]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productMean_restrict (S : Finset I) (g : (∀ i : S, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => g (fun i => x i)) =
      (FiniteProbabilityWeights.pi (fun i : S => μ i)).mean g := by
  classical
  let pS := FiniteProbabilityWeights.pi (fun i : S => μ i)
  let pC := FiniteProbabilityWeights.pi (fun i : {i // i ∉ S} => μ i)
  have hw (x : ∀ i, X i) : (FiniteProbabilityWeights.pi μ).weight x =
      pS.weight (fun i => x i) * pC.weight (fun i => x i) := by
    have hu : @Finset.univ S (Subtype.fintype (fun i : I => i ∈ S)) =
        @Finset.univ S (Finset.Subtype.fintype S) := by
      ext i
      simp only [Finset.mem_univ]
    simpa only [pS, pC, FiniteProbabilityWeights.pi, hu] using
      (Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ S) (fun i => (μ i).weight (x i))).symm
  calc
    (FiniteProbabilityWeights.pi μ).mean (fun x => g (fun i => x i)) =
        ∑ z : (∀ i : S, X i) × (∀ i : {i // i ∉ S}, X i),
          pS.weight z.1 * pC.weight z.2 * g z.1 := by
      apply Fintype.sum_equiv (Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) X)
      intro x
      change (FiniteProbabilityWeights.pi μ).weight x * g (fun i => x i) =
        pS.weight (fun i => x i) * pC.weight (fun i => x i) * g (fun i => x i)
      rw [hw]
    _ = pS.mean g := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro z _
      calc
        (∑ v, pS.weight z * pC.weight v * g z) = pS.weight z * g z * ∑ v, pC.weight v := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro v _
          ring
        _ = pS.weight z * g z := by rw [pC.total, mul_one]

theorem productMean_of_depends (S : Finset I) (f : (∀ i, X i) → ℝ)
    (hf : ProductDependsOn S f) (base : ∀ i, X i) :
    (FiniteProbabilityWeights.pi μ).mean f =
      (FiniteProbabilityWeights.pi (fun i : S => μ i)).mean
        (fun z => f (productSubtypePoint S z base)) := by
  rw [← productMean_restrict μ S]
  congr 1
  funext x
  exact (hf.subtypePoint x base).symm

end Erdos3

end

section

namespace Erdos3

variable {I J : Type*} [DecidableEq I] [Fintype J] {X : I → Type*}

noncomputable abbrev productTupleIndexEquiv (a : J → I) (ha : Function.Injective a) :
    J ≃ ↥(Finset.univ.image a) :=
  Equiv.ofBijective (fun j => ⟨a j, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩)
    ⟨fun _ _ h => ha (congrArg Subtype.val h), by
      intro i
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp i.property
      exact ⟨j, Subtype.ext hj⟩⟩

noncomputable def productTuplePoint (a : J → I) (ha : Function.Injective a)
    (v : ∀ j, X (a j)) (base : ∀ i, X i) : ∀ i, X i :=
  productSubtypePoint (Finset.univ.image a)
    (Equiv.piCongrLeft (fun i : ↥(Finset.univ.image a) => X i)
      (productTupleIndexEquiv a ha) v) base

theorem productTuplePoint_apply (a : J → I) (ha : Function.Injective a)
    (v : ∀ j, X (a j)) (base : ∀ i, X i) (j : J) :
    productTuplePoint a ha v base (a j) = v j := by
  unfold productTuplePoint
  exact (productSubtypePoint_apply_mem (Finset.univ.image a) _ base
    (productTupleIndexEquiv a ha j)).trans
      (Equiv.piCongrLeft_apply_apply (fun i : ↥(Finset.univ.image a) => X i)
        (productTupleIndexEquiv a ha) v j)

theorem ProductDependsOn.tuplePoint {a : J → I} (ha : Function.Injective a)
    {f : (∀ i, X i) → ℝ} (hf : ProductDependsOn (Finset.univ.image a) f)
    (x base : ∀ i, X i) : f (productTuplePoint a ha (fun j => x (a j)) base) = f x := by
  apply hf
  intro i hi
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
  exact productTuplePoint_apply a ha _ base j

end Erdos3

end

section

namespace Erdos3

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)]

theorem productMean_tuple (μ : ∀ i, FiniteProbabilityWeights (X i))
    (a : J → I) (ha : Function.Injective a) (f : (∀ i, X i) → ℝ)
    (hf : ProductDependsOn (Finset.univ.image a) f) (base : ∀ i, X i) :
    (FiniteProbabilityWeights.pi (fun j => μ (a j))).mean
      (fun v => f (productTuplePoint a ha v base)) = (FiniteProbabilityWeights.pi μ).mean f := by
  rw [productMean_of_depends μ (Finset.univ.image a) f hf base]
  let e := productTupleIndexEquiv a ha
  let eP := Equiv.piCongrLeft (fun i : ↥(Finset.univ.image a) => X i) e
  have h := productMean_reindex (fun i : ↥(Finset.univ.image a) => μ i) e
    (fun v => f (productTuplePoint a ha v base))
  have he (x : ∀ i : ↥(Finset.univ.image a), X i) :
      productTuplePoint a ha (fun j => x (e j)) base =
        productSubtypePoint (Finset.univ.image a) x base := by
    change productSubtypePoint (Finset.univ.image a) (eP (eP.symm x)) base = _
    rw [eP.apply_symm_apply]
  simp_rw [he] at h
  exact h.symm

end Erdos3

end

section

namespace Erdos3

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)]

theorem productMean_pullback (μ : ∀ i, FiniteProbabilityWeights (X i))
    (a : J → I) (ha : Function.Injective a) (base : ∀ i, X i)
    (g : (∀ j, X (a j)) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => g (fun j => x (a j))) =
      (FiniteProbabilityWeights.pi (fun j => μ (a j))).mean g := by
  have hd : ProductDependsOn (Finset.univ.image a) (fun x => g (fun j => x (a j))) := by
    intro x y h
    apply congrArg g
    funext j
    exact h (a j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  have h := productMean_tuple μ a ha (fun x => g (fun j => x (a j))) hd base
  simpa only [productTuplePoint_apply] using h.symm

end Erdos3

end

end OAI
