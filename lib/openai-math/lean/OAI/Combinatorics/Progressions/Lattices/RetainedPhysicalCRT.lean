/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Data.ZMod.QuotientRing
import OAI.Combinatorics.Progressions.Estimates.ObservedMarginalTesting
import OAI.Combinatorics.Progressions.Geometry.CoordinateLeafCount
import OAI.Combinatorics.Progressions.Probability.CouplingOneSidedTruncation

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {J I : Type*} [Fintype J] [Fintype I] {q : ℕ} [NeZero q]

noncomputable def affineSampleKernel (z : Option J × I → ZMod q) : FiniteProbabilityWeights (I → ZMod q) :=
  residueAffineKernel (q := q) (affineSampleAlphabetEquiv z)

theorem affineSampleKernel_mean (z : Option J × I → ZMod q) (f : (I → ZMod q) → ℝ) :
    (affineSampleKernel z).mean f =
      𝔼 t : J → ZMod q, f (fun i => z (none, i) + ∑ j, t j * z (some j, i)) := by
  rw [affineSampleKernel, residueAffineKernel_mean]
  unfold residueColumnRealAverage
  apply Finset.expect_congr rfl
  intro t _
  change f ((fun i => z (none, i)) + ∑ j, t j • (fun i => z (some j, i))) = _
  congr 1
  funext i
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem affineSampleKernel_preserves_mean (f : (I → ZMod q) → ℝ) :
    (FiniteProbabilityWeights.uniform (Option J × I → ZMod q)).mean
      (fun z => (affineSampleKernel z).mean f) = (FiniteProbabilityWeights.uniform (I → ZMod q)).mean f := by
  unfold affineSampleKernel
  rw [affineSampleAlphabet_mean
    (fun z : (J → I → ZMod q) × (I → ZMod q) => (residueAffineKernel (q := q) z).mean f)]
  exact residueAffineKernel_preserves_mean f

noncomputable def affineSampleCoupling :
    FiniteProbabilityCoupling (FiniteProbabilityWeights.uniform (Option J × I → ZMod q))
      (FiniteProbabilityWeights.uniform (I → ZMod q)) :=
  FiniteProbabilityCoupling.ofKernel _ _ affineSampleKernel affineSampleKernel_preserves_mean

theorem affineSampleKernel_centered_sq {p a : ℕ} (hp : p.Prime) (hq : q = p ^ a)
    (f : (I → ZMod q) → ℝ) (hf : (FiniteProbabilityWeights.uniform (I → ZMod q)).mean f = 0) :
    (FiniteProbabilityWeights.uniform (Option J × I → ZMod q)).mean
      (fun z => (affineSampleKernel z).mean f ^ 2) ≤
      (p : ℝ)⁻¹ ^ Fintype.card J * (FiniteProbabilityWeights.uniform (I → ZMod q)).mean (fun x => f x ^ 2) := by
  unfold affineSampleKernel
  rw [affineSampleAlphabet_mean
    (fun z : (J → I → ZMod q) × (I → ZMod q) => (residueAffineKernel (q := q) z).mean f ^ 2)]
  have hcard : Fintype.card (I → ZMod q) = p ^ (a * Fintype.card I) := by simp [hq, pow_mul]
  exact residueAffineKernel_centered_sq hp hcard f hf

omit [Fintype I] in
theorem affinePrimeCoordinateObservation_site {ι : Type*} (qs : ι → ℕ) [∀ i, NeZero (qs i)]
    (t : J → ℤ) (z : Option J × I → ℤ) (i : ι) :
    primeCoordinateObservation qs (BooleanCubeKernel.integerPhysicalSite t z) i =
      (affinePrimeCoordinateObservation qs z i).2 +
        residueColumnMap (q := qs i) (affinePrimeCoordinateObservation qs z i).1 (fun j => (t j : ZMod (qs i))) := by
  funext k
  simp only [primeCoordinateObservation, BooleanCubeKernel.integerPhysicalSite, Int.cast_add,
    Int.cast_sum, Int.cast_mul, affinePrimeCoordinateObservation_apply, Pi.add_apply,
    residueColumnMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {J I : Type*} [Fintype J] [Fintype I] {q : ℕ} [NeZero q]

theorem affineSampleFixedParameter_mean (t : J → ZMod q) (f : (I → ZMod q) → ℝ) :
    (FiniteProbabilityWeights.uniform (Option J × I → ZMod q)).mean
      (fun z => f ((affineSampleAlphabetEquiv z).2 +
        residueColumnMap (q := q) (affineSampleAlphabetEquiv z).1 t)) =
      (FiniteProbabilityWeights.uniform (I → ZMod q)).mean f := by
  rw [affineSampleAlphabet_mean
    (fun z : (J → I → ZMod q) × (I → ZMod q) => f (z.2 + residueColumnMap (q := q) z.1 t))]
  rw [residueAffineSource, FiniteProbabilityWeights.mean_prod]
  have hs (V : J → I → ZMod q) :
      (FiniteProbabilityWeights.uniform (I → ZMod q)).mean
        (fun x => f (x + residueColumnMap (q := q) V t)) =
      (FiniteProbabilityWeights.uniform (I → ZMod q)).mean f :=
    FiniteProbabilityWeights.uniform_mean_equiv (Equiv.addRight (residueColumnMap (q := q) V t)) f
  simp only [hs, FiniteProbabilityWeights.mean_const]

noncomputable def affineSampleParameterKernel (π : FiniteProbabilityWeights (J → ZMod q))
    (z : Option J × I → ZMod q) : FiniteProbabilityWeights (I → ZMod q) :=
  π.fiberLaw (fun t => (affineSampleAlphabetEquiv z).2 +
    residueColumnMap (q := q) (affineSampleAlphabetEquiv z).1 t)

theorem affineSampleParameterKernel_mean (π : FiniteProbabilityWeights (J → ZMod q))
    (z : Option J × I → ZMod q) (f : (I → ZMod q) → ℝ) :
    (affineSampleParameterKernel π z).mean f =
      π.mean (fun t => f ((affineSampleAlphabetEquiv z).2 +
        residueColumnMap (q := q) (affineSampleAlphabetEquiv z).1 t)) :=
  π.fiberLaw_mean _ f

theorem affineSampleParameterKernel_preserves_mean (π : FiniteProbabilityWeights (J → ZMod q))
    (f : (I → ZMod q) → ℝ) :
    (FiniteProbabilityWeights.uniform (Option J × I → ZMod q)).mean
      (fun z => (affineSampleParameterKernel π z).mean f) =
      (FiniteProbabilityWeights.uniform (I → ZMod q)).mean f := by
  simp only [affineSampleParameterKernel_mean]
  rw [FiniteProbabilityWeights.mean_comm]
  simp only [affineSampleFixedParameter_mean, FiniteProbabilityWeights.mean_const]

noncomputable def affineSampleParameterCoupling (π : FiniteProbabilityWeights (J → ZMod q)) :
    FiniteProbabilityCoupling (FiniteProbabilityWeights.uniform (Option J × I → ZMod q))
      (FiniteProbabilityWeights.uniform (I → ZMod q)) :=
  FiniteProbabilityCoupling.ofKernel _ _ (affineSampleParameterKernel π)
    (affineSampleParameterKernel_preserves_mean π)

theorem affineSampleParameterKernel_uniform (z : Option J × I → ZMod q) :
    affineSampleParameterKernel (FiniteProbabilityWeights.uniform (J → ZMod q)) z = affineSampleKernel z := rfl

end Erdos3

end

section

namespace Erdos3

open scoped Classical

theorem inverse_prime_power_le_square {p ell : ℕ} {κ : ℝ}
    (hp : p.Prime) (hell : 2 ≤ ell) (_hκ : 0 ≤ κ) (hlarge : (p : ℝ)⁻¹ ≤ κ) :
    (p : ℝ)⁻¹ ^ ell ≤ κ ^ 2 := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hi1 : (p : ℝ)⁻¹ ≤ 1 := by
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hp1
  exact (pow_le_pow_of_le_one (inv_nonneg.mpr (Nat.cast_nonneg p)) hi1 hell).trans
    (pow_le_pow_left₀ (inv_nonneg.mpr (Nat.cast_nonneg p)) hlarge 2)

theorem affineSampleKernel_centered_sq_of_inverse_le {J I : Type*} [Fintype J] [Fintype I]
    {q p a : ℕ} [NeZero q] {κ : ℝ} (hp : p.Prime) (hq : q = p ^ a)
    (hJ : 2 ≤ Fintype.card J) (hκ : 0 ≤ κ) (hlarge : (p : ℝ)⁻¹ ≤ κ)
    (f : (I → ZMod q) → ℝ) (hf : (FiniteProbabilityWeights.uniform (I → ZMod q)).mean f = 0) :
    (FiniteProbabilityWeights.uniform (Option J × I → ZMod q)).mean
      (fun z => (affineSampleKernel z).mean f ^ 2) ≤
      κ ^ 2 * (FiniteProbabilityWeights.uniform (I → ZMod q)).mean (fun y => f y ^ 2) := by
  exact (affineSampleKernel_centered_sq hp hq f hf).trans
    (mul_le_mul_of_nonneg_right (inverse_prime_power_le_square hp hJ hκ hlarge)
      ((FiniteProbabilityWeights.uniform (I → ZMod q)).mean_nonneg (fun _ => sq_nonneg _)))

theorem residue_function_alphabet_card_le_exp {I : Type*} [Fintype I] {q : ℕ} [NeZero q]
    {B : ℝ} (hq : (q : ℝ) ≤ Real.exp B) :
    (Fintype.card (I → ZMod q) : ℝ) ≤ Real.exp ((Fintype.card I : ℝ) * B) := by
  simp only [Fintype.card_fun, ZMod.card, Nat.cast_pow]
  exact (pow_le_pow_left₀ (Nat.cast_nonneg q) hq _).trans_eq (Real.exp_nat_mul _ _).symm

end Erdos3

end

section

namespace Erdos3

open scoped Classical

noncomputable def affineSampleProductCoupling {ι J σ : Type*} [Fintype J] [Fintype σ]
    (q : ι → ℕ) [∀ i, NeZero (q i)] :
    ∀ i, FiniteProbabilityCoupling
      (primeCoordinateReference (σ := Option J × σ) q i)
      (primeCoordinateReference (σ := σ) q i) :=
  fun i => affineSampleCoupling (J := J) (I := σ) (q := q i)

noncomputable def affineResidueTruncatedPairing {ι J σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype J] [Fintype σ] (q : ι → ℕ) [∀ i, NeZero (q i)]
    (D : Finset (Finset ι)) (w : (∀ i, Option J × σ → ZMod (q i)) → ℝ)
    (f : (∀ i, σ → ZMod (q i)) → ℝ) : ℝ :=
  productTruncatedPairing (affineSampleProductCoupling (J := J) (σ := σ) q) D w f

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {J : Type*} [Fintype J] {q : ℕ} [NeZero q]

noncomputable def affinePeriodParameterLaw (D : ℕ) (a : J → ℤ) :
    FiniteProbabilityWeights (J → ZMod q) :=
  (FiniteProbabilityWeights.uniform (J → ZMod q)).fiberLaw
    (fun s j => (a j : ZMod q) + (D : ZMod q) * s j)

theorem affinePeriodParameterLaw_mean (D : ℕ) (a : J → ℤ)
    (f : (J → ZMod q) → ℝ) :
    (affinePeriodParameterLaw D a).mean f =
      (FiniteProbabilityWeights.uniform (J → ZMod q)).mean
        (fun s => f (fun j => (a j : ZMod q) + (D : ZMod q) * s j)) :=
  FiniteProbabilityWeights.fiberLaw_mean _ _ _

theorem affinePeriodParameterLaw_uniform (D : ℕ) (a : J → ℤ) (hD : D.Coprime q) :
    affinePeriodParameterLaw (q := q) D a =
      FiniteProbabilityWeights.uniform (J → ZMod q) := by
  let e : (J → ZMod q) ≃ (J → ZMod q) :=
    Equiv.piCongrRight (fun j => (ZMod.unitOfCoprime D hD).mulLeft.trans
      (Equiv.addLeft (a j : ZMod q)))
  have hm (f : (J → ZMod q) → ℝ) :
      (affinePeriodParameterLaw D a).mean f =
        (FiniteProbabilityWeights.uniform (J → ZMod q)).mean f := by
    rw [affinePeriodParameterLaw_mean]
    exact FiniteProbabilityWeights.uniform_mean_equiv e f
  apply FiniteProbabilityWeights.eq_of_weight_eq
  intro x
  have h := hm (fun y => if y = x then (1 : ℝ) else 0)
  simpa only [FiniteProbabilityWeights.mean, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] using h

omit [Fintype J] [NeZero q] in
theorem affinePeriodParameterLaw_integer (D : ℕ) (a s : J → ℤ) :
    (fun j => ((a j + (D : ℤ) * s j : ℤ) : ZMod q)) =
      (fun j => (a j : ZMod q) + (D : ZMod q) * (s j : ZMod q)) := by
  funext j
  push_cast
  rfl

end Erdos3

end

section

namespace Erdos3

open scoped Classical

theorem affineSampleParameterKernel_centered_bound {ι J I : Type*}
    [DecidableEq ι] [Fintype J] [Fintype I]
    (p q a : ι → ℕ) [∀ i, NeZero (q i)]
    (hp : ∀ i, (p i).Prime) (hq : ∀ i, q i = p i ^ a i) (A : Finset ι)
    (π : ∀ i, FiniteProbabilityWeights (J → ZMod (q i)))
    (hπ : ∀ i ∉ A, π i = FiniteProbabilityWeights.uniform (J → ZMod (q i)))
    (i : ι) (f : (I → ZMod (q i)) → ℝ)
    (hf : (FiniteProbabilityWeights.uniform (I → ZMod (q i))).mean f = 0) :
    (FiniteProbabilityWeights.uniform (Option J × I → ZMod (q i))).mean
      (fun z => (affineSampleParameterKernel (π i) z).mean f ^ 2) ≤
      (if i ∈ A then 1 else (p i : ℝ)⁻¹ ^ Fintype.card J) *
        (FiniteProbabilityWeights.uniform (I → ZMod (q i))).mean (fun x => f x ^ 2) := by
  by_cases hi : i ∈ A
  · rw [ite_eq_left hi, one_mul]
    exact finiteKernel_contraction_sq _ _ _ (affineSampleParameterKernel_preserves_mean (π i)) f
  · rw [ite_eq_right hi, hπ i hi]
    simp only [affineSampleParameterKernel_uniform]
    exact affineSampleKernel_centered_sq (hp i) (hq i) f hf

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem affine_leaf_source_assignments_card_le_exp {ι J σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype J] [Fintype σ]
    (q : ι → ℕ) [∀ i, NeZero (q i)]
    {Good : Finset ι → (∀ i, σ → ZMod (q i)) → Prop}
    {tree : CoordinateDecisionTree ι (fun i => σ → ZMod (q i))}
    {I : Finset ι} {base : ∀ i, σ → ZMod (q i)} {d A : ℕ}
    (h : CoordinateDecisionTree.Valid Good I base tree d) (hA : I.card + d ≤ A)
    {P modLog : ℝ} (hP : 0 ≤ P) (hmodLog : 0 ≤ modLog)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hmoduli : ∀ i, (q i : ℝ) ≤ Real.exp modLog) :
    ((CoordinateDecisionTree.leafSourceAssignments (fun i => Option J × σ → ZMod (q i)) tree I base).card : ℝ) ≤
      Real.exp ((A : ℝ) * (P + (Fintype.card (Option J × σ) : ℝ) * modLog +
        (Fintype.card σ : ℝ) * modLog + 1)) := by
  exact h.leafSourceAssignments_card_le_exp (fun i => Option J × σ → ZMod (q i)) hA hP
    (by positivity) (by positivity) hcount
    (fun i => by simpa only [Fintype.card_fun, ZMod.card] using
      residue_function_alphabet_card_le_exp (I := Option J × σ) (q := q i) (hmoduli i))
    (fun i => residue_function_alphabet_card_le_exp (I := σ) (q := q i) (hmoduli i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J σ : Type*} [Fintype J] [Fintype σ]
  (q : ι → ℕ) [∀ i, NeZero (q i)]

noncomputable def affineParameterProductCoupling
    (π : ∀ i, FiniteProbabilityWeights (J → ZMod (q i))) :
    ∀ i, FiniteProbabilityCoupling
      (primeCoordinateReference (σ := Option J × σ) q i)
      (primeCoordinateReference (σ := σ) q i) :=
  fun i => affineSampleParameterCoupling (π i)

theorem affineSampleParameterCoupling_uniform {q : ℕ} [NeZero q] :
    affineSampleParameterCoupling (I := σ) (FiniteProbabilityWeights.uniform (J → ZMod q)) =
      affineSampleCoupling := rfl

theorem affineSampleParameterKernel_sq (i : ι)
    (π : FiniteProbabilityWeights (J → ZMod (q i))) (f : (σ → ZMod (q i)) → ℝ) :
    (primeCoordinateReference (σ := Option J × σ) q i).mean
      (fun z => (affineSampleParameterKernel π z).mean f ^ 2) ≤
      (primeCoordinateReference (σ := σ) q i).mean (fun y => f y ^ 2) := by
  calc
    _ ≤ (primeCoordinateReference (σ := Option J × σ) q i).mean
        (fun z => (affineSampleParameterKernel π z).mean (fun y => f y ^ 2)) :=
      FiniteProbabilityWeights.mean_mono _ (fun z => (affineSampleParameterKernel π z).mean_square_le f)
    _ = _ := affineSampleParameterKernel_preserves_mean π (fun y => f y ^ 2)

variable [Fintype ι] [DecidableEq ι]

theorem affineParameterProductCoupling_pairing
    (π : ∀ i, FiniteProbabilityWeights (J → ZMod (q i)))
    (w : (∀ i, Option J × σ → ZMod (q i)) → ℝ)
    (f : (∀ i, σ → ZMod (q i)) → ℝ) :
    productCouplingPairing (affineParameterProductCoupling (σ := σ) q π) w f =
      (FiniteProbabilityWeights.pi (primeCoordinateReference (σ := Option J × σ) q)).mean
        (fun z => w z * (FiniteProbabilityWeights.pi π).mean
          (fun t => f (fun i => (affineSampleAlphabetEquiv (z i)).2 +
            residueColumnMap (q := q i) (affineSampleAlphabetEquiv (z i)).1 (t i)))) := by
  change (FiniteProbabilityWeights.pi (fun i =>
    (primeCoordinateReference (σ := Option J × σ) q i).joint (affineSampleParameterKernel (π i)))).mean
      (fun z => w (fun i => (z i).1) * f (fun i => (z i).2)) = _
  rw [productJoint_mean (primeCoordinateReference (σ := Option J × σ) q)
    (fun i => affineSampleParameterKernel (π i)) (fun x y => w x * f y)]
  simp only [FiniteProbabilityWeights.mean_const_mul]
  congr 1
  funext z
  congr 1
  exact (productMean_coordinate_transport π
    (fun i => affineSampleParameterKernel (π i) (z i))
    (fun i t => (affineSampleAlphabetEquiv (z i)).2 +
      residueColumnMap (q := q i) (affineSampleAlphabetEquiv (z i)).1 t)
    (fun i g => (affineSampleParameterKernel_mean (π i) (z i) g).symm) f).symm

omit [Fintype ι] [DecidableEq ι] in
theorem affineParameterProductCoupling_outside
    (π : ∀ i, FiniteProbabilityWeights (J → ZMod (q i))) (K : Finset ι)
    (hπ : ∀ i ∉ K, π i = FiniteProbabilityWeights.uniform (J → ZMod (q i))) :
    (fun i : {i // i ∉ K} => affineParameterProductCoupling (σ := σ) q π i.val) =
      affineSampleProductCoupling (J := J) (σ := σ) (fun i : {i // i ∉ K} => q i.val) := by
  funext i
  change affineSampleParameterCoupling (π i.val) = affineSampleCoupling
  rw [hπ i.val i.property]
  rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
  (q : ι → ℕ) [∀ i, NeZero (q i)] [NeZero (∏ i, q i)]
  (hpair : Pairwise (fun i k => (q i).Coprime (q k)))

noncomputable def affineParameterCRTequiv :
    (J → ZMod (∏ i, q i)) ≃ (∀ i, J → ZMod (q i)) :=
  (Equiv.piCongrRight (fun _ : J => (ZMod.prodEquivPi q hpair).toEquiv)).trans
    (Equiv.piComm (fun (_ : J) i => ZMod (q i)))

omit [DecidableEq ι] [Fintype J] [∀ i, NeZero (q i)] [NeZero (∏ i, q i)] in
theorem affineParameterCRTequiv_apply (s : J → ZMod (∏ i, q i)) (i : ι) (j : J) :
    affineParameterCRTequiv q hpair s i j =
      (ZMod.castHom (Finset.dvd_prod_of_mem q (Finset.mem_univ i)) (ZMod (q i))) (s j) :=
  ZMod.prodEquivPi_apply q hpair (s j) i

theorem affineParameterCRT_mean (f : (∀ i, J → ZMod (q i)) → ℝ) :
    (FiniteProbabilityWeights.uniform (J → ZMod (∏ i, q i))).mean
      (fun s => f (affineParameterCRTequiv q hpair s)) =
      (FiniteProbabilityWeights.pi (fun i => FiniteProbabilityWeights.uniform (J → ZMod (q i)))).mean f := by
  rw [FiniteProbabilityWeights.uniform_mean_equiv (affineParameterCRTequiv q hpair) f]
  have hweight : FiniteProbabilityWeights.uniform (∀ i, J → ZMod (q i)) =
      FiniteProbabilityWeights.pi (fun i => FiniteProbabilityWeights.uniform (J → ZMod (q i))) := by
    apply FiniteProbabilityWeights.eq_of_weight_eq
    intro x
    change (Fintype.card (∀ i, J → ZMod (q i)) : ℝ)⁻¹ =
      ∏ i, (Fintype.card (J → ZMod (q i)) : ℝ)⁻¹
    rw [Fintype.card_pi, Nat.cast_prod, Finset.prod_inv_distrib]
  rw [hweight]

theorem affinePeriodParameterLaw_CRT (D : ℕ) (a : J → ℤ)
    (f : (∀ i, J → ZMod (q i)) → ℝ) :
    (FiniteProbabilityWeights.uniform (J → ZMod (∏ i, q i))).mean
      (fun s => f (fun i j => (a j : ZMod (q i)) +
        (D : ZMod (q i)) * affineParameterCRTequiv q hpair s i j)) =
      (FiniteProbabilityWeights.pi (fun i => affinePeriodParameterLaw (q := q i) D a)).mean f := by
  rw [affineParameterCRT_mean q hpair
    (fun s => f (fun i j => (a j : ZMod (q i)) + (D : ZMod (q i)) * s i j))]
  exact productMean_coordinate_transport
    (fun i => FiniteProbabilityWeights.uniform (J → ZMod (q i)))
    (fun i => affinePeriodParameterLaw (q := q i) D a)
    (fun i s j => (a j : ZMod (q i)) + (D : ZMod (q i)) * s j)
    (fun i g => (affinePeriodParameterLaw_mean D a g).symm) f

omit [DecidableEq ι] [Fintype J] [∀ i, NeZero (q i)] in
theorem affineParameterCRTequiv_integer (s : J → ZMod (∏ i, q i)) (i : ι) (j : J) :
    affineParameterCRTequiv q hpair s i j = ((s j).val : ZMod (q i)) := by
  rw [affineParameterCRTequiv_apply]
  have h := map_natCast (ZMod.castHom (Finset.dvd_prod_of_mem q (Finset.mem_univ i)) (ZMod (q i))) (s j).val
  simpa only [ZMod.natCast_zmod_val] using h

include hpair in
theorem affinePeriodParameterLaw_CRT_integer (D : ℕ) (a : J → ℤ)
    (f : (∀ i, J → ZMod (q i)) → ℝ) :
    (FiniteProbabilityWeights.uniform (J → ZMod (∏ i, q i))).mean
      (fun s => f (fun i j => ((a j + (D : ℤ) * (s j).val : ℤ) : ZMod (q i)))) =
      (FiniteProbabilityWeights.pi (fun i => affinePeriodParameterLaw (q := q i) D a)).mean f := by
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, affineParameterCRTequiv_integer]
    using affinePeriodParameterLaw_CRT q hpair D a f

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J σ : Type*} [Fintype J] [Fintype σ]
  (q : ι → ℕ) [∀ i, NeZero (q i)]

noncomputable def affinePeriodProductCoupling (D : ℕ) (a : J → ℤ) :
    ∀ i, FiniteProbabilityCoupling
      (primeCoordinateReference (σ := Option J × σ) q i)
      (primeCoordinateReference (σ := σ) q i) :=
  affineParameterProductCoupling q (fun i => affinePeriodParameterLaw (q := q i) D a)

theorem affinePeriodProductCoupling_outside (D : ℕ) (a : J → ℤ) (K : Finset ι)
    (hD : ∀ i ∉ K, D.Coprime (q i)) :
    (fun i : {i // i ∉ K} => affinePeriodProductCoupling (σ := σ) q D a i.val) =
      affineSampleProductCoupling (J := J) (σ := σ) (fun i : {i // i ∉ K} => q i.val) :=
  affineParameterProductCoupling_outside q _ K
    (fun i hi => affinePeriodParameterLaw_uniform D a (hD i hi))

variable [Fintype ι] [DecidableEq ι]

theorem affinePeriodProductCoupling_pairing (D : ℕ) (a : J → ℤ)
    (w : (∀ i, Option J × σ → ZMod (q i)) → ℝ)
    (f : (∀ i, σ → ZMod (q i)) → ℝ) :
    productCouplingPairing (affinePeriodProductCoupling (σ := σ) q D a) w f =
      (FiniteProbabilityWeights.pi (primeCoordinateReference (σ := Option J × σ) q)).mean
        (fun z => w z * (FiniteProbabilityWeights.pi
          (fun i => FiniteProbabilityWeights.uniform (J → ZMod (q i)))).mean
          (fun s => f (fun i => (affineSampleAlphabetEquiv (z i)).2 +
            residueColumnMap (q := q i) (affineSampleAlphabetEquiv (z i)).1
              (fun j => (a j : ZMod (q i)) + (D : ZMod (q i)) * s i j)))) := by
  rw [affinePeriodProductCoupling, affineParameterProductCoupling_pairing]
  congr 1
  funext z
  congr 1
  exact (productMean_coordinate_transport
    (fun i => FiniteProbabilityWeights.uniform (J → ZMod (q i)))
    (fun i => affinePeriodParameterLaw (q := q i) D a)
    (fun i s j => (a j : ZMod (q i)) + (D : ZMod (q i)) * s j)
    (fun i g => (affinePeriodParameterLaw_mean D a g).symm) _).symm

omit [Fintype ι] in
theorem affinePeriodParameterKernel_centered_sq
    (D : ℕ) (a : J → ℤ) (K : Finset ι) (prime power : ι → ℕ)
    (hprime : ∀ i, (prime i).Prime) (hpower : ∀ i, q i = prime i ^ power i)
    (hD : ∀ i ∉ K, D.Coprime (q i))
    {κ : ℝ} (hκ : 0 ≤ κ) (hJ : 2 ≤ Fintype.card J)
    (hlarge : ∀ i ∉ K, (prime i : ℝ)⁻¹ ≤ κ)
    (i : ι) (f : (σ → ZMod (q i)) → ℝ)
    (hf : (primeCoordinateReference (σ := σ) q i).mean f = 0) :
    (primeCoordinateReference (σ := Option J × σ) q i).mean
      (fun z => (affineSampleParameterKernel (affinePeriodParameterLaw D a) z).mean f ^ 2) ≤
      (if i ∈ K then 1 else κ ^ 2) *
        (primeCoordinateReference (σ := σ) q i).mean (fun y => f y ^ 2) := by
  by_cases hi : i ∈ K
  · rw [ite_eq_left hi, one_mul]
    exact affineSampleParameterKernel_sq q i _ f
  · rw [ite_eq_right hi, affinePeriodParameterLaw_uniform D a (hD i hi)]
    exact affineSampleKernel_centered_sq_of_inverse_le (hprime i) (hpower i) hJ hκ (hlarge i hi) f hf

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J I : Type*} [Fintype J] [Fintype I]
  (q : ι → ℕ) [∀ i, NeZero (q i)]

noncomputable def affinePeriodResidueSample (D : ℕ) (a : J → ℤ)
    (z : ∀ i, Option J × I → ZMod (q i)) (s : ∀ i, J → ZMod (q i)) :
    ∀ i, I → ZMod (q i) :=
  fun i => (affineSampleAlphabetEquiv (z i)).2 +
    residueColumnMap (q := q i) (affineSampleAlphabetEquiv (z i)).1
      (fun j => (a j : ZMod (q i)) + (D : ZMod (q i)) * s i j)

omit [Fintype I] [∀ i, NeZero (q i)] in
theorem affinePeriodResidueSample_integer (D : ℕ) (a t : J → ℤ)
    (z : Option J × I → ℤ) :
    primeCoordinateObservation q (smoothAffineSample (fun j => a j + (D : ℤ) * t j) z) =
      affinePeriodResidueSample q D a (primeCoordinateObservation q z) (primeCoordinateObservation q t) := by
  funext i k
  simp [primeCoordinateObservation, smoothAffineSample, affinePeriodResidueSample,
    affineSampleAlphabetEquiv, residueColumnMap]
  rfl

omit [Fintype I] [∀ i, NeZero (q i)] in
theorem affinePeriodResidueSample_depends (D : ℕ) (a : J → ℤ)
    (z : ∀ i, Option J × I → ZMod (q i)) (S : Finset ι)
    (f : (∀ i, I → ZMod (q i)) → ℝ) (hf : ProductDependsOn S f) :
    ProductDependsOn S (fun s => f (affinePeriodResidueSample q D a z s)) := by
  intro s t hst
  apply hf
  intro i hi
  dsimp only [affinePeriodResidueSample]
  rw [hst i hi]

variable [Fintype ι] [DecidableEq ι]

theorem affinePeriodProductCoupling_observed {Ω : Type*} [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, Option J × I → ZMod (q i))
    (D : ℕ) (a : J → ℤ) (w : Ω → ℝ) (f : (∀ i, I → ZMod (q i)) → ℝ) :
    productCouplingPairing (affinePeriodProductCoupling (σ := I) q D a)
      (observedProductDensity (primeCoordinateReference (σ := Option J × I) q) p F w) f =
      p.mean (fun z => w z * (FiniteProbabilityWeights.pi
        (primeCoordinateReference (σ := J) q)).mean
          (fun s => f (affinePeriodResidueSample q D a (F z) s))) := by
  rw [affinePeriodProductCoupling_pairing]
  exact observedProductDensity_test (primeCoordinateReference (σ := Option J × I) q) p F
    (primeCoordinateReference_weight_pos q) w _

theorem affinePeriodTruncatedPairing_observed {Ω : Type*} [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, Option J × I → ZMod (q i))
    (D : ℕ) (a : J → ℤ) (supports : Finset (Finset ι))
    (w : Ω → ℝ) (f : (∀ i, I → ZMod (q i)) → ℝ) :
    productTruncatedPairing (affinePeriodProductCoupling (σ := I) q D a) supports
      (observedProductDensity (primeCoordinateReference (σ := Option J × I) q) p F w) f =
      p.mean (fun z => w z * (FiniteProbabilityWeights.pi
        (primeCoordinateReference (σ := J) q)).mean
          (fun s => productANOVATruncation (primeCoordinateReference (σ := I) q) supports f
            (affinePeriodResidueSample q D a (F z) s))) := by
  rw [← productCouplingPairing_truncation_right]
  exact affinePeriodProductCoupling_observed q p F D a w _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype J] [Fintype σ]
  (q : ι → ℕ) [∀ i, NeZero (q i)] [NeZero (∏ i, q i)]
  (hpair : Pairwise (fun i k => (q i).Coprime (q k)))

include hpair in
theorem affinePeriodProductCoupling_pairing_CRT (D : ℕ) (a : J → ℤ)
    (w : (∀ i, Option J × σ → ZMod (q i)) → ℝ)
    (f : (∀ i, σ → ZMod (q i)) → ℝ) :
    productCouplingPairing (affinePeriodProductCoupling (σ := σ) q D a) w f =
      (FiniteProbabilityWeights.pi (primeCoordinateReference (σ := Option J × σ) q)).mean
        (fun z => w z * (FiniteProbabilityWeights.uniform (J → ZMod (∏ i, q i))).mean
          (fun s => f (fun i => (affineSampleAlphabetEquiv (z i)).2 +
            residueColumnMap (q := q i) (affineSampleAlphabetEquiv (z i)).1
              (fun j => ((a j + (D : ℤ) * (s j).val : ℤ) : ZMod (q i)))))) := by
  rw [affinePeriodProductCoupling, affineParameterProductCoupling_pairing]
  congr 1
  funext z
  congr 1
  exact (affinePeriodParameterLaw_CRT_integer q hpair D a _).symm

omit [Fintype σ] in
include hpair in
theorem affinePeriodParameterLaw_physical_site (D : ℕ) (a : J → ℤ)
    (z : Option J × σ → ℤ) (f : (∀ i, σ → ZMod (q i)) → ℝ) :
    (FiniteProbabilityWeights.pi (fun i => affinePeriodParameterLaw (q := q i) D a)).mean
      (fun t => f (fun i => (affinePrimeCoordinateObservation q z i).2 +
        residueColumnMap (q := q i) (affinePrimeCoordinateObservation q z i).1 (t i))) =
      (FiniteProbabilityWeights.uniform (J → ZMod (∏ i, q i))).mean
        (fun s => f (primeCoordinateObservation q
          (BooleanCubeKernel.integerPhysicalSite (fun j => a j + (D : ℤ) * (s j).val) z))) := by
  rw [← affinePeriodParameterLaw_CRT_integer q hpair D a]
  congr 1
  funext s
  apply congrArg f
  funext i
  exact (affinePrimeCoordinateObservation_site q (fun j => a j + (D : ℤ) * (s j).val) z i).symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J I Ω Θ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype J] [Fintype I] [Fintype Ω] [Fintype Θ]
  (q : ι → ℕ) [∀ i, NeZero (q i)]

theorem affinePeriodTruncatedPairing_comparison
    (p : FiniteProbabilityWeights Ω) (r : FiniteProbabilityWeights Θ)
    (F : Ω → ∀ i, Option J × I → ZMod (q i)) (G : Θ → ∀ i, J → ZMod (q i))
    (D : ℕ) (a : J → ℤ) (supports : Finset (Finset ι))
    (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1)
    (f : (∀ i, I → ZMod (q i)) → ℝ) {b : ℕ} {eta C : ℝ} (heta : 0 ≤ eta)
    (hcard : ∀ S ∈ supports, S.card ≤ b)
    (hclose : ProductMarginalsClose (primeCoordinateReference (σ := J) q)
      (observedProductDensity (primeCoordinateReference (σ := J) q) r G (fun _ => 1)) eta b)
    (hcap : ∀ S ∈ supports, ∀ x, |productANOVA (primeCoordinateReference (σ := I) q) S f x| ≤ C) :
    |p.mean (fun z => w z * r.mean (fun t =>
        productANOVATruncation (primeCoordinateReference (σ := I) q) supports f
          (affinePeriodResidueSample q D a (F z) (G t)))) -
      productTruncatedPairing (affinePeriodProductCoupling (σ := I) q D a) supports
        (observedProductDensity (primeCoordinateReference (σ := Option J × I) q) p F w) f| ≤
      eta * supports.card * C := by
  rw [affinePeriodTruncatedPairing_observed, ← p.mean_sub]
  apply p.abs_mean_le_on_support
  intro z _
  have he := observedProductDensity_family_test_error (primeCoordinateReference (σ := J) q)
    r G (primeCoordinateReference_weight_pos q) supports
    (fun S s => productANOVA (primeCoordinateReference (σ := I) q) S f
      (affinePeriodResidueSample q D a (F z) s)) heta hcard
    (fun S _ => affinePeriodResidueSample_depends q D a (F z) S _
      (productANOVA_depends (primeCoordinateReference (σ := I) q) S f))
    hclose (fun S hS x => hcap S hS (affinePeriodResidueSample q D a (F z) x))
  change |r.mean (fun t => productANOVATruncation (primeCoordinateReference (σ := I) q) supports f
      (affinePeriodResidueSample q D a (F z) (G t))) -
    (FiniteProbabilityWeights.pi (primeCoordinateReference (σ := J) q)).mean
      (fun s => productANOVATruncation (primeCoordinateReference (σ := I) q) supports f
        (affinePeriodResidueSample q D a (F z) s))| ≤ _ at he
  rw [← mul_sub, abs_mul, abs_of_nonneg (hw z).1]
  exact (mul_le_mul (hw z).2 he (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem affinePeriodTruncation_sample_comparison
    (p : FiniteProbabilityWeights Ω) (r : FiniteProbabilityWeights Θ)
    (source : Ω → Option J × I → ℤ) (index : Θ → J → ℤ)
    (D : ℕ) (a : J → ℤ) (supports : Finset (Finset ι))
    (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1)
    (f : (∀ i, I → ZMod (q i)) → ℝ) {b : ℕ} {eta C : ℝ} (heta : 0 ≤ eta)
    (hcard : ∀ S ∈ supports, S.card ≤ b)
    (hclose : ProductMarginalsClose (primeCoordinateReference (σ := J) q)
      (observedProductDensity (primeCoordinateReference (σ := J) q) r
        (fun t => primeCoordinateObservation q (index t)) (fun _ => 1)) eta b)
    (hcap : ∀ S ∈ supports, ∀ x, |productANOVA (primeCoordinateReference (σ := I) q) S f x| ≤ C) :
    |p.mean (fun z => w z * r.mean (fun t =>
        productANOVATruncation (primeCoordinateReference (σ := I) q) supports f
          (primeCoordinateObservation q
            (smoothAffineSample (fun j => a j + (D : ℤ) * index t j) (source z))))) -
      productTruncatedPairing (affinePeriodProductCoupling (σ := I) q D a) supports
        (observedProductDensity (primeCoordinateReference (σ := Option J × I) q) p
          (fun z => primeCoordinateObservation q (source z)) w) f| ≤
      eta * supports.card * C := by
  simp only [affinePeriodResidueSample_integer]
  exact affinePeriodTruncatedPairing_comparison q p r
    (fun z => primeCoordinateObservation q (source z))
    (fun t => primeCoordinateObservation q (index t)) D a supports w hw f heta hcard hclose hcap

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem residuePrimeCoordinateDensity_component_cap {ι I : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]
    (lo : I → ℤ) (N : I → ℕ) (M : ℕ) (a : I → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun i => lo i + N i) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (b : ℕ) (f : (I → ℤ) → ℝ)
    (hf : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ f z ∧ f z ≤ 1)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hclose : ProductMarginalsClose (primeCoordinateReference (σ := I) q)
      (residuePrimeCoordinateDensity lo N M a hne q (fun _ => 1)) eta b)
    (S : Finset ι) (hS : S.card ≤ b) (x : ∀ i, I → ZMod (q i)) :
    |productANOVA (primeCoordinateReference (σ := I) q) S
      (residuePrimeCoordinateDensity lo N M a hne q f) x| ≤ (2 : ℝ) ^ b * (1 + eta) := by
  let := hne
  have hw (z : IntegerResidueBox lo (fun i => lo i + N i) (fun _ => (M : ℤ)) a) :
      0 ≤ f (fun i => (z i).val) ∧ f (fun i => (z i).val) ≤ 1 := by
    apply hf
    apply (mem_translatedIntegerBox lo N _).mpr
    intro i
    exact Finset.mem_Ico.mp (Finset.mem_filter.mp (z i).property).1
  have h := observedProductDensity_component_cap (primeCoordinateReference (σ := I) q)
    (FiniteProbabilityWeights.uniform
      (IntegerResidueBox lo (fun i => lo i + N i) (fun _ => (M : ℤ)) a))
    (fun z => primeCoordinateObservation q (fun i => (z i).val))
    (primeCoordinateReference_weight_pos q) (fun z => f (fun i => (z i).val))
    zero_le_one heta hw hclose S hS x
  simpa only [mul_one, residuePrimeCoordinateDensity] using h

variable {ι J I : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
  [Fintype I]
  (q : ι → ℕ) [∀ i, NeZero (q i)]
  (sourceLo : Option J × I → ℤ) (sourceN : Option J × I → ℕ)
  (sourceHne : Nonempty (IntegerResidueBox sourceLo (fun i => sourceLo i + sourceN i)
    (fun _ => 1) (fun _ => 0)))
  (paramLo : J → ℤ) (paramN : J → ℕ)
  (paramHne : Nonempty (IntegerResidueBox paramLo (fun j => paramLo j + paramN j)
    (fun _ => 1) (fun _ => 0)))
  (siteLo : I → ℤ) (siteN : I → ℕ)
  (siteHne : Nonempty (IntegerResidueBox siteLo (fun i => siteLo i + siteN i)
    (fun _ => 1) (fun _ => 0)))
  (D : ℕ) (a : J → ℤ) (b : ℕ) (w : (Option J × I → ℤ) → ℝ) (f : (I → ℤ) → ℝ)

noncomputable def residueAffineTruncationError : ℝ :=
  |(𝔼 z : IntegerResidueBox sourceLo (fun i => sourceLo i + sourceN i) (fun _ => 1) (fun _ => 0),
      w (fun i => (z i).val) *
        (𝔼 t : IntegerResidueBox paramLo (fun j => paramLo j + paramN j) (fun _ => 1) (fun _ => 0),
          residuePhysicalTruncation siteLo siteN 1 (fun _ => 0) siteHne q b f
            (smoothAffineSample (fun j => a j + (D : ℤ) * (t j).val) (fun i => (z i).val)))) -
    productTruncatedPairing (affinePeriodProductCoupling (σ := I) q D a) (lowDegreeCoordinateSets ι b)
      (residuePrimeCoordinateDensity sourceLo sourceN 1 (fun _ => 0) sourceHne q w)
      (residuePrimeCoordinateDensity siteLo siteN 1 (fun _ => 0) siteHne q f)|

theorem residueAffineTruncation_comparison
    (hw : ∀ z ∈ translatedIntegerBox sourceLo sourceN, 0 ≤ w z ∧ w z ≤ 1)
    (hf : ∀ z ∈ translatedIntegerBox siteLo siteN, 0 ≤ f z ∧ f z ≤ 1)
    {etaParam etaSite : ℝ} (hparam : 0 ≤ etaParam) (hsite : 0 ≤ etaSite)
    (hcloseParam : ProductMarginalsClose (primeCoordinateReference (σ := J) q)
      (residuePrimeCoordinateDensity paramLo paramN 1 (fun _ => 0) paramHne q (fun _ => 1)) etaParam b)
    (hcloseSite : ProductMarginalsClose (primeCoordinateReference (σ := I) q)
      (residuePrimeCoordinateDensity siteLo siteN 1 (fun _ => 0) siteHne q (fun _ => 1)) etaSite b) :
    residueAffineTruncationError q sourceLo sourceN sourceHne paramLo paramN
      siteLo siteN siteHne D a b w f ≤ etaParam * residueTruncationCap ι b etaSite := by
  let := sourceHne
  let := paramHne
  have hw' (z : IntegerResidueBox sourceLo (fun i => sourceLo i + sourceN i) (fun _ => 1) (fun _ => 0)) :
      0 ≤ w (fun i => (z i).val) ∧ w (fun i => (z i).val) ≤ 1 := by
    apply hw
    apply (mem_translatedIntegerBox sourceLo sourceN _).mpr
    intro i
    exact Finset.mem_Ico.mp (Finset.mem_filter.mp (z i).property).1
  have h := affinePeriodTruncation_sample_comparison q
    (FiniteProbabilityWeights.uniform
      (IntegerResidueBox sourceLo (fun i => sourceLo i + sourceN i) (fun _ => 1) (fun _ => 0)))
    (FiniteProbabilityWeights.uniform
      (IntegerResidueBox paramLo (fun j => paramLo j + paramN j) (fun _ => 1) (fun _ => 0)))
    (fun z i => (z i).val) (fun t j => (t j).val) D a (lowDegreeCoordinateSets ι b)
    (fun z => w (fun i => (z i).val)) hw'
    (residuePrimeCoordinateDensity siteLo siteN 1 (fun _ => 0) siteHne q f)
    hparam (fun S hS => (mem_lowDegreeCoordinateSets ι b S).mp hS) hcloseParam
    (fun S hS x => residuePrimeCoordinateDensity_component_cap siteLo siteN 1 (fun _ => 0)
      siteHne q b f hf hsite hcloseSite S ((mem_lowDegreeCoordinateSets ι b S).mp hS) x)
  convert h using 1 <;>
    simp only [residueAffineTruncationError, residuePhysicalTruncation, residuePrimeCoordinateDensity,
      FiniteProbabilityWeights.uniform_mean, residueTruncationCap, mul_assoc]
  congr 1

include paramHne in
theorem residueAffineTruncation_comparison_of_lengths
    (hw : ∀ z ∈ translatedIntegerBox sourceLo sourceN, 0 ≤ w z ∧ w z ≤ 1)
    (hf : ∀ z ∈ translatedIntegerBox siteLo siteN, 0 ≤ f z ∧ f z ≤ 1)
    (hpair : Pairwise (fun i l => (q i).Coprime (q l)))
    (modLog dimLog accLog etaParam etaSite : ℝ)
    (hmodLog : 0 ≤ modLog) (hparam : etaParam ≤ 1) (hsite : 0 ≤ etaSite)
    (haccuracy : Real.exp (-accLog) ≤ etaParam)
    (hmoduli : ∀ i, (q i : ℝ) ≤ Real.exp modLog)
    (hdim : (Fintype.card J : ℝ) ≤ Real.exp dimLog)
    (hlength : ∀ j, Real.exp (modLog * b + accLog + dimLog + 1) ≤
      (residueIndexLength (paramLo j) (paramLo j + paramN j) 1 0 : ℝ))
    (hcloseSite : ProductMarginalsClose (primeCoordinateReference (σ := I) q)
      (residuePrimeCoordinateDensity siteLo siteN 1 (fun _ => 0) siteHne q (fun _ => 1)) etaSite b) :
    residueAffineTruncationError q sourceLo sourceN sourceHne paramLo paramN
      siteLo siteN siteHne D a b w f ≤ etaParam * residueTruncationCap ι b etaSite := by
  have hc := residuePrimeDensity_close_of_lengths paramLo paramN 1 (fun _ => 0) paramHne q
    (by decide) (fun i => Nat.coprime_one_left (q i)) hpair b modLog dimLog accLog etaParam
    hmodLog hparam haccuracy hmoduli hdim hlength
  exact residueAffineTruncation_comparison q sourceLo sourceN sourceHne paramLo paramN paramHne
    siteLo siteN siteHne D a b w f hw hf ((Real.exp_pos _).le.trans haccuracy) hsite hc hcloseSite

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι I : Type*} [Fintype ι] [DecidableEq ι] [Fintype I]

theorem physicalBoxTruncation_of_classify_some (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hpos : ∀ i c, 0 < (P i).length c)
    (q : ι → ℕ) [∀ i, NeZero (q i)] (b : ℕ) (f : (I → ℤ) → ℝ)
    (x : I → ℤ) (c : ∀ i, (P i).Label) (hx : physicalBoxClassify lo N P x = some c) :
    physicalBoxTruncation lo N P hpos q b f x =
      residuePhysicalTruncation (fun i => intervalCellLower (lo i) (P i) (c i))
        (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q b f x := by
  by_cases h : x ∈ translatedIntegerBox lo N
  · simp only [physicalBoxClassify, dite_eq_left h, Option.some.injEq] at hx
    simp only [physicalBoxTruncation, dite_eq_left h]
    rw [hx]
  · simp only [physicalBoxClassify, dite_eq_right h] at hx
    cases hx

theorem physicalBoxTruncation_of_classify_none (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hpos : ∀ i c, 0 < (P i).length c)
    (q : ι → ℕ) [∀ i, NeZero (q i)] (b : ℕ) (f : (I → ℤ) → ℝ)
    (x : I → ℤ) (hx : physicalBoxClassify lo N P x = none) :
    physicalBoxTruncation lo N P hpos q b f x = 0 := by
  by_cases h : x ∈ translatedIntegerBox lo N
  · simp only [physicalBoxClassify, dite_eq_left h] at hx
    cases hx
  · simp only [physicalBoxTruncation, dite_eq_right h]

theorem retained_physical_truncation_crt {J : Type*} [Fintype J]
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i c, (P i).step c = 1) (hpos : ∀ i c, 0 < (P i).length c)
    (c : ∀ i, (P i).Label) (q : ι → ℕ) [∀ i, NeZero (q i)]
    (sourceLo : Option J × I → ℤ) (sourceN : Option J × I → ℕ)
    (sourceHne : Nonempty (IntegerResidueBox sourceLo (fun i => sourceLo i + sourceN i)
      (fun _ => 1) (fun _ => 0)))
    (paramLo : J → ℤ) (paramN : J → ℕ)
    (paramHne : Nonempty (IntegerResidueBox paramLo (fun j => paramLo j + paramN j)
      (fun _ => 1) (fun _ => 0)))
    (D : ℕ) (a : J → ℤ) (b : ℕ) (w : (Option J × I → ℤ) → ℝ) (f : (I → ℤ) → ℝ)
    (hw : ∀ z ∈ translatedIntegerBox sourceLo sourceN, 0 ≤ w z ∧ w z ≤ 1)
    (hf : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ f x ∧ f x ≤ 1)
    (hretained : ∀ z ∈ translatedIntegerBox sourceLo sourceN,
      ∀ t ∈ translatedIntegerBox paramLo paramN,
        physicalBoxClassify lo N P (smoothAffineSample (fun j => a j + (D : ℤ) * t j) z) = some c)
    {etaParam etaSite : ℝ} (hparam : 0 ≤ etaParam) (hsite : 0 ≤ etaSite)
    (hcloseParam : ProductMarginalsClose (primeCoordinateReference (σ := J) q)
      (residuePrimeCoordinateDensity paramLo paramN 1 (fun _ => 0) paramHne q (fun _ => 1)) etaParam b)
    (hcloseSite : ProductMarginalsClose (primeCoordinateReference (σ := I) q)
      (residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
        (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c)
        q (fun _ => 1)) etaSite b) :
    |(𝔼 z : IntegerResidueBox sourceLo (fun i => sourceLo i + sourceN i) (fun _ => 1) (fun _ => 0),
        w (fun i => (z i).val) *
          (𝔼 t : IntegerResidueBox paramLo (fun j => paramLo j + paramN j) (fun _ => 1) (fun _ => 0),
            physicalBoxTruncation lo N P hpos q b f
              (smoothAffineSample (fun j => a j + (D : ℤ) * (t j).val) (fun i => (z i).val)))) -
      productTruncatedPairing (affinePeriodProductCoupling (σ := I) q D a) (lowDegreeCoordinateSets ι b)
        (residuePrimeCoordinateDensity sourceLo sourceN 1 (fun _ => 0) sourceHne q w)
        (residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
          (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q f)| ≤
      etaParam * residueTruncationCap ι b etaSite := by
  have he (z : IntegerResidueBox sourceLo (fun i => sourceLo i + sourceN i) (fun _ => 1) (fun _ => 0))
      (t : IntegerResidueBox paramLo (fun j => paramLo j + paramN j) (fun _ => 1) (fun _ => 0)) :
      physicalBoxTruncation lo N P hpos q b f
          (smoothAffineSample (fun j => a j + (D : ℤ) * (t j).val) (fun i => (z i).val)) =
        residuePhysicalTruncation (fun i => intervalCellLower (lo i) (P i) (c i))
          (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q b f
          (smoothAffineSample (fun j => a j + (D : ℤ) * (t j).val) (fun i => (z i).val)) := by
    apply physicalBoxTruncation_of_classify_some
    apply hretained
    · exact (mem_translatedIntegerBox _ _ _).mpr
        (fun i => Finset.mem_Ico.mp (Finset.mem_filter.mp (z i).property).1)
    · exact (mem_translatedIntegerBox _ _ _).mpr
        (fun j => Finset.mem_Ico.mp (Finset.mem_filter.mp (t j).property).1)
  simp_rw [he]
  exact residueAffineTruncation_comparison q sourceLo sourceN sourceHne paramLo paramN paramHne
    (fun i => intervalCellLower (lo i) (P i) (c i)) (fun i => (P i).length (c i))
    (physicalBoxCell_nonempty lo N P hpos c) D a b w f hw
    (fun x hx => hf x (physicalBoxCell_subset lo N P hstep hpos c hx))
    hparam hsite hcloseParam hcloseSite

end Erdos3

end

end OAI
