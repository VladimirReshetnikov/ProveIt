/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.BigOperators
import OAI.Compat.TensorProduct
import Mathlib.Data.Finsupp.Weight
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Pi
import OAI.Combinatorics.Progressions.Geometry.IndependentProductTransport
import OAI.Combinatorics.Progressions.Lattices.IntegralAffineModeRemoval
import OAI.Combinatorics.Progressions.Polynomial.PolynomialTermCount
import OAI.Combinatorics.Progressions.Polynomial.PrincipalMonomialScale

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct Classical

variable {σ R W Z : Type*} [CommRing R] [AddCommGroup W] [Module R W]
  [AddCommGroup Z] [Module R Z]

def Homogeneous (h : ℕ) (p : VectorPolynomial σ R W) : Prop :=
  ∀ d : σ →₀ ℕ, d.degree ≠ h → coefficients p d = 0

theorem homogeneous_tmul {P : MvPolynomial σ R} {h : ℕ} (hP : P.IsHomogeneous h) (w : W) :
    Homogeneous h (P ⊗ₜ[R] w) := by
  intro d hd
  rw [coefficients_tmul, hP.coeff_eq_zero hd, zero_smul]

theorem homogeneous_support_degree {p : VectorPolynomial σ R W} {h : ℕ}
    (hp : Homogeneous h p) {d : σ →₀ ℕ} (hd : d ∈ (coefficients p).support) : d.degree = h := by
  by_contra hn
  exact (Finsupp.mem_support_iff.mp hd) (hp d hn)

theorem eq_of_homogeneous_tmul (f g : VectorPolynomial σ R W →ₗ[R] Z) (h : ℕ)
    (he : ∀ (P : MvPolynomial σ R), P.IsHomogeneous h → ∀ w, f (P ⊗ₜ[R] w) = g (P ⊗ₜ[R] w))
    {p : VectorPolynomial σ R W} (hp : Homogeneous h p) : f p = g p := by
  have hexp := sum_monomial_coefficients p
  conv_lhs => rw [← hexp]
  conv_rhs => rw [← hexp]
  simp only [Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  exact he (MvPolynomial.monomial d 1)
    (MvPolynomial.isHomogeneous_monomial 1 (homogeneous_support_degree hp hd)) (coefficients p d)

noncomputable def siteEvaluation {ι : Type*} (x : ι → σ → R) :
    VectorPolynomial σ R W →ₗ[R] (ι → W) := LinearMap.pi (fun i => eval (x i))

theorem siteEvaluation_tmul {ι : Type*} (x : ι → σ → R) (P : MvPolynomial σ R) (w : W) :
    siteEvaluation x (P ⊗ₜ[R] w) = fun i => MvPolynomial.eval (x i) P • w := rfl

noncomputable def siteFunctional {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → R) →ₗ[R] (W →ₗ[R] R)) : (ι → W) →ₗ[R] R :=
  ∑ i, (L (Pi.single i 1)).comp (LinearMap.proj i)

theorem siteFunctional_tmul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → R) →ₗ[R] (W →ₗ[R] R)) (z : ι → R) (w : W) :
    siteFunctional L (fun i => z i • w) = L z w := by
  have hz : z = ∑ i, z i • Pi.single i (1 : R) := by
    ext j
    simp [Pi.single_apply]
  conv_rhs => rw [hz]
  simp only [siteFunctional, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.proj_apply]

theorem curried_nonfactor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → σ → R) (Λ : VectorPolynomial σ R W →ₗ[R] R) (h : ℕ)
    (hn : ¬ ∃ M : (ι → W) →ₗ[R] R, ∀ p, Homogeneous h p → Λ p = M (siteEvaluation x p)) :
    ¬ ∃ L : (ι → R) →ₗ[R] (W →ₗ[R] R),
      ∀ P, P.IsHomogeneous h → TensorProduct.curry Λ P = L (fun i => MvPolynomial.eval (x i) P) := by
  rintro ⟨L, hL⟩
  apply hn
  refine ⟨siteFunctional L, ?_⟩
  intro p hp
  apply eq_of_homogeneous_tmul Λ ((siteFunctional L).comp (siteEvaluation x)) h _ hp
  intro P hP w
  have he := congrArg (fun F : W →ₗ[R] R => F w) (hL P hP)
  rw [TensorProduct.curry_apply] at he
  change Λ (P ⊗ₜ[R] w) = siteFunctional L (siteEvaluation x (P ⊗ₜ[R] w))
  rw [siteEvaluation_tmul, siteFunctional_tmul]
  exact he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {I R S W : Type*} [CommRing R] [CommRing S] [AddCommGroup W] [Module R W]

noncomputable def homogeneousPart (h : ℕ) :
    VectorPolynomial I R W →ₗ[R] VectorPolynomial I R W :=
  (MvPolynomial.homogeneousComponent h).rTensor W

theorem homogeneousPart_tmul (h : ℕ) (P : MvPolynomial I R) (w : W) :
    homogeneousPart h (P ⊗ₜ[R] w) = MvPolynomial.homogeneousComponent h P ⊗ₜ[R] w := rfl

theorem coefficients_homogeneousPart (h : ℕ) (p : VectorPolynomial I R W) (d : I →₀ ℕ) :
    coefficients (homogeneousPart h p) d = if d.degree = h then coefficients p d else 0 := by
  classical
  induction p using TensorProduct.inductionOn with
  | tmul P w =>
    rw [homogeneousPart_tmul, coefficients_tmul, MvPolynomial.coeff_homogeneousComponent,
      coefficients_tmul]
    split <;> simp_all
  | add p q hp hq =>
    simp only [map_add, Finsupp.add_apply, hp, hq]
    split <;> simp

theorem homogeneousPart_homogeneous (h : ℕ) (p : VectorPolynomial I R W) :
    Homogeneous h (homogeneousPart h p) := by
  intro d hd
  simp only [coefficients_homogeneousPart, ite_eq_right hd]

theorem homogeneousPart_eq_self {h : ℕ} {p : VectorPolynomial I R W} (hp : Homogeneous h p) :
    homogeneousPart h p = p := by
  apply coefficients.injective
  ext d
  rw [coefficients_homogeneousPart]
  split
  · rfl
  · exact (hp d ‹_›).symm

theorem sub_homogeneousPart_degreeLE {n : ℕ} {p : VectorPolynomial I R W}
    (hp : DegreeLE (1 : I → ℕ) (n + 1) p) :
    DegreeLE (1 : I → ℕ) n (p - homogeneousPart (n + 1) p) := by
  intro d hd
  have hd' : n < d.degree := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hd
  simp only [map_sub, Finsupp.sub_apply, coefficients_homogeneousPart]
  by_cases he : d.degree = n + 1
  · simp only [ite_eq_left he, sub_self]
  · have hh : n + 1 < Finsupp.weight (1 : I → ℕ) d := by
      have hh' : n + 1 < d.degree := by omega
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hh'
    simp only [ite_eq_right he, hp d hh, sub_zero]

theorem coordinate_homogeneousPart (f : W →+ S) (h : ℕ) (p : VectorPolynomial I R W) :
    coordinate f (homogeneousPart h p) = MvPolynomial.homogeneousComponent h (coordinate f p) := by
  classical
  ext d
  simp only [coeff_coordinate, coefficients_homogeneousPart, MvPolynomial.coeff_homogeneousComponent]
  split <;> simp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory

theorem independentProductPMF_marginal {I J X : Type*} [Fintype I] [Fintype J]
    [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : I → PMF X) (e : J → I) (he : Function.Injective e) :
    (independentProductPMF p).map (fun (x : I → X) (j : J) => x (e j)) =
      independentProductPMF (fun j => p (e j)) := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map (fun (x : I → X) j => x (e j)) _ (by fun_prop)]
  simp only [independentProductPMF, Measure.toPMF_toMeasure]
  exact (finiteProductMarginal_measurePreserving (fun i => (p i).toMeasure) e he).map_eq

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct Classical

theorem linearFunctional_eq_coordinate_sum {J R : Type*} [Fintype J] [CommRing R]
    (L : (J → R) →ₗ[R] R) (w : J → R) :
    L w = ∑ j, L (Pi.single j 1) * w j := by
  have hw : w = ∑ j, w j • Pi.single j (1 : R) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hw]
  simp only [map_sum, map_smul, smul_eq_mul, mul_comm]

theorem realPolynomialMass_fin_prod_le {σ : Type*} {h : ℕ}
    (P : Fin h → MvPolynomial σ ℝ) {B : ℝ}
    (hP : ∀ i, realPolynomialMass (P i) ≤ B) :
    realPolynomialMass (∏ i, P i) ≤ B ^ h := by
  apply (realPolynomialMass_prod_le Finset.univ P).trans
  calc
    _ ≤ ∏ _i : Fin h, B := Finset.prod_le_prod₀
      (fun i _ => realPolynomialMass_nonneg (P i)) (fun i _ => hP i)
    _ = B ^ h := by simp

namespace VectorPolynomial

noncomputable def contractedRow {σ J R : Type*} [CommRing R]
    (Λ : VectorPolynomial σ R (J → R) →ₗ[R] R) (P : MvPolynomial σ R) : J → R :=
  fun j => Λ (P ⊗ₜ[R] Pi.single j 1)

theorem contractedRow_apply {σ J R : Type*} [Fintype J] [CommRing R]
    (Λ : VectorPolynomial σ R (J → R) →ₗ[R] R) (P : MvPolynomial σ R) (w : J → R) :
    ∑ j, contractedRow Λ P j * w j = Λ (P ⊗ₜ[R] w) :=
  (linearFunctional_eq_coordinate_sum (TensorProduct.curry Λ P) w).symm

def MonomialRowBound {σ J : Type*}
    (Λ : VectorPolynomial σ ℝ (J → ℝ) →ₗ[ℝ] ℝ) (h : ℕ) (C : ℝ) : Prop :=
  ∀ (d : σ →₀ ℕ), d.degree = h → ∀ j, |Λ (MvPolynomial.monomial d 1 ⊗ₜ[ℝ] Pi.single j 1)| ≤ C

theorem contractedRow_le_mass {σ J : Type*}
    (Λ : VectorPolynomial σ ℝ (J → ℝ) →ₗ[ℝ] ℝ) {P : MvPolynomial σ ℝ} {h : ℕ}
    (hP : P.IsHomogeneous h) {C : ℝ} (hΛ : MonomialRowBound Λ h C) (j : J) :
    |contractedRow Λ P j| ≤ C * realPolynomialMass P :=
  polynomialFunctional_homogeneous_le_mass ((TensorProduct.curry Λ).flip (Pi.single j 1))
    hP (fun d hd => hΛ d hd j)

theorem contractedRow_prod_bound {σ J : Type*}
    (Λ : VectorPolynomial σ ℝ (J → ℝ) →ₗ[ℝ] ℝ) {h : ℕ}
    (P : Fin h → MvPolynomial σ ℝ) (hP : ∀ i, (P i).IsHomogeneous 1)
    {B C : ℝ} (hmass : ∀ i, realPolynomialMass (P i) ≤ B)
    (hC : 0 ≤ C) (hΛ : MonomialRowBound Λ h C) (j : J) :
    |contractedRow Λ (∏ i, P i) j| ≤ C * B ^ h := by
  have hp : (∏ i, P i).IsHomogeneous h := by
    simpa using MvPolynomial.IsHomogeneous.prod Finset.univ P (fun _ => 1) (fun i _ => hP i)
  exact (contractedRow_le_mass Λ hp hΛ j).trans
    (mul_le_mul_of_nonneg_left (realPolynomialMass_fin_prod_le P hmass) hC)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open MeasureTheory ProbabilityTheory

theorem dependentProductPMF_marginal {I J : Type*} [Fintype I] [Fintype J]
    {X : I → Type*} [∀ i, Countable (X i)] [∀ i, MeasurableSpace (X i)]
    [∀ i, MeasurableSingletonClass (X i)]
    (p : ∀ i, PMF (X i)) (e : J → I) (he : Function.Injective e) :
    (dependentProductPMF p).map (fun (x : ∀ i, X i) (j : J) => x (e j)) =
      dependentProductPMF (fun j => p (e j)) := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map (fun (x : ∀ i, X i) (j : J) => x (e j)) _ (by fun_prop)]
  simp only [dependentProductPMF, Measure.toPMF_toMeasure]
  have hind : iIndepFun (fun i (x : ∀ i, X i) => x i)
      (Measure.pi (fun i => (p i).toMeasure)) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hsel := iIndepFun.precomp he hind
  have hm := hsel.map_fun_eq_pi_map (fun j => (measurable_pi_apply (e j)).aemeasurable)
  apply hm.trans
  congr 1
  funext j
  exact (measurePreserving_eval (fun i => (p i).toMeasure) (e j)).map_eq

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct Classical

noncomputable def coefficientFunctional {σ J R : Type*} [Fintype J] [CommRing R]
    (frequency : (σ →₀ ℕ) → J → R) : VectorPolynomial σ R (J → R) →ₗ[R] R :=
  (Finsupp.lsum R (fun d => ∑ j, frequency d j • LinearMap.proj j)).comp coefficients.toLinearMap

theorem coefficientFunctional_monomial {σ J R : Type*} [Fintype J] [CommRing R]
    (frequency : (σ →₀ ℕ) → J → R) (d : σ →₀ ℕ) (w : J → R) :
    coefficientFunctional frequency (monomial d w) = ∑ j, frequency d j * w j := by
  simp only [coefficientFunctional, LinearMap.comp_apply, LinearEquiv.coe_coe,
    coefficients_monomial, Finsupp.lsum_single, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]

theorem coefficientFunctional_unit {σ J R : Type*} [Fintype J] [CommRing R]
    (frequency : (σ →₀ ℕ) → J → R) (d : σ →₀ ℕ) (j : J) :
    coefficientFunctional frequency (MvPolynomial.monomial d 1 ⊗ₜ[R] Pi.single j 1) = frequency d j := by
  change coefficientFunctional frequency (monomial d (Pi.single j 1)) = _
  rw [coefficientFunctional_monomial]
  simp [Pi.single_apply]

theorem coefficientFunctional_rowBound {σ J : Type*} [Fintype J]
    (frequency : (σ →₀ ℕ) → J → ℝ) {h : ℕ} {C : ℝ}
    (hfrequency : ∀ d, d.degree = h → ∀ j, |frequency d j| ≤ C) :
    MonomialRowBound (coefficientFunctional frequency) h C := by
  intro d hd j
  rw [coefficientFunctional_unit]
  exact hfrequency d hd j

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

abbrev BoundedCoefficientExponent (K : Type*) (h : ℕ) :=
  {d : K →₀ ℕ // d.degree ≤ h}

noncomputable instance boundedCoefficientExponentFintype (K : Type*) [Fintype K] (h : ℕ) :
    Fintype (BoundedCoefficientExponent K h) := (Finsupp.finite_of_degree_le h).fintype

abbrev CoefficientSlot (K : Type*) (m : ℕ) :=
  Σ j : Fin m, BoundedCoefficientExponent K (j.val + 1)

abbrev CoefficientArray {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) := ∀ s : CoefficientSlot K m, U s.1

noncomputable def coefficientArrayFunctional {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) : CoefficientArray (K := K) U →ₗ[ℝ] ℝ where
  toFun x := ∑ s, ∑ a, (frequency s.1 s.2.val a : ℝ) * (x s).val a
  map_add' x y := by
    simp only [Pi.add_apply, Submodule.coe_add, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, Submodule.coe_smul, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum, mul_left_comm]

theorem coefficientArrayFunctional_single {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (s : CoefficientSlot K m) (w : U s.1) :
    coefficientArrayFunctional U frequency (Pi.single s w) =
      ∑ a, (frequency s.1 s.2.val a : ℝ) * w.val a := by
  classical
  change (∑ t : CoefficientSlot K m, ∑ a, (frequency t.1 t.2.val a : ℝ) *
    ((Pi.single s w : CoefficientArray (K := K) U) t).val a) = _
  rw [Finset.sum_eq_single s]
  · simp
  · intro t _ hts
    simp [Pi.single_eq_of_ne hts]
  · simp

theorem coefficientArrayFunctional_eq_zero_iff {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) :
    coefficientArrayFunctional U frequency = 0 ↔
      ∀ (s : CoefficientSlot K m) (w : U s.1), ∑ a, (frequency s.1 s.2.val a : ℝ) * w.val a = 0 := by
  constructor
  · intro hz s w
    have he := DFunLike.congr_fun hz (Pi.single s w)
    simpa only [coefficientArrayFunctional_single, LinearMap.zero_apply] using he
  · intro hz
    apply LinearMap.ext
    intro x
    change (∑ s, ∑ a, (frequency s.1 s.2.val a : ℝ) * (x s).val a) = 0
    exact Finset.sum_eq_zero (fun s _ => hz s (x s))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

theorem exists_homogeneous_monomial_nonzero {K W : Type*}
    [AddCommGroup W] [Module ℝ W]
    (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) {h : ℕ}
    (hnonzero : ∃ p, Homogeneous h p ∧ L p ≠ 0) :
    ∃ d : K →₀ ℕ, d.degree = h ∧ ∃ w : W, L (monomial d w) ≠ 0 := by
  obtain ⟨p, hp, hLp⟩ := hnonzero
  by_contra hn
  push Not at hn
  apply hLp
  rw [← sum_monomial_coefficients p, Finsupp.sum, map_sum]
  apply Finset.sum_eq_zero
  intro d hd
  exact hn d (homogeneous_support_degree hp hd) (coefficients p d)

theorem homogeneous_empty_factorization_iff {K W : Type*}
    [AddCommGroup W] [Module ℝ W]
    (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) (h : ℕ) (site : Empty → K → ℝ) :
    (∃ M : (Empty → W) →ₗ[ℝ] ℝ,
      ∀ p, Homogeneous h p → L p = M (siteEvaluation site p)) ↔
      ∀ p, Homogeneous h p → L p = 0 := by
  constructor
  · rintro ⟨M, hM⟩ p hp
    have he := hM p hp
    rwa [Subsingleton.elim (siteEvaluation site p) 0, map_zero] at he
  · intro hz
    exact ⟨0, fun p hp => by simpa using hz p hp⟩

theorem exists_restricted_coefficient_nonzero {K J : Type*} [Fintype J]
    (W : Submodule ℝ (J → ℝ)) (frequency : (K →₀ ℕ) → J → ℤ) {h : ℕ}
    (hnonzero : ∃ p, Homogeneous h p ∧
      coefficientFunctional (fun d j => (frequency d j : ℝ)) (map W.subtype p) ≠ 0) :
    ∃ d : K →₀ ℕ, d.degree = h ∧ ∃ w : W,
      (∑ j, (frequency d j : ℝ) * w.val j) ≠ 0 := by
  obtain ⟨d, hd, w, hw⟩ := exists_homogeneous_monomial_nonzero
    ((coefficientFunctional (fun d j => (frequency d j : ℝ))).comp (map W.subtype)) hnonzero
  refine ⟨d, hd, w, ?_⟩
  simpa only [LinearMap.comp_apply, map_monomial, Submodule.subtype_apply,
    coefficientFunctional_monomial] using hw

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem boundedCoefficientExponent_card_le {K : Type*} [Fintype K] (h : ℕ) :
    Fintype.card (BoundedCoefficientExponent K h) ≤
      (h + 1) * (Fintype.card K + 1) ^ h := by
  classical
  let code : BoundedCoefficientExponent K h → (Σ n : Fin (h + 1), Fin n.val → K) := fun d =>
    ⟨⟨d.val.toMultiset.toList.length, by
      rw [Multiset.length_toList, Finsupp.card_toMultiset]
      exact Nat.lt_succ_of_le d.property⟩, d.val.toMultiset.toList.get⟩
  have hinj : Function.Injective code := by
    intro d e he
    have hl := congrArg (fun z : Σ n : Fin (h + 1), Fin n.val → K => List.ofFn z.2) he
    change List.ofFn d.val.toMultiset.toList.get = List.ofFn e.val.toMultiset.toList.get at hl
    rw [List.ofFn_get, List.ofFn_get] at hl
    have hm := congrArg (fun l : List K => (l : Multiset K)) hl
    rw [Multiset.coe_toList, Multiset.coe_toList] at hm
    apply Subtype.ext
    ext k
    have hk := congrArg (fun l : Multiset K => l.count k) hm
    simpa only [Finsupp.count_toMultiset] using hk
  have hc := Fintype.card_le_of_injective code hinj
  simp only [Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin] at hc
  calc
    _ ≤ ∑ n : Fin (h + 1), Fintype.card K ^ n.val := hc
    _ ≤ ∑ _n : Fin (h + 1), (Fintype.card K + 1) ^ h := by
      apply Finset.sum_le_sum
      intro n _
      exact (Nat.pow_le_pow_left (Nat.le_succ _) _).trans
        (Nat.pow_le_pow_right (by omega) (Nat.le_of_lt_succ n.isLt))
    _ = _ := by simp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped TensorProduct Classical

def integerCubeWitnessBound (q : ℕ) (H D : ℝ) : ℝ :=
  integerFormMassBound q H D ((q.factorial : ℝ) * D ^ q)
    ((q : ℝ) * (((q.factorial : ℝ) * D ^ (q - 1)) * (1 + H)))

theorem integerCubeWitnessBound_nonneg (q : ℕ) {H D : ℝ} (hH : 0 ≤ H) (hD : 0 ≤ D) :
    0 ≤ integerCubeWitnessBound q H D := by
  unfold integerCubeWitnessBound integerFormMassBound
  positivity

theorem integer_coefficient_le_mass {σ : Type*} (P : MvPolynomial σ ℤ) (d : σ →₀ ℕ) :
    |((P.coeff d : ℤ) : ℝ)| ≤ realPolynomialMass (map (Int.castRingHom ℝ) P) := by
  simpa only [coeff_map, Int.coe_castRingHom] using
    realPolynomialMass_coeff_le (map (Int.castRingHom ℝ) P) d

theorem exists_integral_vector_mode_witness {α K W : Type*} [Fintype α] [DecidableEq α]
    [AddCommGroup W] [Module ℝ W]
    (root : K → ℤ) (difference : α → K → ℤ) (selection : α → K)
    (hdet : (integerDifferencePivot difference selection).det ≠ 0)
    {H D : ℝ} (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hroot : ∀ k, |(root k : ℝ)| ≤ H) (hdiff : ∀ i k, |(difference i k : ℝ)| ≤ D)
    (Λ : VectorPolynomial (Option K) ℝ W →ₗ[ℝ] ℝ) (h : ℕ)
    (hnonfactor : ¬ ∃ M : (Finset α → W) →ₗ[ℝ] ℝ,
      ∀ p, VectorPolynomial.Homogeneous h p → Λ p = M (VectorPolynomial.siteEvaluation
        (fun s => affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s) p)) :
    ∃ forms : List (MvPolynomial (Option K) ℤ), forms.length = h ∧
      (∀ P ∈ forms, P.IsHomogeneous 1 ∧
        realPolynomialMass (map (Int.castRingHom ℝ) P) ≤ integerCubeWitnessBound (Fintype.card α) H D) ∧
      (∀ s : Finset α, ∃ P ∈ forms, eval (affineSite root difference s) P = 0) ∧
      ∃ w : W, Λ ((map (Int.castRingHom ℝ) forms.prod) ⊗ₜ[ℝ] w) ≠ 0 := by
  have hn := VectorPolynomial.curried_nonfactor
    (fun s => affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s) Λ h hnonfactor
  obtain ⟨forms, hlen, hforms, hz, hΛ⟩ := exists_bounded_integer_vanishing_product
    root difference selection hdet hH hD hroot hdiff (TensorProduct.curry Λ) h hn
  refine ⟨forms, hlen, hforms, hz, ?_⟩
  by_contra hnone
  apply hΛ
  ext w
  change Λ ((map (Int.castRingHom ℝ) forms.prod) ⊗ₜ[ℝ] w) = 0
  by_contra hw
  exact hnone ⟨w, hw⟩

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

theorem productBlockExponent_degree {K : Type*} {h : ℕ} (principal : Fin h → K) :
    (productBlockExponent principal).degree = h := by
  simp [productBlockExponent, map_sum, Finsupp.degree_single]

theorem canonicalPrincipalExponent_degree {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) (b : B d) :
    (canonicalPrincipalExponent (G := G) h d b).degree = h d :=
  productBlockExponent_degree _

def constantCoefficientSlot (K : Type*) (h : ℕ) : BoundedCoefficientExponent K h :=
  ⟨0, by simp⟩

noncomputable def principalCoefficientSlot {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) (b : B d) :
    BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d) :=
  ⟨canonicalPrincipalExponent h d b, (canonicalPrincipalExponent_degree h d b).le⟩

theorem principalCoefficientSlot_injective {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) (hd : 0 < h d) :
    Function.Injective (principalCoefficientSlot (G := G) (B := B) h d) := by
  intro b b' he
  exact canonicalPrincipalExponent_injective h d hd (congrArg Subtype.val he)

noncomputable def principalCoefficientSlots {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) [Fintype (B d)] :
    Finset (BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d)) := by
  classical
  exact Finset.univ.image (principalCoefficientSlot h d)

theorem mem_principalCoefficientSlots {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) [Fintype (B d)] (e) :
    e ∈ principalCoefficientSlots (G := G) (B := B) h d ↔
      ∃ b, principalCoefficientSlot h d b = e := by
  classical
  simp [principalCoefficientSlots]

theorem principalCoefficientSlots_card {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) [Fintype (B d)] (hd : 0 < h d) :
    (principalCoefficientSlots (G := G) (B := B) h d).card = Fintype.card (B d) := by
  classical
  exact (Finset.card_image_of_injective _ (principalCoefficientSlot_injective h d hd)).trans
    (Finset.card_univ)

theorem constantCoefficientSlot_not_principal {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) [Fintype (B d)] (hd : 0 < h d) :
    constantCoefficientSlot (SamplerTupleIndex G B h) (h d) ∉ principalCoefficientSlots h d := by
  intro he
  obtain ⟨b, hb⟩ := (mem_principalCoefficientSlots h d _).mp he
  exact canonicalPrincipalExponent_ne_zero h d hd b (congrArg Subtype.val hb)

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial

noncomputable def principalCoefficientChoice {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) :
    Option (B d) → BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d)
  | none => constantCoefficientSlot _ _
  | some b => principalCoefficientSlot h d b

theorem principalCoefficientChoice_injective {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) (hd : 0 < h d) :
    Function.Injective (principalCoefficientChoice (G := G) (B := B) h d) := by
  intro x y hxy
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some b =>
      exact False.elim (canonicalPrincipalExponent_ne_zero h d hd b
        (congrArg Subtype.val hxy).symm)
  | some b =>
    cases y with
    | none =>
      exact False.elim (canonicalPrincipalExponent_ne_zero h d hd b
        (congrArg Subtype.val hxy))
    | some b' =>
      exact congrArg some (principalCoefficientSlot_injective h d hd hxy)

theorem principalCoefficientMarginal {D G : Type*} [Fintype D] [Fintype G]
    {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (d : D) (hd : 0 < h d)
    (p : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d) → PMF ℤ) :
    (independentProductPMF p).map (fun a r => a (principalCoefficientChoice h d r)) =
      independentProductPMF (fun r => p (principalCoefficientChoice h d r)) :=
  independentProductPMF_marginal p _ (principalCoefficientChoice_injective h d hd)

end Erdos3

end

end OAI
