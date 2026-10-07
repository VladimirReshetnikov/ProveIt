/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Estimates.CommonMarkedMultidegree

namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators TensorProduct

namespace VectorPolynomial

variable {σ L : Type*} [AddCommGroup L] [Module ℚ L]

noncomputable def monomialLinearMap (α : σ →₀ ℕ) : L →ₗ[ℚ] VectorPolynomial σ ℚ L where
  toFun := monomial α
  map_add' x y := by simp only [monomial, TensorProduct.tmul_add]
  map_smul' a x := by
    change monomial α (a • x) = a • monomial α x
    simp only [monomial, TensorProduct.tmul_smul]

theorem realMonomial_eval (α : σ →₀ ℕ) (x : ℝ ⊗[ℚ] L) (a : σ → ℚ) :
    (eval a).baseChange ℝ ((monomialLinearMap α).baseChange ℝ x) =
      (α.prod (fun i n => a i ^ n)) • x := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    change r ⊗ₜ[ℚ] eval a (monomial α x) = (α.prod (fun i n => a i ^ n)) • (r ⊗ₜ[ℚ] x)
    rw [eval_monomial, TensorProduct.tmul_smul]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

noncomputable def realAffinePolynomial [Fintype σ] (x : ℝ ⊗[ℚ] L) (y : σ → ℝ ⊗[ℚ] L) :
    ℝ ⊗[ℚ] VectorPolynomial σ ℚ L :=
  (monomialLinearMap (0 : σ →₀ ℕ)).baseChange ℝ x +
    ∑ i, (monomialLinearMap (Finsupp.single i 1)).baseChange ℝ (y i)

theorem realAffinePolynomial_eval [Fintype σ] (x : ℝ ⊗[ℚ] L) (y : σ → ℝ ⊗[ℚ] L) (a : σ → ℚ) :
    (eval a).baseChange ℝ (realAffinePolynomial x y) = x + ∑ i, a i • y i := by
  classical
  simp only [realAffinePolynomial, map_add, map_sum, realMonomial_eval,
    Finsupp.prod_zero_index, one_smul, Finsupp.prod_single_index, pow_one, pow_zero]

end VectorPolynomial

variable {I σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem realMonomial_mem_markedPolynomialLayer
    (v : I → L) (w : I → ℕ) (marked : I → Bool) (d k l : ℕ) (α : σ →₀ ℕ)
    {x : ℝ ⊗[ℚ] L}
    (hx : x ∈ (markedLieSpan v w marked d (k + Finsupp.weight (fun _ : σ => 1) α) l).baseChange ℝ) :
    (monomialLinearMap α).baseChange ℝ x ∈
      (markedPolynomialLayer v w marked d k l).baseChange ℝ := by
  have hmap : (markedLieSpan v w marked d (k + Finsupp.weight (fun _ : σ => 1) α) l).map
      (monomialLinearMap α) ≤ markedPolynomialLayer v w marked d k l := by
    rintro z ⟨y, hy, rfl⟩
    exact monomial_mem_markedPolynomialLayer v w marked d k l α hy
  have h := Submodule.baseChange_mono ℝ hmap
  rw [realification_map] at h
  exact h ⟨x, hx, rfl⟩

theorem realAffinePolynomial_mem_marked [Fintype σ]
    (v : I → L) (w : I → ℕ) (marked : I → Bool) {d k l : ℕ}
    {x : ℝ ⊗[ℚ] L} {y : σ → ℝ ⊗[ℚ] L}
    (hx : x ∈ (markedLieSpan v w marked d k l).baseChange ℝ)
    (hy : ∀ i, y i ∈ (markedLieSpan v w marked d (k + 1) l).baseChange ℝ) :
    realAffinePolynomial x y ∈ (markedPolynomialLayer v w marked d k l).baseChange ℝ := by
  apply Submodule.add_mem
  · apply realMonomial_mem_markedPolynomialLayer v w marked d k l 0
    simpa only [map_zero, Nat.add_zero] using hx
  · apply Submodule.sum_mem
    intro i _
    apply realMonomial_mem_markedPolynomialLayer v w marked d k l (Finsupp.single i 1)
    simpa only [Finsupp.weight_single, one_smul] using hy i

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

noncomputable def correlationExponent (h n : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 h + Finsupp.single 1 n

@[simp] theorem correlationExponent_apply (h n : ℕ) (i : Fin 2) :
    correlationExponent h n i = correlationInput h n i := by
  fin_cases i
  · change correlationExponent h n 0 = h
    simp [correlationExponent]
  · change correlationExponent h n 1 = n
    simp [correlationExponent]

theorem eval_correlation_monomial {L : Type*} [AddCommGroup L] [Module ℚ L]
    (h n : ℕ) (v : L) (x : Fin 2 → ℚ) :
    eval x (monomial (correlationExponent h n) v) = (x 0 ^ h * x 1 ^ n) • v := by
  classical
  rw [eval_monomial]
  simp [correlationExponent, Finsupp.prod_add_index, pow_add]

noncomputable def affineMixedLog {L : Type*} [AddCommGroup L] [Module ℚ L]
    {m : ℕ} (c d : Fin m → L) : VectorPolynomial (Fin 2) ℚ L :=
  ∑ j, (monomial (correlationExponent 0 (j.val + 1)) (c j) +
    monomial (correlationExponent 1 (j.val + 1)) (d j))

theorem affineMixedLog_eval {L : Type*} [AddCommGroup L] [Module ℚ L]
    {m : ℕ} (c d : Fin m → L) (x : Fin 2 → ℚ) :
    eval x (affineMixedLog c d) =
      ∑ j, x 1 ^ (j.val + 1) • (c j + x 0 • d j) := by
  simp only [affineMixedLog, map_sum, map_add, eval_correlation_monomial,
    pow_zero, one_mul, pow_one, smul_add, smul_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm (x 0)]

namespace MultidegreeLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s m : ℕ} {bound : Fin 2 → ℕ}
  (F : MultidegreeLieFiltration (Fin 2) L s bound)
  (c d : Fin m → L)
  (hc : ∀ j, c j ∈ F.layer (correlationInput 0 (j.val + 1)))
  (hd : ∀ j, d j ∈ F.layer (correlationInput 1 (j.val + 1)))

include hc hd in
theorem affineMixedLog_adapted : F.Adapted (affineMixedLog c d) := by
  apply F.adaptedSubmodule.sum_mem
  intro j _
  apply F.adaptedSubmodule.add_mem
  · apply F.monomial_mem_adaptedSubmodule
    simpa only [correlationExponent_apply] using hc j
  · apply F.monomial_mem_adaptedSubmodule
    simpa only [correlationExponent_apply] using hd j

noncomputable def affineMixedOrbit : F.PolynomialOrbit :=
  F.polynomialOrbitOfLog (affineMixedLog c d) (F.affineMixedLog_adapted c d hc hd)

theorem affineMixedOrbit_eval (x : Fin 2 → ℤ) :
    (F.polynomialOrbitEval x (F.affineMixedOrbit c d hc hd)).coord =
      ∑ j, (x 1 : ℚ) ^ (j.val + 1) • (c j + (x 0 : ℚ) • d j) :=
  affineMixedLog_eval c d _

theorem affineMixedOrbit_at_zero (h : ℤ) :
    F.polynomialOrbitEval (correlationInput h 0) (F.affineMixedOrbit c d hc hd) = 1 := by
  apply NilpotentLieBCHGroup.ext
  rw [F.affineMixedOrbit_eval]
  have hz : correlationInput h (0 : ℤ) 1 = 0 := rfl
  rw [hz]
  simp

theorem affineMixedOrbit_normalized :
    F.polynomialOrbitEval 0 (F.affineMixedOrbit c d hc hd) = 1 := by
  have hz : correlationInput (0 : ℤ) 0 = 0 := by
    ext i
    fin_cases i <;> rfl
  rw [← hz]
  exact F.affineMixedOrbit_at_zero c d hc hd 0

end MultidegreeLieFiltration

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)

theorem markedShiftLayerPolynomialMap_mem (t d k l : ℕ)
    (p : markedPolynomialLayer (σ := Fin t) v w marked d k l) :
    markedShiftLayerPolynomialMap F v w marked hw hv t d k l p ∈
      markedShiftBiLayer F v w marked t k d := by
  refine ⟨?_, fun _ => rfl⟩
  exact markedPolynomialLayer_antitone v w marked le_rfl le_rfl (Nat.zero_le l) p.property

theorem markedShiftLayerPolynomialMap_quotient_mem (t d k l : ℕ)
    (p : markedPolynomialLayer (σ := Fin t) v w marked d k l) :
    lieQuotientMap (markedShiftSecondIdeal F v w marked t)
      (markedShiftLayerPolynomialMap F v w marked hw hv t d k l p) ∈
        (markedShiftMultidegree F v w marked hw hv t).layer (correlationInput k d) := by
  refine ⟨_, ?_, rfl⟩
  exact markedShiftLayerPolynomialMap_mem F v w marked hw hv t d k l p

noncomputable def markedAffineShiftCoefficient (t d k l : ℕ) (x : L) (y : Fin t → L)
    (hx : x ∈ markedLieSpan v w marked d k l)
    (hy : ∀ i, y i ∈ markedLieSpan v w marked d (k + 1) l) :
    markedShiftSubalgebra F v w marked t :=
  markedShiftLayerPolynomialMap F v w marked hw hv t d k l
    ⟨markedAffinePolynomial x y, markedAffinePolynomial_mem v w marked hx hy⟩

noncomputable def markedDirectionalShiftCoefficient (t d k l : ℕ) (u : Fin t → ℚ) (y : Fin t → L)
    (hy : ∀ i, y i ∈ markedLieSpan v w marked d k l) :
    markedShiftSubalgebra F v w marked t :=
  markedShiftLayerPolynomialMap F v w marked hw hv t d k l
    ⟨monomial 0 (∑ i, u i • y i), markedPolynomialLayer_constant v w marked
      ((markedLieSpan v w marked d k l).sum_mem
        (fun i _ => (markedLieSpan v w marked d k l).smul_mem (u i) (hy i)))⟩

theorem markedAffineShiftCoefficient_quotient_mem (t d k l : ℕ) (x : L) (y : Fin t → L)
    (hx : x ∈ markedLieSpan v w marked d k l)
    (hy : ∀ i, y i ∈ markedLieSpan v w marked d (k + 1) l) :
    lieQuotientMap (markedShiftSecondIdeal F v w marked t)
      (markedAffineShiftCoefficient F v w marked hw hv t d k l x y hx hy) ∈
        (markedShiftMultidegree F v w marked hw hv t).layer (correlationInput k d) :=
  markedShiftLayerPolynomialMap_quotient_mem F v w marked hw hv t d k l _

theorem markedDirectionalShiftCoefficient_quotient_mem (t d k l : ℕ)
    (u : Fin t → ℚ) (y : Fin t → L)
    (hy : ∀ i, y i ∈ markedLieSpan v w marked d k l) :
    lieQuotientMap (markedShiftSecondIdeal F v w marked t)
      (markedDirectionalShiftCoefficient F v w marked hw hv t d k l u y hy) ∈
        (markedShiftMultidegree F v w marked hw hv t).layer (correlationInput k d) :=
  markedShiftLayerPolynomialMap_quotient_mem F v w marked hw hv t d k l _

theorem markedAffineShiftCoefficient_eval (t d k l : ℕ) (x : L) (y : Fin t → L)
    (hx : x ∈ markedLieSpan v w marked d k l)
    (hy : ∀ i, y i ∈ markedLieSpan v w marked d (k + 1) l) (a : Fin t → ℚ) :
    markedShiftEval F v w marked t a (markedAffineShiftCoefficient F v w marked hw hv t d k l x y hx hy) =
      x + ∑ i, a i • y i := markedAffinePolynomial_eval x y a

theorem markedDirectionalShiftCoefficient_eval (t d k l : ℕ) (u : Fin t → ℚ) (y : Fin t → L)
    (hy : ∀ i, y i ∈ markedLieSpan v w marked d k l) (a : Fin t → ℚ) :
    markedShiftEval F v w marked t a
      (markedDirectionalShiftCoefficient F v w marked hw hv t d k l u y hy) = ∑ i, u i • y i := by
  change eval a (monomial 0 (∑ i, u i • y i)) = _
  rw [eval_monomial, Finsupp.prod_zero_index, one_smul]

theorem markedAffineShiftCoefficient_shift_eval (t d k l : ℕ)
    (x : L) (y : Fin t → L) (hx : x ∈ markedLieSpan v w marked d k l)
    (hy : ∀ i, y i ∈ markedLieSpan v w marked d (k + 1) l)
    (a u : Fin t → ℚ) (h : ℚ) :
    markedShiftEval F v w marked t a
      (markedAffineShiftCoefficient F v w marked hw hv t d k l x y hx hy +
        h • markedDirectionalShiftCoefficient F v w marked hw hv t d (k + 1) l u y hy) =
      x + ∑ i, (a i + h * u i) • y i := by
  rw [map_add, map_smul, markedAffineShiftCoefficient_eval, markedDirectionalShiftCoefficient_eval]
  simp only [add_smul, Finset.sum_add_distrib, Finset.smul_sum, smul_smul, add_assoc]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
  (t l : ℕ) (x : Fin s → L) (y : Fin s → Fin t → L)
  (hx : ∀ j, x j ∈ markedLieSpan v w marked (j.val + 1) 0 l)
  (hy : ∀ j i, y j i ∈ markedLieSpan v w marked (j.val + 1) 1 l)
  (u : Fin t → ℚ)

noncomputable def markedAffineBaseCoefficient (j : Fin s) : markedShiftSubalgebra F v w marked t :=
  markedAffineShiftCoefficient F v w marked hw hv t (j.val + 1) 0 l (x j) (y j) (hx j) (hy j)

noncomputable def markedAffineSlopeCoefficient (j : Fin s) : markedShiftSubalgebra F v w marked t :=
  markedDirectionalShiftCoefficient F v w marked hw hv t (j.val + 1) 1 l u (y j) (hy j)

noncomputable def markedAffineMixedLift (h n : ℚ) : markedShiftSubalgebra F v w marked t :=
  ∑ j, n ^ (j.val + 1) • (markedAffineBaseCoefficient F v w marked hw hv t l x y hx hy j +
    h • markedAffineSlopeCoefficient F v w marked hw hv t l y hy u j)

theorem markedAffineMixedLift_eval (a : Fin t → ℚ) (h n : ℚ) :
    markedShiftEval F v w marked t a (markedAffineMixedLift F v w marked hw hv t l x y hx hy u h n) =
      ∑ j, n ^ (j.val + 1) • (x j + ∑ i, (a i + h * u i) • y j i) := by
  simp only [markedAffineMixedLift, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact markedAffineShiftCoefficient_shift_eval F v w marked hw hv
    t (j.val + 1) 0 l (x j) (y j) (hx j) (hy j) a u h

noncomputable def markedAffineMixedOrbit :
    (markedShiftMultidegree F v w marked hw hv t).PolynomialOrbit :=
  (markedShiftMultidegree F v w marked hw hv t).affineMixedOrbit
    (fun j => lieQuotientMap (markedShiftSecondIdeal F v w marked t)
      (markedAffineBaseCoefficient F v w marked hw hv t l x y hx hy j))
    (fun j => lieQuotientMap (markedShiftSecondIdeal F v w marked t)
      (markedAffineSlopeCoefficient F v w marked hw hv t l y hy u j))
    (fun j => markedAffineShiftCoefficient_quotient_mem F v w marked hw hv
      t (j.val + 1) 0 l (x j) (y j) (hx j) (hy j))
    (fun j => markedDirectionalShiftCoefficient_quotient_mem F v w marked hw hv
      t (j.val + 1) 1 l u (y j) (hy j))

theorem markedAffineMixedOrbit_eval (h n : ℤ) :
    ((markedShiftMultidegree F v w marked hw hv t).polynomialOrbitEval (correlationInput h n)
      (markedAffineMixedOrbit F v w marked hw hv t l x y hx hy u)).coord =
        lieQuotientMap (markedShiftSecondIdeal F v w marked t)
          (markedAffineMixedLift F v w marked hw hv t l x y hx hy u (h : ℚ) (n : ℚ)) := by
  calc
    _ = ∑ j, (n : ℚ) ^ (j.val + 1) •
        (lieQuotientMap (markedShiftSecondIdeal F v w marked t)
          (markedAffineBaseCoefficient F v w marked hw hv t l x y hx hy j) +
        (h : ℚ) • lieQuotientMap (markedShiftSecondIdeal F v w marked t)
          (markedAffineSlopeCoefficient F v w marked hw hv t l y hy u j)) :=
      MultidegreeLieFiltration.affineMixedOrbit_eval _ _ _ _ _ (correlationInput h n)
    _ = _ := by simp only [markedAffineMixedLift, map_sum, map_smul, map_add]

theorem markedAffineMixedOrbit_at_zero (h : ℤ) :
    (markedShiftMultidegree F v w marked hw hv t).polynomialOrbitEval (correlationInput h 0)
      (markedAffineMixedOrbit F v w marked hw hv t l x y hx hy u) = 1 :=
  MultidegreeLieFiltration.affineMixedOrbit_at_zero _ _ _ _ _ h

theorem markedAffineMixedOrbit_normalized :
    (markedShiftMultidegree F v w marked hw hv t).polynomialOrbitEval 0
      (markedAffineMixedOrbit F v w marked hw hv t l x y hx hy u) = 1 :=
  MultidegreeLieFiltration.affineMixedOrbit_normalized _ _ _ _ _

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)

noncomputable def realMarkedPolynomialLift (t d k l : ℕ) :
    (markedPolynomialLayer (σ := Fin t) v w marked d k l).baseChange ℝ →ₗ[ℝ]
      ℝ ⊗[ℚ] (markedShiftSubalgebra F v w marked t) :=
  ((markedShiftLayerPolynomialMap F v w marked hw hv t d k l).baseChange ℝ).comp
    (realificationSubmoduleEquiv (markedPolynomialLayer (σ := Fin t) v w marked d k l)).symm.toLinearMap

theorem realMarkedPolynomialLift_mem (t d k l : ℕ)
    (p : (markedPolynomialLayer (σ := Fin t) v w marked d k l).baseChange ℝ) :
    realMarkedPolynomialLift F v w marked hw hv t d k l p ∈
      (markedShiftBiLayer F v w marked t k d).baseChange ℝ := by
  obtain ⟨z, rfl⟩ := (realificationSubmoduleEquiv _).surjective p
  change (markedShiftLayerPolynomialMap F v w marked hw hv t d k l).baseChange ℝ
    ((realificationSubmoduleEquiv _).symm (realificationSubmoduleEquiv _ z)) ∈ _
  rw [LinearEquiv.symm_apply_apply]
  induction z using TensorProduct.inductionOn with
  | tmul a z =>
    rw [LinearMap.baseChange_tmul]
    exact Submodule.tmul_mem_baseChange_of_mem a
      (markedShiftLayerPolynomialMap_mem F v w marked hw hv t d k l z)
  | add z z' hz hz' => simpa only [map_add] using Submodule.add_mem _ hz hz'

theorem realMarkedPolynomialLift_eval (t d k l : ℕ)
    (p : (markedPolynomialLayer (σ := Fin t) v w marked d k l).baseChange ℝ) (a : Fin t → ℚ) :
    (markedShiftEval F v w marked t a).baseChange ℝ
      (realMarkedPolynomialLift F v w marked hw hv t d k l p) =
        (eval a).baseChange ℝ p.val := by
  obtain ⟨z, rfl⟩ := (realificationSubmoduleEquiv _).surjective p
  change (markedShiftEval F v w marked t a).baseChange ℝ
    ((markedShiftLayerPolynomialMap F v w marked hw hv t d k l).baseChange ℝ
      ((realificationSubmoduleEquiv _).symm (realificationSubmoduleEquiv _ z))) = _
  rw [LinearEquiv.symm_apply_apply]
  rw [realificationSubmoduleEquiv_coe]
  induction z using TensorProduct.inductionOn with
  | tmul a z => rfl
  | add z z' hz hz' => simp only [map_add, hz, hz']

noncomputable def realMarkedQuotientCoefficient (t d k l : ℕ) :
    (markedPolynomialLayer (σ := Fin t) v w marked d k l).baseChange ℝ →ₗ[ℝ]
      ℝ ⊗[ℚ] (MarkedShiftQuotient F v w marked t) :=
  ((lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.baseChange ℝ).comp
    (realMarkedPolynomialLift F v w marked hw hv t d k l)

theorem realMarkedPolynomialLift_quotient_mem (t d k l : ℕ)
    (p : (markedPolynomialLayer (σ := Fin t) v w marked d k l).baseChange ℝ) :
    realMarkedQuotientCoefficient F v w marked hw hv t d k l p ∈
        (markedShiftMultidegree F v w marked hw hv t).realification.layer (correlationInput k d) := by
  change _ ∈ ((markedShiftBiLayer F v w marked t k d).map
    (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap).baseChange ℝ
  rw [realification_map]
  exact ⟨_, realMarkedPolynomialLift_mem F v w marked hw hv t d k l p, rfl⟩

variable (t l : ℕ)
  (c : ∀ j : Fin s, (markedPolynomialLayer (σ := Fin t) v w marked (j.val + 1) 0 l).baseChange ℝ)
  (d : ∀ j : Fin s, (markedPolynomialLayer (σ := Fin t) v w marked (j.val + 1) 1 l).baseChange ℝ)

noncomputable def realMarkedAffineMixedOrbit :
    (markedShiftMultidegree F v w marked hw hv t).realification.PolynomialOrbit :=
  (markedShiftMultidegree F v w marked hw hv t).realification.affineMixedOrbit
    (fun j => realMarkedQuotientCoefficient F v w marked hw hv t (j.val + 1) 0 l (c j))
    (fun j => realMarkedQuotientCoefficient F v w marked hw hv t (j.val + 1) 1 l (d j))
    (fun j => realMarkedPolynomialLift_quotient_mem F v w marked hw hv t (j.val + 1) 0 l (c j))
    (fun j => realMarkedPolynomialLift_quotient_mem F v w marked hw hv t (j.val + 1) 1 l (d j))

theorem realMarkedAffineMixedOrbit_eval (h n : ℤ) :
    ((markedShiftMultidegree F v w marked hw hv t).realification.polynomialOrbitEval
      (correlationInput h n) (realMarkedAffineMixedOrbit F v w marked hw hv t l c d)).coord =
        ∑ j : Fin s, (n : ℚ) ^ (j.val + 1) •
          (realMarkedQuotientCoefficient F v w marked hw hv t (j.val + 1) 0 l (c j) +
          (h : ℚ) • realMarkedQuotientCoefficient F v w marked hw hv t (j.val + 1) 1 l (d j)) :=
  MultidegreeLieFiltration.affineMixedOrbit_eval _ _ _ _ _ (correlationInput h n)

theorem realMarkedAffineMixedOrbit_at_zero (h : ℤ) :
    (markedShiftMultidegree F v w marked hw hv t).realification.polynomialOrbitEval
      (correlationInput h 0) (realMarkedAffineMixedOrbit F v w marked hw hv t l c d) = 1 :=
  MultidegreeLieFiltration.affineMixedOrbit_at_zero _ _ _ _ _ h

theorem realMarkedAffineMixedOrbit_normalized :
    (markedShiftMultidegree F v w marked hw hv t).realification.polynomialOrbitEval 0
      (realMarkedAffineMixedOrbit F v w marked hw hv t l c d) = 1 :=
  MultidegreeLieFiltration.affineMixedOrbit_normalized _ _ _ _ _

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ) (u : Fin t → ℝ)

noncomputable def realAffineMarkedBase (j : Fin s) :
    (D.dependentPolynomialLayer (σ := Fin t) (j.val + 1) 0 1).baseChange ℝ :=
  ⟨realAffinePolynomial (x j).val (fun i => (y j i).val),
    realAffinePolynomial_mem_marked D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent
      (Submodule.baseChange_mono ℝ (D.coefficientFreeSpan_le_dependentWordLayer j) (x j).property)
      (fun i => Submodule.baseChange_mono ℝ (D.dependentFreeSpan_le_dependentWordLayer j) (y j i).property)⟩

noncomputable def realAffineMarkedSlope (j : Fin s) :
    (D.dependentPolynomialLayer (σ := Fin t) (j.val + 1) 1 1).baseChange ℝ := by
  let z := ∑ i, u i • (y j i).val
  refine ⟨(monomialLinearMap (0 : Fin t →₀ ℕ)).baseChange ℝ z, ?_⟩
  apply realMonomial_mem_markedPolynomialLayer
  simp only [map_zero, Nat.add_zero]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact Submodule.baseChange_mono ℝ (D.dependentFreeSpan_le_dependentWordLayer j) (y j i).property

theorem realAffineMarkedBase_eval (j : Fin s) (a : Fin t → ℚ) :
    (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t a).baseChange ℝ
        (realMarkedPolynomialLift D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
          D.coefficientFreeGenerator_mem_layer t (j.val + 1) 0 1 (D.realAffineMarkedBase t x y j)) =
            (x j).val + ∑ i, a i • (y j i).val := by
  exact (realMarkedPolynomialLift_eval D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t (j.val + 1) 0 1 (D.realAffineMarkedBase t x y j) a).trans
      (realAffinePolynomial_eval (x j).val (fun i => (y j i).val) a)

theorem realAffineMarkedSlope_eval (j : Fin s) (a : Fin t → ℚ) :
    (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t a).baseChange ℝ
        (realMarkedPolynomialLift D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
          D.coefficientFreeGenerator_mem_layer t (j.val + 1) 1 1 (D.realAffineMarkedSlope t y u j)) =
            ∑ i, u i • (y j i).val := by
  apply (realMarkedPolynomialLift_eval D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t (j.val + 1) 1 1 (D.realAffineMarkedSlope t y u j) a).trans
  change (eval a).baseChange ℝ ((monomialLinearMap 0).baseChange ℝ (∑ i, u i • (y j i).val)) = _
  rw [realMonomial_eval, Finsupp.prod_zero_index, one_smul]

noncomputable def commonAffineMarkedOrbit : (D.markedQuotientMultidegree t).realification.PolynomialOrbit :=
  realMarkedAffineMixedOrbit D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t 1 (D.realAffineMarkedBase t x y) (D.realAffineMarkedSlope t y u)

theorem commonAffineMarkedOrbit_at_zero (h : ℤ) :
    (D.markedQuotientMultidegree t).realification.polynomialOrbitEval (correlationInput h 0)
      (D.commonAffineMarkedOrbit t x y u) = 1 :=
  realMarkedAffineMixedOrbit_at_zero _ _ _ _ _ _ _ _ _ _ h

theorem commonAffineMarkedOrbit_normalized :
    (D.markedQuotientMultidegree t).realification.polynomialOrbitEval 0
      (D.commonAffineMarkedOrbit t x y u) = 1 :=
  realMarkedAffineMixedOrbit_normalized _ _ _ _ _ _ _ _ _ _

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ) (u : Fin t → ℝ)

noncomputable def commonAffineMarkedLift (h n : ℤ) :
    ℝ ⊗[ℚ] markedShiftSubalgebra D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t :=
  ∑ j : Fin s, (n : ℚ) ^ (j.val + 1) •
    (realMarkedPolynomialLift D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
      D.coefficientFreeGenerator_mem_layer t (j.val + 1) 0 1 (D.realAffineMarkedBase t x y j) +
    (h : ℚ) • realMarkedPolynomialLift D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
      D.coefficientFreeGenerator_mem_layer t (j.val + 1) 1 1 (D.realAffineMarkedSlope t y u j))

theorem commonAffineMarkedOrbit_eval (h n : ℤ) :
    ((D.markedQuotientMultidegree t).realification.polynomialOrbitEval (correlationInput h n)
      (D.commonAffineMarkedOrbit t x y u)).coord =
        (lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent t)).toLinearMap.baseChange ℝ
            (D.commonAffineMarkedLift t x y u h n) := by
  have he := realMarkedAffineMixedOrbit_eval D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t 1 (D.realAffineMarkedBase t x y) (D.realAffineMarkedSlope t y u) h n
  apply he.trans
  simp only [commonAffineMarkedLift, map_sum, LinearMap.map_smul_of_tower, map_add]
  rfl

theorem commonAffineMarkedLift_eval (a : Fin t → ℚ) (h n : ℤ) :
    (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t a).baseChange ℝ
        (D.commonAffineMarkedLift t x y u h n) =
          ∑ j : Fin s, (n : ℚ) ^ (j.val + 1) •
            ((x j).val + ∑ i, ((a i : ℝ) + (h : ℝ) * u i) • (y j i).val) := by
  simp only [commonAffineMarkedLift, map_sum, LinearMap.map_smul_of_tower, map_add]
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun z : ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra => (n : ℚ) ^ (j.val + 1) • z)
  calc
    _ = ((x j).val + ∑ i, a i • (y j i).val) + (h : ℚ) • (∑ i, u i • (y j i).val) :=
      congrArg₂ (fun z z' : ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra => z + (h : ℚ) • z')
        (D.realAffineMarkedBase_eval t x y j a) (D.realAffineMarkedSlope_eval t y u j a)
    _ = _ := by
      simp only [add_smul, Finset.sum_add_distrib, Finset.smul_sum,
        ← Rat.cast_smul_eq_qsmul ℝ, Rat.cast_intCast, smul_smul, add_assoc]

end Erdos3.NativeRankRelation.CommonData

end

end OAI
