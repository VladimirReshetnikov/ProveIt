import Mathlib.LinearAlgebra.Projection
import OAI.Combinatorics.Progressions.Geometry.TerminalChartSlowEvaluation

namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical

noncomputable def retainedTagProjection {T : Type*} [Fintype T]
    (U : Submodule ℝ (T → ℝ)) : (T → ℝ) →ₗ[ℝ] (T → ℝ) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : T => ℝ)).toLinearMap.comp
    ((euclideanSubspace U).starProjection.toLinearMap.comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : T => ℝ)).symm.toLinearMap)

theorem retainedTagProjection_mem {T : Type*} [Fintype T]
    (U : Submodule ℝ (T → ℝ)) (x : T → ℝ) : retainedTagProjection U x ∈ U :=
  (euclideanSubspace U).starProjection_apply_mem _

theorem retainedTagProjection_eq {T : Type*} [Fintype T]
    (U : Submodule ℝ (T → ℝ)) {x : T → ℝ} (hx : x ∈ U) :
    retainedTagProjection U x = x := by
  have he : (euclideanSubspace U).starProjection (WithLp.toLp 2 x) = WithLp.toLp 2 x :=
    Submodule.starProjection_eq_self_iff.mpr hx
  exact congrArg WithLp.ofLp he

theorem retainedTagProjection_entry_le_one {T : Type*} [Fintype T]
    (U : Submodule ℝ (T → ℝ)) (a i : T) :
    |retainedTagProjection U (Pi.single a 1) i| ≤ 1 := by
  have h := (PiLp.norm_apply_le
    ((euclideanSubspace U).starProjection (WithLp.toLp 2 (Pi.single a (1 : ℝ)))) i).trans
      ((euclideanSubspace U).norm_starProjection_apply_le _)
  change |((euclideanSubspace U).starProjection
    (WithLp.toLp 2 (Pi.single a (1 : ℝ)))) i| ≤ 1
  simpa only [Real.norm_eq_abs, PiLp.toLp_single, PiLp.norm_single, norm_one] using h

variable {m : ℕ} {X : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]

noncomputable def fullTaggedLinearMapChart
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) :
    X ⊕ (Σ j, J j) → MvPolynomial (X ⊕ (Σ j, J j)) ℝ
  | Sum.inl x => MvPolynomial.X (Sum.inl x)
  | Sum.inr ⟨j, i⟩ => ∑ a : J j,
      (P j (Pi.single a 1) i) • MvPolynomial.X (Sum.inr ⟨j, a⟩)

noncomputable def fullTaggedAffineMapChart
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (c : ∀ j, J j → ℝ) :
    X ⊕ (Σ j, J j) → MvPolynomial (X ⊕ (Σ j, J j)) ℝ
  | Sum.inl x => MvPolynomial.X (Sum.inl x)
  | Sum.inr ⟨j, i⟩ => C (c j i - P j (c j) i) +
      fullTaggedLinearMapChart J P (Sum.inr ⟨j, i⟩)

theorem fullTaggedLinearMapChart_homogeneous
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (v : X ⊕ (Σ j, J j)) :
    (fullTaggedLinearMapChart J P v).IsWeightedHomogeneous
      (fullTaggedVariableWeight J) (fullTaggedVariableWeight J v) := by
  cases v with
  | inl x => exact isWeightedHomogeneous_X (R := ℝ) _ _
  | inr v =>
    apply (weightedHomogeneousSubmodule ℝ _ _).sum_mem
    intro a _
    exact (weightedHomogeneousSubmodule ℝ _ _).smul_mem _
      (isWeightedHomogeneous_X (R := ℝ) (fullTaggedVariableWeight J) (Sum.inr ⟨v.1, a⟩))

theorem fullTaggedAffineMapChart_support
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (v : X ⊕ (Σ j, J j)) :
    fullTaggedAffineMapChart J P c v ∈
      weightedSupportLE (fullTaggedVariableWeight J) (fullTaggedVariableWeight J v) := by
  cases v with
  | inl x => exact weightedSupportLE_X _ _
  | inr v =>
    apply (weightedSupportLE _ _).add_mem (weightedSupportLE_C _ _ _)
    apply (weightedSupportLE _ _).sum_mem
    intro a _
    exact (weightedSupportLE _ _).smul_mem _
      (weightedSupportLE_X (R := ℝ) (fullTaggedVariableWeight J) (Sum.inr ⟨v.1, a⟩))

theorem fullTaggedAffineMapChart_top
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (v : X ⊕ (Σ j, J j)) :
    weightedHomogeneousComponent (fullTaggedVariableWeight J) (fullTaggedVariableWeight J v)
      (fullTaggedAffineMapChart J P c v) = fullTaggedLinearMapChart J P v := by
  cases v with
  | inl x => exact weightedHomogeneousComponent_eq_self (isWeightedHomogeneous_X (R := ℝ) _ _)
  | inr v =>
    change weightedHomogeneousComponent _ _ (C _ + _) = _
    rw [map_add, weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_C (R := ℝ) _ _)]
    simp only [fullTaggedVariableWeight, Sum.elim_inr, Nat.add_eq_zero_iff,
      Nat.one_ne_zero, and_false, ↓reduceIte, zero_add]
    exact weightedHomogeneousComponent_eq_self (fullTaggedLinearMapChart_homogeneous J P _)

theorem fullTaggedLinearMapChart_eval_tag
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (x : X ⊕ (Σ j, J j) → ℝ)
    (j : Fin m) (i : J j) :
    MvPolynomial.eval x (fullTaggedLinearMapChart J P (Sum.inr ⟨j, i⟩)) =
      P j (fun a => x (Sum.inr ⟨j, a⟩)) i := by
  have hsum : ∑ a : J j, x (Sum.inr ⟨j, a⟩) • Pi.single a (1 : ℝ) =
      (fun a => x (Sum.inr ⟨j, a⟩)) := by
    ext a
    simp [Pi.smul_apply, Pi.single_apply]
  rw [fullTaggedLinearMapChart]
  simp only [map_sum, smul_eq_C_mul, map_mul, eval_C, eval_X]
  rw [← hsum, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

theorem fullTaggedAffineMapChart_eval_tag
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (x : X ⊕ (Σ j, J j) → ℝ) (j : Fin m) (i : J j) :
    MvPolynomial.eval x (fullTaggedAffineMapChart J P c (Sum.inr ⟨j, i⟩)) =
      c j i + P j ((fun a => x (Sum.inr ⟨j, a⟩)) - c j) i := by
  rw [fullTaggedAffineMapChart, map_add, eval_C, fullTaggedLinearMapChart_eval_tag,
    map_sub, Pi.sub_apply]
  ring

theorem fullTaggedAffineMapChart_top_mem_set
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (hP : ∀ j x, P j x ∈ U j)
    (K : Set ((X ⊕ (Σ j, J j)) → ℝ))
    (hK : ∀ y, (∀ j, (fun i => y (Sum.inr ⟨j, i⟩)) ∈ U j) → y ∈ K)
    (x : X ⊕ (Σ j, J j) → ℝ) :
    (fun v => MvPolynomial.eval x
      (weightedHomogeneousComponent (fullTaggedVariableWeight J) (fullTaggedVariableWeight J v)
        (fullTaggedAffineMapChart J P c v))) ∈ K := by
  apply hK
  intro j
  simp_rw [fullTaggedAffineMapChart_top, fullTaggedLinearMapChart_eval_tag]
  exact hP j _

theorem fullTaggedAffineMapChart_eval_eq
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (hP : ∀ j y, y ∈ U j → P j y = y)
    (x : X ⊕ (Σ j, J j) → ℝ)
    (hx : ∀ j, (fun a => x (Sum.inr ⟨j, a⟩)) - c j ∈ U j) :
    (fun v => MvPolynomial.eval x (fullTaggedAffineMapChart J P c v)) = x := by
  funext v
  cases v with
  | inl a => exact MvPolynomial.eval_X _
  | inr v =>
    rw [fullTaggedAffineMapChart_eval_tag, hP _ _ (hx _), Pi.sub_apply]
    ring

theorem fullTaggedAffineMapChart_eval_eq_of_quotient
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (hP : ∀ j y, y ∈ U j → P j y = y)
    {D : Fin m → Type*} [∀ j, AddCommGroup (D j)] [∀ j, Module ℝ (D j)]
    (Q : ∀ j, (J j → ℝ) →ₗ[ℝ] D j) (hQ : ∀ j, LinearMap.ker (Q j) = U j)
    (x : X ⊕ (Σ j, J j) → ℝ)
    (hx : ∀ j, Q j (fun a => x (Sum.inr ⟨j, a⟩)) = Q j (c j)) :
    (fun v => MvPolynomial.eval x (fullTaggedAffineMapChart J P c v)) = x := by
  apply fullTaggedAffineMapChart_eval_eq J P c U hP x
  intro j
  rw [← hQ j, LinearMap.mem_ker, map_sub, hx j, sub_self]

noncomputable def fullTaggedLinearRetraction
    (U : ∀ j, Submodule ℝ (J j → ℝ)) :
    X ⊕ (Σ j, J j) → MvPolynomial (X ⊕ (Σ j, J j)) ℝ
  | Sum.inl x => MvPolynomial.X (Sum.inl x)
  | Sum.inr ⟨j, i⟩ => ∑ a : J j,
      (retainedTagProjection (U j) (Pi.single a 1) i) • MvPolynomial.X (Sum.inr ⟨j, a⟩)

noncomputable def fullTaggedAffineRetraction
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ) :
    X ⊕ (Σ j, J j) → MvPolynomial (X ⊕ (Σ j, J j)) ℝ
  | Sum.inl x => MvPolynomial.X (Sum.inl x)
  | Sum.inr ⟨j, i⟩ =>
      C (c j i - retainedTagProjection (U j) (c j) i) +
        fullTaggedLinearRetraction J U (Sum.inr ⟨j, i⟩)

theorem fullTaggedLinearRetraction_homogeneous
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (v : X ⊕ (Σ j, J j)) :
    (fullTaggedLinearRetraction J U v).IsWeightedHomogeneous
      (fullTaggedVariableWeight J) (fullTaggedVariableWeight J v) := by
  classical
  cases v with
  | inl x => exact isWeightedHomogeneous_X (R := ℝ) _ _
  | inr v =>
    apply (weightedHomogeneousSubmodule ℝ _ _).sum_mem
    intro a _
    exact (weightedHomogeneousSubmodule ℝ _ _).smul_mem _
      (isWeightedHomogeneous_X (R := ℝ) (fullTaggedVariableWeight J) (Sum.inr ⟨v.1, a⟩))

theorem fullTaggedAffineRetraction_support
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (v : X ⊕ (Σ j, J j)) :
    fullTaggedAffineRetraction J U c v ∈
      weightedSupportLE (fullTaggedVariableWeight J) (fullTaggedVariableWeight J v) := by
  classical
  cases v with
  | inl x => exact weightedSupportLE_X _ _
  | inr v =>
    apply (weightedSupportLE _ _).add_mem (weightedSupportLE_C _ _ _)
    apply (weightedSupportLE _ _).sum_mem
    intro a _
    exact (weightedSupportLE _ _).smul_mem _
      (weightedSupportLE_X (R := ℝ) (fullTaggedVariableWeight J) (Sum.inr ⟨v.1, a⟩))

theorem fullTaggedAffineRetraction_top
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (v : X ⊕ (Σ j, J j)) :
    weightedHomogeneousComponent (fullTaggedVariableWeight J) (fullTaggedVariableWeight J v)
      (fullTaggedAffineRetraction J U c v) = fullTaggedLinearRetraction J U v := by
  cases v with
  | inl x => exact weightedHomogeneousComponent_eq_self (isWeightedHomogeneous_X (R := ℝ) _ _)
  | inr v =>
    change weightedHomogeneousComponent _ _ (C _ + _) = _
    rw [map_add, weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_C (R := ℝ) _ _)]
    simp only [fullTaggedVariableWeight, Sum.elim_inr, Nat.add_eq_zero_iff,
      Nat.one_ne_zero, and_false, ↓reduceIte, zero_add]
    exact weightedHomogeneousComponent_eq_self (fullTaggedLinearRetraction_homogeneous J U _)

theorem fullTaggedLinearRetraction_eval_tag
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (x : X ⊕ (Σ j, J j) → ℝ)
    (j : Fin m) (i : J j) :
    MvPolynomial.eval x (fullTaggedLinearRetraction J U (Sum.inr ⟨j, i⟩)) =
      retainedTagProjection (U j) (fun a => x (Sum.inr ⟨j, a⟩)) i := by
  classical
  have hsum : ∑ a : J j, x (Sum.inr ⟨j, a⟩) • Pi.single a (1 : ℝ) =
      (fun a => x (Sum.inr ⟨j, a⟩)) := by
    ext a
    simp [Pi.smul_apply, Pi.single_apply]
  rw [fullTaggedLinearRetraction]
  simp only [map_sum, smul_eq_C_mul, map_mul, eval_C, eval_X]
  rw [← hsum, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

theorem fullTaggedAffineRetraction_eval_tag
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (x : X ⊕ (Σ j, J j) → ℝ) (j : Fin m) (i : J j) :
    MvPolynomial.eval x (fullTaggedAffineRetraction J U c (Sum.inr ⟨j, i⟩)) =
      c j i + retainedTagProjection (U j) ((fun a => x (Sum.inr ⟨j, a⟩)) - c j) i := by
  rw [fullTaggedAffineRetraction, map_add, eval_C, fullTaggedLinearRetraction_eval_tag,
    map_sub, Pi.sub_apply]
  ring

theorem fullTaggedAffineRetraction_top_mem
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (x : X ⊕ (Σ j, J j) → ℝ) (j : Fin m) :
    (fun i => MvPolynomial.eval x (weightedHomogeneousComponent (fullTaggedVariableWeight J)
      (fullTaggedVariableWeight (X := X) J (Sum.inr ⟨j, i⟩))
      (fullTaggedAffineRetraction J U c (Sum.inr ⟨j, i⟩)))) ∈ U j := by
  simp_rw [fullTaggedAffineRetraction_top, fullTaggedLinearRetraction_eval_tag]
  exact retainedTagProjection_mem _ _

theorem fullTaggedAffineRetraction_top_mem_set
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (K : Set ((X ⊕ (Σ j, J j)) → ℝ))
    (hK : ∀ y, (∀ j, (fun i => y (Sum.inr ⟨j, i⟩)) ∈ U j) → y ∈ K)
    (x : X ⊕ (Σ j, J j) → ℝ) :
    (fun v => MvPolynomial.eval x
      (weightedHomogeneousComponent (fullTaggedVariableWeight J) (fullTaggedVariableWeight J v)
        (fullTaggedAffineRetraction J U c v))) ∈ K :=
  hK _ (fun j => fullTaggedAffineRetraction_top_mem J U c x j)

theorem fullTaggedAffineRetraction_eval_eq
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (x : X ⊕ (Σ j, J j) → ℝ)
    (hx : ∀ j, (fun a => x (Sum.inr ⟨j, a⟩)) - c j ∈ U j) :
    (fun v => MvPolynomial.eval x (fullTaggedAffineRetraction J U c v)) = x := by
  funext v
  cases v with
  | inl a => exact MvPolynomial.eval_X _
  | inr v =>
    rw [fullTaggedAffineRetraction_eval_tag, retainedTagProjection_eq _ (hx _), Pi.sub_apply]
    ring

theorem fullTaggedAffineRetraction_eval_eq_of_quotient
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ)
    {D : Fin m → Type*} [∀ j, AddCommGroup (D j)] [∀ j, Module ℝ (D j)]
    (Q : ∀ j, (J j → ℝ) →ₗ[ℝ] D j) (hQ : ∀ j, LinearMap.ker (Q j) = U j)
    (x : X ⊕ (Σ j, J j) → ℝ)
    (hx : ∀ j, Q j (fun a => x (Sum.inr ⟨j, a⟩)) = Q j (c j)) :
    (fun v => MvPolynomial.eval x (fullTaggedAffineRetraction J U c v)) = x := by
  apply fullTaggedAffineRetraction_eval_eq J U c x
  intro j
  rw [← hQ j, LinearMap.mem_ker, map_sub, hx j, sub_self]

theorem RationalTaggedConstraintCertificate.exists_affineRetraction
    {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {p : ℝ} {Cblocks : ℕ}
    (hcert : RationalTaggedConstraintCertificate J Set.univ K p Cblocks)
    (hp : 0 ≤ p) (hdim : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (hblocks : (Cblocks : ℝ) ≤ p) :
    ∃ U : ∀ j, Submodule ℝ (J j → ℝ),
      K = {x | ∀ j, (fun i => x (Sum.inr ⟨j, i⟩)) ∈ U j} ∧
      ∀ (c : ∀ j, J j → ℝ) (x : X ⊕ (Σ j, J j) → ℝ),
        (fun v => MvPolynomial.eval x
          (weightedHomogeneousComponent (fullTaggedVariableWeight J)
            (fullTaggedVariableWeight J v) (fullTaggedAffineRetraction J U c v))) ∈ K := by
  obtain ⟨W, n, b, _, _, hK⟩ := hcert.exists_bounded_tag_bases_univ hp hdim hblocks
  let U := fun j => Submodule.span ℝ
    (Set.range (fun a i => ((b j a : J j → ℚ) i : ℝ)))
  refine ⟨U, hK, ?_⟩
  intro c x
  apply fullTaggedAffineRetraction_top_mem_set J U c K _ x
  intro y hy
  rw [hK]
  exact hy

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

namespace CertifiedFullChartFiniteHistory

variable {m s : ℕ} {X ι η L : Type} [Fintype ι] [Fintype η]
  [LieRing L] [LieAlgebra ℚ L]
  {F : NilpotentLieFiltration L s} {b : Basis ι ℚ L} {ω : ι → ℕ}
  {hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})}
  {J : Fin m → Type} [∀ j, Fintype (J j)]
  {W : LieSubalgebra ℚ F.AssociatedGraded}
  {basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ W.toSubmodule))}
  {lift : (F.AssociatedGraded ⧸ W.toSubmodule) →ₗ[ℚ] F.AssociatedGraded}
  {Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
  {Utag : ∀ j, Submodule ℝ (J j → ℝ)}
  {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)} {N : X → ℕ} {Bphase : ℝ}

local notation "wt" => fullTaggedVariableWeight (X := X) J

theorem exists_affine_globalMarkedNativeFactors
    (history : CertifiedFullChartFiniteHistory F b ω hF J W.toSubmodule basis lift
      Z Set.univ Utag poly N Bphase s)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule)
    (g : (F.realification.adaptedPolynomialFiltration wt).Group)
    (hZ : F.realPolynomialSymbolHom b ω hF wt g = Z)
    {p : ℝ} {blocks : ℕ}
    (hcert : RationalTaggedConstraintCertificate J Set.univ history.K p blocks)
    (hp : 0 ≤ p) (hdim : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (hblocks : (blocks : ℝ) ≤ p) :
    ∃ (V : ∀ j, Submodule ℚ (J j → ℚ)) (n : Fin m → ℕ)
      (v : ∀ j, Basis (Fin (n j)) ℚ (V j)),
      (∀ j, n j ≤ Fintype.card (J j)) ∧
      (∀ j a i, rationalLogHeight ((v j a : J j → ℚ) i) ≤ ((p + 2) ^ 2 + 2) ^ 63) ∧
      let Ktag := fun j => Submodule.span ℝ
        (Set.range (fun a i => ((v j a : J j → ℚ) i : ℝ)))
      history.K = {t | ∀ j, (fun i => t (Sum.inr ⟨j, i⟩)) ∈ Ktag j} ∧
      ∀ c : ∀ j, J j → ℝ,
        let β := fullTaggedAffineRetraction (X := X) J Ktag c
        let pull := F.realSymbolHomogeneousPullbackHom b ω hF wt wt
          (fun i => weightedHomogeneousComponent wt (wt i) (β i))
          (fun _i => weightedHomogeneousComponent_isWeightedHomogeneous _ _)
        Nonempty (GlobalMarkedNativeFactors F b ω hF wt W
          (F.weightedAdaptedRealChartHom wt wt β
            (fullTaggedAffineRetraction_support J Ktag c) g)
          (pull history.outer.1) (pull history.outer.2)) := by
  obtain ⟨V, n, v, hn, hv, hK⟩ := hcert.exists_bounded_tag_bases_univ hp hdim hblocks
  refine ⟨V, n, v, hn, hv, hK, ?_⟩
  intro c
  apply history.nonempty_globalMarkedNativeFactors hW _ _ g hZ
  intro t
  rw [hK]
  exact fun j => fullTaggedAffineRetraction_top_mem J
    (fun j => Submodule.span ℝ (Set.range (fun a i => ((v j a : J j → ℚ) i : ℝ)))) c t j

end CertifiedFullChartFiniteHistory

namespace GlobalMarkedNativeFactors

variable {m s : ℕ} {X ι L : Type*} [LieRing L] [LieAlgebra ℚ L]
  {F : NilpotentLieFiltration L s} {b : Basis ι ℚ L} {ω : ι → ℕ}
  {hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})}
  {J : Fin m → Type*} [∀ j, Fintype (J j)]
  {W : LieSubalgebra ℚ F.AssociatedGraded}
  {Ktag : ∀ j, Submodule ℝ (J j → ℝ)} {c : ∀ j, J j → ℝ}

local notation "wt" => fullTaggedVariableWeight (X := X) J
local notation "β" => fullTaggedAffineRetraction (X := X) J Ktag c

theorem affine_product_values
    {g : (F.realification.adaptedPolynomialFiltration wt).Group}
    {E R : F.RealPolynomialSymbolGroup wt}
    (A : GlobalMarkedNativeFactors F b ω hF wt W
      (F.weightedAdaptedRealChartHom wt wt β
        (fullTaggedAffineRetraction_support J Ktag c) g) E R)
    (t : X ⊕ (Σ j, J j) → ℝ)
    (ht : ∀ j, (fun i => t (Sum.inr ⟨j, i⟩)) - c j ∈ Ktag j) :
    F.adaptedPolynomialRealValueHom wt t A.left *
        NilpotentLieBCHGroup.realificationMap
          (hnil := (F.gradedRefiltration W).lowerCentralSeries_eq_bot)
          (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra W).incl
          ((F.gradedRefiltration W).realification.polynomialOrbitRealEval wt t A.markedMiddle) *
        F.adaptedPolynomialRealValueHom wt t A.right =
      F.adaptedPolynomialRealValueHom wt t g := by
  rw [A.product_values, F.adaptedPolynomialRealValueHom_weightedChart]
  rw [fullTaggedAffineRetraction_eval_eq J Ktag c t ht]

end GlobalMarkedNativeFactors
end Erdos3.NilpotentLieFiltration

end

end OAI
