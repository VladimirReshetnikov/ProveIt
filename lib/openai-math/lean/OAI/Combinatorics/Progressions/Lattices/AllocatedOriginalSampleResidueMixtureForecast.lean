import OAI.Combinatorics.Progressions.Sampling.AllocatedKernelForecastSourceDecoupling
import OAI.Combinatorics.Progressions.Sampling.AllocatedOriginalSampleConditionalForecastComparison
import OAI.Combinatorics.Progressions.Sampling.ForecastInactiveFiberLaw
import OAI.Combinatorics.Progressions.Sampling.ForecastInactiveSlicedFixedProduct

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem forecastInactive_kernel_disintegration
    {Ω Z R : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype R] [DecidableEq R]
    (p : FiniteProbabilityWeights Ω) (residue : Ω → R)
    (kernel : Ω → PMF Z) (z : Z) (coefficient : R → ℂ) :
    p.complexMean (fun x => coefficient (residue x) * ((kernel x z).toReal : ℂ)) =
      ∑ r : {r : R // 0 < p.mass (Finset.univ.filter (fun x => residue x = r))},
        (p.mass (Finset.univ.filter (fun x => residue x = r.val)) : ℂ) * coefficient r.val *
          ((((p.condition (Finset.univ.filter (fun x => residue x = r.val)) r.property).toPMF.bind
            kernel) z).toReal : ℂ) := by
  calc
    _ = p.complexMean (fun x => ((kernel x z).toReal : ℂ) * coefficient (residue x)) := by
      congr 1
      funext x
      exact mul_comm _ _
    _ = ∑ r, (p.fiberMean residue r (fun x => (kernel x z).toReal) : ℂ) * coefficient r :=
      p.complexMean_fiber_factor residue (fun x => (kernel x z).toReal) coefficient
    _ = _ := by
      apply Finset.sum_congr_set
        {r : R | 0 < p.mass (Finset.univ.filter (fun x => residue x = r))}
      · intro r hr
        rw [forecastInactive_fiber_kernel p residue r hr kernel z, Complex.ofReal_mul]
        ring
      · intro r hr
        have hzero : p.mass (Finset.univ.filter (fun x => residue x = r)) = 0 :=
          le_antisymm (le_of_not_gt hr) (p.mass_nonneg _)
        have hf : p.fiberMean residue r (fun x => (kernel x z).toReal) = 0 := by
          simpa only [FiniteProbabilityWeights.fiberMean, Finset.mem_filter,
            Finset.mem_univ, true_and] using p.mean_mask_zero
            (Finset.univ.filter (fun x => residue x = r)) hzero
            (fun x => (kernel x z).toReal)
        rw [hf, Complex.ofReal_zero, zero_mul]

theorem forecastInactive_indicator_disintegration
    {Ω Z R : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype R] [DecidableEq R]
    [DecidableEq Z] (p : FiniteProbabilityWeights Ω) (residue : Ω → R)
    (F : Ω → Z) (z : Z) (coefficient : R → ℂ) :
    p.complexMean (fun y => coefficient (residue y) * (if F y = z then 1 else 0)) =
      ∑ r : {r : R // 0 < p.mass (Finset.univ.filter (fun y => residue y = r))},
        (p.mass (Finset.univ.filter (fun y => residue y = r.val)) : ℂ) * coefficient r.val *
          ((((p.condition (Finset.univ.filter (fun y => residue y = r.val)) r.property).toPMF.map
            F) z).toReal : ℂ) := by
  have hp (y : Ω) : ((PMF.pure (F y) z).toReal : ℂ) = if F y = z then 1 else 0 := by
    by_cases hy : F y = z
    · simp [PMF.pure_apply, hy]
    · simp [PMF.pure_apply, hy, Ne.symm hy]
  simpa only [PMF.bind_pure_comp, Function.comp_apply, hp] using
    forecastInactive_kernel_disintegration p residue (PMF.pure ∘ F) z coefficient

theorem forecastInactive_positiveResidue_mass_sum
    {Ω R : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype R] [DecidableEq R]
    (p : FiniteProbabilityWeights Ω) (residue : Ω → R) :
    (∑ r : {r : R // 0 < p.mass (Finset.univ.filter (fun x => residue x = r))},
      p.mass (Finset.univ.filter (fun x => residue x = r.val))) = 1 := by
  have hsum : (∑ r : R, p.mass (Finset.univ.filter (fun x => residue x = r))) =
      ∑ r : {r : R // 0 < p.mass (Finset.univ.filter (fun x => residue x = r))},
        p.mass (Finset.univ.filter (fun x => residue x = r.val)) := by
    apply Finset.sum_congr_set
      {r : R | 0 < p.mass (Finset.univ.filter (fun x => residue x = r))}
    · intro r hr
      rfl
    · intro r hr
      exact le_antisymm (le_of_not_gt hr) (p.mass_nonneg _)
  rw [← hsum]
  simpa only [FiniteProbabilityWeights.fiberLaw_weight_eq_mass] using
    (p.fiberLaw residue).total

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {A : Type*} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (rows : A → Finset (Finset α)) (x : G → IntegerScalarCubeBox α S.value)

noncomputable def forecastInactivePhysicalJointKernel
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S)) :
    PMF (∀ a, rows a → ℤ) :=
  dependentProductPMF (fun a => integerMatrixImagePMF (boundedCoefficientJetMatrix
    (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
    (allocatedPhysicalCubeDirections B U b S x y) ((selected a).1.val + 1)
    (fun t : rows a => (t : Finset α)))
    (allocatedLayerIntegerPMFs B U b hR hσ S (selected a).1 (selected a).2))

theorem forecastInactive_physical_fiber_kernel
    (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (z : ∀ a, rows a → ℤ) :
    (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).fiberMean
        (principalResidueLabel q) r
        (fun y => (forecastInactivePhysicalJointKernel B U b hR hσ S selected rows x y z).toReal) =
      (principalTupleWeights (α := α) B (layerSamplerDegree I n)
        (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)) *
        (allocatedSupportedPhysicalJointPMF B U b hR hσ S q r hcell selected rows x z).toReal := by
  exact forecastInactive_fiber_kernel _ (principalResidueLabel q) r hcell
    (forecastInactivePhysicalJointKernel B U b hR hσ S selected rows x) z

theorem forecastInactive_physical_kernel_disintegration
    (q : ℕ) [NeZero q]
    (coefficient : (PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q) → ℂ)
    (z : ∀ a, rows a → ℤ) :
    let p := principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    p.complexMean (fun y => coefficient (principalResidueLabel q y) *
      ((forecastInactivePhysicalJointKernel B U b hR hσ S selected rows x y z).toReal : ℂ)) =
      ∑ r : {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q //
          0 < p.mass (Finset.univ.filter (fun y => principalResidueLabel q y = r))},
        (p.mass (Finset.univ.filter (fun y => principalResidueLabel q y = r.val)) : ℂ) *
          coefficient r.val *
          ((allocatedSupportedPhysicalJointPMF B U b hR hσ S q r.val r.property
            selected rows x z).toReal : ℂ) := by
  exact forecastInactive_kernel_disintegration _ (principalResidueLabel q)
    (forecastInactivePhysicalJointKernel B U b hR hσ S selected rows x) z coefficient

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {X R : Type*} [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R]

omit [Fintype R] in
theorem condition_complexMean_fiber_apply (p : FiniteProbabilityWeights X) (residue : X → R)
    (r : R) (hr : 0 < p.mass (Finset.univ.filter (fun x => residue x = r)))
    (test : R → X → ℂ) :
    (p.condition _ hr).complexMean (fun x => test (residue x) x) =
      (p.condition _ hr).complexMean (test r) := by
  apply (p.condition _ hr).complexMean_congr_support
  intro x hx
  have hxr : residue x = r :=
    (Finset.mem_filter.mp (condition_weight_support p _ hr x hx).1).2
  rw [hxr]

theorem complexMean_positiveResidue_disintegration
    (p : FiniteProbabilityWeights X) (residue : X → R) (test : R → X → ℂ) :
    p.complexMean (fun x => test (residue x) x) =
      ∑ r : {r : R // 0 < p.mass (Finset.univ.filter (fun x => residue x = r))},
        (p.mass (Finset.univ.filter (fun x => residue x = r.val)) : ℂ) *
          (p.condition (Finset.univ.filter (fun x => residue x = r.val)) r.property).complexMean
            (test r.val) := by
  calc
    _ = ∑ r, p.fiberComplexMean residue r (fun x => test (residue x) x) := by
      simpa only [Finset.mem_univ, ite_true] using
        (p.sum_fiberComplexMean_on residue Finset.univ (fun x => test (residue x) x)).symm
    _ = _ := by
      apply Finset.sum_congr_set
        {r : R | 0 < p.mass (Finset.univ.filter (fun x => residue x = r))}
      · intro r hr
        rw [p.fiberComplexMean_eq_condition residue r _ hr,
          p.condition_complexMean_fiber_apply residue r hr test]
      · intro r hr
        apply p.fiberComplexMean_zero
        rw [p.fiberLaw_weight_eq_mass]
        exact le_antisymm (le_of_not_gt hr) (p.mass_nonneg _)

theorem complexMean_positiveResidue_weighted_disintegration
    (p : FiniteProbabilityWeights X) (residue : X → R)
    (coefficient : R → ℂ) (test : R → X → ℂ) :
    p.complexMean (fun x => coefficient (residue x) * test (residue x) x) =
      ∑ r : {r : R // 0 < p.mass (Finset.univ.filter (fun x => residue x = r))},
        (p.mass (Finset.univ.filter (fun x => residue x = r.val)) : ℂ) * coefficient r.val *
          (p.condition (Finset.univ.filter (fun x => residue x = r.val)) r.property).complexMean
            (test r.val) := by
  rw [p.complexMean_positiveResidue_disintegration residue
    (fun r x => coefficient r * test r x)]
  apply Finset.sum_congr rfl
  intro r _
  rw [complexMean_mul_left, mul_assoc]

theorem complexMean_positiveResidue_weighted_error
    (p : FiniteProbabilityWeights X) (residue : X → R)
    (coefficient : R → ℂ) (test : R → X → ℂ)
    (target : {r : R // 0 < p.mass (Finset.univ.filter (fun x => residue x = r))} → ℂ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hcoefficient : ∀ r : {r : R // 0 < p.mass (Finset.univ.filter (fun x => residue x = r))},
      ‖coefficient r.val‖ ≤ 1)
    (herror : ∀ r : {r : R // 0 < p.mass (Finset.univ.filter (fun x => residue x = r))},
      ‖(p.condition (Finset.univ.filter (fun x => residue x = r.val)) r.property).complexMean
        (test r.val) - target r‖ ≤ ε) :
    ‖p.complexMean (fun x => coefficient (residue x) * test (residue x) x) -
      ∑ r : {r : R // 0 < p.mass (Finset.univ.filter (fun x => residue x = r))},
        (p.mass (Finset.univ.filter (fun x => residue x = r.val)) : ℂ) * coefficient r.val *
          target r‖ ≤ ε := by
  rw [p.complexMean_positiveResidue_weighted_disintegration residue,
    ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ r : {r : R // 0 < p.mass (Finset.univ.filter (fun x => residue x = r))},
        p.mass (Finset.univ.filter (fun x => residue x = r.val)) * ε := by
      apply Finset.sum_le_sum
      intro r _
      rw [← mul_sub, norm_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (p.mass_nonneg _), mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (p.mass_nonneg _)
      exact (mul_le_mul_of_nonneg_left (herror r) (norm_nonneg _)).trans
        ((mul_le_mul_of_nonneg_right (hcoefficient r) hε).trans_eq (one_mul ε))
    _ = ε := by
      rw [← Finset.sum_mul, forecastInactive_positiveResidue_mass_sum p residue, one_mul]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "degree" => layerSamplerDegree I n
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "hSides" => allocatedPrincipalSides_pos B U basis S
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Short" => {a : LayerSamplerAxis I n // short a}
local notation "activeB" => (fun a : Active => B (Subtype.val a))
local notation "activeDegree" => (fun a : Active => degree (Subtype.val a))
local notation "ActiveInput" => PrincipalTupleIndex activeB activeDegree
local notation "FullInput" => PrincipalTupleIndex B degree
local notation "ShortTuple" => PrincipalAxisTuples (α := Empty) short sides
local notation "ActiveTuple" => PrincipalAxisTuples (α := Empty) (fun a => ¬short a) sides
local notation "law" => principalTupleWeights (α := Empty) B degree sides hSides

noncomputable def allocatedUnconditionalShortPrincipalLaw :
    FiniteProbabilityWeights ShortTuple :=
  principalTupleWeights (fun a : Short => B a.val) (fun a => degree a.val)
    (principalAxisLength short sides) (fun j => hSides ⟨j.1.val, j.2⟩)

noncomputable def allocatedUnconditionalActivePrincipalLaw :
    FiniteProbabilityWeights ActiveTuple :=
  principalTupleWeights activeB activeDegree (principalAxisLength (fun a => ¬short a) sides)
    (fun j => hSides ⟨j.1.val, j.2⟩)

noncomputable def allocatedPrincipalResidueJoin (q : ℕ) (u : ShortTuple)
    (r : ActiveInput → ZMod q) : FullInput → Option Empty → ZMod q :=
  principalAxisResidueJoin short u q (fun j _ => r j)

theorem allocatedPrincipalResidueJoin_label_join (q : ℕ) (u : ShortTuple) (v : ActiveTuple) :
    principalResidueLabel q (principalAxisJoin short u v) =
      allocatedPrincipalResidueJoin B U basis S q u (fun j => ((v j none : ℤ) : ZMod q)) := by
  rw [principalResidueLabel_join]
  unfold allocatedPrincipalResidueJoin
  congr 1
  funext j c
  cases c with
  | none => rfl
  | some e => exact e.elim

theorem allocatedPrincipalResidue_short_marginal
    (q : ℕ) (r : FullInput → Option Empty → ZMod q)
    (hr : 0 < (law).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (f : ShortTuple → ℂ) :
    ((law).condition (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hr).complexMean
        (fun y => f (principalAxisRestrict short y)) =
      (allocatedShortPrincipalResidueLaw B U basis S q r hr).complexMean f := by
  rw [allocatedPrincipalResidue_partition B U basis S q r hr]
  simp only [principalAxisRestrict_join_left, FiniteProbabilityWeights.complexMean_const]

theorem allocatedPrincipalResidue_mixture_reconstruct
    (q : ℕ) [NeZero q] (f : (FullInput → Option Empty → ZMod q) → ShortTuple → ℂ) :
    (∑ r : {r : FullInput → Option Empty → ZMod q //
        0 < (law).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r))},
      ((law).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r.val)) : ℂ) *
        (allocatedShortPrincipalResidueLaw B U basis S q r.val r.property).complexMean (f r.val)) =
      (law).complexMean (fun y => f (principalResidueLabel q y) (principalAxisRestrict short y)) := by
  rw [(law).complexMean_positiveResidue_disintegration (principalResidueLabel q)
    (fun r y => f r (principalAxisRestrict short y))]
  apply Finset.sum_congr rfl
  intro r _
  rw [allocatedPrincipalResidue_short_marginal B U basis S q r.val r.property]

theorem allocatedPrincipalResidue_mixture_partition
    (q : ℕ) [NeZero q] (f : (FullInput → Option Empty → ZMod q) → ShortTuple → ℂ) :
    (∑ r : {r : FullInput → Option Empty → ZMod q //
        0 < (law).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r))},
      ((law).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r.val)) : ℂ) *
        (allocatedShortPrincipalResidueLaw B U basis S q r.val r.property).complexMean (f r.val)) =
      (allocatedUnconditionalShortPrincipalLaw B U basis S).complexMean (fun u =>
        (allocatedUnconditionalActivePrincipalLaw B U basis S).complexMean (fun v =>
          f (allocatedPrincipalResidueJoin B U basis S q u
            (fun j => ((v j none : ℤ) : ZMod q))) u)) := by
  rw [allocatedPrincipalResidue_mixture_reconstruct B U basis S q f,
    principalTupleWeights_partition short sides hSides]
  simp only [principalAxisRestrict_join_left,
    allocatedPrincipalResidueJoin_label_join B U basis S]
  rfl

theorem allocatedPrincipalResidue_mixture_active_residue
    (q : ℕ) [NeZero q] (f : (FullInput → Option Empty → ZMod q) → ShortTuple → ℂ) :
    (∑ r : {r : FullInput → Option Empty → ZMod q //
        0 < (law).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r))},
      ((law).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r.val)) : ℂ) *
        (allocatedShortPrincipalResidueLaw B U basis S q r.val r.property).complexMean (f r.val)) =
      (allocatedUnconditionalShortPrincipalLaw B U basis S).complexMean (fun u =>
        ((allocatedUnconditionalActivePrincipalLaw B U basis S).fiberLaw
          (fun v j => ((v j none : ℤ) : ZMod q))).complexMean
            (fun r => f (allocatedPrincipalResidueJoin B U basis S q u r) u)) := by
  simp only [FiniteProbabilityWeights.fiberLaw_complexMean]
  exact allocatedPrincipalResidue_mixture_partition B U basis S q f

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "hSides" => allocatedPrincipalSides_pos B U basis S
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "AI" => PrincipalTupleIndex (fun a : Active => B (Subtype.val a)) (fun a : Active => degree (Subtype.val a))
local notation "FullInput" => PrincipalTupleIndex B degree
local notation "ShortTuple" => PrincipalAxisTuples (α := Empty) short sides
local notation "law" => principalTupleWeights (α := Empty) B degree sides hSides

theorem allocatedPrincipalResidue_mixture_active_uniform
    (q : ℕ) [NeZero q]
    (f : (FullInput → Option Empty → ZMod q) → ShortTuple → ℂ)
    (hf : ∀ r u, ‖f r u‖ ≤ 1) :
    ‖(∑ r : {r : FullInput → Option Empty → ZMod q //
        0 < (law).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r))},
      ((law).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r.val)) : ℂ) *
        (allocatedShortPrincipalResidueLaw B U basis S q r.val r.property).complexMean (f r.val)) -
      (allocatedUnconditionalShortPrincipalLaw B U basis S).complexMean (fun u =>
        (FiniteProbabilityWeights.uniform (AI → ZMod q)).complexMean (fun r =>
          f (allocatedPrincipalResidueJoin B U basis S q u r) u))‖ ≤
      4 * Fintype.card AI * ((q : ℝ) / S.value) := by
  rw [allocatedPrincipalResidue_mixture_partition B U basis S q f]
  apply ((allocatedUnconditionalShortPrincipalLaw B U basis S).norm_complexMean_sub_le
    _ _ (fun _ => 4 * Fintype.card AI * ((q : ℝ) / S.value)) ?_).trans_eq
      ((allocatedUnconditionalShortPrincipalLaw B U basis S).mean_const _)
  intro u _
  have h := allocatedActive_affine_residue_comparison B U basis S q (fun _ => 0)
    (fun _ => 1) (fun r => allocatedPrincipalResidueJoin B U basis S q u r)
    (fun r => f r u) (fun r => hf r u)
  simpa only [zero_add, one_mul, Int.cast_zero, Int.cast_one,
    allocatedUnconditionalActivePrincipalLaw] using h

variable {X Zsp : Type*} [Fintype X] [Fintype Zsp] [DecidableEq Zsp]
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "Domain" => (((Σ _ : X, Unit ⊕ Empty) → ℝ) × ((Σ _a : Active, Unit) → ℝ))

theorem allocatedOriginalSampleForecastSource_active_uniform
    (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)
    (lower width : ∀ a : Active, B a.val × Fin (degree a.val) → ℝ)
    (sample : Sample) (q : ℕ) [NeZero q]
    (φ : (FullInput → Option Empty → ZMod q) → ShortTuple → Domain → ℂ)
    (hφ : ∀ r u y, ‖φ r u y‖ ≤ 1) :
    let μ := allocatedOriginalSampleForecastSource (X := X) (W := W) (L := L)
      B U basis S s root D lower width sample
    ‖(∑ r : {r : FullInput → Option Empty → ZMod q //
        0 < (law).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r))},
      ((law).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r.val)) : ℂ) *
        (allocatedShortPrincipalResidueLaw B U basis S q r.val r.property).complexMean
          (fun u => ∫ y, φ r.val u y ∂μ)) -
      (allocatedUnconditionalShortPrincipalLaw B U basis S).complexMean (fun u =>
        (FiniteProbabilityWeights.uniform (AI → ZMod q)).complexMean (fun r =>
          ∫ y, φ (allocatedPrincipalResidueJoin B U basis S q u r) u y ∂μ))‖ ≤
      4 * Fintype.card AI * ((q : ℝ) / S.value) := by
  intro μ
  let : IsProbabilityMeasure μ := allocatedOriginalSampleForecastSource_probability
    B U basis S lower width s root D hp hW hL sample
  have hb (r : FullInput → Option Empty → ZMod q) (u : ShortTuple) :
      ‖∫ y, φ r u y ∂μ‖ ≤ 1 := by
    simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const
      (μ := μ) (Filter.Eventually.of_forall (fun y => hφ r u y))
  exact allocatedPrincipalResidue_mixture_active_uniform B U basis S q
    (fun r u => ∫ y, φ r u y ∂μ) hb

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "degree" => layerSamplerDegree I n
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "hSides" => allocatedPrincipalSides_pos B U basis S
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "activeB" => (fun a : Active => B (Subtype.val a))
local notation "activeDegree" => (fun a : Active => degree (Subtype.val a))
local notation "ActiveInput" => PrincipalTupleIndex activeB activeDegree
local notation "activeLength" => principalAxisLength (fun a => ¬short a) sides
local notation "activePos" => (fun j : ActiveInput => hSides (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))
local notation "ShortTuple" => PrincipalAxisTuples (α := Empty) short sides

private theorem scalarIntegerMean_congr
    (L₁ L₂ : ℕ) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (he : L₁ = L₂) (f : ℤ → ℂ) :
    (integerScalarCubeWeights Empty L₁ hL₁).complexMean (fun z => f (z none : ℤ)) =
      (integerScalarCubeWeights Empty L₂ hL₂).complexMean (fun z => f (z none : ℤ)) := by
  subst L₂
  rfl

theorem allocatedUnconditionalActivePrincipalLaw_integer_mean
    (f : (ActiveInput → ℤ) → ℂ) :
    (allocatedUnconditionalActivePrincipalLaw B U basis S).complexMean
        (fun y => f (fun j => (y j none : ℤ))) =
      (FiniteProbabilityWeights.pi
        (fun _ : ActiveInput => integerScalarCubeWeights Empty S.value S.positive)).complexMean
          (fun y => f (fun j => (y j none : ℤ))) := by
  exact FiniteProbabilityWeights.complexMean_pi_transport_fintype
    (fun j => integerScalarCubeWeights Empty (activeLength j) (activePos j))
    (fun _ : ActiveInput => integerScalarCubeWeights Empty S.value S.positive)
    (fun _ z => (z none : ℤ)) (fun _ z => (z none : ℤ))
    (fun j g => scalarIntegerMean_congr (activeLength j) S.value (activePos j)
      S.positive (allocatedActivePrincipalResidue_length B U basis S j) g) f

theorem allocatedPrincipal_integer_partition
    (f : ShortTuple → (ActiveInput → ℤ) → ℂ) :
    (principalTupleWeights (α := Empty) B degree sides hSides).complexMean
        (fun y => f (principalAxisRestrict short y)
          (fun j => ((principalAxisRestrict (fun a => ¬short a) y) j none : ℤ))) =
      (allocatedUnconditionalShortPrincipalLaw B U basis S).complexMean (fun u =>
        (FiniteProbabilityWeights.pi
          (fun _ : ActiveInput => integerScalarCubeWeights Empty S.value S.positive)).complexMean
            (fun v => f u (fun j => (v j none : ℤ)))) := by
  rw [principalTupleWeights_partition short sides hSides]
  simp only [principalAxisRestrict_join_left, principalAxisRestrict_join_right]
  change (allocatedUnconditionalShortPrincipalLaw B U basis S).complexMean
    (fun u => (allocatedUnconditionalActivePrincipalLaw B U basis S).complexMean
      (fun v => f u (fun j => (v j none : ℤ)))) = _
  congr 1
  funext u
  exact allocatedUnconditionalActivePrincipalLaw_integer_mean B U basis S (f u)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [DecidableEq G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)
local notation "Domain" => (Spatial × (Output → ℝ))
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "ShortTuple" => PrincipalAxisTuples (α := Empty) short sides

variable (lower width : ∀ a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

theorem allocatedJointLongForecast_residue_decoupling
    (s : Empty ↪ G) (sample : Sample)
    (q : ℕ) [NeZero q] (hsize : q ≤ S.value)
    (hsmall : scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / S.value) < 1)
    (φ : (G → ZMod q) → (Input → ZMod q) → ShortTuple → Domain → ℂ) {K : ℝ≥0}
    (hφ : ∀ rG rA u, LipschitzWith K (φ rG rA u))
    (hbound : ∀ rG rA u y, ‖φ rG rA u y‖ ≤ 1) :
    let kernel := FiniteProbabilityWeights.pi (fun _ : G => integerScalarCubeWeights Empty S.value S.positive)
    let shortLaw := allocatedUnconditionalShortPrincipalLaw B U basis S
    let activeResidues := FiniteProbabilityWeights.uniform (Input → ZMod q)
    let kernelResidues := FiniteProbabilityWeights.uniform (G → ZMod q)
    ‖kernel.complexMean (fun x => shortLaw.complexMean (fun u => activeResidues.complexMean (fun rA =>
        ∫ y, φ (fun g => ((x g none : ℤ) : ZMod q)) rA u y
          ∂allocatedOriginalSampleForecastSource (X := X) (W := budget) (L := (S.value : ℝ))
            B U basis S s (fun g => (x g none : ℤ)) (scalarCubeDifferenceMatrix x)
            lower width sample))) -
      shortLaw.complexMean (fun u => activeResidues.complexMean (fun rA =>
        kernelResidues.complexMean (fun rG => kernel.complexMean (fun x =>
          ∫ y, φ rG rA u y
            ∂allocatedOriginalSampleForecastSource (X := X) (W := budget) (L := (S.value : ℝ))
              B U basis S s (fun g => (x g none : ℤ)) (scalarCubeDifferenceMatrix x)
              lower width sample))))‖ ≤
      2 * ((1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + K)) *
        (Fintype.card G * ((q : ℝ) / S.value))) := by
  classical
  intro kernel shortLaw activeResidues kernelResidues
  let E : ℝ := 2 * ((1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + K)) *
    (Fintype.card G * ((q : ℝ) / S.value)))
  let value := fun (x : G → IntegerScalarCubeBox Empty S.value) rG rA (u : ShortTuple) =>
    ∫ y, φ rG rA u y
      ∂allocatedOriginalSampleForecastSource (X := X) (W := budget) (L := (S.value : ℝ))
        B U basis S s (fun g => (x g none : ℤ)) (scalarCubeDifferenceMatrix x)
        lower width sample
  have hpoint (u : ShortTuple) (rA : Input → ZMod q) :
      ‖kernel.complexMean (fun x => value x (fun g => ((x g none : ℤ) : ZMod q)) rA u) -
        kernelResidues.complexMean (fun rG => kernel.complexMean (fun x => value x rG rA u))‖ ≤ E := by
    simpa only [kernelResidues, FiniteProbabilityWeights.uniform_complexMean] using
      allocatedKernel_forecastSource_residue_decoupling B U basis S lower width s sample
        q hsize hsmall (fun rG => φ rG rA u) (fun rG => hφ rG rA u) (fun rG => hbound rG rA u)
  have hcomm :
      kernel.complexMean (fun x => shortLaw.complexMean (fun u => activeResidues.complexMean
        (fun rA => value x (fun g => ((x g none : ℤ) : ZMod q)) rA u))) =
        shortLaw.complexMean (fun u => activeResidues.complexMean (fun rA => kernel.complexMean
          (fun x => value x (fun g => ((x g none : ℤ) : ZMod q)) rA u))) := by
    rw [FiniteProbabilityWeights.complexMean_commute kernel shortLaw]
    congr 1
    funext u
    exact FiniteProbabilityWeights.complexMean_commute kernel activeResidues _
  rw [hcomm]
  apply (shortLaw.norm_complexMean_sub_le _ _ (fun _ => E) ?_).trans_eq (shortLaw.mean_const E)
  intro u _
  exact (activeResidues.norm_complexMean_sub_le _ _ (fun _ => E)
    (fun rA _ => hpoint u rA)).trans_eq (activeResidues.mean_const E)

theorem allocatedJointLongForecast_weighted_residue_decoupling
    (s : Empty ↪ G) (sample : Sample)
    (q : ℕ) [NeZero q] (hsize : q ≤ S.value)
    (hsmall : scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / S.value) < 1)
    (coefficient : (G → ZMod q) → (Input → ZMod q) → ShortTuple → ℂ)
    (hcoefficient : ∀ rG rA u, ‖coefficient rG rA u‖ ≤ 1)
    (φ : (G → ZMod q) → (Input → ZMod q) → ShortTuple → Domain → ℂ) {K : ℝ≥0}
    (hφ : ∀ rG rA u, LipschitzWith K (φ rG rA u))
    (hbound : ∀ rG rA u y, ‖φ rG rA u y‖ ≤ 1) :
    let kernel := FiniteProbabilityWeights.pi (fun _ : G => integerScalarCubeWeights Empty S.value S.positive)
    let shortLaw := allocatedUnconditionalShortPrincipalLaw B U basis S
    let activeResidues := FiniteProbabilityWeights.uniform (Input → ZMod q)
    let kernelResidues := FiniteProbabilityWeights.uniform (G → ZMod q)
    ‖kernel.complexMean (fun x => shortLaw.complexMean (fun u => activeResidues.complexMean (fun rA =>
        coefficient (fun g => ((x g none : ℤ) : ZMod q)) rA u *
        ∫ y, φ (fun g => ((x g none : ℤ) : ZMod q)) rA u y
          ∂allocatedOriginalSampleForecastSource (X := X) (W := budget) (L := (S.value : ℝ))
            B U basis S s (fun g => (x g none : ℤ)) (scalarCubeDifferenceMatrix x)
            lower width sample))) -
      shortLaw.complexMean (fun u => activeResidues.complexMean (fun rA =>
        kernelResidues.complexMean (fun rG => kernel.complexMean (fun x =>
          coefficient rG rA u * ∫ y, φ rG rA u y
            ∂allocatedOriginalSampleForecastSource (X := X) (W := budget) (L := (S.value : ℝ))
              B U basis S s (fun g => (x g none : ℤ)) (scalarCubeDifferenceMatrix x)
              lower width sample))))‖ ≤
      2 * ((1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + K)) *
        (Fintype.card G * ((q : ℝ) / S.value))) := by
  have hmul (rG : G → ZMod q) (rA : Input → ZMod q) (u : ShortTuple) :
      LipschitzWith K (fun y => coefficient rG rA u * φ rG rA u y) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    rw [dist_eq_norm, ← mul_sub, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hcoefficient rG rA u)).trans
      (by simpa only [dist_eq_norm] using (hφ rG rA u).dist_le_mul y z)
  have hb (rG : G → ZMod q) (rA : Input → ZMod q) (u : ShortTuple) (y : Domain) :
      ‖coefficient rG rA u * φ rG rA u y‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hcoefficient rG rA u)).trans
      (hbound rG rA u y)
  simpa only [integral_const_mul] using
    allocatedJointLongForecast_residue_decoupling B U basis S lower width s sample q hsize hsmall
      (fun rG rA u y => coefficient rG rA u * φ rG rA u y) hmul hb

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X Zsp : Type*} [Fintype G] [Fintype X] [Fintype Zsp] [DecidableEq Zsp]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "activeB" => (fun a : Active => B (Subtype.val a))
local notation "activeDegree" => (fun a : Active => degree (Subtype.val a))
local notation "Input" => PrincipalTupleIndex activeB activeDegree
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

local notation "sides" => allocatedPrincipalSides B U basis S
local notation "hSides" => allocatedPrincipalSides_pos B U basis S
local notation "ShortTuple" => PrincipalAxisTuples (α := Empty) short sides
local notation "FullInput" => PrincipalTupleIndex B degree
local notation "Original" => PrincipalIntegerTuples B degree Empty sides
local notation "Domain" => (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (Output → ℝ))

theorem allocatedOriginalSample_residue_mixture_forecast_comparison
    (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)
    (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (hroot : ∀ j, |(root j : ℝ)| ≤ 1 + W)
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hS : 2 ≤ S.value)
    (q : ℕ) [NeZero q] (hsize : q ≤ S.value)
    (hsmall : scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / S.value) < 1)
    (coefficient : (FullInput → Option Empty → ZMod q) → ℂ)
    (hcoefficient : ∀ r, ‖coefficient r‖ ≤ 1)
    (φ : (FullInput → Option Empty → ZMod q) → ShortTuple → Domain → ℂ)
    {Kφ : ℝ≥0} (hφ : ∀ r u, LipschitzWith Kφ (φ r u))
    (hφone : ∀ r u y, ‖φ r u y‖ ≤ 1) :
    let lower := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) => (0 : ℝ)
    let width := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) =>
      ((S.value : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleLiftLip B U basis S
    let law := principalTupleWeights (α := Empty) B degree sides hSides
    let Pos := {r : FullInput → Option Empty → ZMod q //
      0 < law.mass (Finset.univ.filter (fun y => principalResidueLabel q y = r))}
    ‖(∫ z, law.complexMean (fun v => coefficient (principalResidueLabel q v) *
          φ (principalResidueLabel q v) (principalAxisRestrict short v)
          (z, allocatedOriginalSampleLiftMap B U basis S (fun _ _ => 0) (fun _ _ => 1)
            sample (fun j => (((principalAxisRestrict (fun a => ¬short a) v) j none : ℤ) : ℝ) / S.value)))
          ∂canonicalZeroSpatialLaw (X := X) s root D W L) -
      ∑ r : Pos, (law.mass (Finset.univ.filter (fun y => principalResidueLabel q y = r.val)) : ℂ) *
        coefficient r.val * (allocatedShortPrincipalResidueLaw B U basis S q r.val r.property).complexMean
          (fun u => ∫ y, φ r.val u y ∂realDensityMeasure volume (allocatedOriginalSampleForecastDensity (X := X)
            B U basis S s root D hp hW hL hB lower width sample))‖ ≤
      2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ _j : Input, (q : ℝ) / S.value + K * (1 / S.value)) := by
  classical
  intro lower width K law Pos
  let μ := canonicalZeroSpatialLaw (X := X) s root D W L
  let := canonicalZeroSpatialLaw_probability (X := X) s root D hp hW hL
  let F := allocatedOriginalSampleLiftMap B U basis S (fun _ _ => 0) (fun _ _ => 1) sample
  let value := fun (z : (Σ _ : X, Unit ⊕ Empty) → ℝ) (r : FullInput → Option Empty → ZMod q)
    (v : Original) => φ r (principalAxisRestrict short v)
      (z, F (fun j => (((principalAxisRestrict (fun a => ¬short a) v) j none : ℤ) : ℝ) / S.value))
  have hint (r : FullInput → Option Empty → ZMod q) (v : Original) :
      Integrable (fun z => value z r v) μ := by
    have hm : Measurable (fun z => value z r v) :=
      (hφ r (principalAxisRestrict short v)).continuous.measurable.comp
        (measurable_id.prodMk measurable_const)
    exact ⟨hm.aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall (fun z => hφone r _ _))⟩
  have hmean := law.integral_complexMean μ
    (fun z v => coefficient (principalResidueLabel q v) * value z (principalResidueLabel q v) v)
    (fun v => (hint (principalResidueLabel q v) v).const_mul _)
  simp only [integral_const_mul] at hmean
  rw [hmean]
  have hnonneg : 0 ≤ 2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
      ∑ _j : Input, (q : ℝ) / S.value + K * (1 / S.value)) := by
    have hC := (scalarCubeGridBoundaryConstant_pos Empty).le
    positivity
  apply law.complexMean_positiveResidue_weighted_error (principalResidueLabel q)
    coefficient (fun r v => ∫ z, value z r v ∂μ) _ hnonneg (fun r => hcoefficient r.val)
  intro r
  rw [← (law.condition (Finset.univ.filter (fun y => principalResidueLabel q y = r.val))
    r.property).integral_complexMean μ (fun z v => value z r.val v) (hint r.val)]
  exact allocatedOriginalSample_conditional_forecast_comparison
    B U basis hR hσ S s root D hp hW hL hB hroot sample hs hS q (NeZero.pos q)
    r.val r.property hsize hsmall (φ r.val) (hφ r.val) (hφone r.val)

end Erdos3.VectorPolynomial

end

end OAI
