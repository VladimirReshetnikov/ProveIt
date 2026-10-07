import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import OAI.Combinatorics.Progressions.Estimates.ContinuousImageFactor
import OAI.Combinatorics.Progressions.Geometry.IndependentProductTransport
import OAI.Combinatorics.Progressions.Lattices.CoverBasisResidues
import OAI.Combinatorics.Progressions.Probability.SlicedRemainderDensityFamily

namespace OAI

section

namespace Erdos3

open MeasureTheory Topology
open scoped BigOperators

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]
variable (C : G →+ H) [Fintype C.ker]

noncomputable def finiteFiberAverage (f : G → ℝ) (x : G) : ℝ :=
  (Fintype.card C.ker : ℝ)⁻¹ * ∑ k : C.ker, f (x + k.val)

theorem finiteFiberAverage_eq_of_map_eq (f : G → ℝ) {x y : G} (hxy : C x = C y) :
    finiteFiberAverage C f x = finiteFiberAverage C f y := by
  classical
  have hk : x - y ∈ C.ker := by
    change C (x - y) = 0
    rw [map_sub, hxy, sub_self]
  unfold finiteFiberAverage
  congr 1
  apply Fintype.sum_equiv (Equiv.addLeft (⟨x - y, hk⟩ : C.ker))
  intro k
  congr 1
  change x + k.val = y + (x - y + k.val)
  abel

theorem finiteFiberAverage_integral_uniform
    [MeasurableSpace C.ker] [MeasurableSingletonClass C.ker] (f : G → ℝ) (x : G) :
    (∫ k : C.ker, f (x + k.val) ∂(PMF.uniformOfFintype C.ker).toMeasure) =
      finiteFiberAverage C f x := by
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, ← Finset.mul_sum, finiteFiberAverage]

variable [TopologicalSpace G] [IsTopologicalAddGroup G]

theorem finiteFiberAverage_continuous {f : G → ℝ} (hf : Continuous f) :
    Continuous (finiteFiberAverage C f) := by
  apply continuous_const.mul
  apply continuous_finsetSum
  intro k _
  exact hf.comp (continuous_id.add continuous_const)

omit [TopologicalSpace G] [IsTopologicalAddGroup G] in
theorem finiteFiberAverage_norm_le (f : G → ℝ) {B : ℝ} (hf : ∀ x, ‖f x‖ ≤ B) (x : G) :
    ‖finiteFiberAverage C f x‖ ≤ B := by
  have hn : (0 : ℝ) < Fintype.card C.ker := by exact_mod_cast Fintype.card_pos
  rw [finiteFiberAverage, norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le)]
  calc
    _ ≤ (Fintype.card C.ker : ℝ)⁻¹ * ∑ _k : C.ker, B :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => hf _)))
        (inv_nonneg.mpr hn.le)
    _ = B := by simp [hn.ne']

theorem finiteFiberAverage_factor [CompactSpace G] [TopologicalSpace H] [T2Space H]
    (hC : Continuous C) (hCs : Function.Surjective C) {f : G → ℝ} (hf : Continuous f) :
    ∃ g : H → ℝ, Continuous g ∧ ∀ x, g (C x) = finiteFiberAverage C f x := by
  let e : ContinuousMap G H := ⟨C, hC⟩
  have hq : IsQuotientMap e := IsQuotientMap.of_surjective_continuous hCs hC
  let a : ContinuousMap G ℝ := ⟨finiteFiberAverage C f, finiteFiberAverage_continuous C hf⟩
  have hfac : Function.FactorsThrough a e :=
    fun _ _ hxy => finiteFiberAverage_eq_of_map_eq C f hxy
  let g := hq.lift a hfac
  refine ⟨g, g.continuous, ?_⟩
  intro x
  exact DFunLike.congr_fun (hq.lift_comp a hfac) x

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {G H X : Type*} [AddCommGroup G] [AddCommGroup H]
variable [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G]
variable (C : G →+ H) [Fintype C.ker]

theorem finiteFiberAverage_integral_of_invariant
    (μ : Measure G) [IsFiniteMeasure μ]
    (hμ : ∀ k : C.ker, μ.map (fun x => x + k.val) = μ)
    (f : G → ℝ) (hf : Continuous f) {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) :
    (∫ x, finiteFiberAverage C f x ∂μ) = ∫ x, f x ∂μ := by
  have hi (k : C.ker) : Integrable (fun x => f (x + k.val)) μ :=
    Integrable.of_bound (hf.comp (continuous_id.add continuous_const)).aestronglyMeasurable
      B (ae_of_all μ (fun x => hB _))
  have he (k : C.ker) : (∫ x, f (x + k.val) ∂μ) = ∫ x, f x ∂μ := by
    have hm : Measurable (fun x : G => x + k.val) :=
      (continuous_id.add continuous_const).measurable
    have h := integral_map hm.aemeasurable
      (hf.aestronglyMeasurable (μ := μ.map (fun x => x + k.val)))
    rw [hμ k] at h
    exact h.symm
  unfold finiteFiberAverage
  rw [integral_const_mul, integral_finsetSum _ (fun k _ => hi k)]
  simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn : (Fintype.card C.ker : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

variable [T2Space G] [MeasurableSpace X] [MeasurableAdd₂ G]

noncomputable def finiteKernelLiftLaw (ρ : Measure X) (s : X → G) : Measure G :=
  (ρ.prod (PMF.uniformOfFintype C.ker).toMeasure).map (fun p => s p.1 + p.2.val)

omit [IsTopologicalAddGroup G] in
theorem finiteKernelLiftLaw_integral (ρ : Measure X) [IsFiniteMeasure ρ]
    (s : X → G) (hs : Measurable s) (f : G → ℝ) (hf : Measurable f)
    {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) :
    (∫ y, f y ∂finiteKernelLiftLaw C ρ s) = ∫ x, finiteFiberAverage C f (s x) ∂ρ := by
  have hL : Measurable (fun p : X × C.ker => s p.1 + p.2.val) :=
    (hs.comp measurable_fst).add (measurable_subtype_coe.comp measurable_snd)
  have hi : Integrable (fun p : X × C.ker => f (s p.1 + p.2.val))
      (ρ.prod (PMF.uniformOfFintype C.ker).toMeasure) :=
    Integrable.of_bound (hf.comp hL).aestronglyMeasurable B (ae_of_all _ (fun p => hB _))
  rw [finiteKernelLiftLaw, integral_map hL.aemeasurable hf.aestronglyMeasurable,
    integral_prod _ hi]
  exact integral_congr_ae (ae_of_all ρ (fun x => finiteFiberAverage_integral_uniform C f (s x)))

theorem finiteKernelLiftLaw_eq [CompactSpace G] [HasOuterApproxClosed G]
    [TopologicalSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (hC : Continuous C) (hCs : Function.Surjective C)
    (μ : Measure G) [IsFiniteMeasure μ]
    (hμ : ∀ k : C.ker, μ.map (fun x => x + k.val) = μ)
    (ρ : Measure X) [IsFiniteMeasure ρ] (s : X → G) (hs : Measurable s)
    (hbase : ρ.map (C ∘ s) = μ.map C) :
    finiteKernelLiftLaw C ρ s = μ := by
  let _ : IsFiniteMeasure (finiteKernelLiftLaw C ρ s) := by
    unfold finiteKernelLiftLaw
    infer_instance
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro φ
  obtain ⟨g, hgc, hg⟩ := finiteFiberAverage_factor C hC hCs φ.continuous
  calc
    (∫ y, φ y ∂finiteKernelLiftLaw C ρ s) =
        ∫ x, finiteFiberAverage C φ (s x) ∂ρ :=
      finiteKernelLiftLaw_integral C ρ s hs φ φ.continuous.measurable φ.norm_coe_le_norm
    _ = ∫ x, g (C (s x)) ∂ρ := by simp_rw [hg]
    _ = ∫ y, g y ∂ρ.map (C ∘ s) :=
      (integral_map (hC.measurable.comp hs).aemeasurable hgc.aestronglyMeasurable).symm
    _ = ∫ y, g y ∂μ.map C := by rw [hbase]
    _ = ∫ x, g (C x) ∂μ := integral_map hC.measurable.aemeasurable hgc.aestronglyMeasurable
    _ = ∫ x, finiteFiberAverage C φ x ∂μ := by simp_rw [hg]
    _ = ∫ x, φ x ∂μ :=
      finiteFiberAverage_integral_of_invariant C μ hμ φ φ.continuous φ.norm_coe_le_norm

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Classical

theorem uniformPMF_map_equiv {R S : Type*} [Fintype R] [Fintype S]
    [Nonempty R] [Nonempty S] (e : R ≃ S) :
    (PMF.uniformOfFintype R).map e = PMF.uniformOfFintype S := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [pmf_map_injective_at _ e e.injective, PMF.uniformOfFintype_apply,
    PMF.uniformOfFintype_apply, Fintype.card_congr e]

theorem finiteKernelLiftLaw_relabel {G H X R : Type*}
    [AddCommGroup G] [AddCommGroup H]
    [TopologicalSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableAdd₂ G] [MeasurableSpace X]
    (C : G →+ H) [Fintype C.ker] [Fintype R] [Nonempty R]
    [MeasurableSpace R] [MeasurableSingletonClass R]
    (e : R ≃ C.ker) (ρ : Measure X) [SFinite ρ]
    (s : X → G) (hs : Measurable s) :
    (ρ.prod (PMF.uniformOfFintype R).toMeasure).map
        (fun p => s p.1 + (e p.2).val) = finiteKernelLiftLaw C ρ s := by
  have he : Measurable e := measurable_of_finite _
  have hm : (PMF.uniformOfFintype R).toMeasure.map e =
      (PMF.uniformOfFintype C.ker).toMeasure := by
    rw [PMF.toMeasure_map e _ he, uniformPMF_map_equiv]
  have hp : ρ.prod (PMF.uniformOfFintype C.ker).toMeasure =
      (ρ.prod (PMF.uniformOfFintype R).toMeasure).map (Prod.map id e) := by
    rw [← hm, ← Measure.map_prod_map _ _ measurable_id he, Measure.map_id]
  rw [finiteKernelLiftLaw, hp, Measure.map_map]
  · rfl
  · exact (hs.comp measurable_fst).add (measurable_subtype_coe.comp measurable_snd)
  · exact measurable_id.prodMap he

theorem finiteKernelLiftLaw_basisResidues {E I X : Type*}
    [AddCommGroup E] [Module ℝ E] [Fintype I]
    (Γ : AddSubgroup E) (b : Module.Basis I ℤ Γ)
    [TopologicalSpace (E ⧸ Γ)] [T2Space (E ⧸ Γ)]
    [MeasurableSpace (E ⧸ Γ)] [BorelSpace (E ⧸ Γ)] [MeasurableAdd₂ (E ⧸ Γ)]
    [MeasurableSpace X] (d : ℕ) [NeZero d]
    [Fintype (quotientIntegerCover Γ d).ker]
    (ρ : Measure X) [SFinite ρ] (s : X → E ⧸ Γ) (hs : Measurable s) :
    (ρ.prod (PMF.uniformOfFintype (I → ZMod d)).toMeasure).map
        (fun p => s p.1 + (coverKernelBasisEquiv Γ b d (Nat.pos_of_ne_zero (NeZero.ne d)) p.2).val) =
      finiteKernelLiftLaw (quotientIntegerCover Γ d) ρ s :=
  finiteKernelLiftLaw_relabel _ (coverKernelBasisEquiv Γ b d _).toEquiv ρ s hs

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {G H X : Type*} [AddCommGroup G] [AddCommGroup H]
variable [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G]
variable [T2Space G] [CompactSpace G] [HasOuterApproxClosed G]
variable [MeasurableAdd₂ G]
variable [TopologicalSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
variable [MeasurableSpace X] (C : G →+ H) [Fintype C.ker]

theorem finiteKernelLift_density (hC : Continuous C) (hCs : Function.Surjective C)
    (μ : Measure G) [μ.IsAddLeftInvariant] (ν : Measure H)
    (hmp : MeasurePreserving C μ ν)
    (D : H → ℝ) (hD : Measurable D) (hi : Integrable D ν) (h0 : ∀ y, 0 ≤ D y)
    (ρ : Measure X) [IsFiniteMeasure ρ] (s : X → G) (hs : Measurable s)
    (hbase : ρ.map (C ∘ s) = realDensityMeasure ν D) :
    finiteKernelLiftLaw C ρ s = realDensityMeasure μ (fun x => D (C x)) := by
  have hci : Integrable (fun x => D (C x)) μ := hmp.integrable_comp_of_integrable hi
  let _ := realDensityMeasure_finite μ (fun x => D (C x)) hci (fun x => h0 _)
  refine finiteKernelLiftLaw_eq C hC hCs (realDensityMeasure μ (fun x => D (C x)))
    ?_ ρ s hs ?_
  · intro k
    rw [realDensityMeasure_map_add_right]
    congr 1
    funext x
    rw [map_sub, show C k.val = 0 from k.property, sub_zero]
  · rw [measurePreserving_realDensity_map μ ν C hmp D hD hi h0]
    exact hbase

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ENNReal

theorem realDensityMeasure_indicator_one {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {S : Set X} (hS : MeasurableSet S) :
    realDensityMeasure μ (S.indicator (fun _ => (1 : ℝ))) = μ.restrict S := by
  have he : (fun x => ENNReal.ofReal (S.indicator (fun _ => (1 : ℝ)) x)) =
      S.indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext x
    by_cases hx : x ∈ S <;> simp [hx]
  rw [realDensityMeasure, he]
  exact withDensity_indicator_one hS

theorem finiteKernelLift_restrict {G H X : Type*}
    [AddCommGroup G] [AddCommGroup H]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G]
    [T2Space G] [CompactSpace G] [HasOuterApproxClosed G] [MeasurableAdd₂ G]
    [TopologicalSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace X] (C : G →+ H) [Fintype C.ker]
    (hC : Continuous C) (hCs : Function.Surjective C)
    (μ : Measure G) [μ.IsAddLeftInvariant] (ν : Measure H) [IsFiniteMeasure ν]
    (hmp : MeasurePreserving C μ ν) {S : Set H} (hS : MeasurableSet S)
    (ρ : Measure X) [IsFiniteMeasure ρ] (s : X → G) (hs : Measurable s)
    (hbase : ρ.map (C ∘ s) = ν.restrict S) :
    finiteKernelLiftLaw C ρ s = μ.restrict (C ⁻¹' S) := by
  have hb : ρ.map (C ∘ s) = realDensityMeasure ν (S.indicator (fun _ => (1 : ℝ))) := by
    rw [realDensityMeasure_indicator_one ν hS]
    exact hbase
  have he : (fun x => S.indicator (fun _ => (1 : ℝ)) (C x)) =
      (C ⁻¹' S).indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : C x ∈ S <;> simp [hx]
  rw [finiteKernelLift_density C hC hCs μ ν hmp _ (measurable_const.indicator hS)
    ((integrable_const (1 : ℝ)).indicator hS)
    (fun x => by by_cases hx : x ∈ S <;> simp [hx]) ρ s hs hb,
    he, realDensityMeasure_indicator_one μ (hS.preimage hC.measurable)]

end Erdos3

end

end OAI
