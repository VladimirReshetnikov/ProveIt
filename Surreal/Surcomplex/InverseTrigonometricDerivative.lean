import Surreal.Surcomplex.InverseTrigonometry
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# Fine derivatives of inverse trigonometry on the full surreal domains

The order isomorphisms of the actual intervals provide native fine continuity.
The topological-field inverse rule then proves all three derivatives in
`trigonometry:eq:inversederivatives`, including infinite tangent inputs and
infinitesimal distances from the sine and cosine endpoints.
-/

universe u

namespace Surreal.Surcomplex

open Foundations Filter Topology

noncomputable section

private def finiteClosedIntervalOrderIso (a b : ℝ) :
    {θ : SignSequence.FiniteElement.{u} //
      θ.val ∈ Set.Icc (SignSequence.ofReal a) (SignSequence.ofReal b)} ≃o
    Set.Icc (SignSequence.ofReal a : SignSequence.{u}) (SignSequence.ofReal b) where
  toFun θ := ⟨θ.val.val, θ.property⟩
  invFun x := ⟨ArchimedeanClass.FiniteElement.mk x.val
    (SignSequence.isFinite_of_mem_real_Icc x.property), x.property⟩
  left_inv _ := Subtype.ext (ArchimedeanClass.FiniteElement.ext rfl)
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

private def finiteOpenIntervalOrderIso (a b : ℝ) :
    {θ : SignSequence.FiniteElement.{u} //
      θ.val ∈ Set.Ioo (SignSequence.ofReal a) (SignSequence.ofReal b)} ≃o
    Set.Ioo (SignSequence.ofReal a : SignSequence.{u}) (SignSequence.ofReal b) where
  toFun θ := ⟨θ.val.val, θ.property⟩
  invFun x := ⟨ArchimedeanClass.FiniteElement.mk x.val
    (SignSequence.isFinite_of_mem_real_Icc ⟨x.property.1.le, x.property.2.le⟩), x.property⟩
  left_inv _ := Subtype.ext (ArchimedeanClass.FiniteElement.ext rfl)
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- The tangent inverse order isomorphism expressed in native surreal interval coordinates. -/
def arctanValueOrderIso : SignSequence.{u} ≃o
    Set.Ioo (SignSequence.ofReal (-(Real.pi / 2))) (SignSequence.ofReal (Real.pi / 2)) :=
  arctanOrderIso.trans (finiteOpenIntervalOrderIso _ _)

/-- The sine inverse order isomorphism expressed in native surreal interval coordinates. -/
def arcsinValueOrderIso : Set.Icc (-1 : SignSequence.{u}) 1 ≃o
    Set.Icc (SignSequence.ofReal (-(Real.pi / 2))) (SignSequence.ofReal (Real.pi / 2)) :=
  arcsinOrderIso.trans (finiteClosedIntervalOrderIso _ _)

/-- Inverse tangent as a function valued in the native surreal field. -/
def arctanFunction (x : SignSequence.{u}) : SignSequence.{u} := (arctan x).val

/-- Inverse sine as an ambient function; its intended domain is the closed unit interval. -/
def arcsinFunction (x : SignSequence.{u}) : SignSequence.{u} :=
  if hx : x ∈ Set.Icc (-1) 1 then (arcsin ⟨x, hx⟩).val else 0

/-- Inverse cosine as an ambient function; its intended domain is the closed unit interval. -/
def arccosFunction (x : SignSequence.{u}) : SignSequence.{u} :=
  SignSequence.ofReal (Real.pi / 2) - arcsinFunction x

@[simp] theorem arcsinFunction_eq (x : Set.Icc (-1 : SignSequence.{u}) 1) :
    arcsinFunction x.val = (arcsin x).val := dif_pos x.property

@[simp] theorem arccosFunction_eq (x : Set.Icc (-1 : SignSequence.{u}) 1) :
    arccosFunction x.val = (arccos x).val := by
  rw [arccosFunction, arcsinFunction_eq, arccos_eq_pi_div_two_sub_arcsin]
  rfl

/-- Inverse tangent is continuous in the actual fine topology, even at infinite inputs. -/
theorem continuous_arctanFunction : Continuous (arctanFunction : SignSequence.{u} → _) := by
  change Continuous (fun x => (arctanValueOrderIso x).val)
  exact continuous_subtype_val.comp arctanValueOrderIso.continuous

/-- The full closed-interval inverse sine is continuous in the induced fine topology. -/
theorem continuousOn_arcsinFunction :
    ContinuousOn (arcsinFunction : SignSequence.{u} → _) (Set.Icc (-1) 1) := by
  apply continuousOn_iff_continuous_restrict.mpr
  have h := continuous_subtype_val.comp arcsinValueOrderIso.continuous
  convert h using 1
  funext x
  exact arcsinFunction_eq x

/-- The ambient inverse sine is fine-continuous at each actual interior point. -/
theorem continuousAt_arcsinFunction (x : SignSequence.{u}) (hx : x ∈ Set.Ioo (-1) 1) :
    ContinuousAt arcsinFunction x :=
  (continuousOn_arcsinFunction x ⟨hx.1.le, hx.2.le⟩).continuousAt (Icc_mem_nhds hx.1 hx.2)

/-- Sine is a local right inverse for the ambient inverse-sine function. -/
theorem sinFunction_arcsinFunction (x : SignSequence.{u}) (hx : x ∈ Set.Icc (-1) 1) :
    sinFunction (arcsinFunction x) = x := by
  rw [show arcsinFunction x = (arcsin ⟨x, hx⟩).val from arcsinFunction_eq ⟨x, hx⟩,
    sinFunction_eq_finiteSin, finiteSin_arcsin]

/-- Tangent is a global right inverse for the ambient inverse tangent. -/
@[simp] theorem tanFunction_arctanFunction (x : SignSequence.{u}) :
    tanFunction (arctanFunction x) = x := by
  rw [arctanFunction, tanFunction_eq_finiteTan, finiteTan_arctan]

/-- The inverse-tangent derivative holds at every surreal slope, finite or infinite. -/
theorem fineHasDerivAt_arctanFunction (x : SignSequence.{u}) :
    FineHasDerivAt arctanFunction (1 / (1 + x ^ 2)) x := by
  have hc : cosFunction (arctanFunction x) ≠ 0 := by
    rw [arctanFunction, cosFunction_eq_finiteCos, finiteCos_arctan]
    exact one_div_ne_zero (SignSequence.sqrt_pos (by positivity)).ne'
  have h := fineHasDerivAt_tanFunction (arctanFunction x) (arctan x).property hc
  rw [tanFunction_arctanFunction] at h
  simpa only [one_div] using h.of_local_rightInverse (by positivity)
    continuous_arctanFunction.continuousAt (Filter.Eventually.of_forall tanFunction_arctanFunction)

/-- Inverse sine has the reciprocal-square-root fine derivative throughout its open domain. -/
theorem fineHasDerivAt_arcsinFunction (x : SignSequence.{u}) (hx : x ∈ Set.Ioo (-1) 1) :
    FineHasDerivAt arcsinFunction (1 / SignSequence.sqrt (1 - x ^ 2)) x := by
  have hxc : x ∈ Set.Icc (-1) 1 := ⟨hx.1.le, hx.2.le⟩
  have he : arcsinFunction x = (arcsin ⟨x, hxc⟩).val := arcsinFunction_eq ⟨x, hxc⟩
  have hf : SignSequence.IsFinite (arcsinFunction x) := he ▸ (arcsin ⟨x, hxc⟩).property
  have hd : cosFunction (arcsinFunction x) = SignSequence.sqrt (1 - x ^ 2) := by
    rw [he, cosFunction_eq_finiteCos, finiteCos_arcsin]
  have h := fineHasDerivAt_sinFunction (arcsinFunction x) hf
  rw [hd] at h
  have hn : SignSequence.sqrt (1 - x ^ 2) ≠ 0 :=
    (SignSequence.sqrt_pos (by nlinarith [hx.1, hx.2])).ne'
  have hright : ∀ᶠ y in 𝓝 x, sinFunction (arcsinFunction y) = y := by
    filter_upwards [Icc_mem_nhds hx.1 hx.2] with y hy
    exact sinFunction_arcsinFunction y hy
  simpa only [one_div] using
    h.of_local_rightInverse hn (continuousAt_arcsinFunction x hx) hright


/-- Inverse cosine has negative reciprocal-square-root derivative on the same full open domain. -/
theorem fineHasDerivAt_arccosFunction (x : SignSequence.{u}) (hx : x ∈ Set.Ioo (-1) 1) :
    FineHasDerivAt arccosFunction (-1 / SignSequence.sqrt (1 - x ^ 2)) x := by
  change FineHasDerivAt (fun y => SignSequence.ofReal (Real.pi / 2) - arcsinFunction y) _ x
  simpa only [zero_sub, neg_div] using
    (FineHasDerivAt.const (SignSequence.ofReal (Real.pi / 2)) x).sub
      (fineHasDerivAt_arcsinFunction x hx)

end
end Surreal.Surcomplex
