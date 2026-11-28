import Lib.Adelic.Adeles.AdditiveCharacter

/-!
# Principal ideles and a majorant on the complex torus

* `New.principalAdeleUnits`: the principal ideles, a discrete subgroup of the units of the adele
  ring.
* `New.integrable_prod_inv_one_add_log_sq`: `∏ x, (1 + (log |a x|) ^ 2)⁻¹` is integrable for Haar
  measure on `(ι → ℂ)ˣ`; it serves as a majorant at the infinite places.

Notions from other files:

* `New.CMType E`: E is a CM number field with, for each infinite place, a chosen complex embedding
  inducing it.
* `New.toAdele`: the diagonal embedding of E in its adeles, given at the infinite places by the
  chosen embeddings.
* `New.ratAdeles E`: the image of E under `New.toAdele`, a lattice in the adeles.
-/

namespace New

open MeasureTheory Measure Complex

variable (E : Type*) {ι : Type*} [Field E] [CMType E]

/-- The principal ideles: the image of E^× in the unit group of the adeles. -/
noncomputable def principalAdeleUnits : Subgroup (𝔸 E)ˣ :=
  (Units.map (toAdele (E := E)).toMonoidHom).range

/-- For a CM field E, the principal ideles, that is the image of E^× in the units of the adele ring,
form a discrete subgroup: they map into the discrete set `New.ratAdeles E`, the image of E in the
adeles. -/
instance : DiscreteTopology (principalAdeleUnits E) := by
  -- The principal ideles lie in the preimage of the discrete set of rational adeles.
  have h_rat : IsDiscrete (ratAdeles E : Set (𝔸 E)) :=
    ⟨isCovolOneLattice_ratAdeles.toDiscreteTopology⟩
  have h_subset :
      (principalAdeleUnits E : Set (𝔸 E)ˣ) ⊆ Units.val ⁻¹' (ratAdeles E : Set (𝔸 E)) := by
    simp [principalAdeleUnits, ratAdeles, Set.range_subset_iff]
  have h_discrete : IsDiscrete (Units.val ⁻¹' (ratAdeles E : Set (𝔸 E))) :=
    h_rat.preimage (by fun_prop) Units.val_injective
  exact (h_discrete.mono h_subset).to_subtype

@[simp]
lemma piUnits_val_apply_ne_zero (a : (ι → ℂ)ˣ) (x : ι) : a.val x ≠ 0 := (a.isUnit.apply x).ne_zero

/-- For a finite index type `ι`, the function `a ↦ ∏ x, (1 + (log |a x|) ^ 2)⁻¹` on the group
`(ι → ℂ)ˣ` is integrable for Haar measure. -/
lemma integrable_prod_inv_one_add_log_sq [Fintype ι] :
    Integrable (fun a : (ι → ℂ)ˣ ↦ ∏ x : ι, (1 + Real.log ‖a.val x‖ ^ 2)⁻¹) haar := by
  -- Push Haar measure forward along the map `L` sending `a` to `fun x ↦ log |a x|`. The image is
  -- translation invariant and finite on compact sets, hence a multiple of Lebesgue measure on
  -- `ι → ℝ`, for which `t ↦ ∏ x, (1 + t x ^ 2)⁻¹` is integrable.
  let L (a : (ι → ℂ)ˣ) (x : ι) : ℝ := Real.log ‖a.val x‖
  have h_unit (t : ι → ℝ) (θ : ι → Circle) :
      IsUnit fun x : ι ↦ exp (t x : ℝ) * (θ x : Circle) := by simp [Pi.isUnit_iff]
  -- polar coordinates: the unit with moduli `exp (t x)` and phases `θ x`
  let polar (t : ι → ℝ) (θ : ι → Circle) : (ι → ℂ)ˣ := (h_unit t θ).unit
  have hL : Measurable L := by
    refine measurable_pi_iff.2 fun x ↦ ?_
    have h_eval : Measurable fun a : (ι → ℂ)ˣ ↦ a.val x := .eval (by fun_prop)
    exact h_eval.norm.log
  have h_polar : Continuous polar.uncurry := by
    rw [Units.isOpenEmbedding_val.isInducing.continuous_iff]
    simp only [polar]
    fun_prop
  -- `L` turns multiplication by `polar t 1` into translation by `t`
  have h_conj (t : ι → ℝ) : Function.Semiconj L (polar t 1 * ·) (t + ·) := by
    simp [Function.Semiconj, funext_iff, L, polar, Real.log_mul]
  have h_inv : (haar.map L).IsAddLeftInvariant := by
    refine ⟨fun t ↦ ?_⟩
    have h_mul : MeasurePreserving (polar t 1 * ·) haar haar := measurePreserving_mul_left haar _
    have h_add : Measurable fun s : ι → ℝ ↦ t + s := by fun_prop
    exact ((hL.measurePreserving haar).of_semiconj h_mul (h_conj t) h_add).map_eq
  -- the preimage of a compact `K` lies in the image under `polar` of `K × (ι → Circle)`
  have h_fin : IsFiniteMeasureOnCompacts (haar.map L) := by
    refine ⟨fun K hK ↦ ?_⟩
    have h_sub : L ⁻¹' K ⊆ polar.uncurry '' K ×ˢ Set.univ := by
      intro a ha
      refine ⟨(L a, fun x ↦ Circle.exp (arg (a.val x))), ⟨ha, trivial⟩, ?_⟩
      ext x
      simp [polar, L, exp_log, ofReal_log]
    rw [map_apply hL hK.measurableSet]
    have h_compact : IsCompact (polar.uncurry '' K ×ˢ Set.univ) :=
      (hK.prod isCompact_univ).image h_polar
    exact (measure_mono h_sub).trans_lt h_compact.measure_lt_top
  have h_int : Integrable (fun t : ι → ℝ ↦ ∏ x : ι, (1 + t x ^ 2)⁻¹) (haar.map L) := by
    rw [(haar.map L).isAddLeftInvariant_eq_smul volume]
    have h_volume : Integrable (fun t : ι → ℝ ↦ ∏ x : ι, (1 + t x ^ 2)⁻¹) :=
      Integrable.fintype_prod fun _ ↦ integrable_inv_one_add_sq
    exact h_volume.smul_measure_nnreal
  exact h_int.comp_measurable hL

end New
