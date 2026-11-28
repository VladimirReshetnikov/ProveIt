import Lib.GaloisRep.Main.SelmerModules
import Lib.General.Algebra.BlockFittingBound

/-!
# Selmer modules with divisible coefficients

`O` is a discrete valuation ring and `New.Selmer.DivisibleQuot O` is the module `Frac(O) / O`. For a
matrix-valued function `ρ` on the Galois group `Gal(Ω/E)` of `Ω` over the number field `E`
(`EmbeddedNumberField E`) with entries in `O` and `a ≠ 0`, the Selmer module with coefficients in
`O / a` is identified with the `a`-torsion of the Selmer module with coefficients in `Frac(O) / O`,
so it is no longer than the latter.

## Main definitions and results

* `New.Selmer.comp_mem_selmerModule_iff`, `New.Selmer.selmerModuleMapOfInjective`: an injective map
  of coefficient modules preserves and reflects the Selmer conditions, and so maps Selmer modules
  injectively.
* `New.Selmer.length_torsionBy_selmerModule`: if the map identifies `O / a` with the `a`-torsion of
  the coefficients, the Selmer module with coefficients in `O / a` has the length of the `a`-torsion
  of the other.
* `New.Selmer.divisibleSelmerLength`, `New.Selmer.length_le_divisibleSelmerLength`: the length of
  the Selmer module with coefficients in `Frac(O) / O` (for `E` with `CMFieldWithRoot5040 E`), which
  bounds the lengths of those with coefficients in `O / a`.

Notions from other files:
* `New.selmerModule ρ S L B`: the locally constant cocycles for `ρ` with values in `B ^ n` that are
  unramified outside `S` and obey the linear relations `L`.

## Relation to the literature

Known. The comparison of Selmer groups with coefficients in `O / a` and in `Frac(O) / O` is
standard; here it is immediate, because cocycles are counted and not classes.
-/

noncomputable section

namespace New.Selmer

section SelmerLevels

open Module Submodule Ideal IsDiscreteValuationRing LinearMap

variable {O : Type} [CommRing O]
  {E n : Type} [Field E] [EmbeddedNumberField E] [Fintype n] [DecidableEq n]
  (ρ : Gal(Ω/E) → Matrix n n O) (S : Set (FinPlace E)) (L : Set (Gal(Ω/E) →₀ Matrix n n O))
  {B B' : Type} [AddCommGroup B] [Module O B] [AddCommGroup B'] [Module O B']

/-- An injective map `f` of coefficient modules preserves and reflects the Selmer conditions:
`f ∘ z` is in the Selmer module (the locally constant cocycles for `ρ` that are unramified outside
the set `S` of finite places and obey the relations `L`) if and only if `z` is. -/
lemma comp_mem_selmerModule_iff {f : B →ₗ[O] B'} (hf : Function.Injective f)
    {z : Gal(Ω/E) → n → B} :
    (fun (g : Gal(Ω/E)) (i : n) ↦ f (z g i)) ∈ selmerModule ρ S L B' ↔
      z ∈ selmerModule ρ S L B := by
  have h_obeying (R : Set (Gal(Ω/E) →₀ Matrix n n O)) :
      (fun (g : Gal(Ω/E)) (i : n) ↦ f (z g i)) ∈ obeying R B' ↔ z ∈ obeying R B := by
    simp only [comp_mem_obeying_iff, mem_obeying (c := z), map_eq_zero_iff f hf, funext_iff,
      Pi.zero_apply]
  have h_locallyConstant :
      IsLocallyConstant (fun (g : Gal(Ω/E)) (i : n) ↦ f (z g i)) ↔ IsLocallyConstant z :=
    ⟨fun h ↦ IsLocallyConstant.desc z (fun v : n → B ↦ f ∘ v) h hf.comp_left,
      fun h ↦ h.comp fun v : n → B ↦ f ∘ v⟩
  -- The Selmer module is cut out by a set of relations and by local constancy.
  simp only [selmerModule, Submodule.mem_inf]
  exact and_congr (h_obeying _) h_locallyConstant

/-- The map of Selmer modules `z ↦ f ∘ z` induced by an injective map `f` of coefficient
modules. -/
def selmerModuleMapOfInjective {f : B →ₗ[O] B'} (hf : Function.Injective f) :
    selmerModule ρ S L B →ₗ[O] selmerModule ρ S L B' :=
  ((f.compLeft n).compLeft Gal(Ω/E)).restrict fun (_ : Gal(Ω/E) → n → B) hz ↦
    (comp_mem_selmerModule_iff ρ S L hf).2 hz

/-- The value at `g` and `i` of the image of a Selmer cocycle `z` under the map induced by `f` is
`f (z g i)`. -/
lemma selmerModuleMapOfInjective_apply {f : B →ₗ[O] B'} (hf : Function.Injective f)
    (z : selmerModule ρ S L B) (g : Gal(Ω/E)) (i : n) :
    (selmerModuleMapOfInjective ρ S L hf z : Gal(Ω/E) → n → B') g i =
      f ((z : Gal(Ω/E) → n → B) g i) :=
  rfl

/-- An injective map of coefficient modules induces an injective map of Selmer modules. -/
lemma selmerModuleMapOfInjective_injective {f : B →ₗ[O] B'} (hf : Function.Injective f) :
    Function.Injective (selmerModuleMapOfInjective ρ S L hf) := by
  intro z w h_eq
  ext g i
  apply hf
  rw [← selmerModuleMapOfInjective_apply ρ S L hf z, h_eq, selmerModuleMapOfInjective_apply]

/-- If `f` identifies `O / a` (that is, `QuotSpan a`) with the `a`-torsion of `B`, then composition
with `f` maps the Selmer module (cocycles for `ρ` unramified outside `S` that obey the relations
`L`) with coefficients in `O / a` onto the `a`-torsion of the one with coefficients in `B`. -/
lemma range_selmerModuleMapOfInjective {a : O} {f : QuotSpan a →ₗ[O] B}
    (hf : Function.Injective f) (h_onto : ∀ y : B, a • y = 0 → ∃ x : QuotSpan a, f x = y) :
    (selmerModuleMapOfInjective ρ S L hf).range = torsionBy O (selmerModule ρ S L B) a := by
  ext ⟨y, hy_mem⟩
  constructor
  · rintro ⟨z, hz⟩
    have hz_smul : a • z = 0 := by
      ext g i
      exact smul_quot_eq_zero_of_dvd dvd_rfl _
    rw [mem_torsionBy_iff, ← hz, ← map_smul, hz_smul, map_zero]
  · intro hy
    have hy_smul : a • y = 0 := by simpa [Subtype.ext_iff] using hy
    have h_lift (g : Gal(Ω/E)) (i : n) : ∃ x : QuotSpan a, f x = y g i :=
      h_onto (y g i) (congrFun₂ hy_smul g i)
    choose z hz using h_lift
    have hfz_mem : (fun (g : Gal(Ω/E)) (i : n) ↦ f (z g i)) ∈ selmerModule ρ S L B := by
      simpa only [hz] using hy_mem
    refine ⟨⟨z, (comp_mem_selmerModule_iff ρ S L hf).1 hfz_mem⟩, ?_⟩
    ext g i
    rw [selmerModuleMapOfInjective_apply]
    exact hz g i

/-- If `f` identifies `O / a` (that is, `QuotSpan a`) with the `a`-torsion of `B`, then the Selmer
module (cocycles for `ρ` unramified outside `S` that obey the relations `L`, not classes) with
coefficients in `O / a` has the length of the `a`-torsion of the one with coefficients in `B`. -/
lemma length_torsionBy_selmerModule {a : O} {f : QuotSpan a →ₗ[O] B}
    (hf : Function.Injective f) (h_onto : ∀ y : B, a • y = 0 → ∃ x : QuotSpan a, f x = y) :
    length O (torsionBy O (selmerModule ρ S L B) a) =
      length O (selmerModule ρ S L (QuotSpan a)) := by
  rw [← range_selmerModuleMapOfInjective ρ S L hf h_onto,
    ← (LinearEquiv.ofInjective _ (selmerModuleMapOfInjective_injective ρ S L hf)).length_eq]

variable [DVR O]

/-- For `a ≠ 0`, the Selmer module (cocycles for `ρ` unramified outside `S` that obey the relations
`L`) with coefficients in `O / a` has the length of the `a`-torsion of the Selmer module with
coefficients in `DivisibleQuot O = Frac(O) / O`. -/
lemma length_torsionBy_selmerModule_divisibleQuot {a : O} (ha : a ≠ 0) :
    length O (torsionBy O (selmerModule ρ S L (DivisibleQuot O)) a) =
      length O (selmerModule ρ S L (QuotSpan a)) :=
  length_torsionBy_selmerModule ρ S L (divQuot_injective ha) fun _ hy ↦ exists_divQuot_eq ha hy

/-- For `a ≠ 0`, the Selmer module (cocycles for `ρ` unramified outside `S` that obey the relations
`L`) with coefficients in `O / a` is no longer than the one with coefficients in
`DivisibleQuot O = Frac(O) / O`. -/
lemma length_selmerModule_le_divisibleQuot {a : O} (ha : a ≠ 0) :
    length O (selmerModule ρ S L (QuotSpan a)) ≤
      length O (selmerModule ρ S L (DivisibleQuot O)) :=
  (length_torsionBy_selmerModule_divisibleQuot ρ S L ha).symm.trans_le
    (length_le_of_injective _ (subtype_injective _))

end SelmerLevels

section DivisibleLength

variable {E O n : Type} [Field E] [CMFieldWithRoot5040 E] [CommRing O] [DVR O] [Fintype n]
  [DecidableEq n]
  {ρ : Gal(Ω/E) → Matrix n n O} {S : Set (FinPlace E)} {L : Set (Gal(Ω/E) →₀ Matrix n n O)}

variable (ρ S L) in
/-- For `E` a CM field containing the 5040th roots of unity (`CMFieldWithRoot5040`), the length over
`O` of the Selmer module with coefficients in `Frac(O) / O`: the locally constant cocycles for `ρ`
that are unramified outside `S` and obey the relations `L`. -/
noncomputable def divisibleSelmerLength : ℕ∞ :=
  Module.length O (selmerModule ρ S L (DivisibleQuot O))

/-- Let `E` be a CM field containing the 5040th roots of unity (`CMFieldWithRoot5040`) and `a ≠ 0`.
The Selmer module (cocycles for `ρ` unramified outside `S` that obey the relations `L`) with
coefficients in `O / a` has length at most `divisibleSelmerLength ρ S L`, the length of the one with
coefficients in `Frac(O) / O`. -/
lemma length_le_divisibleSelmerLength {a : O} (ha : a ≠ 0) :
    Module.length O (selmerModule ρ S L (QuotSpan a)) ≤ divisibleSelmerLength ρ S L :=
  length_selmerModule_le_divisibleQuot ρ S L ha

end DivisibleLength

end New.Selmer

end
