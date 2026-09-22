import Surreal.Foundations.SmallNormalFormInitialSegment
import Mathlib.Logic.Small.Set

/-!
# Unions of small chains of formal normal forms

A small family comparable by formal initial segment has a union with exactly
the union of its supports and the consistent coefficients of its stages.
Reverse well-foundedness follows because above any chosen support point all
union terms lie in a stage containing that point. Every retained exponent
therefore has its coefficients and earlier truncation already in one stage.
No evaluation or arithmetic preservation in the actual sign field is used.
-/

universe u v

namespace Surreal.Foundations.SmallNormalForm

noncomputable section

open scoped Classical

/-- Construct formal data from actual sign-indexed coefficients, with explicit
lower-universe support smallness and reverse well-foundedness. -/
def fromCoefficients (f : SignSequence.{u} → ℝ)
    (hs : Small.{u} (Function.support f))
    (hw : (Function.support f).WellFoundedOn (· > ·)) : SmallNormalForm.{u} := by
  let g : _root_.Surreal.{u} → ℝ := fun a => f (SignSequence.toSurrealOrderIso.symm a)
  let e : (· > · : Function.support g → Function.support g → Prop) ↪r
      (· > · : Function.support f → Function.support f → Prop) :=
    { toFun a := ⟨SignSequence.toSurrealOrderIso.symm a.val, a.property⟩
      inj' := by
        intro a b h
        apply Subtype.ext
        exact SignSequence.toSurrealOrderIso.symm.injective (congrArg Subtype.val h)
      map_rel_iff' := SignSequence.toSurrealOrderIso.symm.lt_iff_lt }
  letI := hs
  exact _root_.SurrealHahnSeries.mk g (small_of_injective e.injective) (e.wellFounded hw)

@[simp] theorem coeff_fromCoefficients (f : SignSequence.{u} → ℝ)
    (hs : Small.{u} (Function.support f))
    (hw : (Function.support f).WellFoundedOn (· > ·)) (a : SignSequence.{u}) :
    coeff (fromCoefficients f hs hw) a = f a := by
  change f (SignSequence.toSurrealOrderIso.symm (SignSequence.toSurreal a)) = f a
  rw [SignSequence.orderIso_symm_toSurreal]

@[simp] theorem support_fromCoefficients (f : SignSequence.{u} → ℝ)
    (hs : Small.{u} (Function.support f))
    (hw : (Function.support f).WellFoundedOn (· > ·)) :
    support (fromCoefficients f hs hw) = Function.support f := by
  ext a
  simp only [mem_support, coeff_fromCoefficients, Function.mem_support]

variable {I : Type v}

private def unionCoefficients (F : I → SmallNormalForm.{u}) (a : SignSequence.{u}) : ℝ :=
  if h : ∃ i, a ∈ support (F i) then coeff (F h.choose) a else 0

private theorem support_unionCoefficients (F : I → SmallNormalForm.{u}) :
    Function.support (unionCoefficients F) = ⋃ i, support (F i) := by
  ext a
  by_cases h : ∃ i, a ∈ support (F i)
  · have hc : coeff (F h.choose) a ≠ 0 := h.choose_spec
    simp only [Function.mem_support, unionCoefficients, dif_pos h, Set.mem_iUnion]
    exact iff_of_true hc h
  · simp only [Function.mem_support, unionCoefficients, dif_neg h, ne_eq, not_true_eq_false,
      Set.mem_iUnion]
    exact iff_of_false (fun h => h) h

/-- Above any exponent retained at a stage, the union coefficients agree
with that stage, including its zero coefficients. -/
private theorem unionCoefficients_eq_above (F : I → SmallNormalForm.{u})
    (h : ∀ i j, IsInitialSegment (F i) (F j) ∨ IsInitialSegment (F j) (F i))
    (i : I) {a b : SignSequence.{u}} (ha : a ∈ support (F i)) (hab : a ≤ b) :
    unionCoefficients F b = coeff (F i) b := by
  by_cases hb : ∃ j, b ∈ support (F j)
  · rw [unionCoefficients, dif_pos hb]
    rcases h hb.choose i with hji | hij
    · exact hji.coeff_eq hb.choose_spec
    · exact (hij a ha b hab).symm
  · rw [unionCoefficients, dif_neg hb]
    exact (not_ne_iff.mp (fun hbi => hb ⟨i, hbi⟩)).symm

private theorem mem_stage_of_mem_union_above (F : I → SmallNormalForm.{u})
    (h : ∀ i j, IsInitialSegment (F i) (F j) ∨ IsInitialSegment (F j) (F i))
    (i : I) {a b : SignSequence.{u}} (ha : a ∈ support (F i))
    (hb : b ∈ ⋃ j, support (F j)) (hab : a ≤ b) : b ∈ support (F i) := by
  have hb' : b ∈ Function.support (unionCoefficients F) := by
    rwa [support_unionCoefficients]
  change unionCoefficients F b ≠ 0 at hb'
  rw [unionCoefficients_eq_above F h i ha hab] at hb'
  exact hb'

/-- A chain union retains reverse well-founded support. Any nonempty subset
has a greatest point already in one of the original stages. -/
theorem wellFoundedOn_iUnion_support (F : I → SmallNormalForm.{u})
    (h : ∀ i j, IsInitialSegment (F i) (F j) ∨ IsInitialSegment (F j) (F i)) :
    (⋃ i, support (F i)).WellFoundedOn (· > ·) := by
  apply WellFounded.wellFounded_iff_has_min.mpr
  intro s hs
  obtain ⟨a, ha⟩ := hs
  obtain ⟨i, hai⟩ := Set.mem_iUnion.mp a.property
  let T : Set (support (F i)) :=
    {b | ∃ hb : b.val ∈ ⋃ j, support (F j), (⟨b.val, hb⟩ : ⋃ j, support (F j)) ∈ s}
  have hT : T.Nonempty := ⟨⟨a.val, hai⟩, a.property, ha⟩
  obtain ⟨b, hb, hmax⟩ := (wellFoundedOn_support (F i)).has_min T hT
  obtain ⟨hbu, hbs⟩ := hb
  refine ⟨⟨b.val, hbu⟩, hbs, ?_⟩
  intro c hcs hbc
  have hab : a.val ≤ b.val := le_of_not_gt (hmax ⟨a.val, hai⟩ ⟨a.property, ha⟩)
  have hci : c.val ∈ support (F i) :=
    mem_stage_of_mem_union_above F h i hai c.property (hab.trans (le_of_lt hbc))
  exact hmax ⟨c.val, hci⟩ ⟨c.property, hcs⟩ hbc

variable [Small.{u} I]

/-- The formal union of a lower-universe-small chain of initial segments. -/
def chainUnion (F : I → SmallNormalForm.{u})
    (h : ∀ i j, IsInitialSegment (F i) (F j) ∨ IsInitialSegment (F j) (F i)) :
    SmallNormalForm.{u} :=
  fromCoefficients (unionCoefficients F)
    (by rw [support_unionCoefficients]; infer_instance)
    (by rw [support_unionCoefficients]; exact wellFoundedOn_iUnion_support F h)

/-- Exactly the union of the stage supports occurs in the chain union. -/
@[simp] theorem support_chainUnion (F : I → SmallNormalForm.{u})
    (h : ∀ i j, IsInitialSegment (F i) (F j) ∨ IsInitialSegment (F j) (F i)) :
    support (chainUnion F h) = ⋃ i, support (F i) := by
  rw [chainUnion, support_fromCoefficients, support_unionCoefficients]

@[simp] theorem mem_support_chainUnion (F : I → SmallNormalForm.{u})
    (h : ∀ i j, IsInitialSegment (F i) (F j) ∨ IsInitialSegment (F j) (F i))
    (a : SignSequence.{u}) :
    a ∈ support (chainUnion F h) ↔ ∃ i, a ∈ support (F i) := by
  rw [support_chainUnion, Set.mem_iUnion]

/-- Every stage is an initial segment of the chain union. -/
theorem isInitialSegment_chainUnion (F : I → SmallNormalForm.{u})
    (h : ∀ i j, IsInitialSegment (F i) (F j) ∨ IsInitialSegment (F j) (F i))
    (i : I) : IsInitialSegment (F i) (chainUnion F h) := by
  intro a ha b hab
  rw [chainUnion, coeff_fromCoefficients]
  exact (unionCoefficients_eq_above F h i ha hab).symm

/-- At any retained exponent, its stage already has the complete earlier
truncation and exactly the coefficient of the union. -/
theorem exists_stage_of_mem_support_chainUnion (F : I → SmallNormalForm.{u})
    (h : ∀ i j, IsInitialSegment (F i) (F j) ∨ IsInitialSegment (F j) (F i))
    (a : SignSequence.{u}) (ha : a ∈ support (chainUnion F h)) :
    ∃ i, a ∈ support (F i) ∧ coeff (chainUnion F h) a = coeff (F i) a ∧
      trunc (chainUnion F h) a = trunc (F i) a := by
  obtain ⟨i, hai⟩ := (mem_support_chainUnion F h a).mp ha
  have hi := isInitialSegment_chainUnion F h i
  exact ⟨i, hai, (hi.coeff_eq hai).symm, (hi.trunc_eq hai).symm⟩

/-- The chain union is an initial segment of every common extension. -/
theorem chainUnion_isInitialSegment (F : I → SmallNormalForm.{u})
    (h : ∀ i j, IsInitialSegment (F i) (F j) ∨ IsInitialSegment (F j) (F i))
    (G : SmallNormalForm.{u}) (hG : ∀ i, IsInitialSegment (F i) G) :
    IsInitialSegment (chainUnion F h) G := by
  intro a ha b hab
  obtain ⟨i, hai⟩ := (mem_support_chainUnion F h a).mp ha
  exact ((isInitialSegment_chainUnion F h i) a hai b hab).symm.trans (hG i a hai b hab)

/-- The union of an empty family is the zero formal form. -/
@[simp] theorem chainUnion_of_isEmpty [IsEmpty I] (F : I → SmallNormalForm.{u})
    (h : ∀ i j, IsInitialSegment (F i) (F j) ∨ IsInitialSegment (F j) (F i)) :
    chainUnion F h = 0 := by
  apply ext
  intro a
  rw [chainUnion, coeff_fromCoefficients, coeff_zero]
  simp [unionCoefficients]

end

end Surreal.Foundations.SmallNormalForm
