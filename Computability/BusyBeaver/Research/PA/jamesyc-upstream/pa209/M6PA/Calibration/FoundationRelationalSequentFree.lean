module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalSequentSubstitution
@[expose] public section

/-! Exact source substs1/free compatibility, with finite environments explicit.
These equalities are not native quantifier instantiation certificates. -/
namespace M6.PA.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem labelSubstitution_singleton {t y b f : V} (ht : VariableLabel y t b f) :
    LabelSubstitution (t∷0) (y∷0) b f := by
  constructor
  · simp
  · intro i hi
    have he : i=0 := by simpa using hi
    subst i
    simpa using ht

variable [V↓[ℒₒᵣ] ⊧* theory]

theorem translate_substs1 (p t y b f lo z : V) (hp : IsSemiformula language 1 p)
    (ht : VariableLabel y t b f) :
    translate (parameters b f lo z) (substs1 language t p)=
      translate (parameters (y∷0) f lo z) p := by
  have hp' : IsSemiformula language (len (y∷(0:V))) p := by simpa using hp
  exact translate_subst p (t∷0) (y∷0) b f lo z (labelSubstitution_singleton ht) hp'

/-- Foundation free is exactly substitution of free variable zero into the
shifted body. The same allocator and reserve are used on both sides. -/
theorem translate_free (p x b f lo z : V) (hp : IsSemiformula language 1 p) :
    translate (parameters b (x∷f) lo z) (Bootstrapping.free language p)=
      translate (parameters (x∷0) f lo z) p := by
  unfold Bootstrapping.free
  rw [translate_substs1 _ _ x b (x∷f) lo z hp.shift (by
    simpa using label_fvar b (x∷f) 0 (by simp))]
  simpa only [prependFree_parameters] using
    translate_shift p (parameters (x∷0) f lo z) x hp.isUFormula

/-- This is the exact allocator alignment needed at an all-body: the opened
body must be translated at lo+1, not silently at the parent's lo. -/
theorem translate_free_advance (p f lo z : V) (hp : IsSemiformula language 1 p) :
    translate (parameters 0 (lo∷f) (lo+1) z) (Bootstrapping.free language p)=
      translate (advance (parameters 0 f lo z)) p := by
  rw [advance_parameters]
  exact translate_free p lo 0 f (lo+1) z hp

#print axioms labelSubstitution_singleton
#print axioms translate_substs1
#print axioms translate_free
#print axioms translate_free_advance
end M6.PA.RelationalSource.Numeric

