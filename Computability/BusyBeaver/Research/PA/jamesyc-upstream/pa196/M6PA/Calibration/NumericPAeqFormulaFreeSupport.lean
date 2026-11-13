module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaFreeSupportConstruction
@[expose] public section
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => Presentation.language
attribute [local irreducible] NumericPAeqTerm.freeBoundVecGraph


open FreeBound


noncomputable def freeBound (p : V) : V := (FreeBound.construction).result L 0 p

noncomputable def freeBoundGraph : 𝚺ᴬ₁.Semisentence 2 := ((FreeBound.blueprint).result L).rew (Rew.subst ![#0,
  ‘0’, #1])


section

instance freeBound_defined : 𝚺ᴬ₁-Function₁ freeBound (V := V) via freeBoundGraph := .mk fun v ↦ by
  simpa [freeBoundGraph, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using! (FreeBound.construction).result_defined.defined ![v 0, 0, v 1]

instance freeBound_definable : 𝚺ᴬ₁-Function₁ freeBound (V := V) := freeBound_defined.to_definable

instance freeBound_definable' (Γ : Polarity) (m : Nat) : Γᴬ_[m + 1]-Function₁ freeBound (V := V) := freeBound_definable.of_sigmaOne

end

@[simp] lemma freeBound_rel {k R v : V} (hR : Presentation.language.IsRel k R) (hv : IsUTermVec L k v) :
    freeBound (^rel k R v) = listMax (NumericPAeqTerm.freeBoundVec k v) := by simp [freeBound, hR, hv, FreeBound.construction]

@[simp] lemma freeBound_nrel {k R v : V} (hR : Presentation.language.IsRel k R) (hv : IsUTermVec L k v) :
    freeBound (^nrel k R v) = listMax (NumericPAeqTerm.freeBoundVec k v) := by simp [freeBound, hR, hv, FreeBound.construction]

@[simp] lemma freeBound_verum : freeBound (^⊤ : V) = 0 := by simp [freeBound, FreeBound.construction]

@[simp] lemma freeBound_falsum : freeBound (^⊥ : V) = 0 := by simp [freeBound, FreeBound.construction]

@[simp] lemma freeBound_and {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    freeBound (p ^⋏ q) = Max.max (freeBound p) (freeBound q) := by simp [freeBound, hp, hq, FreeBound.construction]

@[simp] lemma freeBound_or {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    freeBound (p ^⋎ q) = Max.max (freeBound p) (freeBound q) := by simp [freeBound, hp, hq, construction]

@[simp] lemma freeBound_all {p : V} (hp : IsUFormula L p) : freeBound (^∀ p) = freeBound p := by simp [freeBound, hp,
  construction]

@[simp] lemma freeBound_ex {p : V} (hp : IsUFormula L p) : freeBound (^∃ p) = freeBound p := by simp [freeBound, hp,
  construction]

lemma freeBound_eq_of_not_isUFormula {p : V} (h : ¬IsUFormula L p) : freeBound p = 0 := (construction).result_prop_not _ h

#print axioms freeBound_defined
#print axioms freeBound_rel
#print axioms freeBound_all
end M6.PA.NumericPAeqFormula

