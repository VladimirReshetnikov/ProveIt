module
/- Generic HFS-vector append, adapted from PA209 without any machine imports. -/
public import Foundation.FirstOrder.Arithmetic.HFS.Vec
@[expose] public section

/-! Definable two-vector append for the existing Foundation HFS sequence code.
This is a prerequisite to internal trace-segment composition, not itself a
machine-execution theorem. The construction works in arbitrary IΣ1 models. -/
namespace PA196.Arithmetic.VectorAppend
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def blueprint : VecRec.Blueprint 1 where
  nil := .mkSigma “y z. y = z”
  adjoin := .mkSigma “y x xs ih z. !adjoinDef y x ih”

noncomputable def construction : VecRec.Construction V blueprint where
  nil param := param 0
  adjoin (_ x _ ih) := x ∷ ih
  nil_defined := .mk fun v ↦ by simp [blueprint]
  adjoin_defined := .mk fun v ↦ by simp [blueprint, Fin.isValue]

noncomputable def append (xs ys : V) : V := construction.result ![ys] xs

@[simp] lemma append_nil (ys : V) : append 0 ys = ys := by
  simp [append,construction]

@[simp] lemma append_adjoin (x xs ys : V) : append (x ∷ xs) ys = x ∷ append xs ys := by
  simp [append,construction]

def appendDef : 𝚺ᴬ₁.Semisentence 3 := blueprint.resultDef

instance append_defined : 𝚺ᴬ₁-Function₂ (append : V → V → V) via appendDef :=
  construction.result_defined

instance append_definable : 𝚺ᴬ₁-Function₂ (append : V → V → V) := append_defined.to_definable

instance append_definable' (Γ m) : Γᴬ_[m + 1]-Function₂ (append : V → V → V) :=
  append_definable.of_sigmaOne

@[simp] lemma len_append (xs ys : V) : len (append xs ys) = len xs + len ys := by
  induction xs using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => simp
  case adjoin x xs ih => simp [ih,add_assoc,add_comm,add_left_comm]

lemma nth_append_left (xs ys : V) {i : V} (hi : i < len xs) :
    nth (append xs ys) i = nth xs i := by
  induction xs using adjoin_ISigma1.sigma1_succ_induction generalizing i
  · definability
  case nil => simp at hi
  case adjoin x xs ih =>
    rcases zero_or_succ i with rfl | ⟨i,rfl⟩
    · simp
    · simp [ih (by simpa using hi)]

lemma nth_append_right (xs ys i : V) :
    nth (append xs ys) (len xs+i) = nth ys i := by
  induction xs using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => simp
  case adjoin x xs ih =>
    rw [append_adjoin,len_adjoin,
      show len xs+1+i = (len xs+i)+1 by ac_rfl,nth_adjoin_succ]
    exact ih

#print axioms len_append
#print axioms nth_append_left
#print axioms nth_append_right
end PA196.Arithmetic.VectorAppend

