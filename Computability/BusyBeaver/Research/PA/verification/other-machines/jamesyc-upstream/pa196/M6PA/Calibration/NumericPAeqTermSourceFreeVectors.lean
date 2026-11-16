module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermSourceShiftParameters
@[expose] public section

namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
namespace DropLast
noncomputable def blueprint : VecRec.Blueprint 0 where
  nil := .mkSigma “y. y=0”
  adjoin := .mkSigma “y x xs ih. (xs=0 ∧ y=0) ∨ (xs≠0 ∧ !adjoinDef y x ih)”
noncomputable def construction : VecRec.Construction V blueprint where
  nil _ := 0
  adjoin (_ x xs ih) := if xs=0 then 0 else x∷ih
  nil_defined := .mk fun v => by simp [blueprint]
  adjoin_defined := .mk fun v => by
    by_cases h : v 2=0 <;> simp [blueprint,h]
end DropLast
noncomputable def dropLast (v : V) : V := DropLast.construction.result ![] v
noncomputable def dropLastGraph : 𝚺ᴬ₁.Semisentence 2 := DropLast.blueprint.resultDef
instance dropLast_defined : 𝚺ᴬ₁-Function₁ (dropLast : V→V) via dropLastGraph :=
  .mk fun v => by simpa [dropLastGraph,dropLast] using! DropLast.construction.result_defined.defined v
instance dropLast_definable : 𝚺ᴬ₁-Function₁ (dropLast : V→V) := dropLast_defined.to_definable
instance dropLast_definable' (Γ m) : Γᴬ_[m+1]-Function₁ (dropLast : V→V) := dropLast_definable.of_sigmaOne
@[simp] theorem dropLast_nil : dropLast (0:V)=0 := by simp [dropLast,DropLast.construction]
theorem dropLast_adjoin (x v : V) : dropLast (x∷v)=if v=0 then 0 else x∷dropLast v := by
  simp [dropLast,DropLast.construction]
theorem dropLast_concat (v x : V) : dropLast (concat v x)=v := by
  induction v using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => simp [dropLast_adjoin]
  case adjoin y v ih =>
    have hn : concat v x ≠ 0 := by intro hh; have := congrArg len hh; simp at this
    simp [dropLast_adjoin,ih,hn]
theorem concat_dropLast {v s : V} (h : len v=s+1) : concat (dropLast v) (nth v s)=v := by
  induction v using adjoin_ISigma1.pi1_succ_induction generalizing s
  · definability
  case nil => simp at h
  case adjoin x v ih =>
    by_cases hv : v=0
    · subst v
      have hs : s=0 := by simpa using h.symm
      subst s; simp [dropLast_adjoin]
    · have hl : len v=s := by simpa using h
      obtain ⟨r,rfl⟩ := (zero_or_succ s).resolve_left (by intro hs; simp [hs] at hl; exact hv hl)
      simp only [dropLast_adjoin,hv,if_false,concat_adjoin,nth_adjoin_succ]
      rw [ih hl]
theorem dropLast_length {v s : V} (h : len v=s+1) : len (dropLast v)=s := by
  have hh := congrArg len (concat_dropLast h)
  simpa [h] using hh
theorem dropLast_nth {v s i : V} (h : len v=s+1) (hi : i<s) : nth (dropLast v) i=nth v i := by
  have hh := congrArg (fun w : V => nth w i) (concat_dropLast h)
  simpa [concat_nth_lt _ _ (show i<len (dropLast v) by rw [dropLast_length h]; exact hi)] using hh

theorem dropLast_valid {s n v : V} (h : IsSemitermVec language (s+1) n v) :
    IsSemitermVec language s n (dropLast v) := by
  refine IsSemitermVec.iff.mpr ⟨dropLast_length h.lh,?_⟩
  intro i hi
  rw [dropLast_nth h.lh hi]
  exact h.nth (lt_trans hi (lt_add_one s))

#print axioms dropLast_defined
#print axioms dropLast_concat
#print axioms concat_dropLast
#print axioms dropLast_length
#print axioms dropLast_nth
#print axioms dropLast_valid
end M6.PA.NumericPAeqTerm

