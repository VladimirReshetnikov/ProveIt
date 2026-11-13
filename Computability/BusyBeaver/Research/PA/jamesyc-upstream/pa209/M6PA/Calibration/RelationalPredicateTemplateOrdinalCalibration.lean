module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateOrdinalSchema
public import M6PA.Calibration.RelationalPredicateTemplateNegation
public import M6PA.Calibration.RelationalPredicateTemplateClosedAgreement
public import M6PA.Calibration.FoundationRelationalSequentSeparationCode
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate.Ordinal
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language

theorem formulaValue_iff {s : Nat} (p q : Formula s) {P b f n : V}
    (hP : IsSemiformula L 1 P) (h : EnvironmentsValid (s:V) n b f)
    (hp : ∀i,p.FVar? i→(i:V)<len f) (hq : ∀i,q.FVar? i→(i:V)<len f) :
    formulaValue (sourceIff p q) P b f =
      Bootstrapping.iff L (formulaValue p P b f) (formulaValue q P b f) := by
  change qqAnd (qqOr (formulaValue (∼p) P b f) (formulaValue q P b f))
    (qqOr (formulaValue (∼q) P b f) (formulaValue p P b f)) = _
  simp only [Semiformula.neg_eq]
  rw [formulaValue_neg p hP h hp,formulaValue_neg q hP h hq]
  rfl

theorem separation_body_value {P b f : V}
    (hP : IsSemiformula L 1 P) (h : EnvironmentsValid (3:V) 3 b f)
    (hi : IdentityBound 3 b) :
    formulaValue (sourceIff (mem (.bvar 1) (.bvar 0))
      (mem (.bvar 2) (.bvar 0) ⋏ traceProperty (∼hole) 2)) P b f =
    Bootstrapping.iff L (RelationalSource.Numeric.sourceMember 1 0)
      (qqAnd (RelationalSource.Numeric.sourceMember 2 0) (Bootstrapping.neg L P)) := by
  rw [formulaValue_iff _ _ hP h]
  · simp only [mem,traceProperty,hole,Semiformula.neg_eq,Semiformula.neg,
      Semiformula.rewAux,formulaValue,atomValue,termValue]
    have hi0 := hi 0
    have hi1 := hi 1
    have hi2 := hi 2
    norm_num at hi0 hi1 hi2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Function.comp_apply]
    simp [Rew.map,hi0,hi1,hi2]
    have he : substs1 L (qqBvar (0:V)) P=P := RelationalSource.Numeric.source_identity_subst hP
    simpa [RelationalSource.Numeric.sourceMember] using congrArg
      (fun x => Bootstrapping.iff L (RelationalSource.Numeric.sourceMember 1 0)
        (qqAnd (RelationalSource.Numeric.sourceMember 2 0) (Bootstrapping.neg L x))) he
  · intro i hi; simpa [mem,Semiformula.FVar?,Semiformula.freeVariables,Semiterm.freeVariables] using hi
  · intro i hi
    simp [mem,traceProperty,hole,Semiformula.FVar?,Semiformula.freeVariables,
      Semiterm.freeVariables,Semiformula.rewAux,Semiformula.neg] at hi
theorem separation_value {P f : V} (hP : IsSemiformula L 1 P)
    (hf : IsSemitermVec L (len f) 0 f) :
    formulaValue (separationFormula (∼hole)) P 0 f =
      RelationalSource.Numeric.sourceSeparation (Bootstrapping.neg L P) := by
  have h0 : EnvironmentsValid (0:V) 0 0 f := ⟨by simp,hf⟩
  have h1 : EnvironmentsValid (1:V) 1 (bindBound 0) (bindFree f) := by
    simpa using bindEnvironments_valid h0
  have h2 : EnvironmentsValid (2:V) 2 (bindBound (bindBound 0)) (bindFree (bindFree f)) := by
    convert bindEnvironments_valid h1 using 1 <;> norm_num
  have h3 : EnvironmentsValid (3:V) 3 (bindBound (bindBound (bindBound 0)))
      (bindFree (bindFree (bindFree f))) := by
    convert bindEnvironments_valid h2 using 1 <;> norm_num
  have hi0 : IdentityBound 0 (0:V) := by intro i; exact Fin.elim0 i
  have hi1 : IdentityBound 1 (bindBound (0:V)) := identityBound_bind h0.1 hi0
  have hi2 : IdentityBound 2 (bindBound (bindBound (0:V))) :=
    identityBound_bind (s:=1) (by simpa only [Nat.cast_one] using h1.1) hi1
  have hi3 : IdentityBound 3 (bindBound (bindBound (bindBound (0:V)))) :=
    identityBound_bind (s:=2) (by convert h2.1 using 1 <;> norm_num) hi2
  change qqAll (qqExs (qqAll (formulaValue _ P (bindBound (bindBound (bindBound 0)))
    (bindFree (bindFree (bindFree f)))))) = _
  rw [separation_body_value hP h3 hi3]
  rfl

#print axioms separation_value
#print axioms formulaValue_iff
#print axioms separation_body_value
end M6.PA.RelationalPredicateTemplate.Ordinal
