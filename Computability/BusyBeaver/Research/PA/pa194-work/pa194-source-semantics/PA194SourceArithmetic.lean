import PA194SourceTotality
import PA194SourceCalibration
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# The arithmetic facts of the source theory, without hypotheses

* `known_full`: the statements of `Known` hold in every nonempty structure with equality that
  satisfies weak adjunction and the separation instances.
* `theta10`, `valid_ten`: the ten sentences `sE1`, `sEI`, `sIs`, `sIt`, `sZ1`, `sZ2`, `sS1`,
  `sS2`, `sA1`, `sM1` are true in its letter structure.
* `tenFacts_semantic : TenFacts adjunctiveFullSepTheory`, in every model `V` of `IΣ₁`, by
  `source_supply`.
* `sourceFacts_semantic`: all twelve `SourceFacts`.
* `calibration`: internal proofs of `sA2`, `sM2`, `sA3` and `sM3`.

No internal proof from `pa194-model-axioms` is used: every fact about the source theory in
this chain is proved in structures and transferred by `source_supply`.
-/
namespace PA194SourceModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194Schematic PA194GuardedCompiler
open M6.PA.RelationalSource

attribute [local instance] PA194ModelLogic.sourceLanguageAdjTheory

section model
variable {N : Type} [Nonempty N] [s : Structure SourceL N] [Structure.Eq SourceL N]
variable (hsep : ∀ (p : Semiproposition SourceL 1) (f : ℕ → N),
  FirstOrder.Semiformula.Evalf (s := s) f (separationFormula p))
variable (hwa : N↓[SourceL] ⊧ sourceWeakAdjunction)
include hsep hwa

theorem known_full (f : ℕ → N) : Known N where
  irefl := iso_refl hsep hwa f
  isym := fun a c da dc h => iso_symm hsep hwa f a da c da dc h
  itrans := fun a c d da dc dd h h' => iso_trans hsep hwa f a da c d da dc dd h h'
  z1 := by
    obtain ⟨e, he⟩ := exists_empty hsep
    exact ⟨e, empty_dom hsep he, he⟩
  z2 := fun a c _ za _ zc => iso_of_empty hsep za zc
  s1 := fun u du => succ_exists hsep hwa du
  s2 := fun u w u' w' du _ du' _ h h' i => iso_succ hsep hwa du du' h h' i
  a1 := fun u u' du du' => add_total hsep hwa f u du u' du du'
  m1 := fun u u' du du' => mul_total hsep hwa f u du u' du du'

theorem theta10 (f : ℕ → N) : @MTheta10 N (sourceLetters s f) := by
  have K := known_full hsep hwa f
  refine @MTheta10.mk N (sourceLetters s f) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun x => (mE_iff f x x).mpr rfl
  · exact fun x a b da _ ha hb => by
      have e1 : a = x := (mE_iff f a x).mp ha
      have e2 : b = x := (mE_iff f b x).mp hb
      rw [e2, ← e1]
      exact (mI_iff f a a).mpr (K.irefl a ((mD_iff f a).mp da))
  · exact fun a b da db h => (mI_iff f b a).mpr
      (K.isym a b ((mD_iff f a).mp da) ((mD_iff f b).mp db) ((mI_iff f a b).mp h))
  · exact fun a b c da db dc h h' => (mI_iff f a c).mpr
      (K.itrans a b c ((mD_iff f a).mp da) ((mD_iff f b).mp db) ((mD_iff f c).mp dc)
        ((mI_iff f a b).mp h) ((mI_iff f b c).mp h'))
  · exact by
      obtain ⟨z, dz, zz⟩ := K.z1
      exact ⟨z, (mD_iff f z).mpr dz, (mZ_iff f z).mpr zz⟩
  · exact fun a b da za db zb => (mI_iff f a b).mpr
      (K.z2 a b ((mD_iff f a).mp da) ((mZ_iff f a).mp za) ((mD_iff f b).mp db)
        ((mZ_iff f b).mp zb))
  · exact fun u du => by
      obtain ⟨w, dw, sw⟩ := K.s1 u ((mD_iff f u).mp du)
      exact ⟨w, (mD_iff f w).mpr dw, (mS_iff f u w).mpr sw⟩
  · exact fun u w u' w' du dw du' dw' h h' i => (mI_iff f w w').mpr
      (K.s2 u w u' w' ((mD_iff f u).mp du) ((mD_iff f w).mp dw) ((mD_iff f u').mp du')
        ((mD_iff f w').mp dw') ((mS_iff f u w).mp h) ((mS_iff f u' w').mp h')
        ((mI_iff f u u').mp i))
  · exact fun u u' du du' => by
      obtain ⟨w, dw, aw⟩ := K.a1 u u' ((mD_iff f u).mp du) ((mD_iff f u').mp du')
      exact ⟨w, (mD_iff f w).mpr dw, (mA_iff f u u' w).mpr aw⟩
  · exact fun u u' du du' => by
      obtain ⟨w, dw, mw⟩ := K.m1 u u' ((mD_iff f u).mp du) ((mD_iff f u').mp du')
      exact ⟨w, (mD_iff f w).mpr dw, (mMu_iff f u u' w).mpr mw⟩

/-- The ten sentences are true in the letter structure. -/
theorem valid_ten (f : ℕ → N) :
    @ev N (sourceLetters s f) 0 (![] : Fin 0 → N) sE1 ∧
    @ev N (sourceLetters s f) 0 (![] : Fin 0 → N) sEI ∧
    @ev N (sourceLetters s f) 0 (![] : Fin 0 → N) sIs ∧
    @ev N (sourceLetters s f) 0 (![] : Fin 0 → N) sIt ∧
    @ev N (sourceLetters s f) 0 (![] : Fin 0 → N) sZ1 ∧
    @ev N (sourceLetters s f) 0 (![] : Fin 0 → N) sZ2 ∧
    @ev N (sourceLetters s f) 0 (![] : Fin 0 → N) sS1 ∧
    @ev N (sourceLetters s f) 0 (![] : Fin 0 → N) sS2 ∧
    @ev N (sourceLetters s f) 0 (![] : Fin 0 → N) sA1 ∧
    @ev N (sourceLetters s f) 0 (![] : Fin 0 → N) sM1 := by
  obtain ⟨e1, ei, is', it', z1, z2, s1, s2, a1, m1⟩ := theta10 hsep hwa f
  exact ⟨(@ev_sE1 N (sourceLetters s f)).mpr e1, (@ev_sEI N (sourceLetters s f)).mpr ei,
    (@ev_sIs N (sourceLetters s f)).mpr is', (@ev_sIt N (sourceLetters s f)).mpr it',
    (@ev_sZ1 N (sourceLetters s f)).mpr z1, (@ev_sZ2 N (sourceLetters s f)).mpr z2,
    (@ev_sS1 N (sourceLetters s f)).mpr s1, (@ev_sS2 N (sourceLetters s f)).mpr s2,
    (@ev_sA1 N (sourceLetters s f)).mpr a1, (@ev_sM1 N (sourceLetters s f)).mpr m1⟩

#print axioms known_full
#print axioms valid_ten
end model

section supply
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local instance] adjunctiveFullSepTheoryDelta

/-- The ten source facts, by truth in the models of the source theory. -/
theorem tenFacts_semantic : TenFacts (V := V) adjunctiveFullSepTheory where
  e1 := source_supply sE1 (fun N _ s _ hwa hsep f => (valid_ten hsep hwa f).1)
  ei := source_supply sEI (fun N _ s _ hwa hsep f => (valid_ten hsep hwa f).2.1)
  is := source_supply sIs (fun N _ s _ hwa hsep f => (valid_ten hsep hwa f).2.2.1)
  it := source_supply sIt (fun N _ s _ hwa hsep f => (valid_ten hsep hwa f).2.2.2.1)
  z1 := source_supply sZ1 (fun N _ s _ hwa hsep f => (valid_ten hsep hwa f).2.2.2.2.1)
  z2 := source_supply sZ2 (fun N _ s _ hwa hsep f => (valid_ten hsep hwa f).2.2.2.2.2.1)
  s1 := source_supply sS1 (fun N _ s _ hwa hsep f => (valid_ten hsep hwa f).2.2.2.2.2.2.1)
  s2 := source_supply sS2 (fun N _ s _ hwa hsep f => (valid_ten hsep hwa f).2.2.2.2.2.2.2.1)
  a1 := source_supply sA1 (fun N _ s _ hwa hsep f => (valid_ten hsep hwa f).2.2.2.2.2.2.2.2.1)
  m1 := source_supply sM1 (fun N _ s _ hwa hsep f => (valid_ten hsep hwa f).2.2.2.2.2.2.2.2.2)

/-- All twelve source facts for the adjunctive source theory with full separation. -/
theorem sourceFacts_semantic : SourceFacts (V := V) adjunctiveFullSepTheory :=
  sourceFacts_full tenFacts_semantic

/-- Coherence of addition and multiplication and the two successor facts are internally
provable in the adjunctive source theory with full separation, in every model of `IΣ₁`. -/
theorem calibration :
    (adjunctiveFullSepTheory.internalize V ⊢ (tHyp sA2 : Bootstrapping.Semiformula V SourceL 0)) ∧
    (adjunctiveFullSepTheory.internalize V ⊢ (tHyp sM2 : Bootstrapping.Semiformula V SourceL 0)) ∧
    (adjunctiveFullSepTheory.internalize V ⊢ (tHyp sA3 : Bootstrapping.Semiformula V SourceL 0)) ∧
    (adjunctiveFullSepTheory.internalize V ⊢ (tHyp sM3 : Bootstrapping.Semiformula V SourceL 0)) :=
  calibration_of_ten tenFacts_semantic

#print axioms tenFacts_semantic
#print axioms sourceFacts_semantic
#print axioms calibration
end supply
end PA194SourceModel
