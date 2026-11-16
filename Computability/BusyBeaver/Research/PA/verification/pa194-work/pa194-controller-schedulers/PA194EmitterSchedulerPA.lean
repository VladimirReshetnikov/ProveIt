import PA194EmitterScheduler
import PA194ControllerSchedulerPA
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
/-!
# The schedulers with a variant axiom emitter and the consistency of arithmetic

For every emitter `e`, every kind `k` of successful MP, every choice `ct` of the halting
test and every AX layout `a`:

* `scheduler_iff_pa_refutation`: in every candidate-PRA model whose arithmetic reduct
  satisfies `𝗜𝚺₁`, the scheduler `haltAfterE e k ct a` halts at some time of the model
  exactly when arithmetic has an internal refutation. It composes
  `PA194EmitterScheduler.halts_iff_primary` with
  `PA194ModeledSchedulerSemanticIFF.scheduler_iff_pa_refutation`.
* `haltSentenceE e k ct a`: the sentence of the PRA language that says that the halt bit
  `haltAfterE e k ct a` is `1` at some time.
* `consistency_iff_scheduler_nonhalt`: the standard theory proves that the consistency
  sentence is equivalent to the negation of `haltSentenceE e k ct a`.

The schedulers are the command-level definitions of `PA194EmitterSchedulerCore`. No
connection with a literal table or with a source program is proved or used here, so these
are not yet statements about machines.
-/
noncomputable section
namespace PA194EmitterSchedulerPA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
open IPRAStandardTheory IPRAPA196Consistency IPRANativeFormula ConPA.ISigma1Models
open PA194EmitterScheduler
open PA194ControllerSchedulerPA (const_vec)
open ConPA.Ctl (MPKind)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The scheduler halts exactly when arithmetic is internally refutable. -/
theorem scheduler_iff_pa_refutation (e : Emitter) (k : MPKind) (ct a : Bool) :
    (∃ n : M, F (haltAfterE e k ct a) ![n] = 1) ↔
      Provable (𝗣𝗔 : ArithmeticTheory) (^⊥ : M) :=
  (halts_iff_primary e k ct a).trans
    PA194ModeledSchedulerSemanticIFF.scheduler_iff_pa_refutation

#print axioms scheduler_iff_pa_refutation
end models

/-! ## The halting sentences -/

def haltTermE (e : Emitter) (k : MPKind) (ct a : Bool) : Semiterm language Empty 1 :=
  .func (haltAfterE e k ct a) (fun _ => #0)
def haltMatrixE (e : Emitter) (k : MPKind) (ct a : Bool) : Semisentence language 1 :=
  .rel .eq ![haltTermE e k ct a, .func oneCode Fin.elim0]
def haltSentenceE (e : Emitter) (k : MPKind) (ct a : Bool) : Sentenceᵢ language :=
  native (∃⁰ haltMatrixE e k ct a)

section eval
variable {M : Type} [Structure language M] [Structure.Eq language M]

theorem haltMatrixE_eval (e : Emitter) (k : MPKind) (ct a : Bool) (t : M) :
    (haltMatrixE e k ct a).Eval ![t] Empty.elim ↔
      Structure.func (L := language) (haltAfterE e k ct a) (fun _ => t) =
        Structure.func (L := language) oneCode Fin.elim0 := by
  change Semiformula.EvalAux (inferInstance : Structure language M) Empty.elim ![t]
    (haltMatrixE e k ct a) ↔ _
  simp only [haltMatrixE, Semiformula.EvalAux, eqRel, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hz (v : Fin 1 → M) :
      (Semiterm.val v Empty.elim ∘ (Fin.elim0 : Fin 0 → Semiterm language Empty 1)) =
        (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simp [haltTermE, Semiterm.val_func, Semiterm.val_bvar, Matrix.fun_eq_vec_one, hz]
end eval

/-- Non-halting of the scheduler implies the consistency sentence. -/
theorem scheduler_nonhalt_consistency (e : Emitter) (k : MPKind) (ct a : Bool) :
    standardTheory ⊢ ∼haltSentenceE e k ct a 🡒 nativePAConsistency := by
  apply ConPA.Directions.ipra_nonhalt_implies_consistency (haltMatrixE e k ct a)
  · simp [haltMatrixE, Semiformula.Open]
  · exact Hierarchy.rel _ _ _ _
  · intro M _ _ _ _ hr hp
    letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
    letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
    letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
    letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
    letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := standard_isigma1 hr
    have hpa : Provable (𝗣𝗔 : ArithmeticTheory) (qqFalsum : M) := by
      rw [models_iff, PA195RefutationBridge.mapped_refutation_iff] at hp
      obtain ⟨d, hd⟩ := hp
      exact ⟨d, by simpa [Sentence.quote_def] using hd⟩
    obtain ⟨n, hn⟩ := (scheduler_iff_pa_refutation (M := M) e k ct a).mpr hpa
    rw [models_iff, Semiformula.eval_ex]
    refine ⟨n, ?_⟩
    apply (haltMatrixE_eval e k ct a n).mpr
    rw [← const_vec n]
    exact hn

/-- The consistency sentence implies non-halting of the scheduler. -/
theorem consistency_scheduler_nonhalt (e : Emitter) (k : MPKind) (ct a : Bool) :
    standardTheory ⊢ nativePAConsistency 🡒 ∼haltSentenceE e k ct a := by
  apply ConPA.Directions.ipra_consistency_implies_nonhalt (haltMatrixE e k ct a)
  · simp [haltMatrixE, Semiformula.Open]
  · intro M _ _ _ _ hr hhalt
    rw [models_iff, Semiformula.eval_ex] at hhalt
    obtain ⟨n, hn⟩ := hhalt
    have hn' := (haltMatrixE_eval e k ct a n).mp hn
    rw [← const_vec n] at hn'
    letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
    letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
    letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
    letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
    letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := standard_isigma1 hr
    rw [models_iff, PA195RefutationBridge.mapped_refutation_iff]
    exact (scheduler_iff_pa_refutation (M := M) e k ct a).mp ⟨n, hn'⟩

/-- The consistency sentence is equivalent to non-halting of the scheduler, in the standard
theory. -/
theorem consistency_iff_scheduler_nonhalt (e : Emitter) (k : MPKind) (ct a : Bool) :
    standardTheory ⊢ nativePAConsistency 🡘 ∼haltSentenceE e k ct a := by
  obtain ⟨hp⟩ := consistency_scheduler_nonhalt e k ct a
  obtain ⟨hq⟩ := scheduler_nonhalt_consistency e k ct a
  exact ⟨Entailment.K_intro hp hq⟩

#print axioms scheduler_nonhalt_consistency
#print axioms consistency_scheduler_nonhalt
#print axioms consistency_iff_scheduler_nonhalt
end PA194EmitterSchedulerPA
