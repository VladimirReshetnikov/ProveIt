import PA194EmitterScheduler
import PA194ControllerSchedulerPA
import PA194TargetSource
import PA194ModeledHaltRefutesPA
import PA194SourceEqVacuity
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
/-!
# The schedulers with a variant axiom emitter and the consistency of arithmetic

For every emitter `e`, every kind `k` of successful MP, every choice `ct` of the halting
test and every AX layout `a`:

* `soundGood`: for every emitter, also with the equality vacuity of PA196 in the gate, the
  set of codes whose translation arithmetic proves (`PA194SourceLineSoundness.good`) is a
  sound invariant in the sense of `PA194EmitterScheduler.Sound`. The heads, the diagonals
  and the gate come from `PA194TargetSource.target_sound` and the distinct-gate proofs, the
  equality vacuity from `PA194SourceEqVacuity`.
* `scheduler_iff_pa_refutation`: in every candidate-PRA model whose arithmetic reduct
  satisfies `𝗜𝚺₁`, the scheduler `haltAfterE e k ct a` halts at some time of the model
  exactly when arithmetic has an internal refutation. A halt puts the contradiction code in
  the invariant `good`, which is a refutation. Conversely a refutation gives a proof of the
  contradiction code in the calculus of the primary table
  (`PA194ModeledSchedulerSemanticIFF.scheduler_iff_pa_refutation`,
  `PA194ModelFairness.halts_iff_provable`), and `PA194EmitterScheduler.provable_halts` turns
  it into a halting command word.
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
open PA194TargetCantor PA194TargetLeaves PA194TargetGate PA194TargetProofLeaf
open PA194SourceLineSoundness (good)

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

/-- Arithmetic proves the translation of the gate of the primary calculus under its
guard. -/
theorem good_gate (x y z : M) (hx : z ≠ x) (hy : z ≠ y) : good (oldBundleValue x y z) :=
  PA194TargetSource.gate_from_separation_tail
    (PA194DistinctGateEndpoint.all_tail_from_distinct
      (fun u v w huv hwu hwv => PA194DistinctGateNumeric.distinct_gate_tail u v w huv hwu hwv))
    x y z hx hy

/-- Arithmetic proves the translation of every theorem of the primary calculus. -/
theorem good_of_provable (r : M) (h : TargetProvable r) : good r :=
  PA194TargetSource.target_sound good_gate r h

/-- Provability of the translation in arithmetic is a sound invariant for every emitter. -/
theorem soundGood (e : Emitter) : Sound (good (M := M)) e where
  definable := PA194SourceLineSoundness.good_definable
  closed :=
    { mp := fun x y hx hxy => PA194SourceMPPreservation.mp x y hxy hx
      gen := fun x y hy =>
        PA194SourceUniversalPreservation.source_universal_preservation x y hy
      row := fun x y z u h => good_of_provable _ (rho8_provable x y z u h)
      h1 := fun d h => good_of_provable _ (by
        rw [← machineHead1_model]
        exact head1_provable d h)
      h2 := fun d x h => good_of_provable _ (head2_provable d x h)
      h6 := fun d x h => good_of_provable _ (head6_provable d x h) }
  h3 := fun d x h => good_of_provable _ (head3_provable d x h)
  h4 := fun d x h => good_of_provable _ (head4_provable d x h)
  h5 := fun d h => good_of_provable _ (head5_provable d h)
  diagonal := fun c => good_of_provable _ (diagonal_provable c)
  gate := good_gate
  eqVac := fun _ x y z hx hy => PA194SourceEqVacuity.eq_vacuity x y z hx hy

/-- A proof of the translation of the contradiction code is a refutation. -/
theorem good_one_refutes (h : good (1 : M)) : Provable (𝗣𝗔 : ArithmeticTheory) (^⊥ : M) := by
  unfold PA194SourceLineSoundness.good PA194SourceLineSoundness.translated at h
  rw [PA194ContradictionTranslation.positive_code_one] at h
  exact PA194ContradictionInternalRefutation.contradiction_provable_implies_falsum h

/-- The scheduler halts exactly when arithmetic is internally refutable. -/
theorem scheduler_iff_pa_refutation (e : Emitter) (k : MPKind) (ct a : Bool) :
    (∃ n : M, F (haltAfterE e k ct a) ![n] = 1) ↔
      Provable (𝗣𝗔 : ArithmeticTheory) (^⊥ : M) := by
  constructor
  · rintro ⟨n, hn⟩
    exact good_one_refutes (halts_in (soundGood e) k ct a n hn)
  · intro hp
    have hprim := PA194ModeledSchedulerSemanticIFF.scheduler_iff_pa_refutation.mpr hp
    exact provable_halts e k ct a (PA194ModelFairness.halts_iff_provable.mp hprim)

#print axioms soundGood
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
