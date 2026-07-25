import ZFCinPA.BaseCertificate

/-!
# The staged successor of the concrete family, from six flat implications

`ZFCinPA.StagedCompiler` states the last obligation of the uniform
internal-provability project as `HasStagedSuccessor`: at every model index
`n` a `ZFCStagedCertificateStep` whose public target code is the family's
next master certificate.  That structure is deliberately *staged*: its four
recursive slots are `UniversalKernel`s stated at four different cumulative
contexts, and the two direct slots are implications out of the previous
certificate and out of the complete new soundness context.

Mathematically, however, all six successor obligations of the concrete
family have the *same* antecedent — the level-`n` master certificate — and
the staged contexts only make more hypotheses available than each stage
needs.  This module performs that reduction once and for all:

* the four kernel fields of the concrete family are `^∀`-headed codes, so
  each has a *peeled* unary predicate (`crossLevelPredicate`, …) whose
  universal closure is the field itself.  The peeling is generic
  (`peelAll`) and takes its well-formedness from the field's own
  `IsFormula` invariant, so no new internal induction is needed;
* `ZFCSuccessorImplications n h` records the six flat implications
  `previous.sentence 🡒 field (n + 1)` together with the well-formedness
  witness for the successor consistency code;
* `stagedStepOfImplications` builds the staged step, weakening each
  cumulative context back to `previous.sentence` with two `⋏`-elimination
  axioms, and `stagedStepOfImplications_target` identifies its public
  target with the family's fields at `n + 1` — hence its code with
  `family.code (n + 1)`.

The upshot, `hasStagedSuccessor_of_successorImplications`, is that the
remaining mathematical content of the project is exactly six internal `𝗭𝗙𝗖`
implications at every (possibly nonstandard) index.  Nothing here weakens
`HasStagedSuccessor`, assumes it, or introduces a premise that the staged
compiler did not already demand — and the final section proves the
converse, `successorImplicationsOfStagedStep`, so that
`hasStagedSuccessor_iff_successorImplications` is an honest *equivalence*:
the flat form is neither stronger nor weaker than the staged one.

## Disciplines

The peeled bodies are stated with the fixed leaf codes abstracted (the
parameter firewall of `ZFCinPA.LevelCodeTower`), and every identification
between a peeled body and its field is a `rfl` between named constants —
no `simp` goal below ever contains a concrete translated-leaf Gödel code.
-/

set_option autoImplicit false

namespace LeanProofs
namespace ZFCinPA

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Peeling one coded universal quantifier

A `UniversalKernel` stores a unary predicate and contributes its universal
closure to the certificate.  The concrete family's four recursive fields
are already universally quantified sentences, so the kernels are installed
at their peeled bodies.  Well-formedness of the body is the field's own
`IsFormula` invariant read through `IsSemiformula.all`; nothing is
recomputed. -/

/-- Peel one coded universal quantifier off a sentence code. -/
noncomputable def peelAll (φ : Bootstrapping.Formula V ℒₛₑₜ) (p : V)
    (h : φ.val = ^∀ p) : Bootstrapping.Semiformula V ℒₛₑₜ 1 :=
  ⟨p, by
    have hs : IsSemiformula ℒₛₑₜ (0 : V) φ.val := by simp
    rw [h] at hs
    simpa using IsSemiformula.all.mp hs⟩

@[simp] theorem peelAll_val (φ : Bootstrapping.Formula V ℒₛₑₜ) (p : V)
    (h : φ.val = ^∀ p) : (peelAll φ p h).val = p := rfl

/-- The universal closure of a peeled body is the original sentence. -/
theorem all_peelAll (φ : Bootstrapping.Formula V ℒₛₑₜ) (p : V)
    (h : φ.val = ^∀ p) : (∀⁰ (peelAll φ p h)) = φ :=
  Bootstrapping.Semiformula.ext (by simp [h])

/-! ## The peeled bodies of the four recursive fields

Each body is the field builder minus its outermost coded quantifier, with
the fixed leaf codes abstracted; the concrete constants enter only by
instantiation. -/

section Bodies

/-- Body of the cross-level field. -/
noncomputable def crossLevelBodyPart (ifc ue qb : ℕ) (x : V) : V :=
  ^∀ (Bootstrapping.imp ℒₛₑₜ ↑ifc
    (Bootstrapping.imp ℒₛₑₜ ↑ue
      (Bootstrapping.imp ℒₛₑₜ (boundedAtPart qb x)
        (sigmaAtCode 1 0 x ^⋎ piFalseAtCode 1 0 x))))

theorem crossLevelPart_eq_all (ifc ue qb : ℕ) (x : V) :
    crossLevelPart ifc ue qb x = ^∀ (crossLevelBodyPart ifc ue qb x) := rfl

/-- Body of the shift-invariance field. -/
noncomputable def shiftInvariantBodyPart (ifc sm rn ue ec : ℕ) (x : V) : V :=
  ^∀ (^∀ (^∀ (Bootstrapping.imp ℒₛₑₜ ↑ifc
    (Bootstrapping.imp ℒₛₑₜ (^∃ (↑sm ^⋏ ↑rn))
      (Bootstrapping.imp ℒₛₑₜ ↑ue
        (^∀ (Bootstrapping.imp ℒₛₑₜ ↑ec
          ((Bootstrapping.iff ℒₛₑₜ (sigmaAtCode 3 0 x) (sigmaAtCode 4 2 x)) ^⋏
           (Bootstrapping.iff ℒₛₑₜ (piFalseAtCode 3 0 x)
             (piFalseAtCode 4 2 x))))))))))

theorem shiftInvariantPart_eq_all (ifc sm rn ue ec : ℕ) (x : V) :
    shiftInvariantPart ifc sm rn ue ec x =
      ^∀ (shiftInvariantBodyPart ifc sm rn ue ec x) := rfl

/-- Body of the substitution-invariance field. -/
noncomputable def substitutionInvariantBodyPart (ifc vm rn ue cp : ℕ)
    (x : V) : V :=
  ^∀ (^∀ (^∀ (^∀ (Bootstrapping.imp ℒₛₑₜ ↑ifc
    (Bootstrapping.imp ℒₛₑₜ ↑vm
      (Bootstrapping.imp ℒₛₑₜ ↑rn
        (Bootstrapping.imp ℒₛₑₜ ↑ue
          (Bootstrapping.imp ℒₛₑₜ ↑cp
            ((Bootstrapping.iff ℒₛₑₜ (sigmaAtCode 2 1 x)
                (sigmaAtCode 4 0 x)) ^⋏
             (Bootstrapping.iff ℒₛₑₜ (piFalseAtCode 2 1 x)
               (piFalseAtCode 4 0 x)))))))))))

theorem substitutionInvariantPart_eq_all (ifc vm rn ue cp : ℕ) (x : V) :
    substitutionInvariantPart ifc vm rn ue cp x =
      ^∀ (substitutionInvariantBodyPart ifc vm rn ue cp x) := rfl

/-- Body of the axiom-soundness field. -/
noncomputable def axiomSoundBodyPart (ax ue qb : ℕ) (x : V) : V :=
  ^∀ (Bootstrapping.imp ℒₛₑₜ ↑ax
    (Bootstrapping.imp ℒₛₑₜ ↑ue
      (Bootstrapping.imp ℒₛₑₜ (boundedAtPart qb x)
        (sigmaAtCode 1 0 x ^⋏ piTrueAtCode 1 0 x))))

theorem axiomSoundPart_eq_all (ax ue qb : ℕ) (x : V) :
    axiomSoundPart ax ue qb x = ^∀ (axiomSoundBodyPart ax ue qb x) := rfl

/-- The peeled body of the cross-level field at the concrete leaf codes. -/
noncomputable def crossLevelBody : V → V :=
  crossLevelBodyPart isFormCode1D2Code univEnv0D2Code quantBoundedD3Code

/-- The peeled body of the shift-invariance field. -/
noncomputable def shiftInvariantBody : V → V :=
  shiftInvariantBodyPart isFormCode3D4Code succMapD5Code renamesShiftD5Code
    univEnv1D4Code econsD5Code

/-- The peeled body of the substitution-invariance field. -/
noncomputable def substitutionInvariantBody : V → V :=
  substitutionInvariantBodyPart isFormCode4D5Code varMap3D5Code
    renamesSubstD5Code univEnv1D5Code compD5Code

/-- The peeled body of the axiom-soundness field. -/
noncomputable def axiomSoundBody : V → V :=
  axiomSoundBodyPart zfcAxiomCodeD2Code univEnv0D2Code quantBoundedD3Code

theorem crossLevelFormula_val_eq_all (x : V) :
    (crossLevelFormula x).val = ^∀ (crossLevelBody x) :=
  crossLevelPart_eq_all _ _ _ x

theorem shiftInvariantFormula_val_eq_all (x : V) :
    (shiftInvariantFormula x).val = ^∀ (shiftInvariantBody x) :=
  shiftInvariantPart_eq_all _ _ _ _ _ x

theorem substitutionInvariantFormula_val_eq_all (x : V) :
    (substitutionInvariantFormula x).val =
      ^∀ (substitutionInvariantBody x) :=
  substitutionInvariantPart_eq_all _ _ _ _ _ x

theorem axiomSoundFormula_val_eq_all (x : V) :
    (axiomSoundFormula x).val = ^∀ (axiomSoundBody x) :=
  axiomSoundPart_eq_all _ _ _ x

/-! ### The four kernel predicates -/

/-- Unary predicate of the cross-level kernel. -/
noncomputable def crossLevelPredicate (x : V) :
    Bootstrapping.Semiformula V ℒₛₑₜ 1 :=
  peelAll (crossLevelFormula x) (crossLevelBody x)
    (crossLevelFormula_val_eq_all x)

/-- Unary predicate of the shift-invariance kernel. -/
noncomputable def shiftInvariantPredicate (x : V) :
    Bootstrapping.Semiformula V ℒₛₑₜ 1 :=
  peelAll (shiftInvariantFormula x) (shiftInvariantBody x)
    (shiftInvariantFormula_val_eq_all x)

/-- Unary predicate of the substitution-invariance kernel. -/
noncomputable def substitutionInvariantPredicate (x : V) :
    Bootstrapping.Semiformula V ℒₛₑₜ 1 :=
  peelAll (substitutionInvariantFormula x) (substitutionInvariantBody x)
    (substitutionInvariantFormula_val_eq_all x)

/-- Unary predicate of the axiom-soundness kernel. -/
noncomputable def axiomSoundPredicate (x : V) :
    Bootstrapping.Semiformula V ℒₛₑₜ 1 :=
  peelAll (axiomSoundFormula x) (axiomSoundBody x)
    (axiomSoundFormula_val_eq_all x)

@[simp] theorem all_crossLevelPredicate (x : V) :
    (∀⁰ (crossLevelPredicate x)) = crossLevelFormula x :=
  all_peelAll _ _ _

@[simp] theorem all_shiftInvariantPredicate (x : V) :
    (∀⁰ (shiftInvariantPredicate x)) = shiftInvariantFormula x :=
  all_peelAll _ _ _

@[simp] theorem all_substitutionInvariantPredicate (x : V) :
    (∀⁰ (substitutionInvariantPredicate x)) = substitutionInvariantFormula x :=
  all_peelAll _ _ _

@[simp] theorem all_axiomSoundPredicate (x : V) :
    (∀⁰ (axiomSoundPredicate x)) = axiomSoundFormula x :=
  all_peelAll _ _ _

end Bodies

/-! ## Weakening the cumulative contexts

Every staged context is a left-nested conjunction whose leftmost conjunct
is the previous master certificate.  Two `⋏`-elimination axioms and
implication transitivity recover it; no represented syntax is inspected. -/

section Contexts

variable {T : InternalTheory V ℒₛₑₜ}

/-- The staged local context implies the previous master certificate. -/
noncomputable def localContext_imp
    (previous : ZFCTruthCertificateFields (V := V))
    (localField : Bootstrapping.Formula V ℒₛₑₜ) :
    T ⊢! localContext previous localField 🡒 previous.sentence :=
  LO.Entailment.and₁

/-- The staged cross-level context implies the previous master
certificate. -/
noncomputable def crossContext_imp
    (previous : ZFCTruthCertificateFields (V := V))
    (localField cross : Bootstrapping.Formula V ℒₛₑₜ) :
    T ⊢! crossContext previous localField cross 🡒 previous.sentence :=
  LO.Entailment.C_trans LO.Entailment.and₁
    (localContext_imp previous localField)

/-- The staged shift context implies the previous master certificate. -/
noncomputable def shiftContext_imp
    (previous : ZFCTruthCertificateFields (V := V))
    (localField cross shift : Bootstrapping.Formula V ℒₛₑₜ) :
    T ⊢! shiftContext previous localField cross shift 🡒 previous.sentence :=
  LO.Entailment.C_trans LO.Entailment.and₁
    (crossContext_imp previous localField cross)

/-- The staged substitution context implies the previous master
certificate. -/
noncomputable def substitutionContext_imp
    (previous : ZFCTruthCertificateFields (V := V))
    (localField cross shift substitution : Bootstrapping.Formula V ℒₛₑₜ) :
    T ⊢! substitutionContext previous localField cross shift substitution 🡒
      previous.sentence :=
  LO.Entailment.C_trans LO.Entailment.and₁
    (shiftContext_imp previous localField cross shift)

/-- The complete staged soundness context implies the previous master
certificate. -/
noncomputable def soundnessContext_imp
    (previous : ZFCTruthCertificateFields (V := V))
    (localField cross shift substitution axiomSound :
      Bootstrapping.Formula V ℒₛₑₜ) :
    T ⊢! soundnessContext previous localField cross shift substitution
        axiomSound 🡒 previous.sentence :=
  LO.Entailment.C_trans LO.Entailment.and₁
    (substitutionContext_imp previous localField cross shift substitution)

/-- Install a kernel whose compiled conclusion is a named field, from a
context weakening and a flat implication out of the previous certificate.
The predicate equality is discharged once, through `Entailment.cast`, so
no represented formula is ever compared definitionally inside a structure
literal. -/
noncomputable def kernelOfImplication
    {context previous field : Bootstrapping.Formula V ℒₛₑₜ}
    (predicate : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (hpredicate : (∀⁰ predicate) = field)
    (hcontext : T ⊢! context 🡒 previous)
    (himplication : T ⊢! previous 🡒 field) :
    UniversalKernel T context :=
  UniversalKernel.ofUniversalProof predicate
    (LO.Entailment.cast (LO.Entailment.C_trans hcontext himplication)
      (by rw [hpredicate]))

@[simp] theorem kernelOfImplication_predicate
    {context previous field : Bootstrapping.Formula V ℒₛₑₜ}
    (predicate : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (hpredicate : (∀⁰ predicate) = field)
    (hcontext : T ⊢! context 🡒 previous)
    (himplication : T ⊢! previous 🡒 field) :
    (kernelOfImplication predicate hpredicate hcontext himplication).predicate =
      predicate := rfl

end Contexts

/-! ## The six flat successor implications -/

/-- **The remaining mathematical obligation of the project, at one model
index.**

Six internal `𝗭𝗙𝗖` implications out of the level-`n` master certificate:
the five level-`(n+1)` truth laws of the concrete family, and the
internalized `Con_{n+1}(ZFC)`.  The extra field `conFormula` is the
well-formedness witness for the successor consistency code, which the
sixth implication's typed statement needs and which any actual proof of it
would supply. -/
structure ZFCSuccessorImplications (n : V)
    (h : IsFormula ℒₛₑₜ (conZFCSetCodeFun n)) where
  /-- Well-formedness of the internalized `Con_{n+1}(ZFC)` code. -/
  conFormula : IsFormula ℒₛₑₜ (conZFCSetCodeFun (n + 1))
  /-- The local polarity laws at level `n + 2`. -/
  localStep : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
    ((concreteZFCTruthCertificateFamily (V := V)).fields n h).sentence 🡒
      localStepFormula (n + 1)
  /-- Decidedness of `(n+1)`-bounded codes at level `n + 2`. -/
  crossLevel : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
    ((concreteZFCTruthCertificateFamily (V := V)).fields n h).sentence 🡒
      crossLevelFormula (n + 1)
  /-- The successor-shift substitution instance at level `n + 2`. -/
  shiftInvariant : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
    ((concreteZFCTruthCertificateFamily (V := V)).fields n h).sentence 🡒
      shiftInvariantFormula (n + 1)
  /-- The general substitution lemma at level `n + 2`. -/
  substitutionInvariant : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
    ((concreteZFCTruthCertificateFamily (V := V)).fields n h).sentence 🡒
      substitutionInvariantFormula (n + 1)
  /-- Axiom-code truth at level `n + 2`, bound `n + 1`. -/
  axiomSound : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
    ((concreteZFCTruthCertificateFamily (V := V)).fields n h).sentence 🡒
      axiomSoundFormula (n + 1)
  /-- The internalized `Con_{n+1}(ZFC)`. -/
  finalConsistency : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
    ((concreteZFCTruthCertificateFamily (V := V)).fields n h).sentence 🡒
      conZFCSetFormula (n + 1) conFormula

/-! ## The staged step built from them -/

/-- Assemble a dependency-ordered staged successor step out of the six flat
implications.  Each stage weakens its cumulative context back to the
previous master certificate and then applies the corresponding
implication. -/
noncomputable def stagedStepOfImplications (n : V)
    (h : IsFormula ℒₛₑₜ (conZFCSetCodeFun n))
    (S : ZFCSuccessorImplications n h) :
    ZFCStagedCertificateStep ((𝗭𝗙𝗖 : SetTheory).internalize V)
      ((concreteZFCTruthCertificateFamily (V := V)).fields n h) where
  localStep := localStepFormula (n + 1)
  proveLocalStep := S.localStep
  crossLevel :=
    kernelOfImplication (crossLevelPredicate (n + 1))
      (all_crossLevelPredicate (n + 1))
      (localContext_imp _ _) S.crossLevel
  shiftInvariant :=
    kernelOfImplication (shiftInvariantPredicate (n + 1))
      (all_shiftInvariantPredicate (n + 1))
      (crossContext_imp _ _ _) S.shiftInvariant
  substitutionInvariant :=
    kernelOfImplication (substitutionInvariantPredicate (n + 1))
      (all_substitutionInvariantPredicate (n + 1))
      (shiftContext_imp _ _ _ _) S.substitutionInvariant
  axiomSound :=
    kernelOfImplication (axiomSoundPredicate (n + 1))
      (all_axiomSoundPredicate (n + 1))
      (substitutionContext_imp _ _ _ _ _) S.axiomSound
  finalConsistency := conZFCSetFormula (n + 1) S.conFormula
  proveFinalConsistency :=
    LO.Entailment.C_trans (soundnessContext_imp _ _ _ _ _ _)
      S.finalConsistency

/-- The step's public six-field target is exactly the concrete family at
the next index. -/
theorem stagedStepOfImplications_target (n : V)
    (h : IsFormula ℒₛₑₜ (conZFCSetCodeFun n))
    (S : ZFCSuccessorImplications n h) :
    (stagedStepOfImplications n h S).target =
      (concreteZFCTruthCertificateFamily (V := V)).fields (n + 1)
        S.conFormula := by
  simp only [ZFCStagedCertificateStep.target, stagedStepOfImplications,
    ZFCTruthCertificateFamily.fields, kernelOfImplication_predicate,
    all_crossLevelPredicate, all_shiftInvariantPredicate,
    all_substitutionInvariantPredicate, all_axiomSoundPredicate,
    concreteZFCTruthCertificateFamily_localStep,
    concreteZFCTruthCertificateFamily_crossLevel,
    concreteZFCTruthCertificateFamily_shiftInvariant,
    concreteZFCTruthCertificateFamily_substitutionInvariant,
    concreteZFCTruthCertificateFamily_axiomSound]

/-- Raw-code form of the target identification, as the staged package
relation requires. -/
theorem stagedStepOfImplications_target_val (n : V)
    (h : IsFormula ℒₛₑₜ (conZFCSetCodeFun n))
    (S : ZFCSuccessorImplications n h) :
    (stagedStepOfImplications n h S).target.sentence.val =
      (concreteZFCTruthCertificateFamily (V := V)).code (n + 1) := by
  rw [show (concreteZFCTruthCertificateFamily (V := V)).code (n + 1) =
        ((concreteZFCTruthCertificateFamily (V := V)).fields (n + 1)
          S.conFormula).sentence.val from rfl]
  exact congrArg (fun F : ZFCTruthCertificateFields (V := V) ↦ F.sentence.val)
    (stagedStepOfImplications_target n h S)

/-! ## The reduction -/

/-- **The staged successor obligation reduces to the six flat
implications.**  Given, at every model index, internal `𝗭𝗙𝗖` proofs that
the level-`n` master certificate implies each of the six level-`(n+1)`
fields, the concrete family has a staged successor — and therefore, by
`zfcProofSelectorIn_of_concreteStagedSuccessor`, a model-internal proof
selector. -/
theorem hasStagedSuccessor_of_successorImplications
    (S : ∀ (n : V) (h : IsFormula ℒₛₑₜ (conZFCSetCodeFun n)),
      ZFCSuccessorImplications n h) :
    HasStagedSuccessor (concreteZFCTruthCertificateFamily (V := V)) := by
  intro n h
  exact ⟨stagedStepOfImplications n h (S n h),
    stagedStepOfImplications_target_val n h (S n h)⟩

/-- Propositional form of the reduction: only the existence of the six
implications matters. -/
theorem hasStagedSuccessor_of_nonempty_successorImplications
    (S : ∀ (n : V) (h : IsFormula ℒₛₑₜ (conZFCSetCodeFun n)),
      Nonempty (ZFCSuccessorImplications n h)) :
    HasStagedSuccessor (concreteZFCTruthCertificateFamily (V := V)) := by
  intro n h
  rcases S n h with ⟨s⟩
  exact ⟨stagedStepOfImplications n h s,
    stagedStepOfImplications_target_val n h s⟩

/-- The whole project, reduced to the six flat implications. -/
theorem zfcProofSelectorIn_of_successorImplications
    (S : ∀ (n : V) (h : IsFormula ℒₛₑₜ (conZFCSetCodeFun n)),
      Nonempty (ZFCSuccessorImplications n h)) :
    ZFCProofSelectorIn V :=
  zfcProofSelectorIn_of_concreteStagedSuccessor
    (hasStagedSuccessor_of_nonempty_successorImplications S)

/-! ## The converse: nothing is lost by flattening

A staged step whose public target code is the family's next master
certificate already contains the six flat implications.  Its four kernels
are stated at cumulative contexts, but each context is reached from the
previous certificate by the implications proved *before* it, so the whole
staircase collapses.  The code equality forces the five field
identifications by injectivity of the coded conjunction, and the sixth
conjunct's well-formedness — the one datum `ZFCSuccessorImplications`
carries besides the six proofs — is read off the step's own typed final
field. -/

section Converse

/-- The staged step's public target code, decomposed. -/
theorem stagedStep_target_sentence_val
    {previous : ZFCTruthCertificateFields (V := V)}
    (step : ZFCStagedCertificateStep
      ((𝗭𝗙𝗖 : SetTheory).internalize V) previous) :
    step.target.sentence.val =
      step.localStep.val ^⋏ ((∀⁰ step.crossLevel.predicate).val ^⋏
        ((∀⁰ step.shiftInvariant.predicate).val ^⋏
          ((∀⁰ step.substitutionInvariant.predicate).val ^⋏
            ((∀⁰ step.axiomSound.predicate).val ^⋏
              step.finalConsistency.val)))) := rfl

/-- The concrete family's master code, decomposed. -/
theorem concreteFamily_code_eq (x : V) :
    (concreteZFCTruthCertificateFamily (V := V)).code x =
      localStepCode x ^⋏ (crossLevelCode x ^⋏ (shiftInvariantCode x ^⋏
        (substitutionInvariantCode x ^⋏
          (axiomSoundCode x ^⋏ conZFCSetCodeFun x)))) := rfl

/-- **Every staged successor step yields the six flat implications.** -/
noncomputable def successorImplicationsOfStagedStep (n : V)
    (h : IsFormula ℒₛₑₜ (conZFCSetCodeFun n))
    (step : ZFCStagedCertificateStep ((𝗭𝗙𝗖 : SetTheory).internalize V)
      ((concreteZFCTruthCertificateFamily (V := V)).fields n h))
    (htarget : step.target.sentence.val =
      (concreteZFCTruthCertificateFamily (V := V)).code (n + 1)) :
    ZFCSuccessorImplications n h := by
  classical
  rw [stagedStep_target_sentence_val, concreteFamily_code_eq] at htarget
  simp only [qqAnd_inj] at htarget
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := htarget
  -- the five field identifications, typed
  have f1 : step.localStep = localStepFormula (n + 1) :=
    Bootstrapping.Semiformula.ext e1
  have f2 : (∀⁰ step.crossLevel.predicate) = crossLevelFormula (n + 1) :=
    Bootstrapping.Semiformula.ext e2
  have f3 : (∀⁰ step.shiftInvariant.predicate) =
      shiftInvariantFormula (n + 1) :=
    Bootstrapping.Semiformula.ext e3
  have f4 : (∀⁰ step.substitutionInvariant.predicate) =
      substitutionInvariantFormula (n + 1) :=
    Bootstrapping.Semiformula.ext e4
  have f5 : (∀⁰ step.axiomSound.predicate) = axiomSoundFormula (n + 1) :=
    Bootstrapping.Semiformula.ext e5
  -- well-formedness of the successor consistency code, from the step
  have hcon : IsFormula ℒₛₑₜ (conZFCSetCodeFun (n + 1)) := by
    have hs := step.finalConsistency.isSemiformula_zero
    rw [e6] at hs
    simpa using hs
  have f6 : step.finalConsistency = conZFCSetFormula (n + 1) hcon :=
    Bootstrapping.Semiformula.ext e6
  -- collapse the staircase of cumulative contexts
  have w1 : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      ((concreteZFCTruthCertificateFamily (V := V)).fields n h).sentence 🡒
        localContext ((concreteZFCTruthCertificateFamily (V := V)).fields n h)
          step.localStep :=
    LO.Entailment.right_K_intro LO.Entailment.C_id step.proveLocalStep
  have c2 := LO.Entailment.C_trans w1 step.crossLevel.compileImplication
  have w2 : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      ((concreteZFCTruthCertificateFamily (V := V)).fields n h).sentence 🡒
        crossContext ((concreteZFCTruthCertificateFamily (V := V)).fields n h)
          step.localStep (∀⁰ step.crossLevel.predicate) :=
    LO.Entailment.right_K_intro w1 c2
  have c3 := LO.Entailment.C_trans w2 step.shiftInvariant.compileImplication
  have w3 : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      ((concreteZFCTruthCertificateFamily (V := V)).fields n h).sentence 🡒
        shiftContext ((concreteZFCTruthCertificateFamily (V := V)).fields n h)
          step.localStep (∀⁰ step.crossLevel.predicate)
          (∀⁰ step.shiftInvariant.predicate) :=
    LO.Entailment.right_K_intro w2 c3
  have c4 :=
    LO.Entailment.C_trans w3 step.substitutionInvariant.compileImplication
  have w4 : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      ((concreteZFCTruthCertificateFamily (V := V)).fields n h).sentence 🡒
        substitutionContext
          ((concreteZFCTruthCertificateFamily (V := V)).fields n h)
          step.localStep (∀⁰ step.crossLevel.predicate)
          (∀⁰ step.shiftInvariant.predicate)
          (∀⁰ step.substitutionInvariant.predicate) :=
    LO.Entailment.right_K_intro w3 c4
  have c5 := LO.Entailment.C_trans w4 step.axiomSound.compileImplication
  have w5 : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      ((concreteZFCTruthCertificateFamily (V := V)).fields n h).sentence 🡒
        soundnessContext
          ((concreteZFCTruthCertificateFamily (V := V)).fields n h)
          step.localStep (∀⁰ step.crossLevel.predicate)
          (∀⁰ step.shiftInvariant.predicate)
          (∀⁰ step.substitutionInvariant.predicate)
          (∀⁰ step.axiomSound.predicate) :=
    LO.Entailment.right_K_intro w4 c5
  have c6 := LO.Entailment.C_trans w5 step.proveFinalConsistency
  exact
    { conFormula := hcon
      localStep := LO.Entailment.cast step.proveLocalStep (by rw [f1])
      crossLevel := LO.Entailment.cast c2 (by rw [f2])
      shiftInvariant := LO.Entailment.cast c3 (by rw [f3])
      substitutionInvariant := LO.Entailment.cast c4 (by rw [f4])
      axiomSound := LO.Entailment.cast c5 (by rw [f5])
      finalConsistency := LO.Entailment.cast c6 (by rw [f6]) }

/-- **The reduction is exact.**  The staged successor obligation for the
concrete family and the six flat implications at every index are
equivalent; neither direction loses information. -/
theorem hasStagedSuccessor_iff_successorImplications :
    HasStagedSuccessor (concreteZFCTruthCertificateFamily (V := V)) ↔
      ∀ (n : V) (h : IsFormula ℒₛₑₜ (conZFCSetCodeFun n)),
        Nonempty (ZFCSuccessorImplications n h) := by
  constructor
  · intro H n h
    rcases H n h with ⟨step, htarget⟩
    exact ⟨successorImplicationsOfStagedStep n h step htarget⟩
  · exact hasStagedSuccessor_of_nonempty_successorImplications

end Converse

end ZFCinPA
end LeanProofs
