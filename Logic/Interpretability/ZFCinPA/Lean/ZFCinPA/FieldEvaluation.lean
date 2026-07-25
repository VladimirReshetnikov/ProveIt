import ZFCinPA.TowerSuccessorEvaluation
import ZFCinPA.LocalStepSuccessor

/-!
# The evaluation bridge, part three: the certificate fields

Item 4 of the residue list in `ZFCinPA.LocalStepTransfer`.  With the
closure spine read (`ZFCinPA.SpineEvaluation`), each *certificate field*'s
source formula evaluates, in an arbitrary template structure, to the
corresponding abstract field bundle over the induced previous level
`TemplateEvaluation.templateLevel` — and its successor form to the same
bundle over `TemplateEvaluation.templateStepLevel`.

* `eval_srcLocalStep` / `eval_srcLocalStepSucc` —
  `LocalStepTransfer.LocalStepLaws`, the **first** certificate field, at
  the placeholder level and at the level one index up.

The two Tarski field readings (`EnlargedFields.TarskiElim` /
`TarskiIntro`) are *not* landed here; the residue section below states them
precisely, together with the one obligation the successor reading newly
exposes.
-/

set_option autoImplicit false
set_option maxRecDepth 8000

namespace LeanProofs
namespace ZFCinPA
namespace TemplateEvaluation

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.SetPlaceholders
open LeanProofs.ZFCinPA.SuccessorSources
open BoundedZFCConsistency
open SetTheory (Form ZFAxioms scons Sat vempty)

local notation "kpair'" => _root_.SetTheory.kpair

section Fields

variable {X : Type*} [Nonempty X] [sX : Structure srcL X] [Structure.Eq srcL X]

/-! ## The base correspondence at arity zero

A certificate field is a `Proposition srcL`, i.e. a formula of arity `0`;
its evaluation uses the trivial valuation `![]` together with a free
assignment `f`, which corresponds to the repository environment `f`
itself. -/

/-- The valuation correspondence a field reading starts from. -/
theorem corr0 (f : ℕ → X) : Corr (k := 0) ![] f f := Corr.zero f

/-! ## The first field -/

/-- **The local-step field evaluates to `LocalStepLaws` over the induced
previous level.** -/
theorem eval_srcLocalStep (f : ℕ → X) (H : ZFAxioms (templateMem X)) :
    Semiformula.Eval (s := sX) ![] f LocalStepSuccessor.srcLocalStep ↔
      LocalStepTransfer.LocalStepLaws H (templateLevel X H) := by
  have hco : ∀ x1 x0 : X,
      Corr (x0 :> x1 :> (![] : Fin 0 → X)) f (scons x0 (scons x1 f)) :=
    fun x1 x0 ↦ ((corr0 f).cons x1).cons x0
  have henv : ∀ x1 x0 : X, Semiformula.Eval (s := sX)
      (x0 :> x1 :> (![] : Fin 0 → X)) f (liftP (toSet 2 (fUnivEnvF 0))) ↔
      IsUnivEnv H x0 := fun x1 x0 ↦
    (eval_liftP (hco x1 x0) _).trans
      (fUnivEnvF_spec H (scons x0 (scons x1 f)) 0)
  have hbot : ∀ x1 x0 : X, Semiformula.Eval (s := sX)
      (x0 :> x1 :> (![] : Fin 0 → X)) f
        (liftP (toSet 2 (fTaggedEmptyF 1 2))) ↔
      x1 = EnlargedFields.botC H := fun x1 x0 ↦
    (eval_liftP (hco x1 x0) _).trans
      (fTaggedEmptyF_spec H (scons x0 (scons x1 f)) 1 2)
  have hcode : ∀ x1 x0 : X, Semiformula.Eval (s := sX)
      (x0 :> x1 :> (![] : Fin 0 → X)) f
        (liftP (toSet 2 (fIsFormCodeF 1))) ↔
      IsFormCodeSem H x1 := fun x1 x0 ↦
    (eval_liftP (hco x1 x0) _).trans
      (fIsFormCodeF_spec H (scons x0 (scons x1 f)) 1)
  have hsig : ∀ x1 x0 : X, Semiformula.Eval (s := sX)
      (x0 :> x1 :> (![] : Fin 0 → X)) f (srcCanonAt srcSigmaTrue) ↔
      templateLevel X H x1 x0 (natV H 1) := fun x1 x0 ↦
    eval_srcPolarAt 2 1 1 0 (hco x1 x0) H
  have hpit : ∀ x1 x0 : X, Semiformula.Eval (s := sX)
      (x0 :> x1 :> (![] : Fin 0 → X)) f (srcCanonAt srcPiTrue) ↔
      ¬ templateLevel X H x1 x0 (natV H 0) := fun x1 x0 ↦
    eval_srcCanonAtPair 2 1 0 srcPiTrue (hco x1 x0)
      (fun y1 y0 ↦ ¬ templateLevel X H y1 y0 (natV H 0))
      (fun y1 y0 ↦ by
        rw [srcPiTrue, LogicalConnective.HomClass.map_imply]
        exact imp_congr
          (eval_srcBitWitnessAt 4 0 (((hco x1 x0).cons y1).cons y0) H)
          (eval_liftP (((hco x1 x0).cons y1).cons y0) Form.fBot))
  have hfls : ∀ x1 x0 : X, Semiformula.Eval (s := sX)
      (x0 :> x1 :> (![] : Fin 0 → X)) f (liftP (toSet 2 Form.fBot)) ↔ False :=
    fun x1 x0 ↦ eval_liftP (hco x1 x0) Form.fBot
  simp only [LocalStepSuccessor.srcLocalStep, Semiformula.eval_all,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    henv, hbot, hcode, hsig, hpit, hfls]
  constructor
  · intro hh
    exact ⟨fun en hen ↦ (hh (EnlargedFields.botC H) en hen).1 rfl,
      fun c en hc hen ↦ (hh c en hen).2 hc⟩
  · intro hh x1 x0 hx0
    refine ⟨?_, fun hc ↦ hh.excl x1 x0 hc hx0⟩
    rintro rfl
    exact hh.botNotSigma x0 hx0

/-- **The local-step field one index up evaluates to `LocalStepLaws` over
the induced successor level.**  The spine is literally the same; only the
two canonical-slot payloads move one level. -/
theorem eval_srcLocalStepSucc (f : ℕ → X) (H : ZFAxioms (templateMem X)) :
    Semiformula.Eval (s := sX) ![] f LocalStepSuccessor.srcLocalStepSucc ↔
      LocalStepTransfer.LocalStepLaws H (templateStepLevel X H) := by
  have hco : ∀ x1 x0 : X,
      Corr (x0 :> x1 :> (![] : Fin 0 → X)) f (scons x0 (scons x1 f)) :=
    fun x1 x0 ↦ ((corr0 f).cons x1).cons x0
  have henv : ∀ x1 x0 : X, Semiformula.Eval (s := sX)
      (x0 :> x1 :> (![] : Fin 0 → X)) f (liftP (toSet 2 (fUnivEnvF 0))) ↔
      IsUnivEnv H x0 := fun x1 x0 ↦
    (eval_liftP (hco x1 x0) _).trans
      (fUnivEnvF_spec H (scons x0 (scons x1 f)) 0)
  have hbot : ∀ x1 x0 : X, Semiformula.Eval (s := sX)
      (x0 :> x1 :> (![] : Fin 0 → X)) f
        (liftP (toSet 2 (fTaggedEmptyF 1 2))) ↔
      x1 = EnlargedFields.botC H := fun x1 x0 ↦
    (eval_liftP (hco x1 x0) _).trans
      (fTaggedEmptyF_spec H (scons x0 (scons x1 f)) 1 2)
  have hcode : ∀ x1 x0 : X, Semiformula.Eval (s := sX)
      (x0 :> x1 :> (![] : Fin 0 → X)) f
        (liftP (toSet 2 (fIsFormCodeF 1))) ↔
      IsFormCodeSem H x1 := fun x1 x0 ↦
    (eval_liftP (hco x1 x0) _).trans
      (fIsFormCodeF_spec H (scons x0 (scons x1 f)) 1)
  have hsig : ∀ x1 x0 : X, Semiformula.Eval (s := sX)
      (x0 :> x1 :> (![] : Fin 0 → X)) f (srcCanonAt srcSigmaTrueSucc) ↔
      templateStepLevel X H x1 x0 (natV H 1) := fun x1 x0 ↦
    eval_srcPolarAtSucc 2 1 1 0 (hco x1 x0) H
  have hpit : ∀ x1 x0 : X, Semiformula.Eval (s := sX)
      (x0 :> x1 :> (![] : Fin 0 → X)) f (srcCanonAt srcPiTrueSucc) ↔
      ¬ templateStepLevel X H x1 x0 (natV H 0) := fun x1 x0 ↦
    eval_srcCanonAtPair 2 1 0 srcPiTrueSucc (hco x1 x0)
      (fun y1 y0 ↦ ¬ templateStepLevel X H y1 y0 (natV H 0))
      (fun y1 y0 ↦ by
        rw [srcPiTrueSucc, LogicalConnective.HomClass.map_imply]
        exact imp_congr
          (eval_srcBitWitnessSuccAt 4 0 (((hco x1 x0).cons y1).cons y0) H)
          (eval_liftP (((hco x1 x0).cons y1).cons y0) Form.fBot))
  have hfls : ∀ x1 x0 : X, Semiformula.Eval (s := sX)
      (x0 :> x1 :> (![] : Fin 0 → X)) f (liftP (toSet 2 Form.fBot)) ↔ False :=
    fun x1 x0 ↦ eval_liftP (hco x1 x0) Form.fBot
  simp only [LocalStepSuccessor.srcLocalStepSucc, Semiformula.eval_all,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    henv, hbot, hcode, hsig, hpit, hfls]
  constructor
  · intro hh
    exact ⟨fun en hen ↦ (hh (EnlargedFields.botC H) en hen).1 rfl,
      fun c en hc hen ↦ (hh c en hen).2 hc⟩
  · intro hh x1 x0 hx0
    refine ⟨?_, fun hc ↦ hh.excl x1 x0 hc hx0⟩
    rintro rfl
    exact hh.botNotSigma x0 hx0

end Fields

/-! ## Residue

The evaluation bridge is complete for the **first** certificate field:
`eval_srcLocalStep` and `eval_srcLocalStepSucc` read `srcLocalStep` and
`srcLocalStepSucc`, in an arbitrary template structure with genuine
equality, as `LocalStepTransfer.LocalStepLaws` at `templateLevel` and at
`templateStepLevel` respectively.  What remains between that and a source
derivation is stated here.

1. **The two Tarski field readings.**  For an abstract polarized gadget
   `P` with a uniform reading `L`, the three skeletons of
   `ZFCinPA.TarskiSources` evaluate as

   * `srcConnSpine t body` — `∀ a₁ a₂ e`, with `IsFormCodeSem` on `a₁`,
     `a₂` and `IsUnivEnv` on `e`, of `body` at the four slots
     `(a₁, a₂, e, kpair (natV t) (kpair a₁ a₂))`;
   * `srcQuantSpine t body` — `∀ a e d`, with `IsFormCodeSem H a` and
     `IsUnivEnv H e`, of `body` at the five slots
     `(a, e, d, kpair (natV t) a, econs d e)` — the fourth premise is
     `fEconsF`, whose `Sat` specification consumes the *second* premise, so
     this reading is a nested-implication argument rather than a
     congruence;
   * `srcBotPiOf P` — `∀ e, IsUnivEnv H e → L (botC H) e (natV H 0)`.

   With those, `srcTarskiElimOf P`/`srcTarskiIntroOf P` evaluate to
   `EnlargedFields.TarskiElim H L`/`TarskiIntro H L` by matching the eight
   and nine rows against the structure fields, and the four headline
   readings are the instances at `srcPolarAt` (`L := templateLevel`) and
   `srcPolarAtSucc` (`L := templateStepLevel`), through
   `TowerEvaluation.eval_srcPolarAt` and
   `TowerSuccessorEvaluation.eval_srcPolarAtSucc`.  Estimated 350–450 LOC.

2. **A source `crossLevel` field.**  `ZFCinPA.LocalStepTransfer`'s
   `LevelLaws` also needs the *decidedness* conjunct
   `∀ c e, IsFormCodeSem H c → IsUnivEnv H e → QuantBounded H b c →
   L c e (natV H 1) ∨ L c e (natV H 0)`.  No source formula for it exists
   yet — `srcCrossLevel` is not defined anywhere in the project — so it has
   to be written in `ZFCinPA.SuccessorSources`' style and then read here.
   Estimated 120–180 LOC (source formula, translation identity,
   free-variable-freeness, evaluation).

3. **The numeral placeholder is not pinned.**  `templateStepLevel`
   existentially quantifies the bound: `∃ k, Num k ∧ Step H L k⁺ c e b`.
   That is forced by the source syntax — `srcNumChainSucc` says only "the
   next index is the successor of *some* `Num`" — and it is *weaker* than
   what `LocalStepTransfer.localStepLaws_step` concludes, which fixes one
   `b`.  Two occurrences of the successor reading may therefore pick
   different witnesses, and the exclusivity conjunct genuinely needs the
   same one.  So the assembled source sentence must carry, besides
   `srcNumOmega` ("every `Num` is a natural", the `hb : mem b (omegaV H)`
   hypothesis of `localStepLaws_step`), a **`Num`-uniqueness** antecedent
   `∀ k k', Num k → Num k' → k = k'`.  After translation `Num` becomes
   `numChainCode x`, which defines exactly the numeral of `x`, so both are
   dischargeable; but neither is implied by any certificate field, and
   neither was recorded before.  This is the counterpart, for the numeral
   placeholder, of the `hb` obligation `ZFCinPA.LocalStepTransfer` records.

4. **The two remaining hypotheses of `localStepLaws_step`.**  `hL`
   (`EnlargedFields.LevelLaws`, i.e. items 1 and 2 above) and `hind`
   (`EnlargedFields.CodeInduction` at `StepGood`) still have to become
   source antecedents.  `hind` is Separation for a placeholder formula, to
   be discharged after translation by
   `ZFCinPA.SeparationKernel.zfcSeparationProofOfShiftFixed`; there is no
   source formula for it yet.

5. **Assembly.**  With 1–4 in place, the source sentence
   `(srcNumOmega ⋏ srcNumUnique ⋏ srcCodeInduction ⋏ srcLaws) 🡒
   srcLocalStepSucc` is proved in every template structure by
   `LocalStepTransfer.localStepLaws_step`, and
   `SetPlaceholderQuotient.complete_underSetPlaceholderCongruence` turns
   that into
   `templateZFC 2 levelArities ⊢! setPlaceholderCongruence 🡒 …`.
   Estimated 200–300 LOC.

Nothing above is assumed anywhere in this project, and nothing here
weakens `StagedSuccessor.ZFCSuccessorImplications`. -/

end TemplateEvaluation
end ZFCinPA
end LeanProofs
