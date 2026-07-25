import ZFCinPA.TemplateEvaluation

/-!
# The evaluation bridge, part two: the closure spine

This module is item 3 of the residue list in
`ZFCinPA.LocalStepTransfer` — the bulk of the evaluation bridge.  It reads
the source spine of `ZFCinPA.SuccessorSources` in an arbitrary template
structure and identifies it, slot by slot, with goal 2's abstract closure
vocabulary over the *induced previous level*
`TemplateEvaluation.templateLevel`.

The correspondence is exact, not approximate: each source formula is the
placeholder-lifted counterpart of one of goal 2's `Form` macros, at the
same de Bruijn slots, so each lemma below is the source-level twin of the
corresponding `…_spec` theorem of
`BoundedZFCConsistency.UniverseTruthLevel`:

| source formula      | goal-2 macro                       |
| ------------------- | ---------------------------------- |
| `srcLvlInstP m ρ`   | the previous-level slot `lF`       |
| `srcAllClause m`    | `fLevelAllF lF 4 3 2 6 1 0 5`      |
| `srcExClause m`     | `fLevelExF lF 4 3 2 6 1 0 5`       |
| `srcJustRow m`      | `fLevelJustifiedF lF 2 1 0 4 3`    |
| `srcClosStep m`     | `fLevelClosedF lF 0 1`             |

so `srcClosStep` reads slot `0` as the previous level's bound and slot `1`
as the certificate, and `srcJustRow` reads slots `0, 1, 2, 3, 4` as the
bit, the environment, the code, the bound and the certificate.

Every fixed leaf is discharged by its own `Sat` specification; the only
genuinely new content is the previous-level slot, which at source level is
the two-existential placeholder gadget `srcLvlInstP` rather than a `Form`,
and is therefore the reason none of goal 2's `…_spec` theorems can simply
be reused.

**No arity side conditions.**  The translation lemmas of
`ZFCinPA.SuccessorSources` need `m` large enough for every fixed leaf's
slots to stay bound; the *evaluation* lemmas do not, because
`TemplateEvaluation.Corr` reads bound and free Foundation slots into the
one repository environment uniformly.  So each lemma below holds at every
ambient arity.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

namespace LeanProofs
namespace ZFCinPA
namespace TemplateEvaluation

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.SetPlaceholders
open LeanProofs.ZFCinPA.SuccessorSources
open BoundedZFCConsistency
open SetTheory (Form ZFAxioms scons Sat)

local notation "kpair'" => _root_.SetTheory.kpair

section Spine

variable {X : Type*} [Nonempty X] [sX : Structure srcL X] [Structure.Eq srcL X]

/-! ## The previous-level slot -/

/-- **The unfolded-instance shape evaluates to its two-existential
reading.**  The two placeholders are opaque, so this is as far as the
source syntax can be resolved: the numeral witness `n`, the certificate
`C`, and the atom read in the extended environment. -/
theorem eval_srcLvlInstP (m : ℕ) (atom : Form) {b : Fin m → X} {f e : ℕ → X}
    (h : Corr b f e) :
    Semiformula.Eval (s := sX) b f (srcLvlInstP m atom) ↔
      ∃ C n, templateNum X n ∧ templateClos X n C ∧
        Sat (templateMem X) (scons n (scons C e)) atom := by
  rw [srcLvlInstP, srcLvlInst, Semiformula.eval_ex]
  refine exists_congr fun C ↦ ?_
  rw [Semiformula.eval_ex]
  refine exists_congr fun n ↦ ?_
  rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_and,
    eval_srcNumAt, eval_srcClsAt, eval_liftP ((h.cons C).cons n)]
  exact Iff.rfl

/-- **The unfolded-instance shape at arbitrary numeral and closure
readings.**  `eval_srcLvlInstP` is the instance where both slots are the
placeholders themselves; `srcLevelSatSuccAt` is the instance where they are
the two successor spines. -/
theorem eval_srcLvlInst (m : ℕ) (atom : Form)
    (num cls : Semiproposition srcL (m + 1 + 1)) {b : Fin m → X}
    {f e : ℕ → X} (h : Corr b f e) (Pn Pc : X → X → Prop)
    (hn : ∀ C n : X,
      Semiformula.Eval (s := sX) (n :> C :> b) f num ↔ Pn C n)
    (hcl : ∀ C n : X,
      Semiformula.Eval (s := sX) (n :> C :> b) f cls ↔ Pc C n) :
    Semiformula.Eval (s := sX) b f (srcLvlInst m atom num cls) ↔
      ∃ C n, Pn C n ∧ Pc C n ∧
        Sat (templateMem X) (scons n (scons C e)) atom := by
  rw [srcLvlInst, Semiformula.eval_ex]
  refine exists_congr fun C ↦ ?_
  rw [Semiformula.eval_ex]
  refine exists_congr fun n ↦ ?_
  rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_and,
    hn C n, hcl C n, eval_liftP ((h.cons C).cons n)]
  exact Iff.rfl

/-- **The previous-level slot is the induced previous level.**  This is the
source-level counterpart of the hypothesis `hl` that every one of goal 2's
level `…_spec` theorems carries. -/
theorem eval_srcLvlInstP_triple (m ci ei bi : ℕ) {b : Fin m → X}
    {f e : ℕ → X} (h : Corr b f e) (H : ZFAxioms (templateMem X)) :
    Semiformula.Eval (s := sX) b f
        (srcLvlInstP m (fTripleMemF (ci + 2) (ei + 2) (bi + 2) 1)) ↔
      templateLevel X H (e ci) (e ei) (e bi) := by
  rw [eval_srcLvlInstP m _ h, templateLevel]
  constructor
  · rintro ⟨C, n, hn, hc, hm⟩
    exact ⟨n, C, hn, hc,
      (fTripleMemF_spec H (scons n (scons C e))
        (ci + 2) (ei + 2) (bi + 2) 1).mp hm⟩
  · rintro ⟨n, C, hn, hc, hm⟩
    exact ⟨C, n, hn, hc,
      (fTripleMemF_spec H (scons n (scons C e))
        (ci + 2) (ei + 2) (bi + 2) 1).mpr hm⟩

/-! ## The two quantifier clauses

Source twins of `fLevelAllF_spec` and `fLevelExF_spec` at the slot
assignment `c_i = 4`, `e_i = 3`, `b_i = 2`, `s_i = 6`, `z_i = 1`,
`o_i = 0`, `bnd_i = 5` — which is where `fLevelJustifiedF` places them
once its two numeral binders are in place. -/

/-- **The universal clause.**  A counterexample is recorded on the false
side; the true side is delegated to the induced previous level under the
Pi-bound. -/
theorem eval_srcAllClause (m : ℕ) {b : Fin m → X} {f e : ℕ → X}
    (h : Corr b f e) (H : ZFAxioms (templateMem X))
    (hE : IsUnivEnv H (e 3)) :
    Semiformula.Eval (s := sX) b f (srcAllClause m) ↔
      ∃ c1, e 4 = kpair' H (natV H 6) c1 ∧
        ((e 2 = e 0 ∧ PiBounded H (e 5) (e 4) ∧
            ¬ templateLevel X H (e 4) (e 3) (e 1)) ∨
         (e 2 = e 1 ∧ ∃ d,
            templateMem X (satTriple H c1 (econs H d (e 3)) (natV H 0))
              (e 6))) := by
  rw [srcAllClause, Semiformula.eval_ex]
  refine exists_congr fun c1 ↦ ?_
  have hc := h.cons c1
  rw [LogicalConnective.HomClass.map_and]
  refine and_congr ((eval_liftP hc (fTagUnF 5 6 0)).trans
    (fTagUnF_spec H (scons c1 e) 5 6 0)) ?_
  rw [LogicalConnective.HomClass.map_or]
  refine or_congr ?_ ?_
  · rw [LogicalConnective.HomClass.map_and]
    refine and_congr (eval_liftP hc (Form.fEq 3 1)) ?_
    rw [LogicalConnective.HomClass.map_and]
    refine and_congr ((eval_liftP hc (fPiBoundedF 6 5)).trans
      (fPiBoundedF_spec H (scons c1 e) 6 5)) ?_
    rw [LogicalConnective.HomClass.map_imply]
    exact imp_congr (eval_srcLvlInstP_triple (m + 1) 5 4 2 hc H)
      (eval_liftP hc Form.fBot)
  · exact (eval_liftP hc
      (Form.fAnd (Form.fEq 3 2)
        (Form.fEx (fShiftTripleMemF 1 0 5 8 0)))).trans
      (and_congr Iff.rfl (exists_congr fun d ↦
        fShiftTripleMemF_spec H (scons d (scons c1 e)) 1 0 5 8 0 hE.1))

/-- **The existential clause**, the dual of `eval_srcAllClause`: a witness
is recorded on the true side, and the false side is delegated under the
Sigma-bound. -/
theorem eval_srcExClause (m : ℕ) {b : Fin m → X} {f e : ℕ → X}
    (h : Corr b f e) (H : ZFAxioms (templateMem X))
    (hE : IsUnivEnv H (e 3)) :
    Semiformula.Eval (s := sX) b f (srcExClause m) ↔
      ∃ c1, e 4 = kpair' H (natV H 7) c1 ∧
        ((e 2 = e 0 ∧ ∃ d,
            templateMem X (satTriple H c1 (econs H d (e 3)) (natV H 1))
              (e 6)) ∨
         (e 2 = e 1 ∧ SigmaBounded H (e 5) (e 4) ∧
            ¬ templateLevel X H (e 4) (e 3) (e 0))) := by
  rw [srcExClause, Semiformula.eval_ex]
  refine exists_congr fun c1 ↦ ?_
  have hc := h.cons c1
  rw [LogicalConnective.HomClass.map_and]
  refine and_congr ((eval_liftP hc (fTagUnF 5 7 0)).trans
    (fTagUnF_spec H (scons c1 e) 5 7 0)) ?_
  rw [LogicalConnective.HomClass.map_or]
  refine or_congr ?_ ?_
  · exact (eval_liftP hc
      (Form.fAnd (Form.fEq 3 1)
        (Form.fEx (fShiftTripleMemF 1 0 5 8 1)))).trans
      (and_congr Iff.rfl (exists_congr fun d ↦
        fShiftTripleMemF_spec H (scons d (scons c1 e)) 1 0 5 8 1 hE.1))
  · rw [LogicalConnective.HomClass.map_and]
    refine and_congr (eval_liftP hc (Form.fEq 3 2)) ?_
    rw [LogicalConnective.HomClass.map_and]
    refine and_congr ((eval_liftP hc (fSigmaBoundedF 6 5)).trans
      (fSigmaBoundedF_spec H (scons c1 e) 6 5)) ?_
    rw [LogicalConnective.HomClass.map_imply]
    exact imp_congr (eval_srcLvlInstP_triple (m + 1) 5 4 1 hc H)
      (eval_liftP hc Form.fBot)

/-! ## The justification row

Source twin of `fLevelJustifiedF_spec` at `c_i = 2`, `e_i = 1`, `b_i = 0`,
`s_i = 4`, `bnd_i = 3` — the slot assignment `fLevelClosedF` imposes.  The
two outermost binders hold the numerals `0` and `1`, exactly as in goal 2,
so that a subrecord's bit is a slot rather than a constant. -/

/-- **The justification row evaluates to `LevelJustified` over the induced
previous level.**  All six disjuncts, slot by slot. -/
theorem eval_srcJustRow (m : ℕ) {b : Fin m → X} {f e : ℕ → X}
    (h : Corr b f e) (H : ZFAxioms (templateMem X))
    (hE : IsUnivEnv H (e 1)) :
    Semiformula.Eval (s := sX) b f (srcJustRow m) ↔
      LevelJustified H (templateLevel X H) (e 3) (e 4) (e 2) (e 1) (e 0) := by
  have hnum : ∀ z o : X, Semiformula.Eval (s := sX) (o :> z :> b) f
      (liftP (toSet (m + 1 + 1) (Form.fAnd (fNumF 1 0) (fNumF 0 1)))) ↔
      (z = natV H 0 ∧ o = natV H 1) := fun z o ↦
    (eval_liftP ((h.cons z).cons o) _).trans
      (and_congr (fNumF_spec H 0 1 (scons o (scons z e)))
        (fNumF_spec H 1 0 (scons o (scons z e))))
  have hdel : ∀ z o : X, Semiformula.Eval (s := sX) (o :> z :> b) f
      (srcLvlInstP (m + 1 + 1) (fTripleMemF 6 5 4 1)) ↔
      templateLevel X H (e 2) (e 1) (e 0) := fun z o ↦
    eval_srcLvlInstP_triple (m + 1 + 1) 4 3 2 ((h.cons z).cons o) H
  have himp : ∀ z o : X, Semiformula.Eval (s := sX) (o :> z :> b) f
      (liftP (toSet (m + 1 + 1) (fLevelImpF 4 3 2 6 1 0))) ↔
      (∃ c1 c2, e 2 = kpair' H (natV H 3) (kpair' H c1 c2) ∧
        ((e 0 = o ∧ (templateMem X (satTriple H c1 (e 1) z) (e 4) ∨
                     templateMem X (satTriple H c2 (e 1) o) (e 4))) ∨
         (e 0 = z ∧ templateMem X (satTriple H c1 (e 1) o) (e 4) ∧
                    templateMem X (satTriple H c2 (e 1) z) (e 4)))) :=
    fun z o ↦ (eval_liftP ((h.cons z).cons o) _).trans
      (fLevelImpF_spec H (scons o (scons z e)) 4 3 2 6 1 0)
  have hand : ∀ z o : X, Semiformula.Eval (s := sX) (o :> z :> b) f
      (liftP (toSet (m + 1 + 1) (fLevelAndF 4 3 2 6 1 0))) ↔
      (∃ c1 c2, e 2 = kpair' H (natV H 4) (kpair' H c1 c2) ∧
        ((e 0 = o ∧ templateMem X (satTriple H c1 (e 1) o) (e 4) ∧
                    templateMem X (satTriple H c2 (e 1) o) (e 4)) ∨
         (e 0 = z ∧ (templateMem X (satTriple H c1 (e 1) z) (e 4) ∨
                     templateMem X (satTriple H c2 (e 1) z) (e 4))))) :=
    fun z o ↦ (eval_liftP ((h.cons z).cons o) _).trans
      (fLevelAndF_spec H (scons o (scons z e)) 4 3 2 6 1 0)
  have hor : ∀ z o : X, Semiformula.Eval (s := sX) (o :> z :> b) f
      (liftP (toSet (m + 1 + 1) (fLevelOrF 4 3 2 6 1 0))) ↔
      (∃ c1 c2, e 2 = kpair' H (natV H 5) (kpair' H c1 c2) ∧
        ((e 0 = o ∧ (templateMem X (satTriple H c1 (e 1) o) (e 4) ∨
                     templateMem X (satTriple H c2 (e 1) o) (e 4))) ∨
         (e 0 = z ∧ templateMem X (satTriple H c1 (e 1) z) (e 4) ∧
                    templateMem X (satTriple H c2 (e 1) z) (e 4)))) :=
    fun z o ↦ (eval_liftP ((h.cons z).cons o) _).trans
      (fLevelOrF_spec H (scons o (scons z e)) 4 3 2 6 1 0)
  have hall : ∀ z o : X, Semiformula.Eval (s := sX) (o :> z :> b) f
      (srcAllClause (m + 1 + 1)) ↔
      (∃ c1, e 2 = kpair' H (natV H 6) c1 ∧
        ((e 0 = o ∧ PiBounded H (e 3) (e 2) ∧
            ¬ templateLevel X H (e 2) (e 1) z) ∨
         (e 0 = z ∧ ∃ d,
            templateMem X (satTriple H c1 (econs H d (e 1)) (natV H 0))
              (e 4)))) := fun z o ↦
    eval_srcAllClause (m + 1 + 1) ((h.cons z).cons o) H hE
  have hex : ∀ z o : X, Semiformula.Eval (s := sX) (o :> z :> b) f
      (srcExClause (m + 1 + 1)) ↔
      (∃ c1, e 2 = kpair' H (natV H 7) c1 ∧
        ((e 0 = o ∧ ∃ d,
            templateMem X (satTriple H c1 (econs H d (e 1)) (natV H 1))
              (e 4)) ∨
         (e 0 = z ∧ SigmaBounded H (e 3) (e 2) ∧
            ¬ templateLevel X H (e 2) (e 1) o))) := fun z o ↦
    eval_srcExClause (m + 1 + 1) ((h.cons z).cons o) H hE
  simp only [srcJustRow, Semiformula.eval_ex,
    LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_or,
    hnum, hdel, himp, hand, hor, hall, hex]
  constructor
  · rintro ⟨z, o, ⟨rfl, rfl⟩, hd⟩
    exact hd
  · intro hd
    exact ⟨natV H 0, natV H 1, ⟨rfl, rfl⟩, hd⟩

/-! ## The closure step

Source twin of `fLevelClosedF_spec` at `bnd_i = 0`, `s_i = 1`: slot `0` of
the ambient arity is the previous level's bound, slot `1` is the
certificate.  The environment clause is not decoration — the justification
row's two quantifier clauses need it, which is why the reading is a genuine
two-direction argument rather than a congruence. -/

/-- **The closure step evaluates to `LevelClosed` over the induced previous
level.** -/
theorem eval_srcClosStep (m : ℕ) {b : Fin m → X} {f e : ℕ → X}
    (h : Corr b f e) (H : ZFAxioms (templateMem X)) :
    Semiformula.Eval (s := sX) b f (srcClosStep m) ↔
      LevelClosed H (templateLevel X H) (e 0) (e 1) := by
  rw [srcClosStep]
  simp only [Semiformula.eval_all, LogicalConnective.HomClass.map_imply,
    LogicalConnective.HomClass.map_and]
  constructor
  · intro hh c en bi hmem
    have hc := ((h.cons c).cons en).cons bi
    have hpre : Semiformula.Eval (s := sX) (bi :> en :> c :> b) f
        (liftP (toSet (m + 1 + 1 + 1) (fTripleMemF 2 1 0 4))) :=
      (eval_liftP hc (fTripleMemF 2 1 0 4)).mpr
        ((fTripleMemF_spec H (scons bi (scons en (scons c e))) 2 1 0 4).mpr
          hmem)
    obtain ⟨h1, h2⟩ := hh c en bi hpre
    have henv : IsUnivEnv H en :=
      (fUnivEnvF_spec H (scons bi (scons en (scons c e))) 1).mp
        ((eval_liftP hc (fUnivEnvF 1)).mp h1)
    exact ⟨henv, (eval_srcJustRow (m + 1 + 1 + 1) hc H henv).mp h2⟩
  · intro hh c en bi hpre
    have hc := ((h.cons c).cons en).cons bi
    have hmem :=
      (fTripleMemF_spec H (scons bi (scons en (scons c e))) 2 1 0 4).mp
        ((eval_liftP hc (fTripleMemF 2 1 0 4)).mp hpre)
    obtain ⟨henv, hj⟩ := hh c en bi hmem
    exact ⟨(eval_liftP hc (fUnivEnvF 1)).mpr
        ((fUnivEnvF_spec H (scons bi (scons en (scons c e))) 1).mpr henv),
      (eval_srcJustRow (m + 1 + 1 + 1) hc H henv).mpr hj⟩

end Spine

end TemplateEvaluation
end ZFCinPA
end LeanProofs
