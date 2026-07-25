import ZFCinPA.FieldEvaluation

/-!
# The evaluation bridge, part four: the two Tarski certificate fields

Item 1 of the residue list in `ZFCinPA.FieldEvaluation`.  With the closure
spine read (`ZFCinPA.SpineEvaluation`) and the level tower read at an
arbitrary ambient arity and slot pair (`ZFCinPA.TowerEvaluation`,
`ZFCinPA.TowerSuccessorEvaluation`), the two Tarski field sources of
`ZFCinPA.TarskiSources` evaluate, in an arbitrary template structure with
genuine equality, to the abstract field bundles
`EnlargedFields.TarskiElim` / `EnlargedFields.TarskiIntro` over the induced
previous level `TemplateEvaluation.templateLevel` — and their successor
forms to the same bundles over `TemplateEvaluation.templateStepLevel`.

## The three skeletons

`ZFCinPA.TarskiSources` assembles both fields from three coded skeletons.
Each is read here once, of an *arbitrary* body, so that the eight
elimination and nine introduction rows are matched against the structure
fields without re-deriving the spine seventeen times.

| skeleton              | binders | slot layout (slot `4 … 0`)                            |
| --------------------- | ------- | ----------------------------------------------------- |
| `srcConnSpine t body` | four    | `a₁`, `a₂`, `e`, `⟨t, ⟨a₁, a₂⟩⟩`                      |
| `srcQuantSpine t body`| five    | `a`, `e`, `d`, `⟨t, a⟩`, `econs d e`                   |
| `srcBotPiOf P`        | two     | `e`, `botC`                                           |

The connective skeleton's four premises (`fIsFormCodeF 3`,
`fIsFormCodeF 2`, `fUnivEnvF 1`, `fTagPairF 0 t 3 2`) and the falsity row's
two (`fUnivEnvF 1`, `fTaggedEmptyF 0 2`) are all *independent* leaves, so
those two readings are congruence rewrites followed by the elimination of
the pinning equation.

**The quantifier skeleton is not.**  Its fourth premise is
`fEconsF 0 2 3`, and `BoundedZFCConsistency.fEconsF_spec` carries the
single-valuedness hypothesis
`∀ x y y', ⟨x,y⟩ ∈ e → ⟨x,y'⟩ ∈ e → y = y'`, which is available only from
the *second* premise `fUnivEnvF 3` (it is `IsUnivEnv.1`).  So
`eval_srcQuantSpine` is proved as a nested-implication argument in both
directions — the fourth premise's reading is a conditional iff, applied
under the environment premise — and not as a congruence.  Attempting it as
a congruence is the predictable way to lose time here; the shape of
`hecons` below is the whole content of the warning.

## The polarized gadget

Both fields are stated in `ZFCinPA.TarskiSources` over an abstract
polarized gadget `P : (m w ci ei : ℕ) → Semiproposition srcL m`.  Its
reading is abstracted here as `PolarReading`: `P m w ci ei` reads, under
any environment correspondence, as `L (e ci) (e ei) (natV H w)`.  The two
instances are `TowerEvaluation.eval_srcPolarAt` (`L := templateLevel`) and
`TowerSuccessorEvaluation.eval_srcPolarAtSucc` (`L := templateStepLevel`),
which is why the four headline readings are four applications of the same
two theorems.

**No arity side conditions.**  As in `ZFCinPA.SpineEvaluation`, the
evaluation side needs none: `TemplateEvaluation.Corr` reads bound and free
Foundation slots into the one repository environment uniformly.  The
`ci < m`, `ei < m` hypotheses of the *translation* lemmas have no
counterpart here.

Nothing in this module is assumed anywhere, and nothing here weakens
`StagedSuccessor.ZFCSuccessorImplications`.
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

section Skeletons

variable {X : Type*} [Nonempty X] [sX : Structure srcL X] [Structure.Eq srcL X]

/-! ## The three base correspondences

Each skeleton is a `Proposition srcL`, i.e. a formula of arity `0`, so
every reading starts from `FieldEvaluation.corr0` and steps once through
each binder. -/

/-- The two-slot correspondence the falsity row runs at: slot `1` is the
environment, slot `0` the falsity code. -/
theorem corr2 (f : ℕ → X) (en bt : X) :
    Corr (bt :> en :> (![] : Fin 0 → X)) f (scons bt (scons en f)) :=
  ((corr0 f).cons en).cons bt

/-- The four-slot correspondence the connective skeleton runs at: slots
`3, 2, 1, 0` are the two subcodes, the environment and the compound code. -/
theorem corr4 (f : ℕ → X) (a1 a2 en c : X) :
    Corr (c :> en :> a2 :> a1 :> (![] : Fin 0 → X)) f
      (scons c (scons en (scons a2 (scons a1 f)))) :=
  ((((corr0 f).cons a1).cons a2).cons en).cons c

/-- The five-slot correspondence the quantifier skeleton runs at: slots
`4, 3, 2, 1, 0` are the matrix code, the environment, the witness, the
compound code and the extended environment. -/
theorem corr5 (f : ℕ → X) (a en d c ec : X) :
    Corr (ec :> c :> d :> en :> a :> (![] : Fin 0 → X)) f
      (scons ec (scons c (scons d (scons en (scons a f))))) :=
  (((((corr0 f).cons a).cons en).cons d).cons c).cons ec

/-! ## The connective skeleton -/

/-- **The connective skeleton evaluates to its four-slot reading.**  The
tag guard pins the fourth binder, so the outer universal quantifier over
it disappears and the body is read at the compound code
`⟨natV t, ⟨a₁, a₂⟩⟩`. -/
theorem eval_srcConnSpine (f : ℕ → X) (H : ZFAxioms (templateMem X)) (t : ℕ)
    (body : Semiproposition srcL 4) (Q : X → X → X → X → Prop)
    (hbody : ∀ a1 a2 en c : X,
      Semiformula.Eval (s := sX)
        (c :> en :> a2 :> a1 :> (![] : Fin 0 → X)) f body ↔ Q a1 a2 en c) :
    Semiformula.Eval (s := sX) ![] f (srcConnSpine t body) ↔
      ∀ a1 a2 en : X, IsFormCodeSem H a1 → IsFormCodeSem H a2 →
        IsUnivEnv H en →
          Q a1 a2 en (kpair' H (natV H t) (kpair' H a1 a2)) := by
  have hc1 : ∀ a1 a2 en c : X, Semiformula.Eval (s := sX)
      (c :> en :> a2 :> a1 :> (![] : Fin 0 → X)) f
        (liftP (toSet 4 (fIsFormCodeF 3))) ↔ IsFormCodeSem H a1 :=
    fun a1 a2 en c ↦ (eval_liftP (corr4 f a1 a2 en c) _).trans
      (fIsFormCodeF_spec H (scons c (scons en (scons a2 (scons a1 f)))) 3)
  have hc2 : ∀ a1 a2 en c : X, Semiformula.Eval (s := sX)
      (c :> en :> a2 :> a1 :> (![] : Fin 0 → X)) f
        (liftP (toSet 4 (fIsFormCodeF 2))) ↔ IsFormCodeSem H a2 :=
    fun a1 a2 en c ↦ (eval_liftP (corr4 f a1 a2 en c) _).trans
      (fIsFormCodeF_spec H (scons c (scons en (scons a2 (scons a1 f)))) 2)
  have henv : ∀ a1 a2 en c : X, Semiformula.Eval (s := sX)
      (c :> en :> a2 :> a1 :> (![] : Fin 0 → X)) f
        (liftP (toSet 4 (fUnivEnvF 1))) ↔ IsUnivEnv H en :=
    fun a1 a2 en c ↦ (eval_liftP (corr4 f a1 a2 en c) _).trans
      (fUnivEnvF_spec H (scons c (scons en (scons a2 (scons a1 f)))) 1)
  have htag : ∀ a1 a2 en c : X, Semiformula.Eval (s := sX)
      (c :> en :> a2 :> a1 :> (![] : Fin 0 → X)) f
        (liftP (toSet 4 (fTagPairF 0 t 3 2))) ↔
      c = kpair' H (natV H t) (kpair' H a1 a2) :=
    fun a1 a2 en c ↦ (eval_liftP (corr4 f a1 a2 en c) _).trans
      (fTagPairF_spec H (scons c (scons en (scons a2 (scons a1 f)))) 0 t 3 2)
  simp only [srcConnSpine, Semiformula.eval_all,
    LogicalConnective.HomClass.map_imply, hc1, hc2, henv, htag, hbody]
  constructor
  · intro hh a1 a2 en h1 h2 h3
    exact hh a1 a2 en _ h1 h2 h3 rfl
  · rintro hh a1 a2 en c h1 h2 h3 rfl
    exact hh a1 a2 en h1 h2 h3

/-! ## The quantifier skeleton

The one place in the bridge where a premise's `Sat` specification consumes
another premise. -/

/-- **The quantifier skeleton evaluates to its five-slot reading.**  The
tag guard pins the fourth binder and the `econs` guard the fifth, but the
latter's specification needs the environment premise, so this is a
nested-implication argument in both directions rather than a congruence
rewrite: `hecons` is stated *under* `IsUnivEnv H en` and is deliberately
left out of the congruence step. -/
theorem eval_srcQuantSpine (f : ℕ → X) (H : ZFAxioms (templateMem X)) (t : ℕ)
    (body : Semiproposition srcL 5) (Q : X → X → X → X → X → Prop)
    (hbody : ∀ a en d c ec : X,
      Semiformula.Eval (s := sX)
        (ec :> c :> d :> en :> a :> (![] : Fin 0 → X)) f body ↔
          Q a en d c ec) :
    Semiformula.Eval (s := sX) ![] f (srcQuantSpine t body) ↔
      ∀ a en d : X, IsFormCodeSem H a → IsUnivEnv H en →
        Q a en d (kpair' H (natV H t) a) (econs H d en) := by
  have hcode : ∀ a en d c ec : X, Semiformula.Eval (s := sX)
      (ec :> c :> d :> en :> a :> (![] : Fin 0 → X)) f
        (liftP (toSet 5 (fIsFormCodeF 4))) ↔ IsFormCodeSem H a :=
    fun a en d c ec ↦ (eval_liftP (corr5 f a en d c ec) _).trans
      (fIsFormCodeF_spec H
        (scons ec (scons c (scons d (scons en (scons a f))))) 4)
  have henv : ∀ a en d c ec : X, Semiformula.Eval (s := sX)
      (ec :> c :> d :> en :> a :> (![] : Fin 0 → X)) f
        (liftP (toSet 5 (fUnivEnvF 3))) ↔ IsUnivEnv H en :=
    fun a en d c ec ↦ (eval_liftP (corr5 f a en d c ec) _).trans
      (fUnivEnvF_spec H
        (scons ec (scons c (scons d (scons en (scons a f))))) 3)
  have htag : ∀ a en d c ec : X, Semiformula.Eval (s := sX)
      (ec :> c :> d :> en :> a :> (![] : Fin 0 → X)) f
        (liftP (toSet 5 (fTagUnF 1 t 4))) ↔ c = kpair' H (natV H t) a :=
    fun a en d c ec ↦ (eval_liftP (corr5 f a en d c ec) _).trans
      (fTagUnF_spec H
        (scons ec (scons c (scons d (scons en (scons a f))))) 1 t 4)
  -- The fourth premise is readable only under the second.
  have hecons : ∀ a en d c ec : X, IsUnivEnv H en →
      (Semiformula.Eval (s := sX)
        (ec :> c :> d :> en :> a :> (![] : Fin 0 → X)) f
          (liftP (toSet 5 (fEconsF 0 2 3))) ↔ ec = econs H d en) :=
    fun a en d c ec hen ↦ (eval_liftP (corr5 f a en d c ec) _).trans
      (fEconsF_spec H
        (scons ec (scons c (scons d (scons en (scons a f))))) 0 2 3 hen.1)
  simp only [srcQuantSpine, Semiformula.eval_all,
    LogicalConnective.HomClass.map_imply, hcode, henv, htag]
  constructor
  · intro hh a en d hca hen
    exact (hbody a en d _ _).mp
      (hh a en d (kpair' H (natV H t) a) (econs H d en) hca hen rfl
        ((hecons a en d (kpair' H (natV H t) a) (econs H d en) hen).mpr rfl))
  · rintro hh a en d c ec hca hen rfl hec
    obtain rfl := (hecons a en d (kpair' H (natV H t) a) ec hen).mp hec
    exact (hbody a en d _ _).mpr (hh a en d hca hen)

/-! ## The falsity row -/

/-- **The falsity row evaluates to its one-slot reading.**  The tagged-empty
guard pins the inner binder to the falsity code. -/
theorem eval_srcBotPiOf (f : ℕ → X) (H : ZFAxioms (templateMem X))
    (P : (m w ci ei : ℕ) → Semiproposition srcL m) (R : X → X → Prop)
    (hP : ∀ en bt : X, Semiformula.Eval (s := sX)
      (bt :> en :> (![] : Fin 0 → X)) f (P 2 0 0 1) ↔ R bt en) :
    Semiformula.Eval (s := sX) ![] f (srcBotPiOf P) ↔
      ∀ en : X, IsUnivEnv H en → R (EnlargedFields.botC H) en := by
  have henv : ∀ en bt : X, Semiformula.Eval (s := sX)
      (bt :> en :> (![] : Fin 0 → X)) f (liftP (toSet 2 (fUnivEnvF 1))) ↔
      IsUnivEnv H en :=
    fun en bt ↦ (eval_liftP (corr2 f en bt) _).trans
      (fUnivEnvF_spec H (scons bt (scons en f)) 1)
  have hbot : ∀ en bt : X, Semiformula.Eval (s := sX)
      (bt :> en :> (![] : Fin 0 → X)) f
        (liftP (toSet 2 (fTaggedEmptyF 0 2))) ↔ bt = EnlargedFields.botC H :=
    fun en bt ↦ (eval_liftP (corr2 f en bt) _).trans
      (fTaggedEmptyF_spec H (scons bt (scons en f)) 0 2)
  simp only [srcBotPiOf, Semiformula.eval_all,
    LogicalConnective.HomClass.map_imply, henv, hbot, hP]
  constructor
  · intro hh en h1
    exact hh en _ h1 rfl
  · rintro hh en bt h1 rfl
    exact hh en h1

end Skeletons

/-! ## The rows, over an abstract polarized gadget

The counterpart of `ZFCinPA.TarskiSources`' `Rows` section: each of the six
row shapes is read once, uniformly in the tag and the polarity bits, from
the abstract reading of the gadget. -/

section Rows

variable {X : Type*} [Nonempty X] [sX : Structure srcL X] [Structure.Eq srcL X]

/-- **The reading a polarized gadget must have.**  `P m w ci ei` reads, at
every ambient arity and under every environment correspondence, as the
level relation `L` at slots `ci`, `ei` and the numeral bit `w`.  This is
the evaluation-side counterpart of the hypothesis `hP` that every
translation lemma of `ZFCinPA.TarskiSources` carries — with the arity side
conditions `ci < m`, `ei < m` dropped, because `Corr` reads bound and free
slots uniformly. -/
@[reducible] def PolarReading (f : ℕ → X) (H : ZFAxioms (templateMem X))
    (P : (m w ci ei : ℕ) → Semiproposition srcL m)
    (L : X → X → X → Prop) : Prop :=
  ∀ (m w ci ei : ℕ) {b : Fin m → X} {e : ℕ → X}, Corr b f e →
    (Semiformula.Eval (s := sX) b f (P m w ci ei) ↔
      L (e ci) (e ei) (natV H w))

variable (f : ℕ → X) (H : ZFAxioms (templateMem X))
  (P : (m w ci ei : ℕ) → Semiproposition srcL m) (L : X → X → X → Prop)

/-- A connective **elimination** row with a disjunctive conclusion. -/
theorem eval_connElimOr (hP : PolarReading f H P L) (t w0 w1 w2 : ℕ) :
    Semiformula.Eval (s := sX) ![] f
        (srcConnSpine t (P 4 w0 0 1 🡒 (P 4 w1 3 1 ⋎ P 4 w2 2 1))) ↔
      ∀ a1 a2 en : X, IsFormCodeSem H a1 → IsFormCodeSem H a2 →
        IsUnivEnv H en →
          L (kpair' H (natV H t) (kpair' H a1 a2)) en (natV H w0) →
            L a1 en (natV H w1) ∨ L a2 en (natV H w2) :=
  eval_srcConnSpine f H t _
    (fun a1 a2 en c ↦ L c en (natV H w0) →
      L a1 en (natV H w1) ∨ L a2 en (natV H w2))
    (fun a1 a2 en c ↦ by
      rw [LogicalConnective.HomClass.map_imply,
        LogicalConnective.HomClass.map_or]
      exact imp_congr (hP 4 w0 0 1 (corr4 f a1 a2 en c))
        (or_congr (hP 4 w1 3 1 (corr4 f a1 a2 en c))
          (hP 4 w2 2 1 (corr4 f a1 a2 en c))))

/-- A connective **elimination** row with a conjunctive conclusion. -/
theorem eval_connElimAnd (hP : PolarReading f H P L) (t w0 w1 w2 : ℕ) :
    Semiformula.Eval (s := sX) ![] f
        (srcConnSpine t (P 4 w0 0 1 🡒 (P 4 w1 3 1 ⋏ P 4 w2 2 1))) ↔
      ∀ a1 a2 en : X, IsFormCodeSem H a1 → IsFormCodeSem H a2 →
        IsUnivEnv H en →
          L (kpair' H (natV H t) (kpair' H a1 a2)) en (natV H w0) →
            L a1 en (natV H w1) ∧ L a2 en (natV H w2) :=
  eval_srcConnSpine f H t _
    (fun a1 a2 en c ↦ L c en (natV H w0) →
      L a1 en (natV H w1) ∧ L a2 en (natV H w2))
    (fun a1 a2 en c ↦ by
      rw [LogicalConnective.HomClass.map_imply,
        LogicalConnective.HomClass.map_and]
      exact imp_congr (hP 4 w0 0 1 (corr4 f a1 a2 en c))
        (and_congr (hP 4 w1 3 1 (corr4 f a1 a2 en c))
          (hP 4 w2 2 1 (corr4 f a1 a2 en c))))

/-- A connective **introduction** row with a disjunctive premise. -/
theorem eval_connIntroOr (hP : PolarReading f H P L) (t w0 w1 w2 : ℕ) :
    Semiformula.Eval (s := sX) ![] f
        (srcConnSpine t ((P 4 w1 3 1 ⋎ P 4 w2 2 1) 🡒 P 4 w0 0 1)) ↔
      ∀ a1 a2 en : X, IsFormCodeSem H a1 → IsFormCodeSem H a2 →
        IsUnivEnv H en →
          (L a1 en (natV H w1) ∨ L a2 en (natV H w2)) →
            L (kpair' H (natV H t) (kpair' H a1 a2)) en (natV H w0) :=
  eval_srcConnSpine f H t _
    (fun a1 a2 en c ↦ (L a1 en (natV H w1) ∨ L a2 en (natV H w2)) →
      L c en (natV H w0))
    (fun a1 a2 en c ↦ by
      rw [LogicalConnective.HomClass.map_imply,
        LogicalConnective.HomClass.map_or]
      exact imp_congr
        (or_congr (hP 4 w1 3 1 (corr4 f a1 a2 en c))
          (hP 4 w2 2 1 (corr4 f a1 a2 en c)))
        (hP 4 w0 0 1 (corr4 f a1 a2 en c)))

/-- A connective **introduction** row with a conjunctive premise. -/
theorem eval_connIntroAnd (hP : PolarReading f H P L) (t w0 w1 w2 : ℕ) :
    Semiformula.Eval (s := sX) ![] f
        (srcConnSpine t ((P 4 w1 3 1 ⋏ P 4 w2 2 1) 🡒 P 4 w0 0 1)) ↔
      ∀ a1 a2 en : X, IsFormCodeSem H a1 → IsFormCodeSem H a2 →
        IsUnivEnv H en →
          (L a1 en (natV H w1) ∧ L a2 en (natV H w2)) →
            L (kpair' H (natV H t) (kpair' H a1 a2)) en (natV H w0) :=
  eval_srcConnSpine f H t _
    (fun a1 a2 en c ↦ (L a1 en (natV H w1) ∧ L a2 en (natV H w2)) →
      L c en (natV H w0))
    (fun a1 a2 en c ↦ by
      rw [LogicalConnective.HomClass.map_imply,
        LogicalConnective.HomClass.map_and]
      exact imp_congr
        (and_congr (hP 4 w1 3 1 (corr4 f a1 a2 en c))
          (hP 4 w2 2 1 (corr4 f a1 a2 en c)))
        (hP 4 w0 0 1 (corr4 f a1 a2 en c)))

/-- A quantifier **elimination** row: the compound code at the ambient
environment yields the matrix at the extended one. -/
theorem eval_quantElim (hP : PolarReading f H P L) (t w : ℕ) :
    Semiformula.Eval (s := sX) ![] f
        (srcQuantSpine t (P 5 w 1 3 🡒 P 5 w 4 0)) ↔
      ∀ a en d : X, IsFormCodeSem H a → IsUnivEnv H en →
        L (kpair' H (natV H t) a) en (natV H w) →
          L a (econs H d en) (natV H w) :=
  eval_srcQuantSpine f H t _
    (fun a en _d c ec ↦ L c en (natV H w) → L a ec (natV H w))
    (fun a en d c ec ↦ by
      rw [LogicalConnective.HomClass.map_imply]
      exact imp_congr (hP 5 w 1 3 (corr5 f a en d c ec))
        (hP 5 w 4 0 (corr5 f a en d c ec)))

/-- A quantifier **introduction** row: the matrix at the extended
environment yields the compound code at the ambient one. -/
theorem eval_quantIntro (hP : PolarReading f H P L) (t w : ℕ) :
    Semiformula.Eval (s := sX) ![] f
        (srcQuantSpine t (P 5 w 4 0 🡒 P 5 w 1 3)) ↔
      ∀ a en d : X, IsFormCodeSem H a → IsUnivEnv H en →
        L a (econs H d en) (natV H w) →
          L (kpair' H (natV H t) a) en (natV H w) :=
  eval_srcQuantSpine f H t _
    (fun a en _d c ec ↦ L a ec (natV H w) → L c en (natV H w))
    (fun a en d c ec ↦ by
      rw [LogicalConnective.HomClass.map_imply]
      exact imp_congr (hP 5 w 4 0 (corr5 f a en d c ec))
        (hP 5 w 1 3 (corr5 f a en d c ec)))

/-- The falsity row at the polarized gadget. -/
theorem eval_botPi (hP : PolarReading f H P L) :
    Semiformula.Eval (s := sX) ![] f (srcBotPiOf P) ↔
      ∀ en : X, IsUnivEnv H en →
        L (EnlargedFields.botC H) en (natV H 0) :=
  eval_srcBotPiOf f H P (fun bt en ↦ L bt en (natV H 0))
    (fun en bt ↦ hP 2 0 0 1 (corr2 f en bt))

end Rows

/-! ## The two fields -/

section Fields

variable {X : Type*} [Nonempty X] [sX : Structure srcL X] [Structure.Eq srcL X]

/-- **The elimination field evaluates to `EnlargedFields.TarskiElim`.**  The
eight rows of `SuccessorSources.srcTarskiElimOf`, in order, are the eight
fields of the structure; the tags `3`, `4`, `5`, `6`, `7` are the code
shapes `impC`, `andC`, `orC`, `allC`, `exC`. -/
theorem eval_srcTarskiElimOf (f : ℕ → X) (H : ZFAxioms (templateMem X))
    (P : (m w ci ei : ℕ) → Semiproposition srcL m) (L : X → X → X → Prop)
    (hP : PolarReading f H P L) :
    Semiformula.Eval (s := sX) ![] f (srcTarskiElimOf P) ↔
      EnlargedFields.TarskiElim H L := by
  simp only [srcTarskiElimOf, LogicalConnective.HomClass.map_and,
    eval_connElimOr f H P L hP, eval_connElimAnd f H P L hP,
    eval_quantElim f H P L hP]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  · intro h
    exact ⟨h.impSigma, h.impPi, h.andSigma, h.andPi, h.orSigma, h.orPi,
      h.allSigma, h.exPi⟩

/-- **The introduction field evaluates to `EnlargedFields.TarskiIntro`.**
Three of the nine rows — implication on the Pi side, conjunction on the
Sigma side, disjunction on the Pi side — have a *conjunctive* premise in
the source and a curried one in the structure, so those three are
re-associated explicitly rather than matched. -/
theorem eval_srcTarskiIntroOf (f : ℕ → X) (H : ZFAxioms (templateMem X))
    (P : (m w ci ei : ℕ) → Semiproposition srcL m) (L : X → X → X → Prop)
    (hP : PolarReading f H P L) :
    Semiformula.Eval (s := sX) ![] f (srcTarskiIntroOf P) ↔
      EnlargedFields.TarskiIntro H L := by
  simp only [srcTarskiIntroOf, LogicalConnective.HomClass.map_and,
    eval_botPi f H P L hP, eval_connIntroOr f H P L hP,
    eval_connIntroAnd f H P L hP, eval_quantIntro f H P L hP]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    exact
      { botPi := h1
        impSigma := h2
        impPi := fun a b e ha hb he k1 k2 ↦ h3 a b e ha hb he ⟨k1, k2⟩
        andSigma := fun a b e ha hb he k1 k2 ↦ h4 a b e ha hb he ⟨k1, k2⟩
        andPi := h5
        orSigma := h6
        orPi := fun a b e ha hb he k1 k2 ↦ h7 a b e ha hb he ⟨k1, k2⟩
        allPi := h8
        exSigma := h9 }
  · intro h
    exact ⟨h.botPi, h.impSigma,
      fun a b e ha hb he k ↦ h.impPi a b e ha hb he k.1 k.2,
      fun a b e ha hb he k ↦ h.andSigma a b e ha hb he k.1 k.2,
      h.andPi, h.orSigma,
      fun a b e ha hb he k ↦ h.orPi a b e ha hb he k.1 k.2,
      h.allPi, h.exSigma⟩

/-! ### The four headline readings -/

/-- **The elimination field at the placeholder level.** -/
theorem eval_srcTarskiElim (f : ℕ → X) (H : ZFAxioms (templateMem X)) :
    Semiformula.Eval (s := sX) ![] f srcTarskiElim ↔
      EnlargedFields.TarskiElim H (templateLevel X H) :=
  eval_srcTarskiElimOf f H srcPolarAt (templateLevel X H)
    (fun m w ci ei {_b _e} h ↦ eval_srcPolarAt m w ci ei h H)

/-- **The elimination field one index up**, at the induced successor
level. -/
theorem eval_srcTarskiElimSucc (f : ℕ → X) (H : ZFAxioms (templateMem X)) :
    Semiformula.Eval (s := sX) ![] f srcTarskiElimSucc ↔
      EnlargedFields.TarskiElim H (templateStepLevel X H) :=
  eval_srcTarskiElimOf f H srcPolarAtSucc (templateStepLevel X H)
    (fun m w ci ei {_b _e} h ↦ eval_srcPolarAtSucc m w ci ei h H)

/-- **The introduction field at the placeholder level.** -/
theorem eval_srcTarskiIntro (f : ℕ → X) (H : ZFAxioms (templateMem X)) :
    Semiformula.Eval (s := sX) ![] f srcTarskiIntro ↔
      EnlargedFields.TarskiIntro H (templateLevel X H) :=
  eval_srcTarskiIntroOf f H srcPolarAt (templateLevel X H)
    (fun m w ci ei {_b _e} h ↦ eval_srcPolarAt m w ci ei h H)

/-- **The introduction field one index up**, at the induced successor
level. -/
theorem eval_srcTarskiIntroSucc (f : ℕ → X) (H : ZFAxioms (templateMem X)) :
    Semiformula.Eval (s := sX) ![] f srcTarskiIntroSucc ↔
      EnlargedFields.TarskiIntro H (templateStepLevel X H) :=
  eval_srcTarskiIntroOf f H srcPolarAtSucc (templateStepLevel X H)
    (fun m w ci ei {_b _e} h ↦ eval_srcPolarAtSucc m w ci ei h H)

end Fields

/-! ## Residue

This module closes item 1 of `ZFCinPA.FieldEvaluation`'s residue list and
nothing else.  What it does **not** do, restated so that no later reader
mistakes the scope:

* **No `LevelLaws` bundle is assembled.**  `EnlargedFields.LevelLaws` has
  four conjuncts; `eval_srcLocalStep` supplies `excl` (through
  `LocalStepTransfer.LocalStepLaws`) and the two theorems here supply
  `elim` and `intr`.  The `decided` conjunct is item 2 of
  `ZFCinPA.FieldEvaluation`'s residue — a source `crossLevel` field — and
  still has no source formula anywhere in the project.
* **The numeral placeholder is still unpinned.**  Both successor readings
  land on `templateStepLevel`, whose bound is existentially quantified;
  item 3 of `ZFCinPA.FieldEvaluation`'s residue records the `Num`
  uniqueness antecedent this forces on the assembled source sentence.  The
  two theorems here do not narrow that gap and do not depend on it.
* **No source derivation is produced.**  Items 4 and 5 of that residue —
  the source `CodeInduction` antecedent and the assembly through
  `SetPlaceholderQuotient.complete_underSetPlaceholderCongruence` — are
  untouched.

Nothing above is assumed anywhere in this project. -/

end TemplateEvaluation
end ZFCinPA
end LeanProofs
