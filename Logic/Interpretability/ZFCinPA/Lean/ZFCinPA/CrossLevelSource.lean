import ZFCinPA.FieldEvaluation

/-!
# The source form of the decidedness field, and its reading

Item 2 of the residue list in `ZFCinPA.FieldEvaluation`: the **second**
certificate field, `crossLevel`, had no source counterpart anywhere in the
project.  `EnlargedFields.LevelLaws` — the antecedent of
`LocalStepTransfer.localStepLaws_step` — needs its `decided` conjunct

> `∀ c e, IsFormCodeSem H c → IsUnivEnv H e → QuantBounded H b c →`
> `L c e (natV H 1) ∨ L c e (natV H 0)`

and the four deliverables that turn such a conjunct into a usable piece of
the compilation route are supplied here, in the shape
`ZFCinPA.LocalStepSuccessor` supplies them for the first field:

* `srcCrossLevel` / `srcCrossLevelSucc` — the fixed source formulas over
  the placeholder language `setTemplateLanguage 2 ![1, 2]`, built from the
  shared source layer of `ZFCinPA.SuccessorSources`;
* `translate_srcCrossLevel` / `translate_srcCrossLevelSucc` — their
  specializations at `levelLeaves x` are `crossLevelCode x` and
  `crossLevelCode (x + 1)`, at *every* model index, standard or not;
* `fvFree_srcCrossLevel` / `fvFree_srcCrossLevelSucc` — free-variable
  freeness, which is what
  `SetPlaceholderQuotient.complete_underSetPlaceholderCongruence` needs
  before the proposition can be closed into a `Sentence srcL`;
* `eval_srcCrossLevel` / `eval_srcCrossLevelSucc` — their readings in an
  arbitrary template structure, over `TemplateEvaluation.templateLevel`
  and `templateStepLevel` respectively.

## The bound is the numeral placeholder, and it is existential

`CertificateFields.crossLevelF` states the bound through
`boundedAtF n 1 = ∃ k (Num k ∧ QuantBounded k c)`, i.e. the numeral chain
is *introduced by an existential* rather than named.  At the source level
the numeral chain is the opaque placeholder `Num`, so the honest reading
of `srcCrossLevel` is

> `∀ c e, IsFormCodeSem H c → IsUnivEnv H e →`
> `(∃ k, Num k ∧ QuantBounded H k c) → L c e ‹1› ∨ L c e ‹0›`

with the bound under an existential in the **antecedent**.  That is
*stronger* than the `decided` conjunct at any one bound, not weaker: the
corollaries `decided_of_srcCrossLevel` / `decided_of_srcCrossLevelSucc`
instantiate it at any `b` the placeholder recognizes and produce exactly
`EnlargedFields.LevelLaws.decided`'s statement at that `b`.  So no
`Num`-uniqueness antecedent is needed *here* — unlike the successor
reading of the level tower, where the existential sits in the consequent
(residue item 3 of `ZFCinPA.FieldEvaluation`).  The successor form's bound
is `vsucc H b`, the numeral one index up, which is the bound
`LocalStepTransfer.localStepLaws_step` produces.

## Free-slot bounds

No new kernel `decide` is performed.  The three fixed leaves of this field
(`fIsFormCodeF 1`, `fUnivEnvF 0` at depth `2` and `fQuantBoundedF 0 2` at
depth `3`) have their `freeMax` evaluations sealed as private constants
inside `ZFCinPA.CertificateFields`; each bound is recovered here from the
field's own closedness theorem `not_free_crossLevelF`, exactly the way
`LocalStepSuccessor.free_univEnv0` recovers its bound from
`not_free_localStepF` and `TarskiSources.free_isFormCode3D4` from
`not_free_connClauseF`.

## Disciplines

The parameter firewall is respected: concrete Gödel constants are reached
only through `coe_toNat_eq_quote`, never by `simp` or evaluation, and the
two `x`-dependent leaves stay behind the placeholder abstraction.  The
evaluation side mentions no code at all.
-/

set_option autoImplicit false
set_option maxRecDepth 8000

namespace LeanProofs
namespace ZFCinPA

namespace SuccessorSources

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.SetPlaceholders
open LeanProofs.ZFCinPA.SubstIdentity
open BoundedZFCConsistency (fUnivEnvF fIsFormCodeF fQuantBoundedF)

/-! ## Free-slot bounds of this field's three fixed leaves

`SetTheory.Free` is definitional on the field's spine, so a hypothetical
free slot of a leaf below the binders that guard it would be a free slot
of the whole closed field. -/

section Bounds

open SetTheory (Form Free)

theorem free_isFormCode1D2 {i : ℕ} (h : Free i (fIsFormCodeF 1)) : i < 2 := by
  by_contra hlt
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := ⟨i - 2, by omega⟩
  exact not_free_crossLevelF 0 k (Or.inl h)

theorem free_univEnv0D2 {i : ℕ} (h : Free i (fUnivEnvF 0)) : i < 2 := by
  by_contra hlt
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := ⟨i - 2, by omega⟩
  exact not_free_crossLevelF 0 k (Or.inr (Or.inl h))

/-- The quantifier-bound leaf sits one binder deeper: the boundedness
gadget introduces the numeral by an existential. -/
theorem free_quantBounded02 {i : ℕ} (h : Free i (fQuantBoundedF 0 2)) :
    i < 3 := by
  by_contra hlt
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 3 := ⟨i - 3, by omega⟩
  exact not_free_crossLevelF 0 k (Or.inr (Or.inr (Or.inl (Or.inr h))))

end Bounds

/-! ## The source form of the second field -/

section Source

open SetTheory (Form Free)

/-- Source counterpart of `CertificateFields.boundedAtF n 1`: the numeral
placeholder introduced by one existential, together with the fixed
quantifier-bound leaf. -/
noncomputable def srcBoundedAt : Semiproposition srcL 2 :=
  ∃⁰ (srcNumAt (n := 3) (by omega) ⋏ liftP (toSet 3 (fQuantBoundedF 0 2)))

/-- The boundedness gadget one index up: the bound is the *successor*
numeral, so the numeral slot is the successor spine of
`ZFCinPA.SuccessorSources` rather than the placeholder itself. -/
noncomputable def srcBoundedAtSucc : Semiproposition srcL 2 :=
  ∃⁰ (srcNumChainSucc 3 ⋏ liftP (toSet 3 (fQuantBoundedF 0 2)))

/-- **The source form of the decidedness field.**  Its specialization at
`levelLeaves x` is `crossLevelCode x`, at every model index. -/
noncomputable def srcCrossLevel : Proposition srcL :=
  ∀⁰ ∀⁰ (liftP (toSet 2 (fIsFormCodeF 1)) 🡒
    (liftP (toSet 2 (fUnivEnvF 0)) 🡒
      (srcBoundedAt 🡒 (srcCanonAt srcSigmaTrue ⋎ srcCanonAt srcPiFalse))))

/-- **The source form of the decidedness field one index up.**  The spine
is literally `srcCrossLevel`'s; the numeral slot and the two
canonical-slot payloads move one level. -/
noncomputable def srcCrossLevelSucc : Proposition srcL :=
  ∀⁰ ∀⁰ (liftP (toSet 2 (fIsFormCodeF 1)) 🡒
    (liftP (toSet 2 (fUnivEnvF 0)) 🡒
      (srcBoundedAtSucc 🡒
        (srcCanonAt srcSigmaTrueSucc ⋎ srcCanonAt srcPiFalseSucc))))

end Source

/-! ## Reconciliation -/

section Reconcile

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open SetTheory (Form Free)

theorem translate_srcBoundedAt (x : V) :
    (translateFormula (levelLeaves x) srcBoundedAt).val =
      boundedAtPart quantBoundedD3Code x := by
  rw [boundedAtPart]
  simp only [srcBoundedAt, translate_exs, translate_and,
    Bootstrapping.Semiformula.val_exs, Bootstrapping.Semiformula.val_and,
    translate_liftP_val, translate_srcNumAt]
  rw [← coe_toNat_eq_quote (V := V) (toSet 3 (fQuantBoundedF 0 2))]
  rfl

theorem translate_srcBoundedAtSucc (x : V) :
    (translateFormula (levelLeaves x) srcBoundedAtSucc).val =
      boundedAtPart quantBoundedD3Code (x + 1) := by
  rw [boundedAtPart]
  simp only [srcBoundedAtSucc, translate_exs, translate_and,
    Bootstrapping.Semiformula.val_exs, Bootstrapping.Semiformula.val_and,
    translate_liftP_val, translate_srcNumChainSucc x 3 (by omega)]
  rw [← coe_toNat_eq_quote (V := V) (toSet 3 (fQuantBoundedF 0 2))]
  rfl

/-- **The decidedness field code is the specialization of a fixed source
formula.**  At every model index `x`, standard or not. -/
theorem translate_srcCrossLevel (x : V) :
    (translateFormula (levelLeaves x) srcCrossLevel).val = crossLevelCode x := by
  rw [crossLevelCode, crossLevelPart,
    show sigmaAtCode 1 0 x =
      canonAtPart (eqGuardCode 1 3) (eqGuardCode 0 2) (sigmaTrueCode (x + 1))
      from rfl,
    show piFalseAtCode 1 0 x =
      canonAtPart (eqGuardCode 1 3) (eqGuardCode 0 2) (piFalseCode (x + 1))
      from rfl]
  simp only [srcCrossLevel, translate_all, translate_or, translateFormula_imp,
    Bootstrapping.Semiformula.val_all, Bootstrapping.Semiformula.val_or,
    Bootstrapping.Semiformula.val_imp, translate_liftP_val,
    translate_srcBoundedAt, translate_srcCanonAt, translate_srcSigmaTrue,
    translate_srcPiFalse]
  rw [← coe_toNat_eq_quote (V := V) (toSet 2 (fIsFormCodeF 1)),
    ← coe_toNat_eq_quote (V := V) (toSet 2 (fUnivEnvF 0))]
  rfl

/-- Typed form. -/
theorem translate_srcCrossLevel_formula (x : V) :
    translateFormula (levelLeaves x) srcCrossLevel = crossLevelFormula x :=
  Bootstrapping.Semiformula.ext (translate_srcCrossLevel x)

/-- **The successor of the decidedness field code is the specialization of
a fixed source formula**, at every model index. -/
theorem translate_srcCrossLevelSucc (x : V) :
    (translateFormula (levelLeaves x) srcCrossLevelSucc).val =
      crossLevelCode (x + 1) := by
  rw [crossLevelCode, crossLevelPart,
    show sigmaAtCode 1 0 (x + 1) =
      canonAtPart (eqGuardCode 1 3) (eqGuardCode 0 2)
        (sigmaTrueCode (x + 1 + 1)) from rfl,
    show piFalseAtCode 1 0 (x + 1) =
      canonAtPart (eqGuardCode 1 3) (eqGuardCode 0 2)
        (piFalseCode (x + 1 + 1)) from rfl]
  simp only [srcCrossLevelSucc, translate_all, translate_or,
    translateFormula_imp, Bootstrapping.Semiformula.val_all,
    Bootstrapping.Semiformula.val_or, Bootstrapping.Semiformula.val_imp,
    translate_liftP_val, translate_srcBoundedAtSucc, translate_srcCanonAt,
    translate_srcSigmaTrueSucc, translate_srcPiFalseSucc]
  rw [← coe_toNat_eq_quote (V := V) (toSet 2 (fIsFormCodeF 1)),
    ← coe_toNat_eq_quote (V := V) (toSet 2 (fUnivEnvF 0))]
  rfl

/-- Typed form. -/
theorem translate_srcCrossLevelSucc_formula (x : V) :
    translateFormula (levelLeaves x) srcCrossLevelSucc =
      crossLevelFormula (x + 1) :=
  Bootstrapping.Semiformula.ext (translate_srcCrossLevelSucc x)

end Reconcile

/-! ## Free-variable-freeness -/

section FvFreeCrossLevel

open SetTheory (Form Free)

theorem fvFree_srcBoundedAt : FvFree srcBoundedAt :=
  .exs ((fvFree_srcNumAt _).and
    (fvFree_liftP (fun _ hi ↦ free_quantBounded02 hi)))

theorem fvFree_srcBoundedAtSucc : FvFree srcBoundedAtSucc :=
  .exs ((fvFree_srcNumChainSucc 3 (by omega)).and
    (fvFree_liftP (fun _ hi ↦ free_quantBounded02 hi)))

theorem fvFree_srcCrossLevel : FvFree srcCrossLevel := by
  refine FvFree.all (FvFree.all (FvFree.imp ?_ (FvFree.imp ?_
    (FvFree.imp ?_ (FvFree.or ?_ ?_)))))
  · exact fvFree_liftP (fun _ hi ↦ free_isFormCode1D2 hi)
  · exact fvFree_liftP (fun _ hi ↦ free_univEnv0D2 hi)
  · exact fvFree_srcBoundedAt
  · exact fvFree_srcCanonAt fvFree_srcSigmaTrue
  · exact fvFree_srcCanonAt fvFree_srcPiFalse

theorem fvFree_srcCrossLevelSucc : FvFree srcCrossLevelSucc := by
  refine FvFree.all (FvFree.all (FvFree.imp ?_ (FvFree.imp ?_
    (FvFree.imp ?_ (FvFree.or ?_ ?_)))))
  · exact fvFree_liftP (fun _ hi ↦ free_isFormCode1D2 hi)
  · exact fvFree_liftP (fun _ hi ↦ free_univEnv0D2 hi)
  · exact fvFree_srcBoundedAtSucc
  · exact fvFree_srcCanonAt fvFree_srcSigmaTrueSucc
  · exact fvFree_srcCanonAt fvFree_srcPiFalseSucc

end FvFreeCrossLevel

end SuccessorSources

/-! ## The reading in an arbitrary template structure -/

namespace TemplateEvaluation

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.SetPlaceholders
open LeanProofs.ZFCinPA.SuccessorSources
open BoundedZFCConsistency
open SetTheory (Form ZFAxioms scons Sat vsucc)

section CrossLevel

variable {X : Type*} [Nonempty X] [sX : Structure srcL X] [Structure.Eq srcL X]

/-- **The boundedness gadget reads the numeral placeholder.**  Nothing at
this level pins the witness: the placeholder is opaque, so the bound is
whatever `Num` recognizes. -/
theorem eval_srcBoundedAt (f : ℕ → X) (H : ZFAxioms (templateMem X))
    (x1 x0 : X) :
    Semiformula.Eval (s := sX) (x0 :> x1 :> (![] : Fin 0 → X)) f
        srcBoundedAt ↔
      ∃ k, templateNum X k ∧ QuantBounded H k x1 := by
  have hco : Corr (x0 :> x1 :> (![] : Fin 0 → X)) f (scons x0 (scons x1 f)) :=
    ((corr0 f).cons x1).cons x0
  rw [srcBoundedAt, Semiformula.eval_ex]
  refine exists_congr fun k ↦ ?_
  rw [LogicalConnective.HomClass.map_and, eval_srcNumAt,
    eval_liftP (hco.cons k) (fQuantBoundedF 0 2),
    fQuantBoundedF_spec H (scons k (scons x0 (scons x1 f))) 0 2]
  exact Iff.rfl

/-- The boundedness gadget one index up: the bound is the successor of a
recognized numeral. -/
theorem eval_srcBoundedAtSucc (f : ℕ → X) (H : ZFAxioms (templateMem X))
    (x1 x0 : X) :
    Semiformula.Eval (s := sX) (x0 :> x1 :> (![] : Fin 0 → X)) f
        srcBoundedAtSucc ↔
      ∃ k, templateNum X k ∧ QuantBounded H (vsucc H k) x1 := by
  have hco : Corr (x0 :> x1 :> (![] : Fin 0 → X)) f (scons x0 (scons x1 f)) :=
    ((corr0 f).cons x1).cons x0
  rw [srcBoundedAtSucc, Semiformula.eval_ex]
  constructor
  · rintro ⟨y, hy⟩
    rw [LogicalConnective.HomClass.map_and] at hy
    obtain ⟨k, hk, hyk⟩ :=
      (eval_srcNumChainSucc 3 (hco.cons y) H).mp hy.1
    have hy2 : QuantBounded H y x1 :=
      (fQuantBoundedF_spec H (scons y (scons x0 (scons x1 f))) 0 2).mp
        ((eval_liftP (hco.cons y) (fQuantBoundedF 0 2)).mp hy.2)
    have hyk' : y = vsucc H k := hyk
    rw [hyk'] at hy2
    exact ⟨k, hk, hy2⟩
  · rintro ⟨k, hk, hq⟩
    refine ⟨vsucc H k, ?_⟩
    rw [LogicalConnective.HomClass.map_and]
    exact ⟨(eval_srcNumChainSucc 3 (hco.cons (vsucc H k)) H).mpr ⟨k, hk, rfl⟩,
      (eval_liftP (hco.cons (vsucc H k)) (fQuantBoundedF 0 2)).mpr
        ((fQuantBoundedF_spec H
          (scons (vsucc H k) (scons x0 (scons x1 f))) 0 2).mpr hq)⟩

/-- **The decidedness field evaluates to decidedness over the induced
previous level**, with the bound supplied — existentially — by the numeral
placeholder. -/
theorem eval_srcCrossLevel (f : ℕ → X) (H : ZFAxioms (templateMem X)) :
    Semiformula.Eval (s := sX) ![] f srcCrossLevel ↔
      ∀ c e, IsFormCodeSem H c → IsUnivEnv H e →
        (∃ k, templateNum X k ∧ QuantBounded H k c) →
        templateLevel X H c e (natV H 1) ∨ templateLevel X H c e (natV H 0) := by
  have hco : ∀ x1 x0 : X,
      Corr (x0 :> x1 :> (![] : Fin 0 → X)) f (scons x0 (scons x1 f)) :=
    fun x1 x0 ↦ ((corr0 f).cons x1).cons x0
  have hcode : ∀ x1 x0 : X, Semiformula.Eval (s := sX)
      (x0 :> x1 :> (![] : Fin 0 → X)) f
        (liftP (toSet 2 (fIsFormCodeF 1))) ↔
      IsFormCodeSem H x1 := fun x1 x0 ↦
    (eval_liftP (hco x1 x0) _).trans
      (fIsFormCodeF_spec H (scons x0 (scons x1 f)) 1)
  have henv : ∀ x1 x0 : X, Semiformula.Eval (s := sX)
      (x0 :> x1 :> (![] : Fin 0 → X)) f (liftP (toSet 2 (fUnivEnvF 0))) ↔
      IsUnivEnv H x0 := fun x1 x0 ↦
    (eval_liftP (hco x1 x0) _).trans
      (fUnivEnvF_spec H (scons x0 (scons x1 f)) 0)
  have hbnd : ∀ x1 x0 : X, Semiformula.Eval (s := sX)
      (x0 :> x1 :> (![] : Fin 0 → X)) f srcBoundedAt ↔
      ∃ k, templateNum X k ∧ QuantBounded H k x1 :=
    fun x1 x0 ↦ eval_srcBoundedAt f H x1 x0
  have hsig : ∀ x1 x0 : X, Semiformula.Eval (s := sX)
      (x0 :> x1 :> (![] : Fin 0 → X)) f (srcCanonAt srcSigmaTrue) ↔
      templateLevel X H x1 x0 (natV H 1) := fun x1 x0 ↦
    eval_srcPolarAt 2 1 1 0 (hco x1 x0) H
  have hpif : ∀ x1 x0 : X, Semiformula.Eval (s := sX)
      (x0 :> x1 :> (![] : Fin 0 → X)) f (srcCanonAt srcPiFalse) ↔
      templateLevel X H x1 x0 (natV H 0) := fun x1 x0 ↦
    eval_srcPolarAt 2 0 1 0 (hco x1 x0) H
  simp only [srcCrossLevel, Semiformula.eval_all,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_or,
    hcode, henv, hbnd, hsig, hpif]
  exact Iff.rfl

/-- The decidedness field one index up, over the induced successor level,
at the successor numeral bound — which is the bound
`LocalStepTransfer.localStepLaws_step` produces. -/
theorem eval_srcCrossLevelSucc (f : ℕ → X) (H : ZFAxioms (templateMem X)) :
    Semiformula.Eval (s := sX) ![] f srcCrossLevelSucc ↔
      ∀ c e, IsFormCodeSem H c → IsUnivEnv H e →
        (∃ k, templateNum X k ∧ QuantBounded H (vsucc H k) c) →
        templateStepLevel X H c e (natV H 1) ∨
          templateStepLevel X H c e (natV H 0) := by
  have hco : ∀ x1 x0 : X,
      Corr (x0 :> x1 :> (![] : Fin 0 → X)) f (scons x0 (scons x1 f)) :=
    fun x1 x0 ↦ ((corr0 f).cons x1).cons x0
  have hcode : ∀ x1 x0 : X, Semiformula.Eval (s := sX)
      (x0 :> x1 :> (![] : Fin 0 → X)) f
        (liftP (toSet 2 (fIsFormCodeF 1))) ↔
      IsFormCodeSem H x1 := fun x1 x0 ↦
    (eval_liftP (hco x1 x0) _).trans
      (fIsFormCodeF_spec H (scons x0 (scons x1 f)) 1)
  have henv : ∀ x1 x0 : X, Semiformula.Eval (s := sX)
      (x0 :> x1 :> (![] : Fin 0 → X)) f (liftP (toSet 2 (fUnivEnvF 0))) ↔
      IsUnivEnv H x0 := fun x1 x0 ↦
    (eval_liftP (hco x1 x0) _).trans
      (fUnivEnvF_spec H (scons x0 (scons x1 f)) 0)
  have hbnd : ∀ x1 x0 : X, Semiformula.Eval (s := sX)
      (x0 :> x1 :> (![] : Fin 0 → X)) f srcBoundedAtSucc ↔
      ∃ k, templateNum X k ∧ QuantBounded H (vsucc H k) x1 :=
    fun x1 x0 ↦ eval_srcBoundedAtSucc f H x1 x0
  have hsig : ∀ x1 x0 : X, Semiformula.Eval (s := sX)
      (x0 :> x1 :> (![] : Fin 0 → X)) f (srcCanonAt srcSigmaTrueSucc) ↔
      templateStepLevel X H x1 x0 (natV H 1) := fun x1 x0 ↦
    eval_srcPolarAtSucc 2 1 1 0 (hco x1 x0) H
  have hpif : ∀ x1 x0 : X, Semiformula.Eval (s := sX)
      (x0 :> x1 :> (![] : Fin 0 → X)) f (srcCanonAt srcPiFalseSucc) ↔
      templateStepLevel X H x1 x0 (natV H 0) := fun x1 x0 ↦
    eval_srcPolarAtSucc 2 0 1 0 (hco x1 x0) H
  simp only [srcCrossLevelSucc, Semiformula.eval_all,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_or,
    hcode, henv, hbnd, hsig, hpif]
  exact Iff.rfl

/-! ### The decidedness conjunct, at a named bound

`EnlargedFields.LevelLaws.decided` fixes one bound `b`.  The source
reading quantifies the bound existentially in its *antecedent*, so it
implies the field at every bound the numeral placeholder recognizes; no
`Num`-uniqueness hypothesis is involved. -/

/-- **The decidedness conjunct of `EnlargedFields.LevelLaws`, at any bound
the numeral placeholder recognizes.** -/
theorem decided_of_srcCrossLevel (f : ℕ → X) (H : ZFAxioms (templateMem X))
    (hev : Semiformula.Eval (s := sX) ![] f srcCrossLevel) {b : X}
    (hb : templateNum X b) :
    ∀ c e, IsFormCodeSem H c → IsUnivEnv H e → QuantBounded H b c →
      templateLevel X H c e (natV H 1) ∨ templateLevel X H c e (natV H 0) :=
  fun c e hc he hq ↦ (eval_srcCrossLevel f H).mp hev c e hc he ⟨b, hb, hq⟩

/-- **The reading is the `decided` field verbatim.**  Given the other
three conjuncts, the source reading completes `EnlargedFields.LevelLaws`
at the induced previous level and any recognized bound.  This is a
type-level check that nothing was weakened on the way: no coercion, no
reformulation, no extra hypothesis — `decided_of_srcCrossLevel`'s
conclusion *is* the structure field. -/
theorem levelLaws_of_srcCrossLevel (f : ℕ → X) (H : ZFAxioms (templateMem X))
    (hev : Semiformula.Eval (s := sX) ![] f srcCrossLevel) {b : X}
    (hb : templateNum X b)
    (hexcl : ∀ c e, IsFormCodeSem H c → IsUnivEnv H e →
      templateLevel X H c e (natV H 1) → ¬ templateLevel X H c e (natV H 0))
    (helim : EnlargedFields.TarskiElim H (templateLevel X H))
    (hintr : EnlargedFields.TarskiIntro H (templateLevel X H)) :
    EnlargedFields.LevelLaws H (templateLevel X H) b where
  excl := hexcl
  decided := decided_of_srcCrossLevel f H hev hb
  elim := helim
  intr := hintr

/-- The same one index up, at the successor bound. -/
theorem decided_of_srcCrossLevelSucc (f : ℕ → X)
    (H : ZFAxioms (templateMem X))
    (hev : Semiformula.Eval (s := sX) ![] f srcCrossLevelSucc) {b : X}
    (hb : templateNum X b) :
    ∀ c e, IsFormCodeSem H c → IsUnivEnv H e →
      QuantBounded H (vsucc H b) c →
      templateStepLevel X H c e (natV H 1) ∨
        templateStepLevel X H c e (natV H 0) :=
  fun c e hc he hq ↦
    (eval_srcCrossLevelSucc f H).mp hev c e hc he ⟨b, hb, hq⟩

end CrossLevel

end TemplateEvaluation

/-! ## Residue

What this module lands is item 2 of `ZFCinPA.FieldEvaluation`'s residue
list, in full: the source formula of the decidedness field, its
translation identity at every (possibly nonstandard) index, its
free-variable-freeness, and its reading in an arbitrary template
structure, at both levels.

What it does **not** land, and does not assume:

* the assembled source sentence and its derivation.  `srcCrossLevel` is a
  conjunct of the antecedent that
  `LocalStepTransfer.localStepLaws_step` consumes (`hL.decided`); the
  remaining conjuncts are the two Tarski readings (item 1) and the source
  `CodeInduction` (item 4), and the assembly is item 5.  Nothing here
  claims any of them;
* any relation between the numeral placeholder and `ω`.  The bound in
  `eval_srcCrossLevel` is whatever `Num` recognizes; `localStepLaws_step`
  additionally needs `mem b (omegaV H)`, which is the `srcNumOmega`
  antecedent recorded in `ZFCinPA.LocalStepTransfer`'s header and is not
  supplied here.

The two readings are exact, not approximate: `eval_srcCrossLevel`'s
right-hand side is `EnlargedFields.LevelLaws.decided`'s statement with the
bound existentially quantified in the antecedent, which
`decided_of_srcCrossLevel` specializes to the conjunct verbatim at any
recognized bound. -/

end ZFCinPA
end LeanProofs
