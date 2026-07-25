import ZFCinPA.SuccessorSources

/-!
# The level tower as a two-placeholder proof template, and the local-step field

This module opens the *compilation* route to the remaining successor
obligation of `ZFCinPA.StagedSuccessor`, and carries it out for the
antecedent side of the first field.

## The observation

At an arbitrary model index `x : V` the certificate field code
`localStepCode x` is a fixed constructor spine over exactly **two**
`x`-dependent leaves:

* `numChainCode x`, a unary `ℒₛₑₜ` formula code, and
* `closCode x`, a binary one.

Everything else in the spine is a standard natural-number code — a
quotation of a fixed `SetTheory.Form` macro at a fixed translation depth.
That is precisely the shape `ZFCinPA.SetPlaceholders` was built for: the
placeholder language `setTemplateLanguage 2 ![1, 2]`, interpreted by
`levelLeaves x = ![numChainCode x, closCode x]`.

So there is a *fixed*, model-free source formula `srcLocalStep` over that
language whose specialization at `levelLeaves x` is `localStepFormula x`,
at every `x`, standard or not.  `translate_srcLocalStep` proves it.

## Why this is the right route

`ZFCinPA.StandardSuccessor` discharges the six successor implications
along the standard cut by D1, and that is exactly what cannot be
uniformized.  A source template is the uniform substitute: one ordinary
Lean proof over `templateZFC 2 ![1, 2]`, compiled once by
`SetPlaceholders.compileSetTemplate`, yields an internal `𝗭𝗙𝗖` proof at
*every* index simultaneously — nonstandard formula codes included.

## The split with `ZFCinPA.SuccessorSources`

Everything in the route that is *field-independent* now lives in
`ZFCinPA.SuccessorSources` and is re-exported here, so nothing downstream
sees the split:

* the template setup (`levelArities`, `srcL`, `levelLeaves`) and the
  proposition-level placeholder atom `srcPlaceholder`, together with its
  reconciliation `translate_srcPlaceholder` — the first real use of
  `ZFCinPA.SubstIdentity`, since the leaves are spliced *raw* at ambient
  arities `7` (both) while their own arities are `1` and `2`;
* the source formulas for the whole level tower at the canonical slots
  (`srcLevelSat`, `srcSigmaTrue`, `srcPiFalse`, `srcPiTrue`) and for the
  canonical-slot gadget (`srcCanonAt`), each with its reconciliation
  lemma;
* **shift-fixedness of the two leaves** (`shift_levelLeaves`), which is
  what `SetPlaceholders.compileSetTemplate` demands of any
  interpretation;
* the source counterparts of the two towers' successor steps
  (`srcNumChainSucc`, `srcClosStep`) and the level tower one level up
  (`srcLevelSatSucc`, `srcSigmaTrueSucc`, `srcPiFalseSucc`,
  `srcPiTrueSucc`).

What this module itself lands is the first field, end to end except for
one derivation:

* `srcLocalStep`, `srcLocalStepSucc` and their reconciliations
  (`translateFormula (levelLeaves x) srcLocalStep = localStepFormula x`
  and the same one index up), at every `x : V`;
* the source **sentence** `srcLocalStepStep` — the universal closure of
  the free-variable-free implication `srcLocalStep 🡒 srcLocalStepSucc` — and
  `translate_srcLocalStepStep`, which is precisely the specialization
  hypothesis `hσ` of `localStepSuccessor_of_source`;
* `localStepSuccessor_of_derivation`, which turns *one* ordinary Lean
  proof `templateZFC 2 ![1, 2] ⊢! srcLocalStepStep` into the `localStep`
  field of `ZFCSuccessorImplications` at every, possibly nonstandard,
  index.

Not landed, and deliberately not assumed anywhere: that derivation.  It is
an explicit argument of `localStepSuccessor_of_derivation`; see the
`Residue` section at the end of the file.

## Disciplines

The parameter firewall is respected throughout: the concrete leaf codes
are touched only through `coe_toNat_eq_quote` and the depth-move lemma
`quote_toSet_congr`, never by `simp` or evaluation, and the two
`x`-dependent leaves stay behind the placeholder abstraction, so their
astronomically large successor codes are never built.
-/

set_option autoImplicit false

namespace LeanProofs
namespace ZFCinPA
namespace LocalStepSuccessor

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.SetPlaceholders
open LeanProofs.ZFCinPA.SubstIdentity
open BoundedZFCConsistency (fNumF fTripleMemF fUnivEnvF fIsFormCodeF
  fTaggedEmptyF)

/-! ## The shared source layer, re-exported

`ZFCinPA.SuccessorSources` holds every part of the route that does not
depend on which certificate field is being compiled.  The names are
re-exported into this namespace so that existing consumers — and the
audit — are unaffected by the extraction. -/

export LeanProofs.ZFCinPA.SuccessorSources
  (ShiftFixed shiftFixed_leafCode shiftFixed_closStepCode
   shift_numChainCode shiftFixed_numChainCode shift_closCode
   shiftFixed_closCode
   levelArities srcL srcPProp srcPlaceholder liftP srcNumAt srcClsAt
   translate_srcPlaceholder translate_liftP translate_liftP_val
   translate_and translate_or translate_all translate_exs
   quote_toSet_eq_code quote_leaf_move
   levelLeaves levelLeaves_zero levelLeaves_one shift_levelLeaves
   translate_srcNumAt translate_srcClsAt
   srcLvlInst srcLvlInstP translate_srcLvlInst translate_srcLvlInstP
   srcLevelSat srcSigmaTrue srcPiFalse srcPiTrue srcCanonAt
   translate_srcLevelSat translate_srcSigmaTrue translate_srcPiFalse
   translate_srcPiTrue translate_srcCanonAt
   srcNumChainSucc srcAllClause srcExClause srcJustRow srcClosStep
   translate_srcNumChainSucc translate_srcAllClause translate_srcExClause
   translate_srcJustRow translate_srcClosStep
   srcLevelSatSucc srcSigmaTrueSucc srcPiFalseSucc srcPiTrueSucc
   translate_srcLevelSatSucc translate_srcSigmaTrueSucc
   translate_srcPiFalseSucc translate_srcPiTrueSucc
   FvFree FvFree.and FvFree.or FvFree.imp FvFree.all FvFree.exs
   fvFree_liftP fvFree_srcCanonAt fvFree_srcSigmaTrue
   fvFree_srcPiTrue fvFree_srcSigmaTrueSucc fvFree_srcPiTrueSucc
   emb_univCl_of_fvFree)

/-! ## The source form of the first field -/

section SourceField

open SetTheory (Form Free)

/-- **The source form of the local-step field.**  Its specialization at
`levelLeaves x` is `localStepFormula x`, at every model index. -/
noncomputable def srcLocalStep : Proposition srcL :=
  ∀⁰ ∀⁰ (liftP (toSet 2 (fUnivEnvF 0)) 🡒
    ((liftP (toSet 2 (fTaggedEmptyF 1 2)) 🡒
        (srcCanonAt srcSigmaTrue 🡒 liftP (toSet 2 Form.fBot))) ⋏
     (liftP (toSet 2 (fIsFormCodeF 1)) 🡒
        (srcCanonAt srcSigmaTrue 🡒 srcCanonAt srcPiTrue))))

/-- **The source form of the local-step field one index up.**  The spine
is literally `srcLocalStep`'s; only the two canonical-slot payloads move
one level, to the successor readings of `ZFCinPA.SuccessorSources` — which
is where the nineteen-leaf closure-step spine is discharged. -/
noncomputable def srcLocalStepSucc : Proposition srcL :=
  ∀⁰ ∀⁰ (liftP (toSet 2 (fUnivEnvF 0)) 🡒
    ((liftP (toSet 2 (fTaggedEmptyF 1 2)) 🡒
        (srcCanonAt srcSigmaTrueSucc 🡒 liftP (toSet 2 Form.fBot))) ⋏
     (liftP (toSet 2 (fIsFormCodeF 1)) 🡒
        (srcCanonAt srcSigmaTrueSucc 🡒 srcCanonAt srcPiTrueSucc))))

/-- **The source form of the whole local-step successor implication**, at
the proposition level. -/
noncomputable def srcLocalStepStepProp : Proposition srcL :=
  srcLocalStep 🡒 srcLocalStepSucc

/-! ### Free-slot bounds of this field's three own leaves

`ZFCinPA.CertificateFields` keeps its kernel evaluations of `freeMax` on
`fUnivEnvF 0`, `fTaggedEmptyF 1 2` and `fIsFormCodeF 1` private.  They are
not needed: closedness of the whole field, `not_free_localStepF`, already
implies each of them, because `SetTheory.Free` is definitional on the
spine — two universal quantifiers put every one of these leaves two slots
up.  So no bound is re-`decide`d here. -/

theorem free_univEnv0 {i : ℕ} (h : Free i (fUnivEnvF 0)) : i < 2 := by
  by_contra hlt
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := ⟨i - 2, by omega⟩
  exact not_free_localStepF 0 k (Or.inl h)

theorem free_taggedEmpty12 {i : ℕ} (h : Free i (fTaggedEmptyF 1 2)) :
    i < 2 := by
  by_contra hlt
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := ⟨i - 2, by omega⟩
  exact not_free_localStepF 0 k (Or.inr (Or.inl (Or.inl h)))

theorem free_isFormCode1 {i : ℕ} (h : Free i (fIsFormCodeF 1)) : i < 2 := by
  by_contra hlt
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := ⟨i - 2, by omega⟩
  exact not_free_localStepF 0 k (Or.inr (Or.inr (Or.inl h)))

/-! ### The field's source formulas are free-variable-free -/

theorem fvFree_srcLocalStep : FvFree srcLocalStep := by
  refine FvFree.all (FvFree.all (FvFree.imp ?_ (FvFree.and
    (FvFree.imp ?_ (FvFree.imp ?_ ?_)) (FvFree.imp ?_ (FvFree.imp ?_ ?_)))))
  · exact fvFree_liftP (fun _ hi ↦ free_univEnv0 hi)
  · exact fvFree_liftP (fun _ hi ↦ free_taggedEmpty12 hi)
  · exact fvFree_srcCanonAt fvFree_srcSigmaTrue
  · exact fvFree_liftP (fun _ hi ↦ absurd hi (by simp [Free]))
  · exact fvFree_liftP (fun _ hi ↦ free_isFormCode1 hi)
  · exact fvFree_srcCanonAt fvFree_srcSigmaTrue
  · exact fvFree_srcCanonAt fvFree_srcPiTrue

theorem fvFree_srcLocalStepSucc : FvFree srcLocalStepSucc := by
  refine FvFree.all (FvFree.all (FvFree.imp ?_ (FvFree.and
    (FvFree.imp ?_ (FvFree.imp ?_ ?_)) (FvFree.imp ?_ (FvFree.imp ?_ ?_)))))
  · exact fvFree_liftP (fun _ hi ↦ free_univEnv0 hi)
  · exact fvFree_liftP (fun _ hi ↦ free_taggedEmpty12 hi)
  · exact fvFree_srcCanonAt fvFree_srcSigmaTrueSucc
  · exact fvFree_liftP (fun _ hi ↦ absurd hi (by simp [Free]))
  · exact fvFree_liftP (fun _ hi ↦ free_isFormCode1 hi)
  · exact fvFree_srcCanonAt fvFree_srcSigmaTrueSucc
  · exact fvFree_srcCanonAt fvFree_srcPiTrueSucc

theorem fvFree_srcLocalStepStepProp : FvFree srcLocalStepStepProp :=
  FvFree.imp fvFree_srcLocalStep fvFree_srcLocalStepSucc

/-- **The source sentence of the local-step successor.**  The universal
closure of a free-variable-free proposition, hence the same formula read
as a `Sentence srcL` — which is what
`SetPlaceholders.compileSetTemplate` consumes. -/
noncomputable def srcLocalStepStep : Sentence srcL :=
  FirstOrder.Semiformula.univCl srcLocalStepStepProp

theorem emb_srcLocalStepStep :
    (Rewriting.emb srcLocalStepStep : Proposition srcL) =
      srcLocalStepStepProp :=
  emb_univCl_of_fvFree fvFree_srcLocalStepStepProp

end SourceField

/-! ## Reconciliation of the first field -/

section Reconcile

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open SetTheory (Form Free)

/-- **The local-step field code is the specialization of a fixed source
formula.**  At every model index `x`, standard or not. -/
theorem translate_srcLocalStep (x : V) :
    (translateFormula (levelLeaves x) srcLocalStep).val = localStepCode x := by
  rw [localStepCode, localStepPart,
    show sigmaAtCode 1 0 x =
      canonAtPart (eqGuardCode 1 3) (eqGuardCode 0 2) (sigmaTrueCode (x + 1))
      from rfl,
    show piTrueAtCode 1 0 x =
      canonAtPart (eqGuardCode 1 3) (eqGuardCode 0 2) (piTrueCode (x + 1))
      from rfl]
  simp only [srcLocalStep, translate_all, translate_and, translateFormula_imp,
    Bootstrapping.Semiformula.val_all, Bootstrapping.Semiformula.val_and,
    Bootstrapping.Semiformula.val_imp, translate_liftP_val,
    translate_srcCanonAt, translate_srcSigmaTrue, translate_srcPiTrue]
  rw [← coe_toNat_eq_quote (V := V) (toSet 2 (fUnivEnvF 0)),
    ← coe_toNat_eq_quote (V := V) (toSet 2 (fTaggedEmptyF 1 2)),
    ← coe_toNat_eq_quote (V := V) (toSet 2 (fIsFormCodeF 1)),
    ← coe_toNat_eq_quote (V := V) (toSet 2 (Form.fBot))]
  rfl

/-- Typed form: the source formula specializes to the family's first
field. -/
theorem translate_srcLocalStep_formula (x : V) :
    translateFormula (levelLeaves x) srcLocalStep = localStepFormula x :=
  Bootstrapping.Semiformula.ext (translate_srcLocalStep x)

/-- **The successor of the local-step field code is the specialization of
a fixed source formula**, at every model index — the consequent half of
what `localStepSuccessor_of_source` needs. -/
theorem translate_srcLocalStepSucc (x : V) :
    (translateFormula (levelLeaves x) srcLocalStepSucc).val =
      localStepCode (x + 1) := by
  rw [localStepCode, localStepPart,
    show sigmaAtCode 1 0 (x + 1) =
      canonAtPart (eqGuardCode 1 3) (eqGuardCode 0 2)
        (sigmaTrueCode (x + 1 + 1)) from rfl,
    show piTrueAtCode 1 0 (x + 1) =
      canonAtPart (eqGuardCode 1 3) (eqGuardCode 0 2)
        (piTrueCode (x + 1 + 1)) from rfl]
  simp only [srcLocalStepSucc, translate_all, translate_and,
    translateFormula_imp, Bootstrapping.Semiformula.val_all,
    Bootstrapping.Semiformula.val_and, Bootstrapping.Semiformula.val_imp,
    translate_liftP_val, translate_srcCanonAt, translate_srcSigmaTrueSucc,
    translate_srcPiTrueSucc]
  rw [← coe_toNat_eq_quote (V := V) (toSet 2 (fUnivEnvF 0)),
    ← coe_toNat_eq_quote (V := V) (toSet 2 (fTaggedEmptyF 1 2)),
    ← coe_toNat_eq_quote (V := V) (toSet 2 (fIsFormCodeF 1)),
    ← coe_toNat_eq_quote (V := V) (toSet 2 (Form.fBot))]
  rfl

theorem translate_srcLocalStepSucc_formula (x : V) :
    translateFormula (levelLeaves x) srcLocalStepSucc =
      localStepFormula (x + 1) :=
  Bootstrapping.Semiformula.ext (translate_srcLocalStepSucc x)

/-- **The whole local-step successor implication is the specialization of
one fixed source proposition.**  This is `hσ` of
`localStepSuccessor_of_source`, at the proposition level: what remains
between it and the sentence-level hypothesis is only the closure of a
free-variable-free proposition into a `Sentence srcL`. -/
theorem translate_srcLocalStepStepProp (x : V) :
    translateFormula (levelLeaves x) srcLocalStepStepProp =
      (localStepFormula x 🡒 localStepFormula (x + 1)) := by
  show translateFormula (levelLeaves x) (srcLocalStep 🡒 srcLocalStepSucc) = _
  rw [translateFormula_imp, translate_srcLocalStep_formula,
    translate_srcLocalStepSucc_formula]

/-- **The specialization identity for the source sentence.**  This is
exactly the hypothesis `hσ` of `localStepSuccessor_of_source`, at
`σ = srcLocalStepStep`, and it is now a theorem. -/
theorem translate_srcLocalStepStep (x : V) :
    translateFormula (levelLeaves x)
        (Rewriting.emb srcLocalStepStep : Proposition srcL) =
      (localStepFormula x 🡒 localStepFormula (x + 1)) := by
  rw [emb_srcLocalStepStep]
  exact translate_srcLocalStepStepProp x

end Reconcile

/-! ## What the master certificate gives away for free -/

section Previous

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The level-`n` master certificate implies its own local-step conjunct.
`ZFCTruthCertificateFields.sentence` is right-associated with `localStep`
outermost, so this is a single `⋏`-elimination — no represented syntax is
inspected. -/
noncomputable def previous_imp_localStep (n : V)
    (h : IsFormula ℒₛₑₜ (conZFCSetCodeFun n)) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      ((concreteZFCTruthCertificateFamily (V := V)).fields n h).sentence 🡒
        localStepFormula n :=
  LO.Entailment.and₁

end Previous

/-! ## The reduction of the local-step successor to source-level data

The remaining obligation for the first field is now a statement about a
*fixed* source sentence over `srcL`, with no model and no index in it.
`localStepSuccessor_of_source` states exactly what is needed and derives
the field successor from it; every hypothesis is explicit. -/

section Reduction

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **From a source template to the local-step successor.**  Two inputs:

* `hσ` — the source sentence specializes, at every index, to the field
  implication.  Its antecedent half is already proved
  (`translate_srcLocalStep_formula`); the consequent half needs the
  successor spine, whose shared part (`srcClosStep`, `srcNumChainSucc`,
  `srcSigmaTrueSucc`, `srcPiTrueSucc`) is proved in
  `ZFCinPA.SuccessorSources`;
* `d` — one ordinary Lean proof over the lifted theory
  `templateZFC 2 ![1, 2]`.

Shift-fixedness of the two model-coded leaves — the third input of the
previous version of this statement — is no longer a hypothesis: it is
`SuccessorSources.shift_levelLeaves`.

The conclusion is the `localStep` field of
`ZFCinPA.StagedSuccessor.ZFCSuccessorImplications` at an arbitrary,
possibly nonstandard, index. -/
noncomputable def localStepSuccessor_of_source
    (σ : Sentence srcL)
    (hσ : ∀ x : V, translateFormula (levelLeaves x) (Rewriting.emb σ) =
      (localStepFormula x 🡒 localStepFormula (x + 1)))
    (d : templateZFC 2 levelArities ⊢! σ)
    (n : V) (h : IsFormula ℒₛₑₜ (conZFCSetCodeFun n)) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      ((concreteZFCTruthCertificateFamily (V := V)).fields n h).sentence 🡒
        localStepFormula (n + 1) := by
  have hc := compileSetTemplate (levelLeaves n) (shift_levelLeaves n) d
  rw [hσ n] at hc
  exact LO.Entailment.C_trans (previous_imp_localStep n h) hc

/-- **The reduction, with the specialization identity discharged.**  Only
two things are left: a *sentence* whose embedding is the source
proposition `srcLocalStepStepProp` (a closure step: the proposition is
free-variable-free, so it is the embedding of a sentence), and the source
proof itself.  Both are explicit arguments; nothing here assumes
either. -/
noncomputable def localStepSuccessor_of_sourceProof
    (σ : Sentence srcL)
    (hemb : (Rewriting.emb σ : Proposition srcL) = srcLocalStepStepProp)
    (d : templateZFC 2 levelArities ⊢! σ)
    (n : V) (h : IsFormula ℒₛₑₜ (conZFCSetCodeFun n)) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      ((concreteZFCTruthCertificateFamily (V := V)).fields n h).sentence 🡒
        localStepFormula (n + 1) :=
  localStepSuccessor_of_source σ
    (fun x ↦ by rw [hemb]; exact translate_srcLocalStepStepProp x) d n h

/-- **The first field's successor, reduced to one derivation.**  Every
other ingredient — the source sentence, its specialization identity at
every (possibly nonstandard) index, and shift-fixedness of the two
model-coded leaves — is proved.  What remains for the `localStep` field is
exactly one ordinary Lean proof of the fixed sentence `srcLocalStepStep`
over the lifted theory `templateZFC 2 ![1, 2]`; it is an explicit
argument, and nothing in this project assumes it. -/
noncomputable def localStepSuccessor_of_derivation
    (d : templateZFC 2 levelArities ⊢! srcLocalStepStep)
    (n : V) (h : IsFormula ℒₛₑₜ (conZFCSetCodeFun n)) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      ((concreteZFCTruthCertificateFamily (V := V)).fields n h).sentence 🡒
        localStepFormula (n + 1) :=
  localStepSuccessor_of_source srcLocalStepStep translate_srcLocalStepStep d n h

end Reduction

/-! ## Residue

The specialization side of the first field is complete:
`translate_srcLocalStepStep` says that at *every* model index `x`,
standard or not, the fixed source sentence `srcLocalStepStep` specializes
to `localStepFormula x 🡒 localStepFormula (x + 1)`.  Together with
`SuccessorSources.shift_levelLeaves` and
`SetPlaceholders.compileSetTemplate` that reduces the `localStep` field of
`ZFCSuccessorImplications` to exactly one obligation:

> `templateZFC 2 levelArities ⊢! srcLocalStepStep`

— one ordinary Lean proof, over a theory with no model and no index in it.

That obligation is the genuine mathematics, and it is *not* small.  The
level-`(x+2)` local polarity laws do not follow from arbitrary
interpretations of the two placeholders — for an opaque `Clos` the falsity
code is trivially certifiable — so the previous certificate really is
consumed, exactly as the implication shape of `ZFCSuccessorImplications`
allows (`srcLocalStepStep` has `srcLocalStep` as its antecedent).
Concretely:

* the first conjunct (`sigmaTrue_bot` one level up) is goal 2's
  `levelJustified_of_tag_low` argument: the justification row of the
  falsity code can only be the delegation disjunct, because the five
  structural disjuncts each force a head tag that the falsity code does
  not have.  That argument is about the *fixed* macros `fLevelImpF`,
  `fLevelAndF`, `fLevelOrF`, `fTagUnF`, so it transfers to an arbitrary
  template structure;
* the second conjunct (`piTrue_of_sigmaTrue` one level up) is goal 2's
  `sigmaTrue_not_piFalse`, whose proof is an induction over *form codes*
  using the collapse lemmas.  A single level-`(x+1)` polarity hypothesis
  is not enough for it; the source proof will need the internal form-code
  induction of `ZFCinPA.SeparationKernel` (`compileOmegaTemplate`) and,
  plausibly, the `crossLevel` conjunct of the previous certificate as
  well.  Should the latter be needed, the antecedent of the source
  sentence has to be widened from `srcLocalStep` to the conjunction of the
  two previous fields — which the implication shape of
  `ZFCSuccessorImplications` still permits, via
  `previous_imp_localStep`'s sibling `⋏`-eliminations, but which changes
  `srcLocalStepStep`; nothing below assumes either shape.

Nothing above weakens `ZFCSuccessorImplications`, and no part of it is
assumed anywhere in this file: `localStepSuccessor_of_derivation` takes
the source proof as an explicit argument. -/

end LocalStepSuccessor
end ZFCinPA
end LeanProofs
