import ZFCinPA.NumeralOmega
import ZFCinPA.TowerEvaluation

/-!
# The numeral placeholder is pinned: `Num` is a singleton, internally and
uniformly

Item 3 of the residue list of `ZFCinPA.FieldEvaluation`.

`TemplateEvaluation.templateStepLevel` reads the successor level as

```
templateStepLevel X H c en bi :≡ ∃ k, Num k ∧ Step H (templateLevel X H) k⁺ c en bi
```

— the bound is *existentially quantified*, because the source syntax
(`SuccessorSources.srcNumChainSucc`) only says "the next index is the
successor of **some** `Num`".  `LocalStepTransfer.localStepLaws_step`, on
the other hand, concludes something about **one** fixed bound `b`, and its
exclusivity conjunct genuinely needs the *same* witness at both
polarities.  Two occurrences of the successor reading may therefore pick
different witnesses, and the gap is closed only by knowing that the
placeholder `Num` has at most one element.

That is not implied by any certificate field, so — exactly like the
`b ∈ ω` obligation discharged in `ZFCinPA.NumeralOmega` — it has to be
carried as a source antecedent and discharged after translation, where the
placeholder has become the concrete numeral chain `numChainCode x`.

This module supplies both halves:

* the source antecedent `srcNumUnique : Proposition srcL`, with its
  translation identity (`translate_srcNumUnique_val`), its
  free-variable-freeness (`fvFree_srcNumUnique`) and its reading in an
  arbitrary template structure (`eval_srcNumUnique`), which is literally
  `∀ k k', Num k → Num k' → k = k'`;
* the **post-translation discharge**, uniformly in `x : V`:

```
zfcInternal_numChain_unique (x : V) :
  (𝗭𝗙𝗖).internalize V ⊢! translateFormula (levelLeaves x) srcNumUnique
```

  so a consumer feeds `zfcInternal_numChain_unique` straight into the
  antecedent slot of the assembled source implication, exactly as
  `LocalStepDerivation.translated_srcCongruence` is fed into the
  congruence slot.

## The shape, and why it needs no substitution bookkeeping

The statement is written with the two occurrences of the placeholder at
**consecutive ambient arities and the same argument `#0`**:

```
srcNumUnique  =  ∀⁰ (Num #0 🡒 ∀⁰ (Num #0 🡒 #1 = #0))
```

rather than the symmetric `∀⁰ ∀⁰ (Num #1 🡒 Num #0 🡒 #1 = #0)`.  The two
are logically the same sentence, but the chosen one specializes without a
single substitution surviving: `SetPlaceholders.translateFormula` sends a
placeholder atom at the identity argument list to the *raw leaf code*
(`SuccessorSources.translate_srcPlaceholder`, via `ZFCinPA.SubstIdentity`),
at **every** ambient arity.  So

```
(translateFormula (levelLeaves x) srcNumUnique).val
  = ^∀ (numChainCode x 🡒 ^∀ (numChainCode x 🡒 ⌜#1 = #0⌝))
```

with `numChainCode x` appearing literally twice.  The symmetric variant
would have produced `subst ![#1]` at the outer slot, whose raw code is
*not* `numChainCode x`, and every downstream identity would have had to
push that substitution through the chain's own successor equation.

## The route: no internal induction at all

`SeparationKernel.zfcOmegaInductionOfShiftFixed` is **not** instantiable
here, for the reason `ZFCinPA.NumeralOmega`'s header records: that kernel
proves `∀⁰ (isVonNeumannNatQ 🡒 K)`, an induction *over sets* with the
ω-predicate in the antecedent, whereas the induction wanted here is over
the **ambient index** `x : V`, which is not a set of the interpreted
universe.  The obstruction is identical and the check was performed
before choosing the route.

But — and this is the cheap route the residue note hoped for — no internal
induction of any kind is needed, and in particular no Separation instance
and no internal ω-induction:

* At a template structure with **genuine equality**, the two fixed leaves
  of the chain are *equations*, not merely descriptions:
  `Sat (fNumF 0 0) e` is `e 0 = natV H 0` (`fNumF_spec`) and
  `Sat (fSuccF 1 0) e` is `e 1 = vsucc H (e 0)` (`fSuccF_spec`).  So
  uniqueness at level `0` is "both are `∅`" and the step from level `x` to
  level `x + 1` is "both are the successor of the same thing".  Both are
  one-line semantic facts; neither uses Extensionality, Separation, or
  Infinity.
* Two fixed source sentences over `templateZFC 2 levelArities` therefore
  suffice, produced by
  `SetPlaceholderQuotient.complete_underSetPlaceholderCongruence` (which
  is what supplies the genuine equality, at the price of the placeholder
  congruence antecedent — discharged after translation by the already
  landed `LocalStepDerivation.translated_srcCongruence`).
* The only induction is the **ambient** `𝚺₁` successor induction on
  `x : V`, in the `ZFCinPA.PackageInduction` pattern used by
  `NumeralOmega.provable_numChainOmegaCode`: the induction predicate is
  `Provable 𝗭𝗙𝗖 (numChainUniqueCode x)`, whose code function is the fixed
  implication spine over `numChainCode x`.

## Disciplines

The parameter firewall of `ZFCinPA.LevelCodeTower` is respected: the only
concrete Gödel constants touched are `numChainZeroCode` (through
`quote_leaf_move`, at its own declared depth) and `eqGuardCode 1 0`
(through `CertificateFields.quote_fEq_move`).  No `simp` goal ever
contains one, and no code is ever evaluated.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

namespace LeanProofs
namespace ZFCinPA
namespace NumeralUnique

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.SetPlaceholders
open LeanProofs.ZFCinPA.SetPlaceholderQuotient
open LeanProofs.ZFCinPA.SuccessorSources
open LeanProofs.ZFCinPA.TemplateEvaluation
open BoundedZFCConsistency (fNumF fNumF_spec natV)
open SetTheory (Form Free ZFAxioms scons Sat vsucc)

/-! ## The source formulas

All four live in `srcL = setTemplateLanguage 2 levelArities`, the
placeholder language of the level tower, and are assembled at the
*proposition* level in the style of `ZFCinPA.SuccessorSources` — the fixed
`ℒₛₑₜ` leaves are `toSet`-translations, which are `Semiproposition`s. -/

section Source

/-- The numeral placeholder at the identity argument list, at ambient
arity `1`. -/
noncomputable def srcNum₁ : Semiproposition srcL 1 := srcNumAt (by omega)

/-- The numeral placeholder at the identity argument list, at ambient
arity `2`.  Its specialization has the *same* raw code as `srcNum₁`'s:
the argument list is `#0` in both cases, and `#0` is the innermost bound
slot at either arity. -/
noncomputable def srcNum₂ : Semiproposition srcL 2 := srcNumAt (by omega)

/-- The equality payload: the outer bound slot equals the inner one. -/
noncomputable def srcEqSlots : Semiproposition srcL 2 :=
  liftP (toSet 2 (Form.fEq 1 0))

/-- **`Num`-uniqueness, as a source formula.**  "For all `k`, if `Num k`
then for all `k'`, if `Num k'` then `k = k'`." -/
noncomputable def srcNumUnique : Proposition srcL :=
  ∀⁰ (srcNum₁ 🡒 ∀⁰ (srcNum₂ 🡒 srcEqSlots))

/-- `Num`-uniqueness one index up: the same statement with the placeholder
replaced by the numeral chain's successor spine. -/
noncomputable def srcNumUniqueSucc : Proposition srcL :=
  ∀⁰ (srcNumChainSucc 1 🡒 ∀⁰ (srcNumChainSucc 2 🡒 srcEqSlots))

/-- `Num`-uniqueness at index zero, written with the chain's base leaf in
place of the placeholder.  No placeholder occurs, so its specialization is
a fixed code — the one the chain has at index `0`. -/
noncomputable def srcNumUniqueZero : Proposition srcL :=
  ∀⁰ (liftP (toSet 1 (fNumF 0 0)) 🡒
    ∀⁰ (liftP (toSet 2 (fNumF 0 0)) 🡒 srcEqSlots))

/-- The successor step of the uniqueness statement. -/
noncomputable def srcNumUniqueStep : Proposition srcL :=
  srcNumUnique 🡒 srcNumUniqueSucc

end Source

/-! ## Free-variable-freeness

`SetPlaceholderQuotient.complete_underSetPlaceholderCongruence` consumes a
`Sentence srcL`; `SuccessorSources.emb_univCl_of_fvFree` reconciles that
with the proposition-level assembly. -/

section FvFree

theorem fvFree_srcNum₁ : FvFree srcNum₁ := fvFree_srcNumAt _

theorem fvFree_srcNum₂ : FvFree srcNum₂ := fvFree_srcNumAt _

theorem fvFree_srcEqSlots : FvFree srcEqSlots :=
  fvFree_liftP (fun i hi ↦ by rcases free_fEq hi with rfl | rfl <;> omega)

theorem fvFree_srcNumUnique : FvFree srcNumUnique :=
  .all (fvFree_srcNum₁.imp (.all (fvFree_srcNum₂.imp fvFree_srcEqSlots)))

theorem fvFree_srcNumUniqueSucc : FvFree srcNumUniqueSucc :=
  .all ((fvFree_srcNumChainSucc 1 (by omega)).imp
    (.all ((fvFree_srcNumChainSucc 2 (by omega)).imp fvFree_srcEqSlots)))

theorem fvFree_srcNumUniqueZero : FvFree srcNumUniqueZero :=
  .all ((fvFree_liftP (fun i hi ↦ by have := free_numChainZero hi; omega)).imp
    (.all ((fvFree_liftP
      (fun i hi ↦ by have := free_numChainZero hi; omega)).imp
        fvFree_srcEqSlots)))

theorem fvFree_srcNumUniqueStep : FvFree srcNumUniqueStep :=
  fvFree_srcNumUnique.imp fvFree_srcNumUniqueSucc

/-- The uniqueness antecedent, as the `Sentence srcL` the completeness
route consumes. -/
noncomputable def srcNumUniqueSentence : Sentence srcL :=
  FirstOrder.Semiformula.univCl srcNumUnique

/-- Its base instance, likewise closed. -/
noncomputable def srcNumUniqueZeroSentence : Sentence srcL :=
  FirstOrder.Semiformula.univCl srcNumUniqueZero

/-- Its successor step, likewise closed. -/
noncomputable def srcNumUniqueStepSentence : Sentence srcL :=
  FirstOrder.Semiformula.univCl srcNumUniqueStep

theorem emb_srcNumUniqueSentence :
    (Rewriting.emb srcNumUniqueSentence : Proposition srcL) = srcNumUnique :=
  emb_univCl_of_fvFree fvFree_srcNumUnique

theorem emb_srcNumUniqueZeroSentence :
    (Rewriting.emb srcNumUniqueZeroSentence : Proposition srcL) =
      srcNumUniqueZero :=
  emb_univCl_of_fvFree fvFree_srcNumUniqueZero

theorem emb_srcNumUniqueStepSentence :
    (Rewriting.emb srcNumUniqueStepSentence : Proposition srcL) =
      srcNumUniqueStep :=
  emb_univCl_of_fvFree fvFree_srcNumUniqueStep

end FvFree

/-! ## The translation identities

The code of the uniqueness statement at index `x` is the fixed
implication spine over `numChainCode x`.  This is the `𝚺₁`-definable
function the ambient induction below runs on. -/

section Translate

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The raw code of the uniqueness statement at index `x`. -/
noncomputable def numChainUniqueCode (x : V) : V :=
  ^∀ (Bootstrapping.imp ℒₛₑₜ (numChainCode x)
    (^∀ (Bootstrapping.imp ℒₛₑₜ (numChainCode x)
      ((eqGuardCode 1 0 : ℕ) : V))))

theorem translate_srcNum₁ (x : V) :
    (translateFormula (levelLeaves x) srcNum₁).val = numChainCode x :=
  translate_srcNumAt _ x

theorem translate_srcNum₂ (x : V) :
    (translateFormula (levelLeaves x) srcNum₂).val = numChainCode x :=
  translate_srcNumAt _ x

theorem translate_srcEqSlots (x : V) :
    (translateFormula (levelLeaves x) srcEqSlots).val
      = ((eqGuardCode 1 0 : ℕ) : V) := by
  rw [srcEqSlots, translate_liftP_val]
  exact quote_fEq_move (V := V) (show (1 : ℕ) < 2 by omega)
    (show (0 : ℕ) < 2 by omega)

/-- The base leaf, read at any depth that can hold it, is the chain's own
code at index `0`. -/
theorem quote_numZeroLeaf {k : ℕ} (hk : ∀ i, Free i (fNumF 0 0) → i < k) :
    (⌜toSet k (fNumF 0 0)⌝ : V) = numChainCode (0 : V) := by
  rw [numChainCode_zero]
  exact quote_leaf_move (fNumF 0 0) k 1 hk (fun i hi ↦ free_numChainZero hi)

/-- **The uniqueness statement specializes to the fixed spine.** -/
theorem translate_srcNumUnique_val (x : V) :
    (translateFormula (levelLeaves x) srcNumUnique).val
      = numChainUniqueCode x := by
  simp only [srcNumUnique, numChainUniqueCode, translate_all,
    translateFormula_imp, Bootstrapping.Semiformula.val_all,
    Bootstrapping.Semiformula.val_imp, translate_srcNum₁, translate_srcNum₂,
    translate_srcEqSlots]

/-- **The successor form specializes to the spine one index up.** -/
theorem translate_srcNumUniqueSucc_val (x : V) :
    (translateFormula (levelLeaves x) srcNumUniqueSucc).val
      = numChainUniqueCode (x + 1) := by
  simp only [srcNumUniqueSucc, numChainUniqueCode, translate_all,
    translateFormula_imp, Bootstrapping.Semiformula.val_all,
    Bootstrapping.Semiformula.val_imp, translate_srcEqSlots,
    translate_srcNumChainSucc x 1 (by omega),
    translate_srcNumChainSucc x 2 (by omega)]

/-- **The base form specializes to the spine at index `0`**, at every
interpretation of the placeholders — it mentions none. -/
theorem translate_srcNumUniqueZero_val (x : V) :
    (translateFormula (levelLeaves x) srcNumUniqueZero).val
      = numChainUniqueCode (0 : V) := by
  simp only [srcNumUniqueZero, numChainUniqueCode, translate_all,
    translateFormula_imp, Bootstrapping.Semiformula.val_all,
    Bootstrapping.Semiformula.val_imp, translate_srcEqSlots,
    translate_liftP_val]
  rw [quote_numZeroLeaf (V := V) (k := 1) (fun i hi ↦ free_numChainZero hi),
    quote_numZeroLeaf (V := V) (k := 2)
      (fun i hi ↦ by have := free_numChainZero hi; omega)]

end Translate

/-! ## Reading the source formulas in an arbitrary template structure

This is the evaluation bridge for the new antecedent, in the vocabulary of
`ZFCinPA.TemplateEvaluation`. -/

section Evaluation

variable {X : Type*} [Nonempty X] [sX : Structure srcL X] [Structure.Eq srcL X]

omit [Nonempty X] [Structure.Eq srcL X] in
/-- The numeral placeholder at ambient arity `1`. -/
theorem eval_srcNum₁ (f : ℕ → X) (x1 : X) :
    Semiformula.Eval (s := sX) (x1 :> (![] : Fin 0 → X)) f srcNum₁ ↔
      templateNum X x1 :=
  eval_srcNumAt _ _ _

omit [Nonempty X] [Structure.Eq srcL X] in
/-- The numeral placeholder at ambient arity `2`: it reads the *inner*
bound slot. -/
theorem eval_srcNum₂ (f : ℕ → X) (x1 x0 : X) :
    Semiformula.Eval (s := sX) (x0 :> x1 :> (![] : Fin 0 → X)) f srcNum₂ ↔
      templateNum X x0 :=
  eval_srcNumAt _ _ _

/-- The equality payload reads as genuine equality of the two bound
slots. -/
theorem eval_srcEqSlots (f : ℕ → X) (x1 x0 : X) :
    Semiformula.Eval (s := sX) (x0 :> x1 :> (![] : Fin 0 → X)) f srcEqSlots ↔
      x1 = x0 :=
  eval_liftP (((Corr.zero f).cons x1).cons x0) (Form.fEq 1 0)

/-- **`srcNumUnique` says exactly that the numeral placeholder has at most
one element.** -/
theorem eval_srcNumUnique (f : ℕ → X) :
    Semiformula.Eval (s := sX) ![] f srcNumUnique ↔
      ∀ k k' : X, templateNum X k → templateNum X k' → k = k' := by
  simp only [srcNumUnique, Semiformula.eval_all,
    LogicalConnective.HomClass.map_imply, eval_srcNum₁, eval_srcNum₂,
    eval_srcEqSlots]
  exact ⟨fun hh k k' h1 h2 ↦ hh k h1 k' h2, fun hh x1 h1 x0 h2 ↦ hh x1 x0 h1 h2⟩

/-- **`srcNumUniqueSucc` says that the successor spine has at most one
element.** -/
theorem eval_srcNumUniqueSucc (f : ℕ → X) (H : ZFAxioms (templateMem X)) :
    Semiformula.Eval (s := sX) ![] f srcNumUniqueSucc ↔
      ∀ k k' : X, (∃ n, templateNum X n ∧ k = vsucc H n) →
        (∃ n, templateNum X n ∧ k' = vsucc H n) → k = k' := by
  have h1 : ∀ x1 : X,
      Semiformula.Eval (s := sX) (x1 :> (![] : Fin 0 → X)) f
          (srcNumChainSucc 1) ↔
        ∃ n, templateNum X n ∧ x1 = vsucc H n :=
    fun x1 ↦ eval_srcNumChainSucc 1 ((Corr.zero f).cons x1) H
  have h2 : ∀ x1 x0 : X,
      Semiformula.Eval (s := sX) (x0 :> x1 :> (![] : Fin 0 → X)) f
          (srcNumChainSucc 2) ↔
        ∃ n, templateNum X n ∧ x0 = vsucc H n :=
    fun x1 x0 ↦ eval_srcNumChainSucc 2 (((Corr.zero f).cons x1).cons x0) H
  simp only [srcNumUniqueSucc, Semiformula.eval_all,
    LogicalConnective.HomClass.map_imply, h1, h2, eval_srcEqSlots]
  exact ⟨fun hh k k' hk hk' ↦ hh k hk k' hk',
    fun hh x1 hx1 x0 hx0 ↦ hh x1 x0 hx1 hx0⟩

/-- **`srcNumUniqueZero` says that the empty set is unique.** -/
theorem eval_srcNumUniqueZero (f : ℕ → X) (H : ZFAxioms (templateMem X)) :
    Semiformula.Eval (s := sX) ![] f srcNumUniqueZero ↔
      ∀ k k' : X, k = natV H 0 → k' = natV H 0 → k = k' := by
  have h1 : ∀ x1 : X,
      Semiformula.Eval (s := sX) (x1 :> (![] : Fin 0 → X)) f
          (liftP (toSet 1 (fNumF 0 0))) ↔ x1 = natV H 0 :=
    fun x1 ↦ (eval_liftP ((Corr.zero f).cons x1) (fNumF 0 0)).trans
      (fNumF_spec H 0 0 (scons x1 f))
  have h2 : ∀ x1 x0 : X,
      Semiformula.Eval (s := sX) (x0 :> x1 :> (![] : Fin 0 → X)) f
          (liftP (toSet 2 (fNumF 0 0))) ↔ x0 = natV H 0 :=
    fun x1 x0 ↦ (eval_liftP (((Corr.zero f).cons x1).cons x0) (fNumF 0 0)).trans
      (fNumF_spec H 0 0 (scons x0 (scons x1 f)))
  simp only [srcNumUniqueZero, Semiformula.eval_all,
    LogicalConnective.HomClass.map_imply, h1, h2, eval_srcEqSlots]
  exact ⟨fun hh k k' hk hk' ↦ hh k hk k' hk',
    fun hh x1 hx1 x0 hx0 ↦ hh x1 x0 hx1 hx0⟩

end Evaluation

/-! ## The two fixed source derivations

Both are obtained by
`SetPlaceholderQuotient.complete_underSetPlaceholderCongruence`, so both
carry the placeholder congruence laws as an antecedent — which is what the
completeness route always yields, and which
`LocalStepDerivation.translated_srcCongruence` discharges after
translation. -/

/-- **The base.**  In a template structure with genuine equality, the
chain's base leaf *is* the equation "`= ∅`", so two witnesses are equal. -/
noncomputable def srcNumUniqueZeroProof :
    templateZFC 2 levelArities ⊢!
      (LocalStepDerivation.srcCongruence 🡒 srcNumUniqueZeroSentence) := by
  refine complete_underSetPlaceholderCongruence srcNumUniqueZeroSentence ?_
  intro X _ _ _ _
  show X↓[srcL] ⊧ FirstOrder.Semiformula.univCl srcNumUniqueZero
  refine models_iff_proposition.mpr fun f ↦ ?_
  have H : ZFAxioms (templateMem X) := zfAxioms_of_template
  exact (eval_srcNumUniqueZero f H).mpr
    (fun _ _ hk hk' ↦ by rw [hk, hk'])

/-- **The step.**  In a template structure with genuine equality, the
chain's step leaf *is* the equation "`= k⁺`", so uniqueness of the
predecessors gives uniqueness of the successors.  No set-theoretic axiom
beyond the six-clause bundle's existence of `vsucc` is used. -/
noncomputable def srcNumUniqueStepProof :
    templateZFC 2 levelArities ⊢!
      (LocalStepDerivation.srcCongruence 🡒 srcNumUniqueStepSentence) := by
  refine complete_underSetPlaceholderCongruence srcNumUniqueStepSentence ?_
  intro X _ _ _ _
  show X↓[srcL] ⊧ FirstOrder.Semiformula.univCl srcNumUniqueStep
  refine models_iff_proposition.mpr fun f ↦ ?_
  have H : ZFAxioms (templateMem X) := zfAxioms_of_template
  show Semiformula.Eval ![] f (srcNumUnique 🡒 srcNumUniqueSucc)
  rw [LogicalConnective.HomClass.map_imply, eval_srcNumUnique,
    eval_srcNumUniqueSucc f H]
  rintro huniq k k' ⟨n, hn, rfl⟩ ⟨n', hn', rfl⟩
  rw [huniq n n' hn hn']

/-! ## The internal discharge

The compiled source derivations, glued by an ambient `𝚺₁` successor
induction on the index. -/

section Internal

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **The uniform internal statement**: the specialization of
`srcNumUnique` at the level tower's own leaves. -/
noncomputable def numChainUniqueStmt (x : V) : Bootstrapping.Formula V ℒₛₑₜ :=
  translateFormula (levelLeaves x) srcNumUnique

theorem numChainUniqueStmt_val (x : V) :
    (numChainUniqueStmt x).val = numChainUniqueCode x :=
  translate_srcNumUnique_val x

/-- Compile a congruence-widened source sentence at the level tower's
leaves and discharge the congruence antecedent. -/
noncomputable def compileCongruent {σ : Sentence srcL}
    (d : templateZFC 2 levelArities ⊢!
      (LocalStepDerivation.srcCongruence 🡒 σ)) (x : V) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      translateFormula (levelLeaves x) (Rewriting.emb σ) := by
  have hc := compileSetTemplate (levelLeaves x) (shift_levelLeaves x) d
  rw [show (Rewriting.emb (LocalStepDerivation.srcCongruence 🡒 σ) :
        Proposition srcL)
      = ((Rewriting.emb LocalStepDerivation.srcCongruence : Proposition srcL) 🡒
        (Rewriting.emb σ : Proposition srcL)) from by
      simp only [LogicalConnective.HomClass.map_imply],
    translateFormula_imp] at hc
  exact TProof.modusPonens hc
    (LocalStepDerivation.translated_srcCongruence (V := V) x).get

/-- **The base**, at the chain's own zero code. -/
noncomputable def numChainUniqueBase :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢! numChainUniqueStmt (0 : V) := by
  have h := compileCongruent srcNumUniqueZeroProof (0 : V)
  rw [emb_srcNumUniqueZeroSentence] at h
  have he : translateFormula (levelLeaves (0 : V)) srcNumUniqueZero
      = numChainUniqueStmt (0 : V) :=
    Bootstrapping.Semiformula.ext (by
      rw [translate_srcNumUniqueZero_val, numChainUniqueStmt_val])
  rwa [he] at h

/-- **The step**, at the chain's own successor equation. -/
noncomputable def numChainUniqueStep (x : V) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      (numChainUniqueStmt x 🡒 numChainUniqueStmt (x + 1)) := by
  have h := compileCongruent srcNumUniqueStepProof x
  rw [emb_srcNumUniqueStepSentence] at h
  have himp : translateFormula (levelLeaves x) srcNumUniqueStep
      = (numChainUniqueStmt x 🡒 numChainUniqueStmt (x + 1)) := by
    apply Bootstrapping.Semiformula.ext
    show (translateFormula (levelLeaves x)
      (srcNumUnique 🡒 srcNumUniqueSucc)).val = _
    rw [translateFormula_imp]
    simp only [Bootstrapping.Semiformula.val_imp, numChainUniqueStmt_val,
      translate_srcNumUnique_val, translate_srcNumUniqueSucc_val]
  rwa [himp] at h

/-- **Uniform provability of the statement code.**  A `𝚺₁` successor
induction inside the ambient model: `x` ranges over all of `V`,
nonstandard indices included.  Nothing here is an external recursion over
`Nat`. -/
theorem provable_numChainUniqueCode (x : V) :
    Provable (𝗭𝗙𝗖 : SetTheory) (numChainUniqueCode x) := by
  induction x using ISigma1.sigma1_succ_induction
  · simp only [numChainUniqueCode, Bootstrapping.imp]
    definability
  case zero =>
    have h : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢ numChainUniqueStmt (0 : V) :=
      ⟨numChainUniqueBase⟩
    have h' := tprovable_iff_provable.mp h
    rwa [numChainUniqueStmt_val] at h'
  case succ x ih =>
    have hx : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢ numChainUniqueStmt x :=
      tprovable_iff_provable.mpr (by rw [numChainUniqueStmt_val]; exact ih)
    have hs : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢ numChainUniqueStmt (x + 1) :=
      ⟨TProof.modusPonens (numChainUniqueStep x) hx.get⟩
    have h' := tprovable_iff_provable.mp hs
    rwa [numChainUniqueStmt_val] at h'

/-- **The uniform internal uniqueness of the numeral chain.**  At every
element `x` of the ambient model — standard or not — `𝗭𝗙𝗖` internally
proves the translated `Num`-uniqueness antecedent at index `x`.  This is
the form a consumer needs: it is *literally* the specialization of the
source formula `srcNumUnique`, so it slots into a compiled source
implication by `TProof.modusPonens`. -/
noncomputable def zfcInternal_numChain_unique (x : V) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢! numChainUniqueStmt x :=
  (tprovable_iff_provable.mpr
    (by rw [numChainUniqueStmt_val]; exact provable_numChainUniqueCode x)).get

/-- The same, as a `Prop`-valued provability statement. -/
theorem zfcInternal_numChain_unique_provable (x : V) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢ numChainUniqueStmt x :=
  ⟨zfcInternal_numChain_unique x⟩

/-- The endpoint spelled out at the source formula, which is the shape the
assembly consumes. -/
noncomputable def zfcInternal_srcNumUnique (x : V) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      translateFormula (levelLeaves x) srcNumUnique :=
  zfcInternal_numChain_unique x

end Internal

/-! ## Residue

Nothing in this module is assumed anywhere, and nothing here weakens
`StagedSuccessor.ZFCSuccessorImplications`.

What this module does **not** do:

* It does not assemble the full source sentence of item 5 of
  `ZFCinPA.FieldEvaluation`'s residue.  `srcNumUnique` is the antecedent;
  the implication `(srcNumOmega ⋏ srcNumUnique ⋏ srcCodeInduction ⋏
  srcLaws) 🡒 srcLocalStepSucc` still has to be stated and proved, and its
  other three antecedents are items 1, 2 and 4 of that list.
* It does not supply the `ω`-membership antecedent; that is
  `ZFCinPA.NumeralOmega.zfcInternal_numChain_omega`, whose statement is
  phrased in `SeparationKernel`'s one-placeholder vocabulary rather than
  in `srcL`.  A consumer that wants both antecedents in the *same*
  vocabulary still has to restate the ω-membership one over `srcL` (the
  code identity is immediate — `translate_srcNum₁` shows the `srcL`
  placeholder specializes to the very same `numChainCode x` — but the
  restatement itself is not written here).
* It says nothing about whether `Num` is *nonempty*.  Uniqueness is what
  `LocalStepTransfer.localStepLaws_step`'s exclusivity conjunct needs;
  an existence antecedent, if a later field turns out to need one, is a
  separate obligation. -/

end NumeralUnique
end ZFCinPA
end LeanProofs
