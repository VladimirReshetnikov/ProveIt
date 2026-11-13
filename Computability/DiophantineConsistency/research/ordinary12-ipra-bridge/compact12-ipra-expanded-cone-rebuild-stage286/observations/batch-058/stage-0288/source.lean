import ZFCinPA.SeparationKernel
import ZFCinPA.ConcreteFamily
import ZFCinPA.SuccessorSources

/-!
# The numeral chain lands in `ω`, internally and uniformly

`ZFCinPA.LocalStepTransfer` recorded a new obligation (item 2 of its
residue): every rank lemma the local-step transfer consumes carries
`mem b (omegaV H)` — "the bound is an internal natural number" — as an
explicit hypothesis, and in the source template the bound is the *numeral
placeholder*, whose interpretation an arbitrary template structure may
choose freely.  So the source sentence has to carry "every `Num` is a
natural" as an antecedent, and after translation, where the placeholder has
become the concrete numeral chain `numChainCode x`, that antecedent has to
be discharged **internally**.

This module discharges it, uniformly in `x : V`:

```
(𝗭𝗙𝗖).internalize V ⊢! ∀⁰ (numChainQ x 🡒 isVonNeumannNatQ)
```

with `numChainQ x` the typed view of `UniformStatement.numChainCode x` (the
code of `toSet 1 (fNumF 0 x)`) and `isVonNeumannNatQ` *exactly* the
ω-predicate of `ZFCinPA.SeparationKernel` — membership in every inductive
set — so that the two kernels' vocabularies agree and a consumer can feed
this proof straight into the rank lemmas' antecedent.

## Why this is not an instance of the ω-induction kernel

`SeparationKernel.zfcOmegaInductionOfShiftFixed` turns a base and a
successor premise into `∀⁰ (isVonNeumannNatQ 🡒 K)`: an induction **over
sets**, with the ω-predicate in the *antecedent*.  The statement here has
the ω-predicate in the *consequent*, and its induction is over the
**ambient index** `x : V`, which is not a set of the interpreted universe
at all.  The kernel is therefore not instantiable here (in either
direction), and the route is the bespoke one:

* a fixed source derivation for the base and one for the successor step,
  over `SeparationKernel.setTemplateLanguage`, both compiled at the
  model-coded predicate `K := numChainQ x` by
  `SeparationKernel.compileOmegaTemplate` — the same typed template proof
  compiler the ω-induction kernel uses;
* a model-internal `𝚺₁` successor induction on `x` gluing them, in the
  pattern of `ZFCinPA.PackageInduction`: the induction predicate is
  `Provable 𝗭𝗙𝗖 (numChainOmegaCode x)`, whose code function is the fixed
  implication spine over `numChainCode x`.

Both source derivations are *logically valid* — they use no set-theoretic
axiom whatever, in particular no Extensionality: the numeral chain's step
leaf `toSet 2 (fSuccF 1 0)` and the successor clause of `isVonNeumannNat`
are the **same** description `∀ z, z ∈ x' ↔ (z ∈ x ∨ z = x)` up to the
order of the two disjuncts, and the inductive-set clause of
`isVonNeumannNat` quantifies universally over the successor, so no
identification of two successor witnesses is ever needed.  They are
nevertheless produced through `omegaSourceTheory` and Foundation's
completeness, exactly like `SeparationKernel.omegaSourceProof`, so that the
placeholder and the membership relation stay uninterpreted.

## The two fixed leaves

`numChainCode` is built from two standard codes,
`numChainZeroCode = (toSet 1 (fNumF 0 0)).toNat` and
`numChainStepCode = (toSet 2 (fSuccF 1 0)).toNat`.  `liftSet` needs
`ℒₛₑₜ`-*semisentences*, so `numZeroS`/`succRelS` write those two
translations out with explicit constructors and `emb_numZeroS`/
`emb_succRelS` check the match.  Both are tiny formulas; the parameter
firewall of `ZFCinPA.LevelCodeTower` is respected throughout — the two
Gödel constants are named `ℕ`s, touched only through `coe_toNat_eq_quote`,
and no `simp` goal ever contains one.
-/

set_option autoImplicit false

namespace LeanProofs
namespace ZFCinPA
namespace NumeralOmega

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.SeparationKernel
open LeanProofs.ZFCinPA.SuccessorSources (shift_numChainCode)

/-! ## The two standard leaves of the numeral chain

`toSet 1 (fNumF 0 0)` and `toSet 2 (fSuccF 1 0)`, written out as
`ℒₛₑₜ`-semisentences so that `SeparationKernel.liftSet` accepts them and so
that their evaluation in an arbitrary structure is transparent. -/

/-- The base leaf: "`#0` is empty", in the exact shape of
`toSet 1 (fNumF 0 0)`. -/
def numZeroS : SetTheorySemisentence 1 :=
  ∀⁰ (FirstOrder.Semiformula.rel Language.Mem.mem ![#0, #1] 🡒 ⊥)

/-- The step leaf: "`#1` is the successor of `#0`", in the exact shape of
`toSet 2 (fSuccF 1 0)` (which is `fSetByF 1 (fOr (fMem 0 1) (fEq 0 1))`,
i.e. an `fIff` unfolded into two implications). -/
def succRelS : SetTheorySemisentence 2 :=
  ∀⁰ (((FirstOrder.Semiformula.rel Language.Mem.mem ![#0, #2]) 🡒
        ((FirstOrder.Semiformula.rel Language.Mem.mem ![#0, #1]) ⋎
          (FirstOrder.Semiformula.rel Language.Eq.eq ![#0, #1]))) ⋏
      (((FirstOrder.Semiformula.rel Language.Mem.mem ![#0, #1]) ⋎
          (FirstOrder.Semiformula.rel Language.Eq.eq ![#0, #1])) 🡒
        (FirstOrder.Semiformula.rel Language.Mem.mem ![#0, #2])))

/-- `numZeroS` is the depth-`1` translation of the chain's base. -/
theorem emb_numZeroS :
    (Rewriting.emb numZeroS : SetTheorySemiproposition 1)
      = toSet 1 (BoundedZFCConsistency.fNumF 0 0) := by
  simp [numZeroS, BoundedZFCConsistency.fNumF, SetTheory.fEmptyF, toSet,
    toSetVar, Matrix.comp_vecCons', Function.comp_def]
  funext i
  match i with
  | 0 => rfl

/-- `succRelS` is the depth-`2` translation of the chain's step. -/
theorem emb_succRelS :
    (Rewriting.emb succRelS : SetTheorySemiproposition 2)
      = toSet 2 (SetTheory.fSuccF 1 0) := by
  simp [succRelS, SetTheory.fSuccF, SetTheory.fSetByF, SetTheory.fIff, toSet,
    toSetVar, Matrix.comp_vecCons', Function.comp_def]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> funext i <;>
    exact match i with | 0 => rfl

section Codes

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The typed quotation of the base leaf is the chain's base code. -/
theorem quote_numZeroS_val :
    (⌜numZeroS⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 1).val
      = ((numChainZeroCode : ℕ) : V) := by
  unfold numChainZeroCode
  rw [coe_toNat_eq_quote (V := V) (toSet 1 (BoundedZFCConsistency.fNumF 0 0)),
    ← emb_numZeroS]
  rfl

/-- The typed quotation of the step leaf is the chain's step code. -/
theorem quote_succRelS_val :
    (⌜succRelS⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 2).val
      = ((numChainStepCode : ℕ) : V) := by
  unfold numChainStepCode
  rw [coe_toNat_eq_quote (V := V) (toSet 2 (SetTheory.fSuccF 1 0)),
    ← emb_succRelS]
  rfl

end Codes

/-! ## The numeral chain as a typed model-coded formula -/

section Chain

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The typed view of `numChainCode x`.  Well-formedness at every (possibly
nonstandard) index is `ConcreteFamily.isSemiformula_numChainCode`. -/
noncomputable def numChainQ (x : V) : Bootstrapping.Semiformula V ℒₛₑₜ 1 :=
  ⟨numChainCode x, by simpa using isSemiformula_numChainCode x⟩

@[simp] theorem numChainQ_val (x : V) : (numChainQ x).val = numChainCode x := rfl

/-- Shift-fixedness, the hypothesis of the template compiler. -/
theorem numChainQ_shift (x : V) :
    Bootstrapping.shift ℒₛₑₜ (numChainQ x).val = (numChainQ x).val :=
  shift_numChainCode x

/-- Substituting `#0` for `#0` into the chain leaves its code alone, also
when the result is read at a larger arity. -/
theorem subst_bvar_numChainCode (x : V) :
    Bootstrapping.subst ℒₛₑₜ
        (Bootstrapping.SemitermVec.val
          (![Bootstrapping.Semiterm.bvar 0] :
            Bootstrapping.SemitermVec V ℒₛₑₜ 1 2))
        (numChainCode x)
      = numChainCode x := by
  have hvec : Bootstrapping.SemitermVec.val
      (![Bootstrapping.Semiterm.bvar 0] :
        Bootstrapping.SemitermVec V ℒₛₑₜ 1 2) = ^#0 ∷ 0 := by
    simp [Bootstrapping.SemitermVec.val, Matrix.vecHead, Matrix.vecTail]
  have hvec' : Bootstrapping.SemitermVec.val
      (![Bootstrapping.Semiterm.bvar 0] :
        Bootstrapping.SemitermVec V ℒₛₑₜ 1 1) = ^#0 ∷ 0 := by
    simp [Bootstrapping.SemitermVec.val, Matrix.vecHead, Matrix.vecTail]
  have h1 : Bootstrapping.subst ℒₛₑₜ
      (Bootstrapping.SemitermVec.val
        (![Bootstrapping.Semiterm.bvar 0] :
          Bootstrapping.SemitermVec V ℒₛₑₜ 1 1))
      (numChainCode x) = numChainCode x :=
    congrArg Bootstrapping.Semiformula.val
      (Bootstrapping.Semiformula.subst_eq_self₁ (numChainQ x))
  rw [hvec]
  rwa [hvec'] at h1

/-- The chain at index `0` is the quotation of its base leaf. -/
theorem numChainQ_zero : numChainQ (0 : V) = ⌜numZeroS⌝ := by
  apply Bootstrapping.Semiformula.ext
  rw [numChainQ_val, numChainCode_zero, quote_numZeroS_val]

/-- The chain's successor step, typed: one existential over the previous
chain and the step leaf. -/
theorem numChainQ_succ (x : V) :
    numChainQ (x + 1)
      = ∃⁰ ((numChainQ x).subst
              (![Bootstrapping.Semiterm.bvar 0] :
                Bootstrapping.SemitermVec V ℒₛₑₜ 1 2) ⋏ ⌜succRelS⌝) := by
  apply Bootstrapping.Semiformula.ext
  rw [numChainQ_val, numChainCode_succ]
  simp only [Bootstrapping.Semiformula.val_exs, Bootstrapping.Semiformula.val_and,
    Bootstrapping.Semiformula.val_substs, numChainQ_val,
    subst_bvar_numChainCode x]
  exact congrArg (fun c ↦ ^∃ (numChainCode x ^⋏ c))
    (quote_succRelS_val (V := V)).symm

end Chain

/-! ## The source sentences

Two sentences over `SeparationKernel.setTemplateLanguage`: the base, which
does not mention the placeholder at all, and the successor step, which
mentions it twice. -/

/-- Source base: everything satisfying the chain's base leaf is a von
Neumann natural. -/
noncomputable def srcNumChainZero : Sentence setTemplateLanguage :=
  ∀⁰ (liftSet numZeroS 🡒 liftSet isVonNeumannNat)

/-- Source step hypothesis: the placeholder implies "von Neumann natural". -/
noncomputable def srcNumChainStepHyp : Sentence setTemplateLanguage :=
  ∀⁰ (srcP #0 🡒 liftSet isVonNeumannNat)

/-- Source step conclusion: one existential layer over the placeholder,
guarded by the step leaf, still implies "von Neumann natural". -/
noncomputable def srcNumChainStepConcl : Sentence setTemplateLanguage :=
  ∀⁰ ((∃⁰ (srcP #0 ⋏ liftSet succRelS)) 🡒 liftSet isVonNeumannNat)

/-- The complete source successor sentence. -/
noncomputable def srcNumChainStep : Sentence setTemplateLanguage :=
  srcNumChainStepHyp 🡒 srcNumChainStepConcl

/-! ### Their specializations at a model-coded predicate -/

section Shapes

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Literal specialization of the source base sentence. -/
theorem translate_srcNumChainZero (K : Bootstrapping.Semiformula V ℒₛₑₜ 1) :
    translateFormula K
        (Rewriting.emb srcNumChainZero : Proposition setTemplateLanguage) =
      ∀⁰ ((⌜numZeroS⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 1) 🡒
        isVonNeumannNatQ) := by
  simp only [srcNumChainZero, Rewriting.app_all, Rew.q_emb,
    FirstOrder.Semiformula.imp_eq, Bootstrapping.Semiformula.imp_def,
    LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    translateFormula, translateFormula_neg,
    translateFormula_emb_liftSet, isVonNeumannNatQ]

/-- Literal specialization of the source step hypothesis. -/
theorem translate_srcNumChainStepHyp (K : Bootstrapping.Semiformula V ℒₛₑₜ 1) :
    translateFormula K
        (Rewriting.emb srcNumChainStepHyp : Proposition setTemplateLanguage) =
      ∀⁰ (K 🡒 isVonNeumannNatQ) := by
  simp only [srcNumChainStepHyp, Rewriting.app_all, Rew.q_emb,
    FirstOrder.Semiformula.imp_eq, Bootstrapping.Semiformula.imp_def,
    LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    translateFormula, translateFormula_neg,
    translateFormula_emb_liftSet, translate_emb_srcP, Rew.emb_bvar,
    translateTerm_bvar, isVonNeumannNatQ]
  rw [Bootstrapping.Semiformula.subst_eq_self₁ K]

/-- Literal specialization of the source step conclusion. -/
theorem translate_srcNumChainStepConcl
    (K : Bootstrapping.Semiformula V ℒₛₑₜ 1) :
    translateFormula K
        (Rewriting.emb srcNumChainStepConcl : Proposition setTemplateLanguage) =
      ∀⁰ ((∃⁰ (K.subst
              (![Bootstrapping.Semiterm.bvar 0] :
                Bootstrapping.SemitermVec V ℒₛₑₜ 1 2) ⋏ ⌜succRelS⌝)) 🡒
        isVonNeumannNatQ) := by
  simp only [srcNumChainStepConcl, Rewriting.app_all, Rewriting.app_exs,
    Rew.q_emb, FirstOrder.Semiformula.imp_eq,
    Bootstrapping.Semiformula.imp_def,
    LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg,
    translateFormula, translateFormula_neg,
    translateFormula_emb_liftSet, translate_emb_srcP, Rew.emb_bvar,
    translateTerm_bvar, isVonNeumannNatQ]

/-- Literal specialization of the complete source step sentence. -/
theorem translate_srcNumChainStep (K : Bootstrapping.Semiformula V ℒₛₑₜ 1) :
    translateFormula K
        (Rewriting.emb srcNumChainStep : Proposition setTemplateLanguage) =
      ((∀⁰ (K 🡒 isVonNeumannNatQ)) 🡒
        (∀⁰ ((∃⁰ (K.subst
                (![Bootstrapping.Semiterm.bvar 0] :
                  Bootstrapping.SemitermVec V ℒₛₑₜ 1 2) ⋏ ⌜succRelS⌝)) 🡒
          isVonNeumannNatQ))) := by
  simp only [srcNumChainStep, LogicalConnective.HomClass.map_imply,
    translateFormula_imp, translate_srcNumChainStepHyp,
    translate_srcNumChainStepConcl]

end Shapes

/-! ## The two fixed source derivations

Both are logically valid; they are produced by completeness over
`SeparationKernel.omegaSourceTheory` so that the placeholder, the
membership relation and the equality symbol all stay uninterpreted. -/

/-- **Base.**  An empty set belongs to every inductive set, because the
first clause of `isInductive` says exactly that. -/
noncomputable def srcNumChainZeroProof :
    omegaSourceTheory ⊢! srcNumChainZero :=
  (Theory.Proof.small_complete <| consequence_iff.mpr fun M _ _ _ ↦ by
    have hmem : (Language.Mem.mem : (ℒₛₑₜ).Rel 2) = Language.Set.Rel.mem := rfl
    have heqr : (Language.Eq.eq : (ℒₛₑₜ).Rel 2) = Language.Set.Rel.eq := rfl
    simp [models_iff, srcNumChainZero, liftSet, numZeroS, isVonNeumannNat,
      FirstOrder.Semiformula.ballMem, FirstOrder.Semiformula.ball_eq,
      FirstOrder.Semiformula.Operator.mem_def,
      FirstOrder.Semiformula.Operator.eq_def, LogicalConnective.iff,
      Function.comp_def, Matrix.comp_vecCons', hmem, heqr]
    intro a ha I hzero _
    exact hzero a ha).get

/-- **Step.**  If the predecessor is a von Neumann natural and the value is
its successor in the sense of the chain's step leaf, then the value belongs
to every inductive set: the second clause of `isInductive` is universal in
the successor, and its description differs from the leaf's only by the
order of the two disjuncts. -/
noncomputable def srcNumChainStepProof :
    omegaSourceTheory ⊢! srcNumChainStep :=
  (Theory.Proof.small_complete <| consequence_iff.mpr fun M _ _ _ ↦ by
    have hmem : (Language.Mem.mem : (ℒₛₑₜ).Rel 2) = Language.Set.Rel.mem := rfl
    have heqr : (Language.Eq.eq : (ℒₛₑₜ).Rel 2) = Language.Set.Rel.eq := rfl
    simp [models_iff, srcNumChainStep, srcNumChainStepHyp,
      srcNumChainStepConcl, srcP, liftSet, succRelS, isVonNeumannNat,
      FirstOrder.Semiformula.ballMem, FirstOrder.Semiformula.ball_eq,
      FirstOrder.Semiformula.Operator.mem_def,
      FirstOrder.Semiformula.Operator.eq_def, LogicalConnective.iff,
      Function.comp_def, Matrix.comp_vecCons', hmem, heqr]
    intro H b a hPa hsucc I hzero hstep
    exact hstep a (H a hPa I hzero hstep) b
      (fun z ↦ ⟨fun hz ↦ ((hsucc z).1 hz).symm,
        fun hz ↦ (hsucc z).2 hz.symm⟩)).get

/-! ## The internal statement and its two halves -/

section Internal

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **The uniform internal statement.**  "Everything satisfying the numeral
chain at `x` is a von Neumann natural", as a typed model-coded `ℒₛₑₜ`
sentence. -/
noncomputable def numChainOmegaStmt (x : V) : Bootstrapping.Formula V ℒₛₑₜ :=
  ∀⁰ (numChainQ x 🡒 isVonNeumannNatQ)

/-- The standard code of the ω-predicate, as a named `ℕ`. -/
def vonNeumannNatCode : ℕ :=
  (Rewriting.emb isVonNeumannNat : SetTheorySemiproposition 1).toNat

/-- The raw code of the statement: the fixed implication spine over the
chain's code.  This is the `𝚺₁`-definable function the internal induction
runs on. -/
noncomputable def numChainOmegaCode (x : V) : V :=
  ^∀ (Bootstrapping.imp ℒₛₑₜ (numChainCode x) ((vonNeumannNatCode : ℕ) : V))

/-- The typed ω-predicate's code is the named constant. -/
theorem isVonNeumannNatQ_val :
    (isVonNeumannNatQ : Bootstrapping.Semiformula V ℒₛₑₜ 1).val
      = ((vonNeumannNatCode : ℕ) : V) := by
  unfold vonNeumannNatCode
  rw [coe_toNat_eq_quote (V := V)
    (Rewriting.emb isVonNeumannNat : SetTheorySemiproposition 1)]
  rfl

/-- The typed statement's code is the raw spine. -/
theorem numChainOmegaStmt_val (x : V) :
    (numChainOmegaStmt x).val = numChainOmegaCode x := by
  simp only [numChainOmegaStmt, numChainOmegaCode,
    Bootstrapping.Semiformula.val_all, Bootstrapping.Semiformula.val_imp,
    numChainQ_val, isVonNeumannNatQ_val]

/-- **The base.**  The compiled source base derivation, at the chain's own
zero code. -/
noncomputable def numChainOmegaBase :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢! numChainOmegaStmt (0 : V) := by
  have h := compileOmegaTemplate (numChainQ (0 : V)) (numChainQ_shift 0)
    srcNumChainZeroProof
  rw [translate_srcNumChainZero] at h
  show (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
    ∀⁰ (numChainQ (0 : V) 🡒 isVonNeumannNatQ)
  rw [numChainQ_zero]
  exact h

/-- **The step.**  The compiled source step derivation, at the chain's own
successor equation. -/
noncomputable def numChainOmegaStep (x : V) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      (numChainOmegaStmt x 🡒 numChainOmegaStmt (x + 1)) := by
  have h := compileOmegaTemplate (numChainQ x) (numChainQ_shift x)
    srcNumChainStepProof
  rw [translate_srcNumChainStep] at h
  show (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
    ((∀⁰ (numChainQ x 🡒 isVonNeumannNatQ)) 🡒
      (∀⁰ (numChainQ (x + 1) 🡒 isVonNeumannNatQ)))
  rw [numChainQ_succ]
  exact h

/-! ## The model-internal induction -/

/-- **Uniform provability of the statement code.**  A `𝚺₁` successor
induction inside the ambient model: `x` ranges over all of `V`, nonstandard
indices included.  Nothing here is an external recursion over `Nat`. -/
theorem provable_numChainOmegaCode (x : V) :
    Provable (𝗭𝗙𝗖 : SetTheory) (numChainOmegaCode x) := by
  induction x using ISigma1.sigma1_succ_induction
  · simp only [numChainOmegaCode, Bootstrapping.imp]
    definability
  case zero =>
    have h : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢ numChainOmegaStmt (0 : V) :=
      ⟨numChainOmegaBase⟩
    have h' := tprovable_iff_provable.mp h
    rwa [numChainOmegaStmt_val] at h'
  case succ x ih =>
    have hx : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢ numChainOmegaStmt x :=
      tprovable_iff_provable.mpr (by rw [numChainOmegaStmt_val]; exact ih)
    have hs : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢ numChainOmegaStmt (x + 1) :=
      ⟨TProof.modusPonens (numChainOmegaStep x) hx.get⟩
    have h' := tprovable_iff_provable.mp hs
    rwa [numChainOmegaStmt_val] at h'

/-- **The uniform internal ω-membership of the numeral chain.**  At every
element `x` of the ambient model — standard or not — `𝗭𝗙𝗖` internally
proves that whatever satisfies the numeral-chain formula at `x` is a von
Neumann natural, in the very formulation
(`SeparationKernel.isVonNeumannNatQ`) that the project's ω-induction kernel
concludes with. -/
noncomputable def zfcInternal_numChain_omega (x : V) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢! numChainOmegaStmt x :=
  (tprovable_iff_provable.mpr
    (by rw [numChainOmegaStmt_val]; exact provable_numChainOmegaCode x)).get

/-- The same, as a `Prop`-valued provability statement. -/
theorem zfcInternal_numChain_omega_provable (x : V) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢ numChainOmegaStmt x :=
  ⟨zfcInternal_numChain_omega x⟩

end Internal

end NumeralOmega
end ZFCinPA
end LeanProofs
