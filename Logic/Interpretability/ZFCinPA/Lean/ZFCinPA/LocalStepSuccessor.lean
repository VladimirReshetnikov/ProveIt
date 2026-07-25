import ZFCinPA.SubstIdentity
import ZFCinPA.StagedSuccessor

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

## What this module lands, and what it does not

Landed:

* the template setup (`levelArities`, `levelLeaves`) and the
  proposition-level placeholder atom `srcPlaceholder`, together with its
  reconciliation `translate_srcPlaceholder` — the first real use of
  `ZFCinPA.SubstIdentity`, since the leaves are spliced *raw* at ambient
  arities `7` (both) while their own arities are `1` and `2`;
* the source formulas for the whole level tower at the canonical slots
  (`srcLevelSat`, `srcSigmaTrue`, `srcPiFalse`, `srcPiTrue`) and for the
  canonical-slot gadget (`srcCanonAt`), each with its reconciliation
  lemma;
* `srcLocalStep` and `translate_srcLocalStep`:
  `translateFormula (levelLeaves x) srcLocalStep = localStepFormula x`
  for every `x : V`.

Not landed, and deliberately not assumed anywhere: the *successor* source
formula (whose leaves are `numChainCode (x+1)` and `closCode (x+1)`,
hence require the closure-step spine to be written out at the source
level), the source proof of the implication, and the compilation.  See the
`Residue` section at the end of the file for the precise remaining steps
and their cost.

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

/-! ## The template language of the level tower -/

/-- The two `x`-dependent leaves of every certificate field: the numeral
chain (unary) and the closure kernel (binary). -/
@[reducible] def levelArities : Fin 2 → ℕ := ![1, 2]

/-- The placeholder-enlarged source language of the level tower. -/
@[reducible] def srcL : Language := setTemplateLanguage 2 levelArities

section Source

open SetTheory (Form Free)

/-- Proposition-level placeholder atom.  `SetPlaceholders.srcP` is
sentence-valued; the fixed `ℒₛₑₜ` leaves of the field spines are
`toSet`-translations, which are `Semiproposition`s, so the whole source
formula is assembled at the proposition level and closed at the very
end. -/
def srcPProp {n : ℕ} (i : Fin 2)
    (ts : Fin (levelArities i) → SyntacticSemiterm srcL n) :
    Semiproposition srcL n :=
  .rel (placeholderRel i) ts

/-- The `i`-th placeholder applied to the identity argument list
`#0, …, #(levelArities i - 1)`, at an ambient arity that can accommodate
it. -/
def srcPlaceholder {n : ℕ} (i : Fin 2) (h : levelArities i ≤ n) :
    Semiproposition srcL n :=
  srcPProp i fun j ↦ #(Fin.castLE h j)

/-- A fixed `ℒₛₑₜ` leaf, lifted into the source language. -/
noncomputable def liftP {n : ℕ} (φ : SetTheorySemiproposition n) :
    Semiproposition srcL n :=
  φ.lMap (setHom 2 levelArities)

end Source

/-! ## Reconciliation of the two atom shapes -/

section Translate

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open SetTheory (Form Free)

/-- **The placeholder atom specializes to the raw leaf.**  This is the
compiler-facing form of `ZFCinPA.SubstIdentity`: the translation always
emits a substitution, and the identity bound-variable vector makes it
vanish even though the leaf's own arity is smaller than the ambient one. -/
theorem translate_srcPlaceholder {n : ℕ}
    (Ks : (i : Fin 2) → Bootstrapping.Semiformula V ℒₛₑₜ (levelArities i))
    (i : Fin 2) (h : levelArities i ≤ n) :
    (translateFormula Ks (srcPlaceholder i h)).val = (Ks i).val := by
  show ((Ks i).subst
    (fun j ↦ translateTerm (V := V)
      ((fun j ↦ #(Fin.castLE h j)) (Fin.cast rfl j)))).val = (Ks i).val
  exact Semiformula.subst_bvarVec_val (Ks i) _ fun _ ↦ rfl

/-- A lifted fixed leaf specializes to its quotation. -/
theorem translate_liftP {n : ℕ}
    (Ks : (i : Fin 2) → Bootstrapping.Semiformula V ℒₛₑₜ (levelArities i))
    (φ : SetTheorySemiproposition n) :
    translateFormula Ks (liftP φ) = (⌜φ⌝ : Bootstrapping.Semiformula V ℒₛₑₜ n) :=
  translateFormula_lMap_set Ks φ

/-- Raw-code form of `translate_liftP`. -/
theorem translate_liftP_val {n : ℕ}
    (Ks : (i : Fin 2) → Bootstrapping.Semiformula V ℒₛₑₜ (levelArities i))
    (φ : SetTheorySemiproposition n) :
    (translateFormula Ks (liftP φ)).val = (⌜φ⌝ : V) := by
  rw [translate_liftP]; rfl

/-- Specialization commutes with conjunction. -/
theorem translate_and {n : ℕ}
    (Ks : (i : Fin 2) → Bootstrapping.Semiformula V ℒₛₑₜ (levelArities i))
    (p q : Semiproposition srcL n) :
    translateFormula Ks (p ⋏ q) =
      translateFormula Ks p ⋏ translateFormula Ks q := rfl

/-- Specialization commutes with the universal quantifier. -/
theorem translate_all {n : ℕ}
    (Ks : (i : Fin 2) → Bootstrapping.Semiformula V ℒₛₑₜ (levelArities i))
    (p : Semiproposition srcL (n + 1)) :
    translateFormula Ks (∀⁰ p) = ∀⁰ translateFormula Ks p := rfl

/-- Specialization commutes with the existential quantifier. -/
theorem translate_exs {n : ℕ}
    (Ks : (i : Fin 2) → Bootstrapping.Semiformula V ℒₛₑₜ (levelArities i))
    (p : Semiproposition srcL (n + 1)) :
    translateFormula Ks (∃⁰ p) = ∃⁰ translateFormula Ks p := rfl

/-- **The depth move, packaged.**  A fixed leaf's quote at the ambient
depth `k` is the named constant computed at the declared depth `d`,
provided every free slot of the underlying `Form` lies below both.  This is
the only way a concrete Gödel code is ever touched below — never by
`simp`, never by evaluation. -/
theorem quote_toSet_eq_code {φ : Form} {k d : ℕ}
    (hk : ∀ i, Free i φ → i < k) (hd : ∀ i, Free i φ → i < d) :
    (⌜toSet k φ⌝ : V) = (((toSet d φ).toNat : ℕ) : V) := by
  rw [quote_toSet_congr hk hd, coe_toNat_eq_quote]

end Translate

/-! ## The two model-coded leaves -/

section Leaves

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The two `x`-dependent leaves of the level tower, typed at their own
arities: the numeral chain and the closure kernel. -/
noncomputable def levelLeaves (x : V) :
    (i : Fin 2) → Bootstrapping.Semiformula V ℒₛₑₜ (levelArities i)
  | ⟨0, _⟩ => ⟨numChainCode x, by simpa using isSemiformula_numChainCode x⟩
  | ⟨1, _⟩ => ⟨closCode x, by simpa using isSemiformula_closCode x⟩

@[simp] theorem levelLeaves_zero (x : V) :
    (levelLeaves x 0).val = numChainCode x := rfl

@[simp] theorem levelLeaves_one (x : V) :
    (levelLeaves x 1).val = closCode x := rfl

end Leaves

/-! ## The source formulas of the level tower

Each definition sits at the ambient arity its occurrence in the field
spine forces: the canonical level instance at `5`, the Sigma/Pi readings at
`4`, the canonical-slot gadget's payload at `4` and the gadget itself at
`2`. -/

section SourceTower

open SetTheory (Form Free)

/-- The unfolded canonical level instance at the *successor* index: two
existentials over the numeral chain and the closure kernel, and the fixed
membership atom.  Both placeholders carry the identity argument list, so
their specializations are the raw leaves. -/
noncomputable def srcLevelSat : Semiproposition srcL 5 :=
  ∃⁰ ∃⁰ (srcPlaceholder 0 (by decide) ⋏
    (srcPlaceholder 1 (by decide) ⋏ liftP (toSet 7 (fTripleMemF 4 3 2 1))))

/-- Sigma-truth at the successor index, canonical slots. -/
noncomputable def srcSigmaTrue : Semiproposition srcL 4 :=
  ∃⁰ (liftP (toSet 5 (fNumF 0 1)) ⋏ srcLevelSat)

/-- Pi-falsity at the successor index, canonical slots. -/
noncomputable def srcPiFalse : Semiproposition srcL 4 :=
  ∃⁰ (liftP (toSet 5 (fNumF 0 0)) ⋏ srcLevelSat)

/-- Pi-truth at the successor index: the negation of Pi-falsity. -/
noncomputable def srcPiTrue : Semiproposition srcL 4 :=
  srcPiFalse 🡒 liftP (toSet 4 Form.fBot)

/-- The canonical-slot gadget at the pair `(1, 0)`: two universal
quantifiers over the two equality guards and the payload. -/
noncomputable def srcCanonAt (inner : Semiproposition srcL 4) :
    Semiproposition srcL 2 :=
  ∀⁰ ∀⁰ (liftP (toSet 4 (Form.fEq 1 3)) 🡒
    (liftP (toSet 4 (Form.fEq 0 2)) 🡒 inner))

/-- **The source form of the local-step field.**  Its specialization at
`levelLeaves x` is `localStepFormula x`, at every model index. -/
noncomputable def srcLocalStep : Proposition srcL :=
  ∀⁰ ∀⁰ (liftP (toSet 2 (fUnivEnvF 0)) 🡒
    ((liftP (toSet 2 (fTaggedEmptyF 1 2)) 🡒
        (srcCanonAt srcSigmaTrue 🡒 liftP (toSet 2 Form.fBot))) ⋏
     (liftP (toSet 2 (fIsFormCodeF 1)) 🡒
        (srcCanonAt srcSigmaTrue 🡒 srcCanonAt srcPiTrue))))

end SourceTower

/-! ## Free-slot bounds of the fixed leaves

Only leaves whose declared depth differs from their ambient depth need a
bound.  There is exactly one such leaf in the level tower that is not
already covered by a named lemma. -/

section FreeBounds

open SetTheory (Form Free)

set_option maxHeartbeats 1000000 in
private theorem freeMax_tripleMemCanon :
    freeMax (fTripleMemF 4 3 2 1) ≤ 5 := by decide

private theorem free_tripleMemCanon {i : ℕ}
    (h : Free i (fTripleMemF 4 3 2 1)) : i < 5 := by
  have h1 := free_lt_freeMax _ i h
  have h2 := freeMax_tripleMemCanon
  omega

end FreeBounds

/-! ## Reconciliation, layer by layer -/

section Reconcile

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open SetTheory (Form Free)

/-- The canonical level instance. -/
theorem translate_srcLevelSat (x : V) :
    (translateFormula (levelLeaves x) srcLevelSat).val = levelSatCode (x + 1) := by
  rw [levelSatCode_succ, lvlInstPart]
  simp only [srcLevelSat, translate_exs, translate_and,
    Bootstrapping.Semiformula.val_exs, Bootstrapping.Semiformula.val_and,
    translate_srcPlaceholder, translate_liftP_val, levelLeaves_zero,
    levelLeaves_one]
  rw [quote_toSet_eq_code (V := V)
    (fun i hi ↦ by have := free_tripleMemCanon hi; omega)
    (fun i hi ↦ free_tripleMemCanon hi)]
  rfl

/-- Sigma-truth at the successor index. -/
theorem translate_srcSigmaTrue (x : V) :
    (translateFormula (levelLeaves x) srcSigmaTrue).val =
      sigmaTrueCode (x + 1) := by
  rw [sigmaTrueCode, bitWitnessPart]
  simp only [srcSigmaTrue, translate_exs, translate_and,
    Bootstrapping.Semiformula.val_exs, Bootstrapping.Semiformula.val_and,
    translate_liftP_val, translate_srcLevelSat]
  rw [quote_toSet_eq_code (V := V) (d := 3)
    (fun i hi ↦ by have := free_fNumF hi; omega)
    (fun i hi ↦ by have := free_fNumF hi; omega)]
  rfl

/-- Pi-falsity at the successor index. -/
theorem translate_srcPiFalse (x : V) :
    (translateFormula (levelLeaves x) srcPiFalse).val =
      piFalseCode (x + 1) := by
  rw [piFalseCode, bitWitnessPart]
  simp only [srcPiFalse, translate_exs, translate_and,
    Bootstrapping.Semiformula.val_exs, Bootstrapping.Semiformula.val_and,
    translate_liftP_val, translate_srcLevelSat]
  rw [quote_toSet_eq_code (V := V) (d := 3)
    (fun i hi ↦ by have := free_fNumF hi; omega)
    (fun i hi ↦ by have := free_fNumF hi; omega)]
  rfl

/-- Pi-truth at the successor index. -/
theorem translate_srcPiTrue (x : V) :
    (translateFormula (levelLeaves x) srcPiTrue).val =
      piTrueCode (x + 1) := by
  rw [piTrueCode, piTruePart]
  simp only [srcPiTrue, translateFormula_imp,
    Bootstrapping.Semiformula.val_imp, translate_liftP_val,
    translate_srcPiFalse]
  rw [quote_toSet_eq_code (V := V) (d := 2)
    (fun i hi ↦ absurd hi (by simp [Free]))
    (fun i hi ↦ absurd hi (by simp [Free]))]
  rfl

/-- The canonical-slot gadget. -/
theorem translate_srcCanonAt (x : V) (inner : Semiproposition srcL 4) :
    (translateFormula (levelLeaves x) (srcCanonAt inner)).val =
      canonAtPart (eqGuardCode 1 3) (eqGuardCode 0 2)
        (translateFormula (levelLeaves x) inner).val := by
  rw [canonAtPart]
  simp only [srcCanonAt, translate_all, translateFormula_imp,
    Bootstrapping.Semiformula.val_all, Bootstrapping.Semiformula.val_imp,
    translate_liftP_val]
  rw [quote_fEq_move (V := V) (show 1 < 4 by omega) (show 3 < 4 by omega),
    quote_fEq_move (V := V) (show 0 < 4 by omega) (show 2 < 4 by omega)]

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

/-- **From a source template to the local-step successor.**  Three inputs:

* `hσ` — the source sentence specializes, at every index, to the field
  implication.  Its antecedent half is already proved
  (`translate_srcLocalStep_formula`); the consequent half needs the
  successor spine (see the `Residue` note below);
* `hshift` — the two model-coded leaves are shift-fixed, which is what
  `SetPlaceholders.compileSetTemplate` demands of any interpretation;
* `d` — one ordinary Lean proof over the lifted theory
  `templateZFC 2 ![1, 2]`.

The conclusion is the `localStep` field of
`ZFCinPA.StagedSuccessor.ZFCSuccessorImplications` at an arbitrary,
possibly nonstandard, index. -/
noncomputable def localStepSuccessor_of_source
    (σ : Sentence srcL)
    (hσ : ∀ x : V, translateFormula (levelLeaves x) (Rewriting.emb σ) =
      (localStepFormula x 🡒 localStepFormula (x + 1)))
    (hshift : ∀ (x : V) (i : Fin 2),
      Bootstrapping.shift ℒₛₑₜ (levelLeaves x i).val = (levelLeaves x i).val)
    (d : templateZFC 2 levelArities ⊢! σ)
    (n : V) (h : IsFormula ℒₛₑₜ (conZFCSetCodeFun n)) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      ((concreteZFCTruthCertificateFamily (V := V)).fields n h).sentence 🡒
        localStepFormula (n + 1) := by
  have hc := compileSetTemplate (levelLeaves n) (hshift n) d
  rw [hσ n] at hc
  exact LO.Entailment.C_trans (previous_imp_localStep n h) hc

end Reduction

/-! ## Residue

What is proved above is the *antecedent* half of `hσ`:
`translateFormula (levelLeaves x) srcLocalStep = localStepFormula x`, at
every index.  Three steps remain before `localStepSuccessor_of_source`
can be applied, and their costs are known:

1. **The successor spine.**  `localStepCode (x + 1)` has the same shape,
   but its two `x`-dependent leaves are `numChainCode (x + 1)` and
   `closCode (x + 1)`.  Both are *definitionally* built from the level-`x`
   leaves — `numChainCode_succ` is one existential over a single fixed
   leaf, and `closCode_succ = closStepCode (numChainCode x) (closCode x)`
   is the nineteen-leaf `closStepPart`/`justRowPart`/`allClausePart`/
   `exClausePart`/`lvlInstPart` spine of `ZFCinPA.LevelCodeTower`.  So the
   successor source formula exists and needs no new idea; writing it out
   costs one source definition per spine layer plus one depth move per
   fixed leaf.  The depth moves need the free-slot bounds `fm01`–`fm16`
   and `freeMax_closF_zero` of `LevelCodeTower`, which are `private` there
   and would have to be re-`decide`d (or exported).

2. **Shift-fixedness of the two leaves.**  Two `𝚺₁` successor inductions in
   the pattern of `ConcreteFamily.isSemiformula_numChainCode` /
   `isSemiformula_closCode`, with the base and every fixed leaf handled by
   `Semiformula.quote_shift` plus `freeVariables_toSet` — i.e. by the same
   free-slot bounds as step 1.

3. **The source proof `d`.**  This is the genuine mathematics, and it is
   *not* small.  The level-`(x+2)` local polarity laws do not follow from
   arbitrary interpretations of the two placeholders — for an opaque
   `Clos` the falsity code is trivially certifiable — so the previous
   certificate really is consumed, exactly as the implication shape of
   `ZFCSuccessorImplications` allows.  Concretely:

   * the first conjunct (`sigmaTrue_bot` one level up) is goal 2's
     `levelJustified_of_tag_low` argument: the justification row of the
     falsity code can only be the delegation disjunct, because the five
     structural disjuncts each force a head tag that the falsity code does
     not have.  That argument is about the *fixed* macros `fLevelImpF`,
     `fLevelAndF`, `fLevelOrF`, `fTagUnF`, so it transfers to an arbitrary
     template structure;
   * the second conjunct (`piTrue_of_sigmaTrue` one level up) is goal 2's
     `sigmaTrue_not_piFalse`, whose proof is an induction over *form
     codes* using the collapse lemmas.  A single level-`(x+1)` polarity
     hypothesis is not enough for it; the source proof will need the
     internal form-code induction of `ZFCinPA.SeparationKernel`
     (`compileOmegaTemplate`) and, plausibly, the `crossLevel` conjunct of
     the previous certificate as well.

   Nothing above weakens `ZFCSuccessorImplications`, and no part of it is
   assumed anywhere in this file: `localStepSuccessor_of_source` takes the
   source proof as an explicit argument. -/

end LocalStepSuccessor
end ZFCinPA
end LeanProofs
