import ZFCinPA.TowerSuccessorEvaluation
import ZFCinPA.LocalStepSuccessor
import ZFCinPA.SeparationKernel

/-!
# Code induction at `StepGood`, as a source antecedent

Item 4 (the "hind" half) of the residue list in `ZFCinPA.FieldEvaluation`:
`LocalStepTransfer.localStepLaws_step` consumes

```
hind : ∀ C, LevelClosed H L (vsucc H b) C →
  EnlargedFields.CodeInduction H (StepGood H L (vsucc H b) C)
```

and for the whole transfer to become one source derivation this has to be a
**source antecedent**, discharged after translation — because once the two
placeholders are instantiated by the real coded formulas `numChainCode x`
and `closCode x`, the induction predicate is an honest set-theoretic
formula and the instance is an instance of **Separation**.

## The design decision, and why it is forced

`ZFCinPA.SeparationKernel.zfcSeparationProofOfShiftFixed` produces an
internal `𝗭𝗙𝗖` proof of

```
sepBody K  =  ∀ x, ∃ y, ∀ z, z ∈ y ↔ z ∈ x ∧ K(z)
```

for a **closed** unary model-coded `K` (`shift ℒₛₑₜ K.val = K.val` is
literally "no free variables"), and with the recognizer witnesses `m = 0`,
so the instance carries **no parameters**.  `StepGood H L bnd C c`,
however, has two parameters: the bound `bnd` and the certificate `C`.  A
naive source antecedent "Separation at `StepGood(·, bnd, C)`" is therefore
*not* an instance of what the kernel supplies.

Two escapes were considered and one is taken.

* **Rejected.**  Quantify the parameters inside the induction predicate:
  `P c :≡ ∀ bnd C, StepGood H L bnd C c`.  That predicate is closed, but
  `CodeInduction H P` does **not** imply `CodeInduction H (StepGood … C)`
  at a fixed `C` — code induction is an implication whose antecedents are
  the eight closure clauses, and the closure clauses for one `C` do not
  give the closure clauses for all `C`.  Taking this route would force
  `EnlargedFields.stepGood_of_levelLaws` to be restated and reproved.
* **Taken.**  Encode the parameters into the *elements being separated*.
  The closed predicate is

  ```
  StepGoodPair H L z  :≡  ∃ bnd C c, z = ⟨⟨bnd, C⟩, c⟩ ∧ StepGood H L bnd C c
  ```

  and `codeInduction_of_pairSeparation` recovers, from one parameter-free
  Separation instance at `StepGoodPair`, the **parametrized** code
  induction at every `bnd` and `C`.  The recovery is pure `𝗭𝗙`: the row
  image `BoundedZFCConsistency.kpImg H q C₀ = {⟨q, c⟩ : c ∈ C₀}` exists by
  Replacement, the placeholder Separation cuts it down to
  `Y = {z ∈ kpImg H q C₀ : StepGoodPair H L z}`, and
  `D = {c ∈ C₀ : ⟨q, c⟩ ∈ Y}` is then an *ordinary* `Form`-Separation
  instance with `q` and `Y` as parameters — which `ZFAxioms.sep` supplies.
  `D` is formula-closed exactly under the eight closure clauses, so
  `IsFormCodeSem H x` forces `x ∈ D`.

So the source antecedent this module builds is the **Separation instance**
itself, not a source rendering of the eight-clause induction schema.  That
is both smaller and strictly more honest: it is literally the sentence that
`ZFCinPA.SeparationKernel` proves, and the eight-clause schema is derived
from it semantically, once, in `codeInduction_stepGood_of_pairSeparation`.

## Contents

1. **Semantic half** (no source syntax): `StepGoodPair`,
   `codeInduction_of_pairSeparation`, `codeInduction_congr`, and the
   headline `codeInduction_stepGood_of_pairSeparation`, whose conclusion is
   exactly `localStepLaws_step`'s `hind` at every bound and certificate.
2. **The shift lemma.**  `shift_translateFormula_of_fvFree` — the
   translation of *any* free-variable-free source proposition is
   shift-fixed, given that the two placeholder leaves are.  This replaces,
   in one line, the `SuccessorSources.shift_closCode`-style spine walk that
   `zfcSeparationProofOfShiftFixed`'s hypothesis would otherwise need: the
   `FvFree` fact is needed anyway, to turn the source proposition into a
   `Sentence srcL`, and `SetPlaceholders.translateFormula_shift` transports
   it.
3. **The source formulas** `srcStepGoodBody`, `srcStepGoodPairAt` and
   `srcCodeInductionOf`, abstract in the polarized gadget
   `P : (m w ci ei : ℕ) → Semiproposition srcL m` in the style of
   `ZFCinPA.TarskiSources`, so that the base reading (`P := srcPolarAt`)
   and the successor reading (`P := srcPolarAtSucc`) are two
   instantiations of the same definitions — together with their `FvFree`
   proofs, their evaluation in an arbitrary template structure, and the
   translation identity to `SeparationKernel.sepBody`.
4. **The discharge** `zfcCodeInductionProof`.

## Free-slot bounds

Four new kernel `decide`s are performed (`freeMax_tripleMemGoodOne`,
`freeMax_tripleMemGoodZero`, `freeMax_kpairPair`, `freeMax_kpairOuter`);
every other leaf reuses an exported bound — in particular the two rank
bounds `LevelCodeTower.fm13`/`fm14` are reused verbatim, which is why the
slot assignment inside `srcStepGoodBody` puts the code at slot `5` and the
bound at slot `6`.
-/

set_option autoImplicit false
set_option maxRecDepth 8000

namespace LeanProofs
namespace ZFCinPA
namespace CodeInductionSource

/-! ## Part 1 — the semantic half

Nothing in this section mentions the source language.  It is stated in
goal 2's abstract closure vocabulary, exactly as `ZFCinPA.EnlargedFields`
and `ZFCinPA.LocalStepTransfer` are. -/

section Semantic

open BoundedZFCConsistency
open SetTheory (ZFAxioms scons sepD sepD_spec fPairMemF fPairMemF_spec
  kpair_inj)

universe u

variable {W : Type u} {mem : W → W → Prop}

local notation "kpair'" => _root_.SetTheory.kpair

/-- **The pair-encoded induction predicate.**  A *closed* unary predicate —
no `bnd`, no `C` — whose instances at the Kuratowski triple
`⟨⟨bnd, C⟩, c⟩` are the parametrized `EnlargedFields.StepGood`.  This is
the predicate the internal Separation instance is taken at. -/
def StepGoodPair (H : ZFAxioms mem) (L : W → W → W → Prop) (z : W) : Prop :=
  ∃ bnd C c, z = kpair' H (kpair' H bnd C) c ∧
    EnlargedFields.StepGood H L bnd C c

/-- Code induction is invariant under a pointwise equivalence of the
induction predicate. -/
theorem codeInduction_congr (H : ZFAxioms mem) {P P' : W → Prop}
    (h : ∀ c, P c ↔ P' c) (hP : EnlargedFields.CodeInduction H P) :
    EnlargedFields.CodeInduction H P' := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 x hx
  refine (h x).mp (hP ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ x hx)
  · exact fun a b ha hb ↦ (h _).mpr (h1 a b ha hb)
  · exact fun a b ha hb ↦ (h _).mpr (h2 a b ha hb)
  · exact (h _).mpr h3
  · exact fun a b ha hb ↦ (h _).mpr (h4 a b ((h a).mp ha) ((h b).mp hb))
  · exact fun a b ha hb ↦ (h _).mpr (h5 a b ((h a).mp ha) ((h b).mp hb))
  · exact fun a b ha hb ↦ (h _).mpr (h6 a b ((h a).mp ha) ((h b).mp hb))
  · exact fun a ha ↦ (h _).mpr (h7 a ((h a).mp ha))
  · exact fun a ha ↦ (h _).mpr (h8 a ((h a).mp ha))

/-- **Parameter-free Separation yields parametrized code induction.**

Given one Separation instance at an arbitrary *closed* predicate `Q` — the
shape `SeparationKernel.zfcSeparationProofOfShiftFixed` supplies — code
induction holds at the section `c ↦ Q ⟨q, c⟩`, at every `q`.

The proof is the standard one, with the parameter carried by the ambient
set rather than by the formula: `kpImg H q C₀` is the row
`{⟨q, c⟩ : c ∈ C₀}` (Replacement), `Y` is its `Q`-part (the hypothesis),
and `D = {c ∈ C₀ : ⟨q, c⟩ ∈ Y}` is a `Form`-Separation instance with `q`
and `Y` as ordinary parameters.  `D` is formula-closed precisely under the
eight clauses of `CodeInduction`. -/
theorem codeInduction_of_pairSeparation (H : ZFAxioms mem) (Q : W → Prop)
    (hsep : ∀ x, ∃ y, ∀ z, mem z y ↔ (mem z x ∧ Q z)) (q : W) :
    EnlargedFields.CodeInduction H (fun c ↦ Q (kpair' H q c)) := by
  intro hMemAtom hEqAtom hBot hImp hAnd hOr hAll hEx x hx
  obtain ⟨C0, hC0⟩ := exists_formulaClosed H
  obtain ⟨Y, hY⟩ := hsep (kpImg H q C0)
  have hD : ∀ c, mem c (sepD H (fPairMemF 1 0 2) (scons q (fun _ ↦ Y)) C0) ↔
      (mem c C0 ∧ Q (kpair' H q c)) := by
    intro c
    rw [sepD_spec H (fPairMemF 1 0 2) (scons q (fun _ ↦ Y)) C0 c,
      fPairMemF_spec H (scons c (scons q (fun _ ↦ Y))) 1 0 2]
    show (mem c C0 ∧ mem (kpair' H q c) Y) ↔ _
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, ((hY _).mp h2).2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (hY _).mpr ⟨(kpImg_spec H q C0 _).mpr ⟨c, h1, rfl⟩, h2⟩⟩
  have hclosed :
      FormulaClosed H (sepD H (fPairMemF 1 0 2) (scons q (fun _ ↦ Y)) C0) := by
    refine ⟨fun a b ha hb ↦ (hD _).mpr ⟨hC0.memAtom a b ha hb,
        hMemAtom a b ha hb⟩,
      fun a b ha hb ↦ (hD _).mpr ⟨hC0.eqAtom a b ha hb, hEqAtom a b ha hb⟩,
      (hD _).mpr ⟨hC0.bot, hBot⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro a b ha hb
      obtain ⟨ha0, ha1⟩ := (hD a).mp ha
      obtain ⟨hb0, hb1⟩ := (hD b).mp hb
      exact (hD _).mpr ⟨hC0.imp a b ha0 hb0, hImp a b ha1 hb1⟩
    · intro a b ha hb
      obtain ⟨ha0, ha1⟩ := (hD a).mp ha
      obtain ⟨hb0, hb1⟩ := (hD b).mp hb
      exact (hD _).mpr ⟨hC0.conj a b ha0 hb0, hAnd a b ha1 hb1⟩
    · intro a b ha hb
      obtain ⟨ha0, ha1⟩ := (hD a).mp ha
      obtain ⟨hb0, hb1⟩ := (hD b).mp hb
      exact (hD _).mpr ⟨hC0.disj a b ha0 hb0, hOr a b ha1 hb1⟩
    · intro a ha
      obtain ⟨ha0, ha1⟩ := (hD a).mp ha
      exact (hD _).mpr ⟨hC0.all a ha0, hAll a ha1⟩
    · intro a ha
      obtain ⟨ha0, ha1⟩ := (hD a).mp ha
      exact (hD _).mpr ⟨hC0.ex a ha0, hEx a ha1⟩
  exact ((hD x).mp (hx _ hclosed)).2

/-- **The headline of the semantic half.**  One parameter-free Separation
instance at `StepGoodPair` gives `EnlargedFields.CodeInduction` at
`StepGood` for **every** bound and **every** certificate — which is exactly
the hypothesis `LocalStepTransfer.localStepLaws_step` carries, with the
`LevelClosed` guard dropped (the statement here is strictly stronger, so
specializing to a closed certificate is immediate). -/
theorem codeInduction_stepGood_of_pairSeparation (H : ZFAxioms mem)
    (L : W → W → W → Prop)
    (hsep : ∀ x, ∃ y, ∀ z, mem z y ↔ (mem z x ∧ StepGoodPair H L z))
    (bnd C : W) :
    EnlargedFields.CodeInduction H (EnlargedFields.StepGood H L bnd C) := by
  refine codeInduction_congr H ?_
    (codeInduction_of_pairSeparation H (StepGoodPair H L) hsep
      (kpair' H bnd C))
  intro c
  constructor
  · rintro ⟨bnd', C', c', heq, hg⟩
    obtain ⟨h1, h2⟩ := kpair_inj H _ _ _ _ heq
    obtain ⟨h3, h4⟩ := kpair_inj H _ _ _ _ h1
    subst h2
    subst h3
    subst h4
    exact hg
  · intro hg
    exact ⟨bnd, C, c, rfl, hg⟩

end Semantic

/-! ## Part 2 — shift-fixedness of a translated source proposition

`SeparationKernel.zfcSeparationProofOfShiftFixed` requires
`shift ℒₛₑₜ K.val = K.val` of the separated core.  For a core produced by
the placeholder translation this is *not* a new spine walk in the style of
`SuccessorSources.shift_closCode`: internal `shift` raises free-variable
indices, the metatheoretic `Rewriting.shift` does the same on the source
side, and `SetPlaceholders.translateFormula_shift` says the two commute.
So free-variable-freeness of the source proposition — which is needed
anyway, to close it into a `Sentence srcL` — already gives it. -/

section Shift

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.SetPlaceholders
open LeanProofs.ZFCinPA.SuccessorSources

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A free-variable-free source proposition is fixed by the source
shift. -/
theorem shift_eq_self_of_fvFree {n : ℕ} {p : Semiproposition srcL n}
    (h : FvFree p) : Rewriting.shift p = p := by
  refine FirstOrder.Semiformula.rew_eq_self_of (by simp) ?_
  intro y hy
  rw [FirstOrder.Semiformula.FVar?, show p.freeVariables = ∅ from h] at hy
  simp at hy

/-- **The translation of a free-variable-free source proposition is
shift-fixed.**  This is the hypothesis
`SeparationKernel.zfcSeparationProofOfShiftFixed` places on the separated
core, obtained once for every source formula of the project instead of by
a per-formula spine walk. -/
theorem shift_translateFormula_of_fvFree {n : ℕ}
    (Ks : (i : Fin 2) → Bootstrapping.Semiformula V ℒₛₑₜ (levelArities i))
    (hKs : ∀ i, Bootstrapping.shift ℒₛₑₜ (Ks i).val = (Ks i).val)
    {p : Semiproposition srcL n} (h : FvFree p) :
    Bootstrapping.shift ℒₛₑₜ (translateFormula Ks p).val
      = (translateFormula Ks p).val := by
  have h1 : translateFormula Ks (Rewriting.shift p)
      = (translateFormula Ks p).shift :=
    translateFormula_shift Ks
      (fun i ↦ Bootstrapping.Semiformula.ext (hKs i)) p
  rw [shift_eq_self_of_fvFree h] at h1
  exact congrArg Bootstrapping.Semiformula.val h1.symm

end Shift

/-! ## Part 3 — the source formulas

The three definitions below are abstract in the polarized gadget

> `P : (m w ci ei : ℕ) → Semiproposition srcL m`

exactly as `ZFCinPA.TarskiSources`' two field bundles are, so that the base
reading (`P := srcPolarAt`, level `templateLevel`) and the successor
reading (`P := srcPolarAtSucc`, level `templateStepLevel`) are two
instantiations of one definition and one proof. -/

section FreeBounds

open SetTheory (Form Free)
open BoundedZFCConsistency (fTripleMemF)

set_option maxHeartbeats 1000000 in
/-- Free-slot bound of the `Sigma`-side record membership. -/
theorem freeMax_tripleMemGoodOne : freeMax (fTripleMemF 5 0 2 4) ≤ 6 := by
  decide

set_option maxHeartbeats 1000000 in
/-- Free-slot bound of the `Pi`-side record membership. -/
theorem freeMax_tripleMemGoodZero : freeMax (fTripleMemF 5 0 1 4) ≤ 6 := by
  decide

set_option maxHeartbeats 1000000 in
/-- Free-slot bound of the inner parameter pairing `⟨bnd, C⟩`. -/
theorem freeMax_kpairPair : freeMax (SetTheory.fKPairF 0 3 1) ≤ 4 := by decide

set_option maxHeartbeats 1000000 in
/-- Free-slot bound of the outer pairing `⟨⟨bnd, C⟩, c⟩`. -/
theorem freeMax_kpairOuter : freeMax (SetTheory.fKPairF 4 0 2) ≤ 5 := by
  decide

theorem free_tripleMemGoodOne {i : ℕ} (h : Free i (fTripleMemF 5 0 2 4)) :
    i < 6 := by
  have := free_lt_freeMax _ i h; have := freeMax_tripleMemGoodOne; omega

theorem free_tripleMemGoodZero {i : ℕ} (h : Free i (fTripleMemF 5 0 1 4)) :
    i < 6 := by
  have := free_lt_freeMax _ i h; have := freeMax_tripleMemGoodZero; omega

theorem free_kpairPair {i : ℕ} (h : Free i (SetTheory.fKPairF 0 3 1)) :
    i < 4 := by
  have := free_lt_freeMax _ i h; have := freeMax_kpairPair; omega

theorem free_kpairOuter {i : ℕ} (h : Free i (SetTheory.fKPairF 4 0 2)) :
    i < 5 := by
  have := free_lt_freeMax _ i h; have := freeMax_kpairOuter; omega

theorem free_fMem {i j n : ℕ} (h : Free n (Form.fMem i j)) : n = i ∨ n = j := h

end FreeBounds

section Source

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.SetPlaceholders
open LeanProofs.ZFCinPA.SuccessorSources
open SetTheory (Form Free)
open BoundedZFCConsistency (fTripleMemF fPiBoundedF fSigmaBoundedF fUnivEnvF
  fIsFormCodeF fNumF)

/-- **The source rendering of `EnlargedFields.StepGood`.**

Ambient slots: `2` is the code, `1` the certificate, `3` the bound.  The
three universal binders introduce — outermost first — the numeral `1`, the
numeral `0` and the environment, so inside the body slot `0` is the
environment, slot `1` the numeral `0`, slot `2` the numeral `1`, slot `4`
the certificate, slot `5` the code and slot `6` the bound.

That assignment is not arbitrary: it makes the two rank guards literally
`fPiBoundedF 6 5` and `fSigmaBoundedF 6 5`, whose free-slot bounds are the
already-exported kernel evaluations `LevelCodeTower.fm13`/`fm14`, so no new
`decide` is needed for the two most expensive leaves. -/
noncomputable def srcStepGoodBody
    (P : (m w ci ei : ℕ) → Semiproposition srcL m) (n : ℕ) :
    Semiproposition srcL n :=
  liftP (toSet n (fIsFormCodeF 2)) ⋏
    (∀⁰ ∀⁰ ∀⁰ (liftP (toSet (n + 3) (fUnivEnvF 0)) 🡒
      (liftP (toSet (n + 3) (fNumF 1 0)) 🡒
        (liftP (toSet (n + 3) (fNumF 2 1)) 🡒
          ((((P (n + 3) 1 5 0 ⋎
                liftP (toSet (n + 3) (fTripleMemF 5 0 2 4))) ⋏
             (P (n + 3) 0 5 0 ⋎
                liftP (toSet (n + 3) (fTripleMemF 5 0 1 4)))) 🡒
              liftP (toSet (n + 3) Form.fBot)) ⋏
           ((liftP (toSet (n + 3) (fPiBoundedF 6 5)) 🡒
              (liftP (toSet (n + 3) (fTripleMemF 5 0 1 4)) 🡒
                P (n + 3) 0 5 0)) ⋏
            (liftP (toSet (n + 3) (fSigmaBoundedF 6 5)) 🡒
              (liftP (toSet (n + 3) (fTripleMemF 5 0 2 4)) 🡒
                P (n + 3) 1 5 0))))))))

/-- **The pair-encoded predicate, at the source level.**  Slot `0` of the
ambient arity is the element being separated; the four existential binders
introduce — outermost first — the bound, the code, the certificate and the
inner pair, so inside slot `0` is `⟨bnd, C⟩`, slot `1` the certificate,
slot `2` the code, slot `3` the bound and slot `4` the separated
element. -/
noncomputable def srcStepGoodPairAt
    (P : (m w ci ei : ℕ) → Semiproposition srcL m) (m : ℕ) :
    Semiproposition srcL m :=
  ∃⁰ ∃⁰ ∃⁰ ∃⁰ (liftP (toSet (m + 4) (SetTheory.fKPairF 0 3 1)) ⋏
    (liftP (toSet (m + 4) (SetTheory.fKPairF 4 0 2)) ⋏
      srcStepGoodBody P (m + 4)))

/-- **The source antecedent.**  The Separation instance at the pair-encoded
`StepGood`, in the exact skeleton of `ZFCinPA.sepBodyMeta`:
`∀ x, ∃ y, ∀ z, z ∈ y ↔ z ∈ x ∧ StepGoodPair z`. -/
noncomputable def srcCodeInductionOf
    (P : (m w ci ei : ℕ) → Semiproposition srcL m) : Proposition srcL :=
  ∀⁰ ∃⁰ ∀⁰ (liftP (toSet 3 (Form.fMem 0 1)) 🡘
    (liftP (toSet 3 (Form.fMem 0 2)) ⋏ srcStepGoodPairAt P 3))

/-- The antecedent at the placeholder level. -/
noncomputable def srcCodeInduction : Proposition srcL :=
  srcCodeInductionOf srcPolarAt

/-- The antecedent one index up. -/
noncomputable def srcCodeInductionSucc : Proposition srcL :=
  srcCodeInductionOf srcPolarAtSucc

/-! ### Free-variable-freeness -/

theorem fvFree_iff' {n : ℕ} {p q : Semiproposition srcL n}
    (hp : FvFree p) (hq : FvFree q) : FvFree (p 🡘 q) :=
  (hp.imp hq).and (hq.imp hp)

theorem fvFree_srcStepGoodBody
    (P : (m w ci ei : ℕ) → Semiproposition srcL m)
    (hP : ∀ m w ci ei, ci < m → ei < m → FvFree (P m w ci ei))
    (n : ℕ) (hn : 5 ≤ n) : FvFree (srcStepGoodBody P n) := by
  have hone : FvFree (liftP (toSet (n + 3) (fTripleMemF 5 0 2 4))) :=
    fvFree_liftP (fun i hi ↦ by have := free_tripleMemGoodOne hi; omega)
  have hzero : FvFree (liftP (toSet (n + 3) (fTripleMemF 5 0 1 4))) :=
    fvFree_liftP (fun i hi ↦ by have := free_tripleMemGoodZero hi; omega)
  have hpol1 : FvFree (P (n + 3) 1 5 0) := hP _ _ _ _ (by omega) (by omega)
  have hpol0 : FvFree (P (n + 3) 0 5 0) := hP _ _ _ _ (by omega) (by omega)
  refine FvFree.and (fvFree_liftP (fun i hi ↦ by
      have := free_isFormCode2D4 hi; omega))
    (FvFree.all (FvFree.all (FvFree.all (FvFree.imp ?_ (FvFree.imp ?_
      (FvFree.imp ?_ (FvFree.and (FvFree.imp (FvFree.and (FvFree.or hpol1 hone)
        (FvFree.or hpol0 hzero)) ?_)
        (FvFree.and (FvFree.imp ?_ (FvFree.imp hzero hpol0))
          (FvFree.imp ?_ (FvFree.imp hone hpol1))))))))))
  · exact fvFree_liftP (fun i hi ↦ by have := LocalStepSuccessor.free_univEnv0 hi; omega)
  · exact fvFree_liftP (fun i hi ↦ by have := free_fNumF hi; omega)
  · exact fvFree_liftP (fun i hi ↦ by have := free_fNumF hi; omega)
  · exact fvFree_liftP (fun i hi ↦ absurd hi (by simp [Free]))
  · exact fvFree_liftP (fun i hi ↦ by have := free_piBoundedLeaf hi; omega)
  · exact fvFree_liftP (fun i hi ↦ by have := free_sigmaBoundedLeaf hi; omega)

theorem fvFree_srcStepGoodPairAt
    (P : (m w ci ei : ℕ) → Semiproposition srcL m)
    (hP : ∀ m w ci ei, ci < m → ei < m → FvFree (P m w ci ei))
    (m : ℕ) (hm : 1 ≤ m) : FvFree (srcStepGoodPairAt P m) :=
  .exs (.exs (.exs (.exs
    ((fvFree_liftP (fun i hi ↦ by have := free_kpairPair hi; omega)).and
      ((fvFree_liftP (fun i hi ↦ by have := free_kpairOuter hi; omega)).and
        (fvFree_srcStepGoodBody P hP (m + 4) (by omega)))))))

theorem fvFree_srcCodeInductionOf
    (P : (m w ci ei : ℕ) → Semiproposition srcL m)
    (hP : ∀ m w ci ei, ci < m → ei < m → FvFree (P m w ci ei)) :
    FvFree (srcCodeInductionOf P) :=
  .all (.exs (.all (fvFree_iff'
    (fvFree_liftP (fun i hi ↦ by rcases free_fMem hi with rfl | rfl <;> omega))
    ((fvFree_liftP
        (fun i hi ↦ by rcases free_fMem hi with rfl | rfl <;> omega)).and
      (fvFree_srcStepGoodPairAt P hP 3 (by omega))))))

theorem fvFree_srcCodeInduction : FvFree srcCodeInduction :=
  fvFree_srcCodeInductionOf srcPolarAt
    (fun _ _ _ _ hci hei ↦ fvFree_srcPolarAt _ _ _ _ hci hei)

theorem fvFree_srcCodeInductionSucc : FvFree srcCodeInductionSucc :=
  fvFree_srcCodeInductionOf srcPolarAtSucc
    (fun _ _ _ _ hci hei ↦ fvFree_srcPolarAtSucc _ _ _ _ hci hei)

end Source

/-! ## Part 3b — evaluation in an arbitrary template structure

The readings are stated over an abstract level relation `L` together with
the uniform reading hypothesis on the polarized gadget, exactly as
`ZFCinPA.TarskiSources`' abstract rows are; the two headline corollaries
are the instances at `TemplateEvaluation.templateLevel` (through
`TowerEvaluation.eval_srcPolarAt`) and at
`TemplateEvaluation.templateStepLevel` (through
`TowerSuccessorEvaluation.eval_srcPolarAtSucc`). -/

section Eval

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.SetPlaceholders
open LeanProofs.ZFCinPA.SuccessorSources
open LeanProofs.ZFCinPA.TemplateEvaluation
open BoundedZFCConsistency
open SetTheory (Form ZFAxioms scons Sat)

local notation "kpair'" => _root_.SetTheory.kpair

variable {X : Type*} [Nonempty X] [sX : Structure srcL X] [Structure.Eq srcL X]

/-- **The source `StepGood` reads as `EnlargedFields.StepGood`** over the
level the polarized gadget denotes, at the slot assignment
"bound `3`, certificate `1`, code `2`". -/
theorem eval_srcStepGoodBody
    (P : (m w ci ei : ℕ) → Semiproposition srcL m)
    (H : ZFAxioms (templateMem X)) (L : X → X → X → Prop)
    (hP : ∀ (m w ci ei : ℕ) {b : Fin m → X} {f e : ℕ → X}, Corr b f e →
      (Semiformula.Eval (s := sX) b f (P m w ci ei) ↔
        L (e ci) (e ei) (natV H w)))
    (n : ℕ) {b : Fin n → X} {f e : ℕ → X} (h : Corr b f e) :
    Semiformula.Eval (s := sX) b f (srcStepGoodBody P n) ↔
      EnlargedFields.StepGood H L (e 3) (e 1) (e 2) := by
  have hco : ∀ o z en : X,
      Corr (en :> z :> o :> b) f (scons en (scons z (scons o e))) :=
    fun o z en ↦ ((h.cons o).cons z).cons en
  have hcode : Semiformula.Eval (s := sX) b f
      (liftP (toSet n (fIsFormCodeF 2))) ↔ IsFormCodeSem H (e 2) :=
    (eval_liftP h _).trans (fIsFormCodeF_spec H e 2)
  have henv : ∀ o z en : X, Semiformula.Eval (s := sX)
      (en :> z :> o :> b) f (liftP (toSet (n + 3) (fUnivEnvF 0))) ↔
      IsUnivEnv H en := fun o z en ↦
    (eval_liftP (hco o z en) _).trans
      (fUnivEnvF_spec H (scons en (scons z (scons o e))) 0)
  have hzn : ∀ o z en : X, Semiformula.Eval (s := sX)
      (en :> z :> o :> b) f (liftP (toSet (n + 3) (fNumF 1 0))) ↔
      z = natV H 0 := fun o z en ↦
    (eval_liftP (hco o z en) _).trans
      (fNumF_spec H 0 1 (scons en (scons z (scons o e))))
  have hon : ∀ o z en : X, Semiformula.Eval (s := sX)
      (en :> z :> o :> b) f (liftP (toSet (n + 3) (fNumF 2 1))) ↔
      o = natV H 1 := fun o z en ↦
    (eval_liftP (hco o z en) _).trans
      (fNumF_spec H 1 2 (scons en (scons z (scons o e))))
  have hm1 : ∀ o z en : X, Semiformula.Eval (s := sX)
      (en :> z :> o :> b) f (liftP (toSet (n + 3) (fTripleMemF 5 0 2 4))) ↔
      templateMem X (satTriple H (e 2) en o) (e 1) := fun o z en ↦
    (eval_liftP (hco o z en) _).trans
      (fTripleMemF_spec H (scons en (scons z (scons o e))) 5 0 2 4)
  have hm0 : ∀ o z en : X, Semiformula.Eval (s := sX)
      (en :> z :> o :> b) f (liftP (toSet (n + 3) (fTripleMemF 5 0 1 4))) ↔
      templateMem X (satTriple H (e 2) en z) (e 1) := fun o z en ↦
    (eval_liftP (hco o z en) _).trans
      (fTripleMemF_spec H (scons en (scons z (scons o e))) 5 0 1 4)
  have hpb : ∀ o z en : X, Semiformula.Eval (s := sX)
      (en :> z :> o :> b) f (liftP (toSet (n + 3) (fPiBoundedF 6 5))) ↔
      PiBounded H (e 3) (e 2) := fun o z en ↦
    (eval_liftP (hco o z en) _).trans
      (fPiBoundedF_spec H (scons en (scons z (scons o e))) 6 5)
  have hsb : ∀ o z en : X, Semiformula.Eval (s := sX)
      (en :> z :> o :> b) f (liftP (toSet (n + 3) (fSigmaBoundedF 6 5))) ↔
      SigmaBounded H (e 3) (e 2) := fun o z en ↦
    (eval_liftP (hco o z en) _).trans
      (fSigmaBoundedF_spec H (scons en (scons z (scons o e))) 6 5)
  have hbot : ∀ o z en : X, Semiformula.Eval (s := sX)
      (en :> z :> o :> b) f (liftP (toSet (n + 3) Form.fBot)) ↔ False :=
    fun o z en ↦ eval_liftP (hco o z en) Form.fBot
  have hp1 : ∀ o z en : X, Semiformula.Eval (s := sX)
      (en :> z :> o :> b) f (P (n + 3) 1 5 0) ↔
      L (e 2) en (natV H 1) := fun o z en ↦ hP (n + 3) 1 5 0 (hco o z en)
  have hp0 : ∀ o z en : X, Semiformula.Eval (s := sX)
      (en :> z :> o :> b) f (P (n + 3) 0 5 0) ↔
      L (e 2) en (natV H 0) := fun o z en ↦ hP (n + 3) 0 5 0 (hco o z en)
  simp only [srcStepGoodBody, Semiformula.eval_all,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    LogicalConnective.HomClass.map_or, hcode, henv, hzn, hon, hm1, hm0,
    hpb, hsb, hbot, hp1, hp0]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun en hen ↦ h2 (natV H 1) (natV H 0) en hen rfl rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun o z en hen hz ho ↦ ?_⟩
    subst hz
    subst ho
    exact h2 en hen

/-- **The pair-encoded source predicate reads as `StepGoodPair`.** -/
theorem eval_srcStepGoodPairAt
    (P : (m w ci ei : ℕ) → Semiproposition srcL m)
    (H : ZFAxioms (templateMem X)) (L : X → X → X → Prop)
    (hP : ∀ (m w ci ei : ℕ) {b : Fin m → X} {f e : ℕ → X}, Corr b f e →
      (Semiformula.Eval (s := sX) b f (P m w ci ei) ↔
        L (e ci) (e ei) (natV H w)))
    (m : ℕ) {b : Fin m → X} {f e : ℕ → X} (h : Corr b f e) :
    Semiformula.Eval (s := sX) b f (srcStepGoodPairAt P m) ↔
      StepGoodPair H L (e 0) := by
  have hco : ∀ bnd c C qq : X,
      Corr (qq :> C :> c :> bnd :> b) f
        (scons qq (scons C (scons c (scons bnd e)))) :=
    fun bnd c C qq ↦ (((h.cons bnd).cons c).cons C).cons qq
  have hk1 : ∀ bnd c C qq : X, Semiformula.Eval (s := sX)
      (qq :> C :> c :> bnd :> b) f
        (liftP (toSet (m + 4) (SetTheory.fKPairF 0 3 1))) ↔
      qq = kpair' H bnd C := fun bnd c C qq ↦
    (eval_liftP (hco bnd c C qq) _).trans
      (SetTheory.fKPairF_spec H (scons qq (scons C (scons c (scons bnd e))))
        0 3 1)
  have hk2 : ∀ bnd c C qq : X, Semiformula.Eval (s := sX)
      (qq :> C :> c :> bnd :> b) f
        (liftP (toSet (m + 4) (SetTheory.fKPairF 4 0 2))) ↔
      e 0 = kpair' H qq c := fun bnd c C qq ↦
    (eval_liftP (hco bnd c C qq) _).trans
      (SetTheory.fKPairF_spec H (scons qq (scons C (scons c (scons bnd e))))
        4 0 2)
  have hbody : ∀ bnd c C qq : X, Semiformula.Eval (s := sX)
      (qq :> C :> c :> bnd :> b) f (srcStepGoodBody P (m + 4)) ↔
      EnlargedFields.StepGood H L bnd C c := fun bnd c C qq ↦
    eval_srcStepGoodBody P H L hP (m + 4) (hco bnd c C qq)
  simp only [srcStepGoodPairAt, Semiformula.eval_ex,
    LogicalConnective.HomClass.map_and, hk1, hk2, hbody]
  constructor
  · rintro ⟨bnd, c, C, qq, rfl, hq, hg⟩
    exact ⟨bnd, C, c, hq, hg⟩
  · rintro ⟨bnd, C, c, hq, hg⟩
    exact ⟨bnd, c, C, kpair' H bnd C, rfl, hq, hg⟩

/-- **The source antecedent reads as the Separation instance at
`StepGoodPair`.** -/
theorem eval_srcCodeInductionOf
    (P : (m w ci ei : ℕ) → Semiproposition srcL m)
    (H : ZFAxioms (templateMem X)) (L : X → X → X → Prop)
    (hP : ∀ (m w ci ei : ℕ) {b : Fin m → X} {f e : ℕ → X}, Corr b f e →
      (Semiformula.Eval (s := sX) b f (P m w ci ei) ↔
        L (e ci) (e ei) (natV H w)))
    (f : ℕ → X) :
    Semiformula.Eval (s := sX) ![] f (srcCodeInductionOf P) ↔
      ∀ x, ∃ y, ∀ z, templateMem X z y ↔
        (templateMem X z x ∧ StepGoodPair H L z) := by
  have hco : ∀ x y z : X,
      Corr (z :> y :> x :> (![] : Fin 0 → X)) f
        (scons z (scons y (scons x f))) :=
    fun x y z ↦ (((Corr.zero f).cons x).cons y).cons z
  have hzy : ∀ x y z : X, Semiformula.Eval (s := sX)
      (z :> y :> x :> (![] : Fin 0 → X)) f
        (liftP (toSet 3 (Form.fMem 0 1))) ↔ templateMem X z y :=
    fun x y z ↦ eval_liftP (hco x y z) (Form.fMem 0 1)
  have hzx : ∀ x y z : X, Semiformula.Eval (s := sX)
      (z :> y :> x :> (![] : Fin 0 → X)) f
        (liftP (toSet 3 (Form.fMem 0 2))) ↔ templateMem X z x :=
    fun x y z ↦ eval_liftP (hco x y z) (Form.fMem 0 2)
  have hpair : ∀ x y z : X, Semiformula.Eval (s := sX)
      (z :> y :> x :> (![] : Fin 0 → X)) f (srcStepGoodPairAt P 3) ↔
      StepGoodPair H L z := fun x y z ↦
    eval_srcStepGoodPairAt P H L hP 3 (hco x y z)
  simp only [srcCodeInductionOf, Semiformula.eval_all, Semiformula.eval_ex,
    LogicalConnective.iff, LogicalConnective.HomClass.map_and,
    LogicalConnective.HomClass.map_imply, hzy, hzx, hpair,
    iff_iff_implies_and_implies]
  exact ⟨fun hh ↦ hh, fun hh ↦ hh⟩

/-- **The headline reading.**  In every template structure, the source
antecedent gives `EnlargedFields.CodeInduction` at `StepGood` over the
level the gadget denotes, at *every* bound and *every* certificate — which
is `LocalStepTransfer.localStepLaws_step`'s `hind` with its `LevelClosed`
guard dropped. -/
theorem codeInduction_stepGood_of_eval
    (P : (m w ci ei : ℕ) → Semiproposition srcL m)
    (H : ZFAxioms (templateMem X)) (L : X → X → X → Prop)
    (hP : ∀ (m w ci ei : ℕ) {b : Fin m → X} {f e : ℕ → X}, Corr b f e →
      (Semiformula.Eval (s := sX) b f (P m w ci ei) ↔
        L (e ci) (e ei) (natV H w)))
    (f : ℕ → X)
    (hsrc : Semiformula.Eval (s := sX) ![] f (srcCodeInductionOf P))
    (bnd C : X) :
    EnlargedFields.CodeInduction H (EnlargedFields.StepGood H L bnd C) :=
  codeInduction_stepGood_of_pairSeparation H L
    ((eval_srcCodeInductionOf P H L hP f).mp hsrc) bnd C

/-- The reading at the placeholder level. -/
theorem codeInduction_of_srcCodeInduction (f : ℕ → X)
    (H : ZFAxioms (templateMem X))
    (hsrc : Semiformula.Eval (s := sX) ![] f srcCodeInduction) (bnd C : X) :
    EnlargedFields.CodeInduction H
      (EnlargedFields.StepGood H (templateLevel X H) bnd C) :=
  by
  refine codeInduction_stepGood_of_eval srcPolarAt H (templateLevel X H) ?_ f
    hsrc bnd C
  intro m w ci ei b f' e hcorr
  exact eval_srcPolarAt m w ci ei hcorr H

/-- The reading one index up — the shape
`LocalStepTransfer.localStepLaws_step` consumes at the successor level. -/
theorem codeInduction_of_srcCodeInductionSucc (f : ℕ → X)
    (H : ZFAxioms (templateMem X))
    (hsrc : Semiformula.Eval (s := sX) ![] f srcCodeInductionSucc)
    (bnd C : X) :
    EnlargedFields.CodeInduction H
      (EnlargedFields.StepGood H (templateStepLevel X H) bnd C) :=
  by
  refine codeInduction_stepGood_of_eval srcPolarAtSucc H
    (templateStepLevel X H) ?_ f hsrc bnd C
  intro m w ci ei b f' e hcorr
  exact eval_srcPolarAtSucc m w ci ei hcorr H

end Eval

/-! ## Part 4 — the post-translation discharge

Once the two placeholders are instantiated by `numChainCode x` and
`closCode x`, the source antecedent becomes literally
`SeparationKernel.sepBody K` at the model-coded core
`K = stepGoodPairQ x`, so
`SeparationKernel.zfcSeparationProofOfShiftFixed` proves it outright.

The only two things to check are that the core is **shift-fixed** — Part 2,
from free-variable-freeness — and that the translation of the source
skeleton is *literally* `sepBody`.  For the latter the source spine is
written at ambient arity `3` while the core is read at arity `1`; the two
translations have the same raw code because every fixed leaf's `toSet`
depth is moved to one common depth by `SuccessorSources.quote_leaf_move`
and the placeholder gadget's translation is arity-independent
(`TarskiSources.translate_srcPolarAt`).  That is
`translate_srcStepGoodPairAt_depth`. -/

section Discharge

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.SetPlaceholders
open LeanProofs.ZFCinPA.SuccessorSources
open SetTheory (Form Free)
open BoundedZFCConsistency (fTripleMemF fPiBoundedF fSigmaBoundedF fUnivEnvF
  fIsFormCodeF fNumF)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **The depth move, on a lifted fixed leaf.**  `SuccessorSources`'
`quote_leaf_move`, phrased on the translation. -/
theorem translate_liftP_move
    (Ks : (i : Fin 2) → Bootstrapping.Semiformula V ℒₛₑₜ (levelArities i))
    (φ : Form) (n d : ℕ) (hn : ∀ i, Free i φ → i < n)
    (hd : ∀ i, Free i φ → i < d) :
    (translateFormula Ks (liftP (toSet n φ))).val
      = (((toSet d φ).toNat : ℕ) : V) := by
  rw [translate_liftP_val, quote_leaf_move (V := V) φ n d hn hd]

/-- **The translated `StepGood` body does not depend on the ambient
arity.**  Every fixed leaf is moved to its own declared depth and the
polarized gadget's translation is arity-independent by hypothesis. -/
theorem translate_srcStepGoodBody_depth
    (Ks : (i : Fin 2) → Bootstrapping.Semiformula V ℒₛₑₜ (levelArities i))
    (P : (m w ci ei : ℕ) → Semiproposition srcL m)
    (hP : ∀ m m' w ci ei, ci < m → ei < m → ci < m' → ei < m' →
      (translateFormula Ks (P m w ci ei)).val
        = (translateFormula Ks (P m' w ci ei)).val)
    (n n' : ℕ) (hn : 5 ≤ n) (hn' : 5 ≤ n') :
    (translateFormula Ks (srcStepGoodBody P n)).val
      = (translateFormula Ks (srcStepGoodBody P n')).val := by
  have hIFC : ∀ k, 4 ≤ k →
      (translateFormula Ks (liftP (toSet k (fIsFormCodeF 2)))).val
        = (((toSet 4 (fIsFormCodeF 2)).toNat : ℕ) : V) := fun k hk ↦
    translate_liftP_move Ks _ k 4
      (fun i hi ↦ by have := free_isFormCode2D4 hi; omega)
      (fun i hi ↦ free_isFormCode2D4 hi)
  have hUE : ∀ k, 2 ≤ k →
      (translateFormula Ks (liftP (toSet k (fUnivEnvF 0)))).val
        = (((toSet 2 (fUnivEnvF 0)).toNat : ℕ) : V) := fun k hk ↦
    translate_liftP_move Ks _ k 2
      (fun i hi ↦ by have := LocalStepSuccessor.free_univEnv0 hi; omega)
      (fun i hi ↦ LocalStepSuccessor.free_univEnv0 hi)
  have hZ : ∀ k, 2 ≤ k →
      (translateFormula Ks (liftP (toSet k (fNumF 1 0)))).val
        = (((toSet 2 (fNumF 1 0)).toNat : ℕ) : V) := fun k hk ↦
    translate_liftP_move Ks _ k 2
      (fun i hi ↦ by have := free_fNumF hi; omega)
      (fun i hi ↦ by have := free_fNumF hi; omega)
  have hO : ∀ k, 3 ≤ k →
      (translateFormula Ks (liftP (toSet k (fNumF 2 1)))).val
        = (((toSet 3 (fNumF 2 1)).toNat : ℕ) : V) := fun k hk ↦
    translate_liftP_move Ks _ k 3
      (fun i hi ↦ by have := free_fNumF hi; omega)
      (fun i hi ↦ by have := free_fNumF hi; omega)
  have hM1 : ∀ k, 6 ≤ k →
      (translateFormula Ks (liftP (toSet k (fTripleMemF 5 0 2 4)))).val
        = (((toSet 6 (fTripleMemF 5 0 2 4)).toNat : ℕ) : V) := fun k hk ↦
    translate_liftP_move Ks _ k 6
      (fun i hi ↦ by have := free_tripleMemGoodOne hi; omega)
      (fun i hi ↦ free_tripleMemGoodOne hi)
  have hM0 : ∀ k, 6 ≤ k →
      (translateFormula Ks (liftP (toSet k (fTripleMemF 5 0 1 4)))).val
        = (((toSet 6 (fTripleMemF 5 0 1 4)).toNat : ℕ) : V) := fun k hk ↦
    translate_liftP_move Ks _ k 6
      (fun i hi ↦ by have := free_tripleMemGoodZero hi; omega)
      (fun i hi ↦ free_tripleMemGoodZero hi)
  have hPB : ∀ k, 8 ≤ k →
      (translateFormula Ks (liftP (toSet k (fPiBoundedF 6 5)))).val
        = (((toSet 8 (fPiBoundedF 6 5)).toNat : ℕ) : V) := fun k hk ↦
    translate_liftP_move Ks _ k 8
      (fun i hi ↦ by have := free_piBoundedLeaf hi; omega)
      (fun i hi ↦ free_piBoundedLeaf hi)
  have hSB : ∀ k, 8 ≤ k →
      (translateFormula Ks (liftP (toSet k (fSigmaBoundedF 6 5)))).val
        = (((toSet 8 (fSigmaBoundedF 6 5)).toNat : ℕ) : V) := fun k hk ↦
    translate_liftP_move Ks _ k 8
      (fun i hi ↦ by have := free_sigmaBoundedLeaf hi; omega)
      (fun i hi ↦ free_sigmaBoundedLeaf hi)
  have hBot : ∀ k : ℕ,
      (translateFormula Ks (liftP (toSet k Form.fBot))).val
        = (((toSet 0 Form.fBot).toNat : ℕ) : V) := fun k ↦
    translate_liftP_move Ks _ k 0
      (fun i hi ↦ absurd hi (by simp [Free]))
      (fun i hi ↦ absurd hi (by simp [Free]))
  simp only [srcStepGoodBody, translate_and, translate_all, translate_or,
    SetPlaceholders.translateFormula_imp, Bootstrapping.Semiformula.val_and,
    Bootstrapping.Semiformula.val_all, Bootstrapping.Semiformula.val_or,
    Bootstrapping.Semiformula.val_imp]
  rw [hIFC n (by omega), hIFC n' (by omega),
    hUE (n + 3) (by omega), hUE (n' + 3) (by omega),
    hZ (n + 3) (by omega), hZ (n' + 3) (by omega),
    hO (n + 3) (by omega), hO (n' + 3) (by omega),
    hM1 (n + 3) (by omega), hM1 (n' + 3) (by omega),
    hM0 (n + 3) (by omega), hM0 (n' + 3) (by omega),
    hPB (n + 3) (by omega), hPB (n' + 3) (by omega),
    hSB (n + 3) (by omega), hSB (n' + 3) (by omega),
    hBot (n + 3), hBot (n' + 3),
    hP (n + 3) (n' + 3) 1 5 0 (by omega) (by omega) (by omega) (by omega),
    hP (n + 3) (n' + 3) 0 5 0 (by omega) (by omega) (by omega) (by omega)]

/-- The same for the pair wrapper: its translation is one fixed raw code,
whatever ambient arity it is read at. -/
theorem translate_srcStepGoodPairAt_depth
    (Ks : (i : Fin 2) → Bootstrapping.Semiformula V ℒₛₑₜ (levelArities i))
    (P : (m w ci ei : ℕ) → Semiproposition srcL m)
    (hP : ∀ m m' w ci ei, ci < m → ei < m → ci < m' → ei < m' →
      (translateFormula Ks (P m w ci ei)).val
        = (translateFormula Ks (P m' w ci ei)).val)
    (m m' : ℕ) (hm : 1 ≤ m) (hm' : 1 ≤ m') :
    (translateFormula Ks (srcStepGoodPairAt P m)).val
      = (translateFormula Ks (srcStepGoodPairAt P m')).val := by
  have hKP : ∀ k, 4 ≤ k →
      (translateFormula Ks (liftP (toSet k (SetTheory.fKPairF 0 3 1)))).val
        = (((toSet 4 (SetTheory.fKPairF 0 3 1)).toNat : ℕ) : V) := fun k hk ↦
    translate_liftP_move Ks _ k 4
      (fun i hi ↦ by have := free_kpairPair hi; omega)
      (fun i hi ↦ free_kpairPair hi)
  have hKO : ∀ k, 5 ≤ k →
      (translateFormula Ks (liftP (toSet k (SetTheory.fKPairF 4 0 2)))).val
        = (((toSet 5 (SetTheory.fKPairF 4 0 2)).toNat : ℕ) : V) := fun k hk ↦
    translate_liftP_move Ks _ k 5
      (fun i hi ↦ by have := free_kpairOuter hi; omega)
      (fun i hi ↦ free_kpairOuter hi)
  simp only [srcStepGoodPairAt, translate_exs, translate_and,
    Bootstrapping.Semiformula.val_exs, Bootstrapping.Semiformula.val_and]
  rw [hKP (m + 4) (by omega), hKP (m' + 4) (by omega),
    hKO (m + 4) (by omega), hKO (m' + 4) (by omega),
    translate_srcStepGoodBody_depth Ks P hP (m + 4) (m' + 4)
      (by omega) (by omega)]

/-- **The model-coded separation core.**  The pair-encoded source predicate
translated at the two real leaves, read at arity `1`. -/
noncomputable def stepGoodPairQ
    (P : (m w ci ei : ℕ) → Semiproposition srcL m) (x : V) :
    Bootstrapping.Semiformula V ℒₛₑₜ 1 :=
  translateFormula (levelLeaves x) (srcStepGoodPairAt P 1)

/-- **The core is shift-fixed** — the hypothesis
`SeparationKernel.zfcSeparationProofOfShiftFixed` places on it — by Part 2. -/
theorem shift_stepGoodPairQ
    (P : (m w ci ei : ℕ) → Semiproposition srcL m)
    (hPfv : ∀ m w ci ei, ci < m → ei < m → FvFree (P m w ci ei)) (x : V) :
    Bootstrapping.shift ℒₛₑₜ (stepGoodPairQ P x).val
      = (stepGoodPairQ P x).val :=
  shift_translateFormula_of_fvFree (levelLeaves x) (shift_levelLeaves x)
    (fvFree_srcStepGoodPairAt P hPfv 1 (by omega))

/-- The `z ∈ y` atom of the separation skeleton, as a `toSet`
translation. -/
theorem toSet_sepAtomZY : toSet 3 (Form.fMem 0 1) = sepAtomZY := by
  rw [toSet, sepAtomZY]
  congr 1

/-- The `z ∈ x` atom of the separation skeleton. -/
theorem toSet_sepAtomZX : toSet 3 (Form.fMem 0 2) = sepAtomZX := by
  rw [toSet, sepAtomZX]
  congr 1

/-- Substituting the identity bound-variable vector into the core leaves
its raw code alone, also when the result is read at arity `3`. -/
theorem subst_sepSubstConst_stepGoodPairQ
    (K : Bootstrapping.Semiformula V ℒₛₑₜ 1) :
    Bootstrapping.subst ℒₛₑₜ ((sepSubstConst : ℕ) : V) K.val = K.val := by
  have hvec :
      ((sepSubstConst : ℕ) : V)
        = Bootstrapping.SemitermVec.val
            (![Bootstrapping.Semiterm.bvar 0] :
              Bootstrapping.SemitermVec V ℒₛₑₜ 1 1) := by
    rw [val_sepSubstConst]
    simp [Bootstrapping.SemitermVec.val, Matrix.vecHead, Matrix.vecTail]
  rw [hvec,
    show Bootstrapping.subst ℒₛₑₜ
        (Bootstrapping.SemitermVec.val
          (![Bootstrapping.Semiterm.bvar 0] :
            Bootstrapping.SemitermVec V ℒₛₑₜ 1 1)) K.val
      = (K.subst (![Bootstrapping.Semiterm.bvar 0] :
          Bootstrapping.SemitermVec V ℒₛₑₜ 1 1)).val from rfl,
    Bootstrapping.Semiformula.subst_eq_self₁]

/-- **The translation identity.**  The source antecedent translates to
literally the separation body at the model-coded core. -/
theorem translate_srcCodeInductionOf
    (P : (m w ci ei : ℕ) → Semiproposition srcL m)
    (hP : ∀ m m' w ci ei, ci < m → ei < m → ci < m' → ei < m' →
      ∀ x : V, (translateFormula (levelLeaves x) (P m w ci ei)).val
        = (translateFormula (levelLeaves x) (P m' w ci ei)).val)
    (x : V) :
    translateFormula (levelLeaves x) (srcCodeInductionOf P)
      = sepBody (stepGoodPairQ P x) := by
  apply Bootstrapping.Semiformula.ext
  rw [← sepBodyVal_eq (stepGoodPairQ P x)]
  simp only [srcCodeInductionOf, translate_all, translate_exs,
    SetPlaceholders.translateFormula_iff, translate_and,
    Bootstrapping.Semiformula.val_all, Bootstrapping.Semiformula.val_exs,
    Bootstrapping.Semiformula.val_iff, Bootstrapping.Semiformula.val_and,
    translate_liftP_val, sepBodyVal, toSet_sepAtomZY, toSet_sepAtomZX,
    sepAtomZYCode, sepAtomZXCode,
    FirstOrder.Semiformula.coe_quote_eq_quote]
  rw [subst_sepSubstConst_stepGoodPairQ (stepGoodPairQ P x), stepGoodPairQ,
    translate_srcStepGoodPairAt_depth (levelLeaves x) P
      (fun m m' w ci ei h1 h2 h3 h4 ↦ hP m m' w ci ei h1 h2 h3 h4 x)
      3 1 (by omega) (by omega)]

/-- **The discharge.**  At every model index — standard or not — the
internalized `𝗭𝗙𝗖` proves the translated source antecedent, because after
translation it *is* a Separation instance. -/
noncomputable def zfcCodeInductionProof
    (P : (m w ci ei : ℕ) → Semiproposition srcL m)
    (hPfv : ∀ m w ci ei, ci < m → ei < m → FvFree (P m w ci ei))
    (hP : ∀ m m' w ci ei, ci < m → ei < m → ci < m' → ei < m' →
      ∀ x : V, (translateFormula (levelLeaves x) (P m w ci ei)).val
        = (translateFormula (levelLeaves x) (P m' w ci ei)).val)
    (x : V) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      translateFormula (levelLeaves x) (srcCodeInductionOf P) := by
  rw [translate_srcCodeInductionOf P hP x]
  exact SeparationKernel.zfcSeparationProofOfShiftFixed (stepGoodPairQ P x)
    (shift_stepGoodPairQ P hPfv x)

/-! ### The two instances, at the sentence level

`SetPlaceholders.compileSetTemplate` consumes a `Sentence srcL`; the source
antecedent is assembled at the proposition level, and
`SuccessorSources.emb_univCl_of_fvFree` reconciles the two. -/

/-- The source antecedent as a sentence. -/
noncomputable def srcCodeInductionSentence : Sentence srcL :=
  FirstOrder.Semiformula.univCl srcCodeInduction

/-- The successor form as a sentence. -/
noncomputable def srcCodeInductionSuccSentence : Sentence srcL :=
  FirstOrder.Semiformula.univCl srcCodeInductionSucc

private theorem polar_depth (m m' w ci ei : ℕ) (h1 : ci < m) (h2 : ei < m)
    (h3 : ci < m') (h4 : ei < m') (x : V) :
    (translateFormula (levelLeaves x) (srcPolarAt m w ci ei)).val
      = (translateFormula (levelLeaves x) (srcPolarAt m' w ci ei)).val := by
  rw [translate_srcPolarAt x m w ci ei h1 h2,
    translate_srcPolarAt x m' w ci ei h3 h4]

private theorem polarSucc_depth (m m' w ci ei : ℕ) (h1 : ci < m)
    (h2 : ei < m) (h3 : ci < m') (h4 : ei < m') (x : V) :
    (translateFormula (levelLeaves x) (srcPolarAtSucc m w ci ei)).val
      = (translateFormula (levelLeaves x) (srcPolarAtSucc m' w ci ei)).val := by
  rw [translate_srcPolarAtSucc x m w ci ei h1 h2,
    translate_srcPolarAtSucc x m' w ci ei h3 h4]

/-- **The discharge at the placeholder level, sentence form.** -/
noncomputable def zfcCodeInductionSentenceProof (x : V) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      translateFormula (levelLeaves x)
        (Rewriting.emb srcCodeInductionSentence) := by
  rw [srcCodeInductionSentence, emb_univCl_of_fvFree fvFree_srcCodeInduction]
  exact zfcCodeInductionProof srcPolarAt
    (fun _ _ _ _ hci hei ↦ fvFree_srcPolarAt _ _ _ _ hci hei)
    (fun m m' w ci ei h1 h2 h3 h4 y ↦
      polar_depth m m' w ci ei h1 h2 h3 h4 y) x

/-- **The discharge one index up, sentence form.** -/
noncomputable def zfcCodeInductionSuccSentenceProof (x : V) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      translateFormula (levelLeaves x)
        (Rewriting.emb srcCodeInductionSuccSentence) := by
  rw [srcCodeInductionSuccSentence,
    emb_univCl_of_fvFree fvFree_srcCodeInductionSucc]
  exact zfcCodeInductionProof srcPolarAtSucc
    (fun _ _ _ _ hci hei ↦ fvFree_srcPolarAtSucc _ _ _ _ hci hei)
    (fun m m' w ci ei h1 h2 h3 h4 y ↦
      polarSucc_depth m m' w ci ei h1 h2 h3 h4 y) x

end Discharge

end CodeInductionSource
end ZFCinPA
end LeanProofs
