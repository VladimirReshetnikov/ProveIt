import ZFCinPA.PackageInduction

/-!
# Level-indexed families of six-field `𝗭𝗙𝗖` truth certificates

This is the `ℒₛₑₜ` mirror of the arithmetic
`BoundedPAConsistency.TruthCertificateProofCompiler` /
`PrimitiveRecursiveTruthCertificate` pair.  A master certificate has six
proof-relevant fields; the first five are the truth-construction data a
future dynamic set-theoretic truth development will supply, and the sixth is
forced to be the *internalized* bounded-consistency target: the formula whose
raw code is `conZFCSetCodeFun x` from `ZFCinPA.UniformStatement`.

## The typed-final-field design decision

The arithmetic family could build its typed final field outright:
`paRestrictedConsistencyFormula n` is `subst` of a quoted standard template,
and typed substitution carries well-formedness with it.  `ℒₛₑₜ` has no
substitution template — `conZFCSetCodeFun` is a raw `𝚺₁`-recursive code
builder, and Foundation's typed wrapper `Bootstrapping.Formula` demands an
`IsFormula` witness that the `PR` tower does not hand out for free at
nonstandard indices.

Instead of a separate internal induction proving
`IsFormula ℒₛₑₜ (conZFCSetCodeFun x)` for every `x`, this module recovers the
witness from the proofs it is already given: Foundation derivations only
derive formula sets (`DerivationOf.isFormulaSet`), so any represented proof
of the master code certifies well-formedness of the whole conjunction, and
`IsSemiformula.and` projects out the final conjunct.  Concretely:

* `ZFCTruthCertificateFamily.fields` takes the witness as an explicit
  argument (proof irrelevance makes the choice of witness immaterial);
* `ZFCTruthCertificateFamily.code` is witness-free raw code assembly, so the
  master-code function and its `𝚺₁` graph never mention well-formedness;
* `toTProof` and `exists_finalProof_of_masterProof` manufacture the witness
  from the incoming proof via `isFormula_conCode_of_masterProof`.

The final extraction produces exactly the shape
`∃ c, ConZFCSetCode c x ∧ Provable 𝗭𝗙𝗖 c` that
`ZFCinPA.PackageInduction`'s final hypothesis consumes, with the witness
`c = conZFCSetCodeFun x` supplied by reflexivity of the code relation.
-/

set_option autoImplicit false

namespace LeanProofs
namespace ZFCinPA

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Formula-hood from proof-hood

Foundation's internal sequent calculus only derives sets of formulas, so a
represented proof of an arbitrary (possibly nonstandard) code certifies that
the code is a formula.  This is the trust-free source of every typed-wrapper
witness below. -/

/-- A represented proof certifies well-formedness of its conclusion. -/
lemma isFormula_of_proof {L : Language} [L.Encodable] [L.LORDefinable]
    {T : Theory L} [T.Δ₁] {d p : V} (h : Proof T d p) :
    IsFormula L p :=
  IsFormulaSet.singleton.mp (DerivationOf.isFormulaSet h)

/-! ## The six-field record -/

/-- The six outer fields retained by a uniform `𝗭𝗙𝗖` truth certificate.

These are typed model-coded formulas, rather than external Lean predicates,
so they can contain nonstandard codes chosen by the package construction. -/
structure ZFCTruthCertificateFields where
  localStep : Bootstrapping.Formula V ℒₛₑₜ
  crossLevel : Bootstrapping.Formula V ℒₛₑₜ
  shiftInvariant : Bootstrapping.Formula V ℒₛₑₜ
  substitutionInvariant : Bootstrapping.Formula V ℒₛₑₜ
  axiomSound : Bootstrapping.Formula V ℒₛₑₜ
  finalConsistency : Bootstrapping.Formula V ℒₛₑₜ

namespace ZFCTruthCertificateFields

/-- The right-associated master sentence stored with one proof code. -/
noncomputable def sentence (F : ZFCTruthCertificateFields (V := V)) :
    Bootstrapping.Formula V ℒₛₑₜ :=
  F.localStep ⋏
    (F.crossLevel ⋏
      (F.shiftInvariant ⋏
        (F.substitutionInvariant ⋏
          (F.axiomSound ⋏ F.finalConsistency))))

variable {T : InternalTheory V ℒₛₑₜ}

/-- Pack proofs of all six fields into one typed proof of the master
certificate.  This is a proof-code constructor, not an existence theorem. -/
noncomputable def intro (F : ZFCTruthCertificateFields (V := V))
    (hlocal : T ⊢! F.localStep)
    (hcross : T ⊢! F.crossLevel)
    (hshift : T ⊢! F.shiftInvariant)
    (hsubst : T ⊢! F.substitutionInvariant)
    (haxiom : T ⊢! F.axiomSound)
    (hfinal : T ⊢! F.finalConsistency) :
    T ⊢! F.sentence :=
  Entailment.K_intro hlocal <|
    Entailment.K_intro hcross <|
      Entailment.K_intro hshift <|
        Entailment.K_intro hsubst <|
          Entailment.K_intro haxiom hfinal

/-- Extract the local-step proof without decoding the proof code. -/
noncomputable def localStepProof {F : ZFCTruthCertificateFields (V := V)}
    (h : T ⊢! F.sentence) : T ⊢! F.localStep :=
  Entailment.K_left h

/-- Extract the cross-level proof without decoding the proof code. -/
noncomputable def crossLevelProof {F : ZFCTruthCertificateFields (V := V)}
    (h : T ⊢! F.sentence) : T ⊢! F.crossLevel :=
  Entailment.K_left (Entailment.K_right h)

/-- Extract the shift-invariance proof without decoding the proof code. -/
noncomputable def shiftInvariantProof
    {F : ZFCTruthCertificateFields (V := V)}
    (h : T ⊢! F.sentence) : T ⊢! F.shiftInvariant :=
  Entailment.K_left (Entailment.K_right (Entailment.K_right h))

/-- Extract the substitution-invariance proof without decoding the proof
code. -/
noncomputable def substitutionInvariantProof
    {F : ZFCTruthCertificateFields (V := V)}
    (h : T ⊢! F.sentence) : T ⊢! F.substitutionInvariant :=
  Entailment.K_left
    (Entailment.K_right (Entailment.K_right (Entailment.K_right h)))

/-- Extract the axiom-soundness proof without decoding the proof code. -/
noncomputable def axiomSoundProof {F : ZFCTruthCertificateFields (V := V)}
    (h : T ⊢! F.sentence) : T ⊢! F.axiomSound :=
  Entailment.K_left
    (Entailment.K_right
      (Entailment.K_right (Entailment.K_right (Entailment.K_right h))))

/-- Extract the final internalized-consistency proof without decoding the
proof code. -/
noncomputable def finalConsistencyProof
    {F : ZFCTruthCertificateFields (V := V)}
    (h : T ⊢! F.sentence) : T ⊢! F.finalConsistency :=
  Entailment.K_right
    (Entailment.K_right
      (Entailment.K_right
        (Entailment.K_right (Entailment.K_right h))))

end ZFCTruthCertificateFields

/-! ## The typed wrapper of the built consistency code -/

/-- The internalized `Conₓ(ZFC)` as a typed model-coded formula, given a
well-formedness witness for the built code.  Proof irrelevance makes the
wrapper independent of the witness supplied. -/
noncomputable def conZFCSetFormula (x : V)
    (h : IsFormula ℒₛₑₜ (conZFCSetCodeFun x)) :
    Bootstrapping.Formula V ℒₛₑₜ :=
  ⟨conZFCSetCodeFun x, by simpa using h⟩

@[simp] lemma conZFCSetFormula_val (x : V)
    (h : IsFormula ℒₛₑₜ (conZFCSetCodeFun x)) :
    (conZFCSetFormula x h).val = conZFCSetCodeFun x := rfl

/-- At a standard point the built code is the quotation of an actual
sentence, so it is well-formed outright. -/
lemma isFormula_conZFCSetCodeFun_natCast (n : ℕ) :
    IsFormula ℒₛₑₜ (conZFCSetCodeFun ((n : ℕ) : V)) := by
  rw [conZFCSetCodeFun_natCast]
  simp

/-- Well-formedness at the base index, as needed by typed base
certificates. -/
lemma isFormula_conZFCSetCodeFun_zero :
    IsFormula ℒₛₑₜ (conZFCSetCodeFun (0 : V)) := by
  simpa using isFormula_conZFCSetCodeFun_natCast (V := V) 0

/-! ## Raw code assembly -/

/-- Assemble the six raw formula codes in exactly the right-associated shape
used by `ZFCTruthCertificateFields.sentence`.

This deliberately operates on arbitrary model elements.  Well-formedness of
the six inputs is a separate invariant of a concrete truth construction; the
represented code operation itself remains total. -/
noncomputable def assembleZFCTruthCertificateCode
    (localStep crossLevel shiftInvariant substitutionInvariant axiomSound
      finalConsistency : V) : V :=
  localStep ^⋏
    (crossLevel ^⋏
      (shiftInvariant ^⋏
        (substitutionInvariant ^⋏
          (axiomSound ^⋏ finalConsistency))))

/-- The six-input outer certificate-code constructor has a `𝚺₁` graph. -/
instance assembleZFCTruthCertificateCode_definable :
    HierarchySymbol.sigmaOne.DefinableFunction
      (fun v : Fin 6 → V ↦
        assembleZFCTruthCertificateCode
          (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) := by
  unfold assembleZFCTruthCertificateCode
  definability

/-! ## The level-indexed family -/

/-- A level-indexed family of the five reusable master-certificate fields.

The final field is deliberately omitted: `fields` below inserts the exact
internalized bounded-consistency target, preventing a package from
certifying some easier unrelated conclusion. -/
structure ZFCTruthCertificateFamily where
  localStep : V → Bootstrapping.Formula V ℒₛₑₜ
  crossLevel : V → Bootstrapping.Formula V ℒₛₑₜ
  shiftInvariant : V → Bootstrapping.Formula V ℒₛₑₜ
  substitutionInvariant : V → Bootstrapping.Formula V ℒₛₑₜ
  axiomSound : V → Bootstrapping.Formula V ℒₛₑₜ

namespace ZFCTruthCertificateFamily

/-- The six typed fields at level `n`, with the internalized consistency
target forced into the last coordinate.  The witness argument is recovered
from a master proof by `isFormula_conCode_of_masterProof`; by proof
irrelevance its choice never matters. -/
noncomputable def fields (family : ZFCTruthCertificateFamily (V := V))
    (n : V) (h : IsFormula ℒₛₑₜ (conZFCSetCodeFun n)) :
    ZFCTruthCertificateFields (V := V) where
  localStep := family.localStep n
  crossLevel := family.crossLevel n
  shiftInvariant := family.shiftInvariant n
  substitutionInvariant := family.substitutionInvariant n
  axiomSound := family.axiomSound n
  finalConsistency := conZFCSetFormula n h

/-- Raw code of the right-associated six-field master certificate.  This is
the `𝚺₁`-definable master-code function handed to the package induction; it
is witness-free by design. -/
noncomputable def code (family : ZFCTruthCertificateFamily (V := V))
    (n : V) : V :=
  assembleZFCTruthCertificateCode
    (family.localStep n).val
    (family.crossLevel n).val
    (family.shiftInvariant n).val
    (family.substitutionInvariant n).val
    (family.axiomSound n).val
    (conZFCSetCodeFun n)

/-- The typed master sentence's raw code is the assembled family code. -/
@[simp] theorem fields_sentence_val
    (family : ZFCTruthCertificateFamily (V := V)) (n : V)
    (h : IsFormula ℒₛₑₜ (conZFCSetCodeFun n)) :
    (family.fields n h).sentence.val = family.code n := rfl

/-- A represented proof of the master code certifies well-formedness of the
built consistency code: the final conjunct of a well-formed conjunction is
well-formed. -/
lemma isFormula_conCode_of_masterProof
    (family : ZFCTruthCertificateFamily (V := V)) {n d : V}
    (h : Proof 𝗭𝗙𝗖 d (family.code n)) :
    IsFormula ℒₛₑₜ (conZFCSetCodeFun n) := by
  have hall : IsFormula ℒₛₑₜ (family.code n) := isFormula_of_proof h
  simp only [code, assembleZFCTruthCertificateCode,
    IsSemiformula.and] at hall
  exact hall.2.2.2.2.2

set_option backward.isDefEq.respectTransparency false in
/-- Regard a represented proof of the raw master code as a typed proof.

The transparency option only identifies the public `ZFC_delta1` instance
with the same instance stored by `Theory.internalize`; it does not choose or
alter the input proof code. -/
noncomputable def toTProof
    (family : ZFCTruthCertificateFamily (V := V)) {n d : V}
    (hcon : IsFormula ℒₛₑₜ (conZFCSetCodeFun n))
    (h : Proof 𝗭𝗙𝗖 d (family.code n)) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢! (family.fields n hcon).sentence :=
  ⟨d, by simpa [Proof] using h⟩

set_option backward.isDefEq.respectTransparency false in
/-- A master-certificate proof always yields an internal `𝗭𝗙𝗖` proof of the
built consistency code — exactly the extraction shape consumed by the
package induction's final hypothesis.  The code-relation witness is
reflexivity: the extracted conclusion *is* the builder's value.  (The
transparency option again only unfolds the `internalize` wrapper's `Δ₁`
instance.) -/
theorem exists_finalProof_of_masterProof
    (family : ZFCTruthCertificateFamily (V := V)) {n d : V}
    (h : Proof 𝗭𝗙𝗖 d (family.code n)) :
    ∃ c : V, ConZFCSetCode c n ∧ Provable 𝗭𝗙𝗖 c := by
  have hcon : IsFormula ℒₛₑₜ (conZFCSetCodeFun n) :=
    family.isFormula_conCode_of_masterProof h
  let master := family.toTProof hcon h
  let final := (family.fields n hcon).finalConsistencyProof master
  refine ⟨conZFCSetCodeFun n, rfl, final.val, ?_⟩
  simpa [Proof, fields, conZFCSetFormula] using final.derivationOf

/-! ## Master-code definability from the five field graphs -/

/-- The `𝚺₁` graph of the internal code builder, in `DefinableFunction`
packaging. -/
theorem conZFCSetCodeFun_definable :
    HierarchySymbol.sigmaOne.DefinableFunction₁
      (conZFCSetCodeFun : V → V) :=
  conZFCSetCodeFun.defined.to_definable

/-- `𝚺₁` graphs for the five variable field-code functions suffice for the
graph of the complete right-associated master certificate.  The final field
needs no premise: its graph is `conZFCSetCodeGraph`, already established in
`ZFCinPA.UniformStatement`. -/
theorem code_definable_of_fields
    (family : ZFCTruthCertificateFamily (V := V))
    (localStepDefinable :
      HierarchySymbol.sigmaOne.DefinableFunction₁
        (fun n : V ↦ (family.localStep n).val))
    (crossLevelDefinable :
      HierarchySymbol.sigmaOne.DefinableFunction₁
        (fun n : V ↦ (family.crossLevel n).val))
    (shiftInvariantDefinable :
      HierarchySymbol.sigmaOne.DefinableFunction₁
        (fun n : V ↦ (family.shiftInvariant n).val))
    (substitutionInvariantDefinable :
      HierarchySymbol.sigmaOne.DefinableFunction₁
        (fun n : V ↦ (family.substitutionInvariant n).val))
    (axiomSoundDefinable :
      HierarchySymbol.sigmaOne.DefinableFunction₁
        (fun n : V ↦ (family.axiomSound n).val)) :
    HierarchySymbol.sigmaOne.DefinableFunction₁ family.code := by
  letI : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ (family.localStep n).val) := localStepDefinable
  letI : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ (family.crossLevel n).val) := crossLevelDefinable
  letI : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ (family.shiftInvariant n).val) := shiftInvariantDefinable
  letI : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ (family.substitutionInvariant n).val) :=
    substitutionInvariantDefinable
  letI : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ (family.axiomSound n).val) := axiomSoundDefinable
  letI : HierarchySymbol.sigmaOne.DefinableFunction₁
      (conZFCSetCodeFun : V → V) := conZFCSetCodeFun_definable
  have hassembled : HierarchySymbol.sigmaOne.DefinableFunction
      (fun v : Fin 1 → V ↦
        assembleZFCTruthCertificateCode
          (family.localStep (v 0)).val
          (family.crossLevel (v 0)).val
          (family.shiftInvariant (v 0)).val
          (family.substitutionInvariant (v 0)).val
          (family.axiomSound (v 0)).val
          (conZFCSetCodeFun (v 0))) := by
    unfold assembleZFCTruthCertificateCode
    definability
  exact HierarchySymbol.DefinableFunction.of_eq
    (fun v : Fin 1 → V ↦ family.code (v 0))
    (fun v ↦ rfl)
    hassembled

end ZFCTruthCertificateFamily

end ZFCinPA
end LeanProofs
