import ZFCinPA.StagedSuccessor

/-!
# The six successor implications at the standard indices

`ZFCinPA.StagedSuccessor` reduces the project's last obligation to six flat
internal `𝗭𝗙𝗖` implications at every model index.  This module discharges
them at every *standard* index `↑n`, by exactly the route
`ZFCinPA.BaseCertificate` used at index `0`:

1. goal 2's semantics proves each field sentence at *every* external level,
   so `𝗭𝗙𝗖 ⊢ localStepSet (n+1)`, …, `𝗭𝗙𝗖 ⊢ conZFCSet (n+1)` are already
   available for every metatheoretic `n`;
2. Hilbert–Bernays **D1** (`internal_provable_of_outer_provable`) pushes
   each derivation inside an arbitrary model of `𝗜𝚺₁`;
3. the standard-point agreement theorems of `ZFCinPA.CertificateFields`
   identify the resulting codes with the family's typed fields at
   `↑n + 1`;
4. weakening (`C_of_conseq`) turns each of the six internal proofs into an
   implication out of the level-`↑n` master certificate.

Two things this module is *not*.  It does not prove `HasStagedSuccessor`:
`ZFCProofSelectorIn V` quantifies over all `x : V`, and in a nonstandard
model the standard cut is not all of `V` — indeed a uniform internal proof
is exactly what no metatheoretic family of derivations can supply.  And it
does not use the level-`↑n` certificate at all: at a standard index the
successor fields are outright provable, so the antecedent is discarded.
The genuine content of the remaining obligation is therefore precisely the
*nonstandard* indices, where the level-`n` certificate must actually be
consumed.

What the module does buy is a check that
`ZFCinPA.StagedSuccessor.ZFCSuccessorImplications` is the right interface:
its six typed statements are exactly what goal 2 plus D1 already deliver
along the standard cut.
-/

set_option autoImplicit false

namespace LeanProofs
namespace ZFCinPA

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping

section Standard

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Well-formedness of the successor consistency code at standard
indices -/

/-- At the successor of a standard index the built consistency code is the
quotation of an actual sentence, hence well-formed. -/
theorem isFormula_conZFCSetCodeFun_natCast_succ (n : ℕ) :
    IsFormula ℒₛₑₜ (conZFCSetCodeFun (((n : ℕ) : V) + 1)) := by
  rw [← Nat.cast_succ]
  exact isFormula_conZFCSetCodeFun_natCast (n + 1)

/-! ## The six typed internal proofs at a standard successor index -/

set_option backward.isDefEq.respectTransparency false in
/-- The local-step field at `↑n + 1`, by completeness and D1. -/
noncomputable def standardLocalStepProof (n : ℕ) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      localStepFormula (((n : ℕ) : V) + 1) := by
  have h := (internal_provable_of_outer_provable (V := V)
    (zfc_proves_localStepSet (n + 1))).get
  have heq : (⌜localStepSet (n + 1)⌝ : Bootstrapping.Formula V ℒₛₑₜ) =
      localStepFormula (((n : ℕ) : V) + 1) := by
    apply Semiformula.ext
    show (⌜localStepSet (n + 1)⌝ : V) = localStepCode (((n : ℕ) : V) + 1)
    rw [← Nat.cast_succ, quote_localStepSet]
  rw [← heq]
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The cross-level field at `↑n + 1`. -/
noncomputable def standardCrossLevelProof (n : ℕ) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      crossLevelFormula (((n : ℕ) : V) + 1) := by
  have h := (internal_provable_of_outer_provable (V := V)
    (zfc_proves_crossLevelSet (n + 1))).get
  have heq : (⌜crossLevelSet (n + 1)⌝ : Bootstrapping.Formula V ℒₛₑₜ) =
      crossLevelFormula (((n : ℕ) : V) + 1) := by
    apply Semiformula.ext
    show (⌜crossLevelSet (n + 1)⌝ : V) = crossLevelCode (((n : ℕ) : V) + 1)
    rw [← Nat.cast_succ, quote_crossLevelSet]
  rw [← heq]
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The shift-invariance field at `↑n + 1`. -/
noncomputable def standardShiftInvariantProof (n : ℕ) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      shiftInvariantFormula (((n : ℕ) : V) + 1) := by
  have h := (internal_provable_of_outer_provable (V := V)
    (zfc_proves_shiftInvariantSet (n + 1))).get
  have heq : (⌜shiftInvariantSet (n + 1)⌝ : Bootstrapping.Formula V ℒₛₑₜ) =
      shiftInvariantFormula (((n : ℕ) : V) + 1) := by
    apply Semiformula.ext
    show (⌜shiftInvariantSet (n + 1)⌝ : V) =
      shiftInvariantCode (((n : ℕ) : V) + 1)
    rw [← Nat.cast_succ, quote_shiftInvariantSet]
  rw [← heq]
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The substitution-invariance field at `↑n + 1`. -/
noncomputable def standardSubstitutionInvariantProof (n : ℕ) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      substitutionInvariantFormula (((n : ℕ) : V) + 1) := by
  have h := (internal_provable_of_outer_provable (V := V)
    (zfc_proves_substitutionInvariantSet (n + 1))).get
  have heq :
      (⌜substitutionInvariantSet (n + 1)⌝ :
        Bootstrapping.Formula V ℒₛₑₜ) =
      substitutionInvariantFormula (((n : ℕ) : V) + 1) := by
    apply Semiformula.ext
    show (⌜substitutionInvariantSet (n + 1)⌝ : V) =
      substitutionInvariantCode (((n : ℕ) : V) + 1)
    rw [← Nat.cast_succ, quote_substitutionInvariantSet]
  rw [← heq]
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The axiom-soundness field at `↑n + 1`. -/
noncomputable def standardAxiomSoundProof (n : ℕ) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      axiomSoundFormula (((n : ℕ) : V) + 1) := by
  have h := (internal_provable_of_outer_provable (V := V)
    (zfc_proves_axiomSoundSet (n + 1))).get
  have heq : (⌜axiomSoundSet (n + 1)⌝ : Bootstrapping.Formula V ℒₛₑₜ) =
      axiomSoundFormula (((n : ℕ) : V) + 1) := by
    apply Semiformula.ext
    show (⌜axiomSoundSet (n + 1)⌝ : V) = axiomSoundCode (((n : ℕ) : V) + 1)
    rw [← Nat.cast_succ, quote_axiomSoundSet]
  rw [← heq]
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The internalized `Con_{↑n+1}(ZFC)`, by D1 from `zfc_proves_conZFCSet`.
As at the base index, the quotation identity of the sealed consistency
sentence enters only as a propositional rewrite. -/
noncomputable def standardFinalConsistencyProof (n : ℕ) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      conZFCSetFormula (((n : ℕ) : V) + 1)
        (isFormula_conZFCSetCodeFun_natCast_succ n) := by
  have hp : Provable 𝗭𝗙𝗖 (conZFCSetCodeFun (((n : ℕ) : V) + 1)) := by
    rw [← Nat.cast_succ, conZFCSetCodeFun_natCast]
    exact provable_conZFCSet_standard_point (n + 1)
  exact ⟨hp.choose, by
    simpa [Proof, conZFCSetFormula] using hp.choose_spec⟩

/-! ## The assembled standard-index successor implications -/

/-- **The six flat successor implications at a standard index.**  Each is
the corresponding internal proof weakened with the level-`↑n` master
certificate as a vacuous antecedent. -/
noncomputable def standardSuccessorImplications (n : ℕ) :
    ZFCSuccessorImplications (V := V) ((n : ℕ) : V)
      (isFormula_conZFCSetCodeFun_natCast n) where
  conFormula := isFormula_conZFCSetCodeFun_natCast_succ n
  localStep := LO.Entailment.C_of_conseq (standardLocalStepProof n)
  crossLevel := LO.Entailment.C_of_conseq (standardCrossLevelProof n)
  shiftInvariant :=
    LO.Entailment.C_of_conseq (standardShiftInvariantProof n)
  substitutionInvariant :=
    LO.Entailment.C_of_conseq (standardSubstitutionInvariantProof n)
  axiomSound := LO.Entailment.C_of_conseq (standardAxiomSoundProof n)
  finalConsistency :=
    LO.Entailment.C_of_conseq (standardFinalConsistencyProof n)

/-- The staged successor step exists at every standard index, with the
family's next master certificate as its public target.  (The obligation
that remains is the same statement at the *nonstandard* indices of a
nonstandard model.) -/
theorem exists_stagedStep_natCast (n : ℕ) :
    ∃ step : ZFCStagedCertificateStep ((𝗭𝗙𝗖 : SetTheory).internalize V)
        ((concreteZFCTruthCertificateFamily (V := V)).fields ((n : ℕ) : V)
          (isFormula_conZFCSetCodeFun_natCast n)),
      step.target.sentence.val =
        (concreteZFCTruthCertificateFamily (V := V)).code
          (((n : ℕ) : V) + 1) :=
  ⟨stagedStepOfImplications _ _ (standardSuccessorImplications n),
    stagedStepOfImplications_target_val _ _ (standardSuccessorImplications n)⟩

end Standard

end ZFCinPA
end LeanProofs
