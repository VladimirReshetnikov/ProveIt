import ZFCinPA.CertificateFields

/-!
# The two Tarski field bundles, and their truth at every level

`ZFCinPA.EnlargedFields` verifies that enlarging the certificate field set
by the Tarski **elimination** and **introduction** clauses repairs the
successor obligation that `ZFCinPA.LocalStepDerivation` refuted.  That
verification needs the two countermodels, so it lives high in the import
order; but the *statements* of the two bundles, and the fact that they are
true of goal 2's actual hierarchy at every level, are needed much lower —
`ZFCinPA.BaseCertificate` proves the corresponding `Form`-level sentences
satisfied in every model of ZFC, and it sits below the countermodels.

This module is therefore the semantic floor of the enlargement:

* the compound **code shapes** (`botC`, `impC`, `andC`, `orC`, `allC`,
  `exC`) in goal 2's own vocabulary;
* the two field bundles `TarskiElim` (eight clauses) and `TarskiIntro`
  (nine clauses), stated of an arbitrary ternary relation standing for
  level satisfaction;
* their **soundness**: `tarskiElim_levelSat` and `tarskiIntro_levelSat`
  discharge every clause of goal 2's real level predicates, so the
  enlargement is not vacuous.

Fifteen of the seventeen clauses are goal-2 exports.  The two quantifier
eliminations are not: goal 2 records the quantifier clauses only in the
`inv` form, whose conclusion descends a level.  They are proved here from
`sigmaTrue_all_inv'`, totality (`sigmaTrue_or_piFalse`) and the collapse
(`piFalse_collapse_le`), which is why the strong, side-condition-free form
is legitimate.

Everything about the *transfer* — the countermodels, the induction
predicate, and `exclusivity_step` — stays in `ZFCinPA.EnlargedFields`,
which imports this module and continues its namespace.
-/

set_option autoImplicit false

namespace LeanProofs
namespace ZFCinPA
namespace EnlargedFields

open BoundedZFCConsistency
open SetTheory (ZFAxioms vempty omegaV)

universe u

variable {W : Type u} {mem : W → W → Prop}

local notation "kpair'" => _root_.SetTheory.kpair

/-! ## Code shapes

Reducible names for the compound code shapes and the falsity code, so that
the law bundles below stay readable.  They are reducible, so goal 2's
row-inversion lemmas apply to them without any unfolding step. -/

/-- The falsity code, tag `2`. -/
@[reducible] noncomputable def botC (H : ZFAxioms mem) : W :=
  kpair' H (natV H 2) (vempty H)

/-- The implication code, tag `3`. -/
@[reducible] noncomputable def impC (H : ZFAxioms mem) (a b : W) : W :=
  kpair' H (natV H 3) (kpair' H a b)

/-- The conjunction code, tag `4`. -/
@[reducible] noncomputable def andC (H : ZFAxioms mem) (a b : W) : W :=
  kpair' H (natV H 4) (kpair' H a b)

/-- The disjunction code, tag `5`. -/
@[reducible] noncomputable def orC (H : ZFAxioms mem) (a b : W) : W :=
  kpair' H (natV H 5) (kpair' H a b)

/-- The universal code, tag `6`. -/
@[reducible] noncomputable def allC (H : ZFAxioms mem) (a : W) : W :=
  kpair' H (natV H 6) a

/-- The existential code, tag `7`. -/
@[reducible] noncomputable def exC (H : ZFAxioms mem) (a : W) : W :=
  kpair' H (natV H 7) a

/-! ## The two field bundles, abstractly

Each clause is stated of an arbitrary ternary relation `L` standing for
level satisfaction, with `L c e (natV H 1)` reading "Sigma-true" and
`L c e (natV H 0)` reading "Pi-false", exactly as the source layer of
`ZFCinPA.SuccessorSources` specializes them. -/

/-- **New field 6, `tarskiElim`.**  The six connective Tarski elimination
clauses, plus the two quantifier eliminations on the polarity that carries
no side condition. -/
structure TarskiElim (H : ZFAxioms mem) (L : W → W → W → Prop) : Prop where
  /-- Sigma-truth of an implication offers Pi-falsity of the antecedent or
  Sigma-truth of the succedent.  This is the clause countermodel B of
  `ZFCinPA.LocalStepDerivation` was built to expose. -/
  impSigma : ∀ a b e, IsFormCodeSem H a → IsFormCodeSem H b → IsUnivEnv H e →
    L (impC H a b) e (natV H 1) → L a e (natV H 0) ∨ L b e (natV H 1)
  /-- Pi-falsity of an implication yields Sigma-truth of the antecedent and
  Pi-falsity of the succedent. -/
  impPi : ∀ a b e, IsFormCodeSem H a → IsFormCodeSem H b → IsUnivEnv H e →
    L (impC H a b) e (natV H 0) → L a e (natV H 1) ∧ L b e (natV H 0)
  /-- Sigma-truth of a conjunction yields both conjuncts. -/
  andSigma : ∀ a b e, IsFormCodeSem H a → IsFormCodeSem H b → IsUnivEnv H e →
    L (andC H a b) e (natV H 1) → L a e (natV H 1) ∧ L b e (natV H 1)
  /-- Pi-falsity of a conjunction offers one conjunct. -/
  andPi : ∀ a b e, IsFormCodeSem H a → IsFormCodeSem H b → IsUnivEnv H e →
    L (andC H a b) e (natV H 0) → L a e (natV H 0) ∨ L b e (natV H 0)
  /-- Sigma-truth of a disjunction offers one disjunct. -/
  orSigma : ∀ a b e, IsFormCodeSem H a → IsFormCodeSem H b → IsUnivEnv H e →
    L (orC H a b) e (natV H 1) → L a e (natV H 1) ∨ L b e (natV H 1)
  /-- Pi-falsity of a disjunction yields both disjuncts. -/
  orPi : ∀ a b e, IsFormCodeSem H a → IsFormCodeSem H b → IsUnivEnv H e →
    L (orC H a b) e (natV H 0) → L a e (natV H 0) ∧ L b e (natV H 0)
  /-- Sigma-truth of a universal code descends to *every* extension of the
  environment.  Goal 2 derives this from `sigmaTrue_all_inv'`, totality and
  the collapse; it is not one of the eleven rows. -/
  allSigma : ∀ a e d, IsFormCodeSem H a → IsUnivEnv H e →
    L (allC H a) e (natV H 1) → L a (econs H d e) (natV H 1)
  /-- Pi-falsity of an existential code descends to every extension. -/
  exPi : ∀ a e d, IsFormCodeSem H a → IsUnivEnv H e →
    L (exC H a) e (natV H 0) → L a (econs H d e) (natV H 0)

/-- **New field 7, `tarskiIntro`.**  Pi-falsity of the falsity code, the six
connective introduction clauses, and the two quantifier introductions.  All
nine hold automatically at a closure level; none is available at an opaque
placeholder level. -/
structure TarskiIntro (H : ZFAxioms mem) (L : W → W → W → Prop) : Prop where
  /-- The falsity code is Pi-false.  Goal-2 counterpart: `piFalse_bot`.
  This is the clause expansion (A) of `ZFCinPA.LocalStepDerivation` fails. -/
  botPi : ∀ e, IsUnivEnv H e → L (botC H) e (natV H 0)
  /-- Implication, Sigma side. -/
  impSigma : ∀ a b e, IsFormCodeSem H a → IsFormCodeSem H b → IsUnivEnv H e →
    (L a e (natV H 0) ∨ L b e (natV H 1)) → L (impC H a b) e (natV H 1)
  /-- Implication, Pi side. -/
  impPi : ∀ a b e, IsFormCodeSem H a → IsFormCodeSem H b → IsUnivEnv H e →
    L a e (natV H 1) → L b e (natV H 0) → L (impC H a b) e (natV H 0)
  /-- Conjunction, Sigma side. -/
  andSigma : ∀ a b e, IsFormCodeSem H a → IsFormCodeSem H b → IsUnivEnv H e →
    L a e (natV H 1) → L b e (natV H 1) → L (andC H a b) e (natV H 1)
  /-- Conjunction, Pi side. -/
  andPi : ∀ a b e, IsFormCodeSem H a → IsFormCodeSem H b → IsUnivEnv H e →
    (L a e (natV H 0) ∨ L b e (natV H 0)) → L (andC H a b) e (natV H 0)
  /-- Disjunction, Sigma side. -/
  orSigma : ∀ a b e, IsFormCodeSem H a → IsFormCodeSem H b → IsUnivEnv H e →
    (L a e (natV H 1) ∨ L b e (natV H 1)) → L (orC H a b) e (natV H 1)
  /-- Disjunction, Pi side. -/
  orPi : ∀ a b e, IsFormCodeSem H a → IsFormCodeSem H b → IsUnivEnv H e →
    L a e (natV H 0) → L b e (natV H 0) → L (orC H a b) e (natV H 0)
  /-- A counterexample makes a universal code Pi-false. -/
  allPi : ∀ a e d, IsFormCodeSem H a → IsUnivEnv H e →
    L a (econs H d e) (natV H 0) → L (allC H a) e (natV H 0)
  /-- A witness makes an existential code Sigma-true. -/
  exSigma : ∀ a e d, IsFormCodeSem H a → IsUnivEnv H e →
    L a (econs H d e) (natV H 1) → L (exC H a) e (natV H 1)

/-! ## Soundness: the two bundles hold of the real hierarchy

A field set that defeats the countermodels but is not true would be
worthless.  These are also exactly the statements
`ZFCinPA.BaseCertificate` needs, externally at every standard index. -/

section Soundness

variable (H : ZFAxioms mem)

/-- **Sigma-truth of a universal code descends to every extension of the
environment**, at every level.  The delegation that made `∀a` Sigma-true
happened at some `k+1 < n`, under a Pi-bound there; the matrix inherits the
bound, totality decides it one level up, and the collapse sends a Pi-false
verdict back to `k+1`, where the counterexample clause contradicts the
recorded Pi-truth. -/
theorem sigmaTrue_all_elim_strong (n : Nat) {a e d : W}
    (hca : IsFormCodeSem H a) (he : IsUnivEnv H e)
    (h : SigmaTrue H n (allC H a) e) :
    SigmaTrue H n a (econs H d e) := by
  obtain ⟨k, hkn, hpb, hpt⟩ := sigmaTrue_all_inv' H n h
  have he' : IsUnivEnv H (econs H d e) := econs_isUnivEnv H he d
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
    cases k with
    | zero => exact absurd hpb (not_piBounded_zero_all H)
    | succ j => exact ⟨j, rfl⟩
  have hba : PiBounded H (natV H (j + 1)) a :=
    piBounded_all H (natV_mem_omega H (j + 1)) hpb
  rcases sigmaTrue_or_piFalse H (j + 1) hca
      (quantBounded_of_piBounded H (natV_mem_omega H (j + 1)) hba) he' with
    hs | hp
  · exact sigmaTrue_mono H (show j + 1 + 1 ≤ n by omega) he' hs
  · exact absurd (piFalse_all_intro H j he
      (piFalse_collapse_le H hca he' hba (j + 1 + 1) (Nat.le_succ _) hp)) hpt

/-- **Pi-falsity of an existential code descends to every extension**, the
dual of `sigmaTrue_all_elim_strong`. -/
theorem piFalse_ex_elim_strong (n : Nat) {a e d : W}
    (hca : IsFormCodeSem H a) (he : IsUnivEnv H e)
    (h : PiFalse H n (exC H a) e) :
    PiFalse H n a (econs H d e) := by
  obtain ⟨k, hkn, hsb, hns⟩ := piFalse_ex_inv' H n h
  have he' : IsUnivEnv H (econs H d e) := econs_isUnivEnv H he d
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
    cases k with
    | zero => exact absurd hsb (not_sigmaBounded_zero_ex H)
    | succ j => exact ⟨j, rfl⟩
  have hsa : SigmaBounded H (natV H (j + 1)) a :=
    sigmaBounded_ex H (natV_mem_omega H (j + 1)) hsb
  rcases sigmaTrue_or_piFalse H (j + 1) hca
      (quantBounded_of_sigmaBounded H (natV_mem_omega H (j + 1)) hsa) he' with
    hs | hp
  · exact absurd (sigmaTrue_ex_intro H j he
      (sigmaTrue_collapse_le H hca he' hsa (j + 1 + 1) (Nat.le_succ _) hs)) hns
  · exact piFalse_mono H (show j + 1 + 1 ≤ n by omega) he' hp

/-- **The elimination field is true at every level.** -/
theorem tarskiElim_levelSat (n : Nat) : TarskiElim H (LevelSat H n) where
  impSigma := fun _ _ _ ha hb he h => sigmaTrue_imp_elim H n ha hb he h
  impPi := fun _ _ _ ha hb he h => piFalse_imp_elim H n ha hb he h
  andSigma := fun _ _ _ ha hb he h => sigmaTrue_and_elim H n ha hb he h
  andPi := fun _ _ _ ha hb he h => piFalse_and_elim H n ha hb he h
  orSigma := fun _ _ _ ha hb he h => sigmaTrue_or_elim H n ha hb he h
  orPi := fun _ _ _ ha hb he h => piFalse_or_elim H n ha hb he h
  allSigma := fun _ _ _ ha he h => sigmaTrue_all_elim_strong H n ha he h
  exPi := fun _ _ _ ha he h => piFalse_ex_elim_strong H n ha he h

/-- **The introduction field is true at every positive level.**  Level zero
is excluded because the introduction clauses build a certificate, and the
level-zero reading has none. -/
theorem tarskiIntro_levelSat (n : Nat) : TarskiIntro H (LevelSat H (n + 1)) where
  botPi := fun _ he => piFalse_bot H (n + 1) he
  impSigma := fun _ _ _ _ _ he k => sigmaTrue_imp_intro H n he k
  impPi := fun _ _ _ _ _ he k1 k2 => piFalse_imp_intro H n he k1 k2
  andSigma := fun _ _ _ _ _ he k1 k2 => sigmaTrue_and_intro H n he k1 k2
  andPi := fun _ _ _ _ _ he k => piFalse_and_intro H n he k
  orSigma := fun _ _ _ _ _ he k => sigmaTrue_or_intro H n he k
  orPi := fun _ _ _ _ _ he k1 k2 => piFalse_or_intro H n he k1 k2
  allPi := fun _ _ _ _ he h => piFalse_all_intro H n he h
  exSigma := fun _ _ _ _ he h => sigmaTrue_ex_intro H n he h

end Soundness

end EnlargedFields
end ZFCinPA

end LeanProofs
