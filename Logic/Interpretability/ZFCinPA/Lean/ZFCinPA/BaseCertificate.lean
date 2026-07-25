import ZFCinPA.ConcreteFamily
import ZFCinPA.StagedCompiler
import ZFCinPA.TarskiFieldSemantics

/-!
# The base master certificate of the concrete family

The staged endpoint
`zfcProofSelectorIn_of_stagedCertificates_and_fieldCodes` consumes a typed
internal `𝗭𝗙𝗖` proof of the concrete family's eight-field master sentence at
level `0`.  This module produces it, by the external route promised in
`ZFCinPA.CertificateFields`:

1. **Satisfaction.**  Each field sentence `localStepF n`, …,
   `axiomSoundF n` is satisfied in *every* structure carrying goal 2's
   nine-axiom semantic bundle — at every level `n`, not only `0`.  The
   proofs are exactly goal 2's endpoint theorems (`sigmaTrue_bot`,
   `piTrue_of_sigmaTrue`, `sigmaTrue_or_piFalse`,
   `sigmaTrue_renames`/`piFalse_renames`, `axiomCodesTrueAt`) read through
   the rendering specs of the macros.
2. **Completeness.**  `SetTheory.provable_of_models` turns satisfaction in
   every Foundation model of `𝗭𝗙𝗖` into actual derivations
   `𝗭𝗙𝗖 ⊢ localStepSet n`, …, the exact pattern of
   `zfc_proves_conZFCSet`.
3. **D1.**  `internal_provable_of_outer_provable` pushes each derivation
   inside an arbitrary model of `𝗜𝚺₁`, and the standard-point agreement
   theorems of `ZFCinPA.CertificateFields` identify the resulting codes
   with the family's typed fields at index `0`.
4. **Assembly.**  `ZFCTruthCertificateFields.intro` packs the eight typed
   proofs into the master certificate, and the endpoint corollary states
   the *exact* remaining obligation of the uniform internal-provability
   project: the staged successor for this concrete family.

Closedness of the field sentences (proved in `CertificateFields`) makes
the universal closures in the `Set`-sentences vacuous at the level of
codes, exactly as in `quote_conZFCSet`.
-/

set_option autoImplicit false

namespace LeanProofs
namespace ZFCinPA

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping

/-! ## Satisfaction of the gadgets -/

section SatGadgets

universe u

open SetTheory (Form Free fIff scons Sat ZFAxioms vempty)
open BoundedZFCConsistency

variable {W : Type u} {mem : W → W → Prop}

/-- Satisfaction of the canonical-slot gadget: given the payload's spec at
the canonical slots, the gadget means the property at the redirected
pair. -/
theorem sat_canonAtF {ci ei : ℕ} {φ : SetTheory.Form} {P : W → W → Prop}
    (hspec : ∀ ee : ℕ → W, Sat mem ee φ ↔ P (ee 1) (ee 0))
    (ee : ℕ → W) :
    Sat mem ee (canonAtF ci ei φ) ↔ P (ee ci) (ee ei) := by
  constructor
  · intro h
    exact (hspec (scons (ee ei) (scons (ee ci) ee))).mp
      (h (ee ci) (ee ei) rfl rfl)
  · intro h a b ha hb
    refine (hspec (scons b (scons a ee))).mpr ?_
    show P a b
    rw [show a = ee ci from ha, show b = ee ei from hb]
    exact h

/-- The Sigma gadget means Sigma-truth at level `n+1` of the pair. -/
theorem sat_sigmaAtF (H : ZFAxioms mem) (n : ℕ) (ee : ℕ → W) (ci ei : ℕ) :
    Sat mem ee (sigmaAtF n ci ei) ↔ SigmaTrue H (n + 1) (ee ci) (ee ei) :=
  sat_canonAtF (fun ee' => fSigmaTrueF_spec H (n + 1) ee' 1 0) ee

/-- The Pi-falsity gadget means Pi-falsity at level `n+1` of the pair. -/
theorem sat_piFalseAtF (H : ZFAxioms mem) (n : ℕ) (ee : ℕ → W) (ci ei : ℕ) :
    Sat mem ee (piFalseAtF n ci ei) ↔ PiFalse H (n + 1) (ee ci) (ee ei) :=
  sat_canonAtF (fun ee' => fPiFalseF_spec H (n + 1) ee' 1 0) ee

/-- The Pi-truth gadget means Pi-truth at level `n+1` of the pair. -/
theorem sat_piTrueAtF (H : ZFAxioms mem) (n : ℕ) (ee : ℕ → W) (ci ei : ℕ) :
    Sat mem ee (piTrueAtF n ci ei) ↔ PiTrue H (n + 1) (ee ci) (ee ei) :=
  sat_canonAtF (fun ee' => fPiTrueF_spec H (n + 1) ee' 1 0) ee

/-- The boundedness gadget means quantifier-boundedness by the numeral. -/
theorem sat_boundedAtF (H : ZFAxioms mem) (n : ℕ) (ee : ℕ → W) (ci : ℕ) :
    Sat mem ee (boundedAtF n ci) ↔
      QuantBounded H (natV H n) (ee ci) := by
  constructor
  · rintro ⟨b, hb, hq⟩
    have hb' : b = natV H n := (fNumF_spec H n 0 (scons b ee)).mp hb
    have hq' := (fQuantBoundedF_spec H (scons b ee) 0 (ci + 1)).mp hq
    rwa [hb'] at hq'
  · intro h
    exact ⟨natV H n, (fNumF_spec H n 0 (scons (natV H n) ee)).mpr rfl,
      (fQuantBoundedF_spec H (scons (natV H n) ee) 0 (ci + 1)).mpr h⟩

/-! ## Satisfaction of the five original field sentences

Every structure carrying the nine-axiom bundle satisfies every field
sentence at every level. -/

/-- **The local polarity laws hold**: `sigmaTrue_bot` and
`piTrue_of_sigmaTrue`, rendered. -/
theorem sat_localStepF (K : ZFCAxioms mem) (n : ℕ) (e : ℕ → W) :
    Sat mem e (localStepF n) := by
  intro c E hUE
  have hUE' : IsUnivEnv K.toZFAxioms E :=
    (fUnivEnvF_spec K.toZFAxioms (scons E (scons c e)) 0).mp hUE
  constructor
  · intro hTE hSig
    have hTE' := (fTaggedEmptyF_spec K.toZFAxioms
      (scons E (scons c e)) 1 2).mp hTE
    have hSig' := (sat_sigmaAtF K.toZFAxioms n
      (scons E (scons c e)) 1 0).mp hSig
    rw [hTE'] at hSig'
    exact sigmaTrue_bot K.toZFAxioms (n + 1) hSig'
  · intro hFC hSig
    refine (sat_piTrueAtF K.toZFAxioms n (scons E (scons c e)) 1 0).mpr ?_
    exact piTrue_of_sigmaTrue K.toZFAxioms (n + 1)
      ((fIsFormCodeF_spec K.toZFAxioms (scons E (scons c e)) 1).mp hFC)
      hUE'
      ((sat_sigmaAtF K.toZFAxioms n (scons E (scons c e)) 1 0).mp hSig)

/-- **Decidedness of bounded codes holds**: `sigmaTrue_or_piFalse`,
rendered. -/
theorem sat_crossLevelF (K : ZFCAxioms mem) (n : ℕ) (e : ℕ → W) :
    Sat mem e (crossLevelF n) := by
  intro c E hFC hUE hBnd
  have hFC' := (fIsFormCodeF_spec K.toZFAxioms (scons E (scons c e)) 1).mp hFC
  have hUE' := (fUnivEnvF_spec K.toZFAxioms (scons E (scons c e)) 0).mp hUE
  have hBnd' := (sat_boundedAtF K.toZFAxioms n (scons E (scons c e)) 1).mp hBnd
  rcases sigmaTrue_or_piFalse K.toZFAxioms n hFC' hBnd' hUE' with h | h
  · exact Or.inl
      ((sat_sigmaAtF K.toZFAxioms n (scons E (scons c e)) 1 0).mpr h)
  · exact Or.inr
      ((sat_piFalseAtF K.toZFAxioms n (scons E (scons c e)) 1 0).mpr h)

/-- **The successor-shift substitution instance holds**:
`sigmaTrue_renames`/`piFalse_renames` at the successor map, through
`compV_succMapU`. -/
theorem sat_shiftInvariantF (K : ZFCAxioms mem) (n : ℕ) (e : ℕ → W) :
    Sat mem e (shiftInvariantF n) := by
  intro c c' E d hFC hEx hUE E' hEc
  set e4 : ℕ → W := scons d (scons E (scons c' (scons c e))) with he4
  have hFC' : IsFormCodeSem K.toZFAxioms c :=
    (fIsFormCodeF_spec K.toZFAxioms e4 3).mp hFC
  have hUE' : IsUnivEnv K.toZFAxioms E :=
    (fUnivEnvF_spec K.toZFAxioms e4 1).mp hUE
  obtain ⟨s, hs, hr⟩ := hEx
  have hs' : s = succMap K.toZFAxioms :=
    (fSuccMapF_spec K.toZFAxioms (scons s e4) 0).mp hs
  have hrn : Renames K.toZFAxioms (succMap K.toZFAxioms) c c' := by
    have := (fRenamesF_spec K.toZFAxioms (scons s e4) 0 4 3).mp hr
    rwa [hs'] at this
  have hEc' : E' = econs K.toZFAxioms d E :=
    (fEconsF_spec K.toZFAxioms (scons E' e4) 0 1 2
      (fun x y y' hy hy' => hUE'.1 x y y' hy hy')).mp hEc
  subst hEc'
  have hE' : IsUnivEnv K.toZFAxioms (econs K.toZFAxioms d E) :=
    econs_isUnivEnv K.toZFAxioms hUE' d
  have hSig := sigmaTrue_renames K.toZFAxioms (n + 1) hFC'
    (succMap_isVarMap K.toZFAxioms) hE' hrn
  have hPiF := piFalse_renames K.toZFAxioms (n + 1) hFC'
    (succMap_isVarMap K.toZFAxioms) hE' hrn
  rw [compV_succMapU K.toZFAxioms hUE' d] at hSig hPiF
  constructor
  · refine SetTheory.Sat_fIff.mpr ?_
    rw [sat_sigmaAtF K.toZFAxioms n
        (scons (econs K.toZFAxioms d E) e4) 3 0,
      sat_sigmaAtF K.toZFAxioms n
        (scons (econs K.toZFAxioms d E) e4) 4 2]
    exact hSig
  · refine SetTheory.Sat_fIff.mpr ?_
    rw [sat_piFalseAtF K.toZFAxioms n
        (scons (econs K.toZFAxioms d E) e4) 3 0,
      sat_piFalseAtF K.toZFAxioms n
        (scons (econs K.toZFAxioms d E) e4) 4 2]
    exact hPiF

/-- **The general substitution lemma holds**:
`sigmaTrue_renames`/`piFalse_renames`, rendered. -/
theorem sat_substitutionInvariantF (K : ZFCAxioms mem) (n : ℕ) (e : ℕ → W) :
    Sat mem e (substitutionInvariantF n) := by
  intro c r c' E E₂ hFC hVM hRN hUE hCp
  set e5 : ℕ → W :=
    scons E₂ (scons E (scons c' (scons r (scons c e)))) with he5
  have hFC' : IsFormCodeSem K.toZFAxioms c :=
    (fIsFormCodeF_spec K.toZFAxioms e5 4).mp hFC
  have hVM' : IsVarMap K.toZFAxioms r :=
    (fVarMapF_spec K.toZFAxioms e5 3).mp hVM
  have hRN' : Renames K.toZFAxioms r c c' :=
    (fRenamesF_spec K.toZFAxioms e5 3 4 2).mp hRN
  have hUE' : IsUnivEnv K.toZFAxioms E :=
    (fUnivEnvF_spec K.toZFAxioms e5 1).mp hUE
  have hCp' : E₂ = compV K.toZFAxioms E r :=
    (fCompF_spec K.toZFAxioms e5 0 1 3
      (isEnvOn_envCarrier K.toZFAxioms hUE' (vempty K.toZFAxioms))
      hVM').mp hCp
  subst hCp'
  have hSig := sigmaTrue_renames K.toZFAxioms (n + 1) hFC' hVM' hUE' hRN'
  have hPiF := piFalse_renames K.toZFAxioms (n + 1) hFC' hVM' hUE' hRN'
  constructor
  · refine SetTheory.Sat_fIff.mpr ?_
    rw [sat_sigmaAtF K.toZFAxioms n e5 2 1,
      sat_sigmaAtF K.toZFAxioms n e5 4 0]
    exact hSig
  · refine SetTheory.Sat_fIff.mpr ?_
    rw [sat_piFalseAtF K.toZFAxioms n e5 2 1,
      sat_piFalseAtF K.toZFAxioms n e5 4 0]
    exact hPiF

/-- **Axiom-code truth holds**: `axiomCodesTrueAt`, rendered. -/
theorem sat_axiomSoundF (K : ZFCAxioms mem) (n : ℕ) (e : ℕ → W) :
    Sat mem e (axiomSoundF n) := by
  intro c E hAx hUE hBnd
  have hAx' := (fZFCAxiomCodeF_spec K.toZFAxioms (scons E (scons c e)) 1).mp hAx
  have hUE' := (fUnivEnvF_spec K.toZFAxioms (scons E (scons c e)) 0).mp hUE
  have hBnd' := (sat_boundedAtF K.toZFAxioms n (scons E (scons c e)) 1).mp hBnd
  have h := axiomCodesTrueAt K n _ _ hAx' hBnd' hUE'
  exact ⟨(sat_sigmaAtF K.toZFAxioms n (scons E (scons c e)) 1 0).mpr h.1,
    (sat_piTrueAtF K.toZFAxioms n (scons E (scons c e)) 1 0).mpr h.2⟩

local notation "kpair'" => _root_.SetTheory.kpair

/-! ## Satisfaction of the two Tarski fields

The polarized gadget is the two old ones read at a literal bit, and the
three clause skeletons of `ZFCinPA.CertificateFields` are discharged once
each; the seventeen rows are then exactly the seventeen clauses of
`ZFCinPA.TarskiFieldSemantics`'s `tarskiElim_levelSat` and
`tarskiIntro_levelSat`. -/

/-- The polarized gadget at bit `1` is the Sigma gadget. -/
theorem sat_polarAtF_one (H : ZFAxioms mem) (n : ℕ) (ee : ℕ → W)
    (ci ei : ℕ) :
    Sat mem ee (polarAtF n 1 ci ei) ↔ SigmaTrue H (n + 1) (ee ci) (ee ei) :=
  sat_sigmaAtF H n ee ci ei

/-- The polarized gadget at bit `0` is the Pi-falsity gadget. -/
theorem sat_polarAtF_zero (H : ZFAxioms mem) (n : ℕ) (ee : ℕ → W)
    (ci ei : ℕ) :
    Sat mem ee (polarAtF n 0 ci ei) ↔ PiFalse H (n + 1) (ee ci) (ee ei) :=
  sat_piFalseAtF H n ee ci ei

/-- **Satisfaction of the connective clause skeleton.**  The four guards
are read through their rendering specs; the compound code is pinned to the
tag shape the semantic clauses expect. -/
theorem sat_connClauseF (K : ZFCAxioms mem) (t : ℕ) (prem concl : Form)
    (e : ℕ → W)
    (hcl : ∀ a b E : W, IsFormCodeSem K.toZFAxioms a →
      IsFormCodeSem K.toZFAxioms b → IsUnivEnv K.toZFAxioms E →
      Sat mem (scons (kpair' K.toZFAxioms (natV K.toZFAxioms t)
          (kpair' K.toZFAxioms a b)) (scons E (scons b (scons a e)))) prem →
      Sat mem (scons (kpair' K.toZFAxioms (natV K.toZFAxioms t)
          (kpair' K.toZFAxioms a b)) (scons E (scons b (scons a e)))) concl) :
    Sat mem e (connClauseF t prem concl) := by
  intro a b E c hca hcb hE htag
  have htag' : c = kpair' K.toZFAxioms (natV K.toZFAxioms t)
      (kpair' K.toZFAxioms a b) :=
    (fTagPairF_spec K.toZFAxioms (scons c (scons E (scons b (scons a e))))
      0 t 3 2).mp htag
  subst htag'
  exact hcl a b E
    ((fIsFormCodeF_spec K.toZFAxioms _ 3).mp hca)
    ((fIsFormCodeF_spec K.toZFAxioms _ 2).mp hcb)
    ((fUnivEnvF_spec K.toZFAxioms _ 1).mp hE)

/-- **Satisfaction of the quantifier clause skeleton.** -/
theorem sat_quantClauseF (K : ZFCAxioms mem) (t : ℕ) (prem concl : Form)
    (e : ℕ → W)
    (hcl : ∀ a E d : W, IsFormCodeSem K.toZFAxioms a →
      IsUnivEnv K.toZFAxioms E →
      Sat mem (scons (econs K.toZFAxioms d E)
          (scons (kpair' K.toZFAxioms (natV K.toZFAxioms t) a)
            (scons d (scons E (scons a e))))) prem →
      Sat mem (scons (econs K.toZFAxioms d E)
          (scons (kpair' K.toZFAxioms (natV K.toZFAxioms t) a)
            (scons d (scons E (scons a e))))) concl) :
    Sat mem e (quantClauseF t prem concl) := by
  intro a E d c E' hca hE htag hec
  have hE' : IsUnivEnv K.toZFAxioms E :=
    (fUnivEnvF_spec K.toZFAxioms
      (scons E' (scons c (scons d (scons E (scons a e))))) 3).mp hE
  have hca' : IsFormCodeSem K.toZFAxioms a :=
    (fIsFormCodeF_spec K.toZFAxioms
      (scons E' (scons c (scons d (scons E (scons a e))))) 4).mp hca
  have htag' : c = kpair' K.toZFAxioms (natV K.toZFAxioms t) a :=
    (fTagUnF_spec K.toZFAxioms
      (scons E' (scons c (scons d (scons E (scons a e))))) 1 t 4).mp htag
  have hec' : E' = econs K.toZFAxioms d E :=
    (fEconsF_spec K.toZFAxioms
      (scons E' (scons c (scons d (scons E (scons a e))))) 0 2 3
      (fun x y y' hy hy' => hE'.1 x y y' hy hy')).mp hec
  subst htag'
  subst hec'
  exact hcl a E d hca' hE'

/-- **Satisfaction of the falsity row.** -/
theorem sat_botClauseF (K : ZFCAxioms mem) (n : ℕ) (e : ℕ → W) :
    Sat mem e (botClauseF n) := by
  intro E c hE htag
  have hE' : IsUnivEnv K.toZFAxioms E :=
    (fUnivEnvF_spec K.toZFAxioms (scons c (scons E e)) 1).mp hE
  have htag' : c = kpair' K.toZFAxioms (natV K.toZFAxioms 2)
      (vempty K.toZFAxioms) :=
    (fTaggedEmptyF_spec K.toZFAxioms (scons c (scons E e)) 0 2).mp htag
  subst htag'
  exact (sat_polarAtF_zero K.toZFAxioms n (scons _ (scons E e)) 0 1).mpr
    ((EnlargedFields.tarskiIntro_levelSat K.toZFAxioms n).botPi E hE')

set_option maxHeartbeats 1000000 in
/-- **The eight Tarski elimination clauses hold** at every level, in every
structure carrying the nine-axiom bundle.  Each row is the corresponding
clause of `EnlargedFields.tarskiElim_levelSat`, rendered. -/
theorem sat_tarskiElimF (K : ZFCAxioms mem) (n : ℕ) (e : ℕ → W) :
    Sat mem e (tarskiElimF n) := by
  have E := EnlargedFields.tarskiElim_levelSat K.toZFAxioms (n + 1)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine sat_connClauseF K 3 _ _ e fun a b F hca hcb hF hp => ?_
    rcases E.impSigma a b F hca hcb hF
        ((sat_polarAtF_one K.toZFAxioms n _ 0 1).mp hp) with k | k
    · exact Or.inl ((sat_polarAtF_zero K.toZFAxioms n _ 3 1).mpr k)
    · exact Or.inr ((sat_polarAtF_one K.toZFAxioms n _ 2 1).mpr k)
  · refine sat_connClauseF K 3 _ _ e fun a b F hca hcb hF hp => ?_
    obtain ⟨k1, k2⟩ := E.impPi a b F hca hcb hF
      ((sat_polarAtF_zero K.toZFAxioms n _ 0 1).mp hp)
    exact ⟨(sat_polarAtF_one K.toZFAxioms n _ 3 1).mpr k1,
      (sat_polarAtF_zero K.toZFAxioms n _ 2 1).mpr k2⟩
  · refine sat_connClauseF K 4 _ _ e fun a b F hca hcb hF hp => ?_
    obtain ⟨k1, k2⟩ := E.andSigma a b F hca hcb hF
      ((sat_polarAtF_one K.toZFAxioms n _ 0 1).mp hp)
    exact ⟨(sat_polarAtF_one K.toZFAxioms n _ 3 1).mpr k1,
      (sat_polarAtF_one K.toZFAxioms n _ 2 1).mpr k2⟩
  · refine sat_connClauseF K 4 _ _ e fun a b F hca hcb hF hp => ?_
    rcases E.andPi a b F hca hcb hF
        ((sat_polarAtF_zero K.toZFAxioms n _ 0 1).mp hp) with k | k
    · exact Or.inl ((sat_polarAtF_zero K.toZFAxioms n _ 3 1).mpr k)
    · exact Or.inr ((sat_polarAtF_zero K.toZFAxioms n _ 2 1).mpr k)
  · refine sat_connClauseF K 5 _ _ e fun a b F hca hcb hF hp => ?_
    rcases E.orSigma a b F hca hcb hF
        ((sat_polarAtF_one K.toZFAxioms n _ 0 1).mp hp) with k | k
    · exact Or.inl ((sat_polarAtF_one K.toZFAxioms n _ 3 1).mpr k)
    · exact Or.inr ((sat_polarAtF_one K.toZFAxioms n _ 2 1).mpr k)
  · refine sat_connClauseF K 5 _ _ e fun a b F hca hcb hF hp => ?_
    obtain ⟨k1, k2⟩ := E.orPi a b F hca hcb hF
      ((sat_polarAtF_zero K.toZFAxioms n _ 0 1).mp hp)
    exact ⟨(sat_polarAtF_zero K.toZFAxioms n _ 3 1).mpr k1,
      (sat_polarAtF_zero K.toZFAxioms n _ 2 1).mpr k2⟩
  · refine sat_quantClauseF K 6 _ _ e fun a F d hca hF hp => ?_
    exact (sat_polarAtF_one K.toZFAxioms n _ 4 0).mpr
      (E.allSigma a F d hca hF ((sat_polarAtF_one K.toZFAxioms n _ 1 3).mp hp))
  · refine sat_quantClauseF K 7 _ _ e fun a F d hca hF hp => ?_
    exact (sat_polarAtF_zero K.toZFAxioms n _ 4 0).mpr
      (E.exPi a F d hca hF ((sat_polarAtF_zero K.toZFAxioms n _ 1 3).mp hp))

set_option maxHeartbeats 1000000 in
/-- **The nine Tarski introduction clauses hold** at every level.  Each row
is the corresponding clause of `EnlargedFields.tarskiIntro_levelSat`,
rendered. -/
theorem sat_tarskiIntroF (K : ZFCAxioms mem) (n : ℕ) (e : ℕ → W) :
    Sat mem e (tarskiIntroF n) := by
  have I := EnlargedFields.tarskiIntro_levelSat K.toZFAxioms n
  refine ⟨sat_botClauseF K n e, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine sat_connClauseF K 3 _ _ e fun a b F hca hcb hF hp => ?_
    refine (sat_polarAtF_one K.toZFAxioms n _ 0 1).mpr
      (I.impSigma a b F hca hcb hF ?_)
    rcases hp with k | k
    · exact Or.inl ((sat_polarAtF_zero K.toZFAxioms n _ 3 1).mp k)
    · exact Or.inr ((sat_polarAtF_one K.toZFAxioms n _ 2 1).mp k)
  · refine sat_connClauseF K 3 _ _ e fun a b F hca hcb hF hp => ?_
    exact (sat_polarAtF_zero K.toZFAxioms n _ 0 1).mpr
      (I.impPi a b F hca hcb hF
        ((sat_polarAtF_one K.toZFAxioms n _ 3 1).mp hp.1)
        ((sat_polarAtF_zero K.toZFAxioms n _ 2 1).mp hp.2))
  · refine sat_connClauseF K 4 _ _ e fun a b F hca hcb hF hp => ?_
    exact (sat_polarAtF_one K.toZFAxioms n _ 0 1).mpr
      (I.andSigma a b F hca hcb hF
        ((sat_polarAtF_one K.toZFAxioms n _ 3 1).mp hp.1)
        ((sat_polarAtF_one K.toZFAxioms n _ 2 1).mp hp.2))
  · refine sat_connClauseF K 4 _ _ e fun a b F hca hcb hF hp => ?_
    refine (sat_polarAtF_zero K.toZFAxioms n _ 0 1).mpr
      (I.andPi a b F hca hcb hF ?_)
    rcases hp with k | k
    · exact Or.inl ((sat_polarAtF_zero K.toZFAxioms n _ 3 1).mp k)
    · exact Or.inr ((sat_polarAtF_zero K.toZFAxioms n _ 2 1).mp k)
  · refine sat_connClauseF K 5 _ _ e fun a b F hca hcb hF hp => ?_
    refine (sat_polarAtF_one K.toZFAxioms n _ 0 1).mpr
      (I.orSigma a b F hca hcb hF ?_)
    rcases hp with k | k
    · exact Or.inl ((sat_polarAtF_one K.toZFAxioms n _ 3 1).mp k)
    · exact Or.inr ((sat_polarAtF_one K.toZFAxioms n _ 2 1).mp k)
  · refine sat_connClauseF K 5 _ _ e fun a b F hca hcb hF hp => ?_
    exact (sat_polarAtF_zero K.toZFAxioms n _ 0 1).mpr
      (I.orPi a b F hca hcb hF
        ((sat_polarAtF_zero K.toZFAxioms n _ 3 1).mp hp.1)
        ((sat_polarAtF_zero K.toZFAxioms n _ 2 1).mp hp.2))
  · refine sat_quantClauseF K 6 _ _ e fun a F d hca hF hp => ?_
    exact (sat_polarAtF_zero K.toZFAxioms n _ 1 3).mpr
      (I.allPi a F d hca hF ((sat_polarAtF_zero K.toZFAxioms n _ 4 0).mp hp))
  · refine sat_quantClauseF K 7 _ _ e fun a F d hca hF hp => ?_
    exact (sat_polarAtF_one K.toZFAxioms n _ 1 3).mpr
      (I.exSigma a F d hca hF ((sat_polarAtF_one K.toZFAxioms n _ 4 0).mp hp))

end SatGadgets

/- The seven field sentences contain the large concrete goal-2 macros, and
reducing a universal closure evaluates `freeVariables` over the whole
translated formula.  Nothing below needs to see through a macro — every
fact enters through a rendering spec or a named lemma — and the elaborator
must not try.  (Same guard as `quote_conZFCSet`'s in
`ZFCinPA.UniformStatement`.) -/
attribute [local irreducible] BoundedZFCConsistency.fQuantBoundedF
  BoundedZFCConsistency.fZFCAxiomCodeF BoundedZFCConsistency.fIsFormCodeF
  BoundedZFCConsistency.fUnivEnvF BoundedZFCConsistency.fTaggedEmptyF
  BoundedZFCConsistency.fRenamesF BoundedZFCConsistency.fVarMapF
  BoundedZFCConsistency.fCompF BoundedZFCConsistency.fEconsF
  BoundedZFCConsistency.fSuccMapF BoundedZFCConsistency.fTagPairF
  BoundedZFCConsistency.fTagUnF

/- `conZFCForm n` unfolds to the sealed closure of a large body, and
reducing the closure evaluates `bound` over the whole of it.  The final
base proof only needs `conZFCSetCodeFun_natCast`, which is a lemma. -/
attribute [local irreducible] BoundedZFCConsistency.conZFCForm
  SetTheory.sealF

/-! ## The field sentences in Foundation's `ℒₛₑₜ`, and their derivations -/

/-- The local-step field, as a Foundation sentence. -/
def localStepSet (n : ℕ) : SetTheorySentence :=
  (toSet 0 (localStepF n)).univCl

/-- The cross-level field, as a Foundation sentence. -/
def crossLevelSet (n : ℕ) : SetTheorySentence :=
  (toSet 0 (crossLevelF n)).univCl

/-- The shift-invariance field, as a Foundation sentence. -/
def shiftInvariantSet (n : ℕ) : SetTheorySentence :=
  (toSet 0 (shiftInvariantF n)).univCl

/-- The substitution-invariance field, as a Foundation sentence. -/
def substitutionInvariantSet (n : ℕ) : SetTheorySentence :=
  (toSet 0 (substitutionInvariantF n)).univCl

/-- The axiom-soundness field, as a Foundation sentence. -/
def axiomSoundSet (n : ℕ) : SetTheorySentence :=
  (toSet 0 (axiomSoundF n)).univCl

/-- The Tarski-elimination field, as a Foundation sentence. -/
def tarskiElimSet (n : ℕ) : SetTheorySentence :=
  (toSet 0 (tarskiElimF n)).univCl

/-- The Tarski-introduction field, as a Foundation sentence. -/
def tarskiIntroSet (n : ℕ) : SetTheorySentence :=
  (toSet 0 (tarskiIntroF n)).univCl

section Provability

/-- **`𝗭𝗙𝗖` derives every local-step field sentence**, by completeness
from `sat_localStepF`. -/
theorem zfc_proves_localStepSet (n : ℕ) : 𝗭𝗙𝗖 ⊢ localStepSet n := by
  refine SetTheory.provable_of_models.{0} 𝗭𝗙𝗖 (localStepSet n) ?_
  intro W _ _ _
  show W↓[ℒₛₑₜ] ⊧ (toSet 0 (localStepF n)).univCl
  refine models_iff_proposition.mpr fun f => ?_
  exact (eval_toSet (localStepF n) 0 ![] f f
    (fun i => i.elim0) (fun j => by rw [Nat.zero_add])).mpr
    (sat_localStepF zfcAxioms_of_models n f)

/-- **`𝗭𝗙𝗖` derives every cross-level field sentence.** -/
theorem zfc_proves_crossLevelSet (n : ℕ) : 𝗭𝗙𝗖 ⊢ crossLevelSet n := by
  refine SetTheory.provable_of_models.{0} 𝗭𝗙𝗖 (crossLevelSet n) ?_
  intro W _ _ _
  show W↓[ℒₛₑₜ] ⊧ (toSet 0 (crossLevelF n)).univCl
  refine models_iff_proposition.mpr fun f => ?_
  exact (eval_toSet (crossLevelF n) 0 ![] f f
    (fun i => i.elim0) (fun j => by rw [Nat.zero_add])).mpr
    (sat_crossLevelF zfcAxioms_of_models n f)

/-- **`𝗭𝗙𝗖` derives every shift-invariance field sentence.** -/
theorem zfc_proves_shiftInvariantSet (n : ℕ) :
    𝗭𝗙𝗖 ⊢ shiftInvariantSet n := by
  refine SetTheory.provable_of_models.{0} 𝗭𝗙𝗖 (shiftInvariantSet n) ?_
  intro W _ _ _
  show W↓[ℒₛₑₜ] ⊧ (toSet 0 (shiftInvariantF n)).univCl
  refine models_iff_proposition.mpr fun f => ?_
  exact (eval_toSet (shiftInvariantF n) 0 ![] f f
    (fun i => i.elim0) (fun j => by rw [Nat.zero_add])).mpr
    (sat_shiftInvariantF zfcAxioms_of_models n f)

/-- **`𝗭𝗙𝗖` derives every substitution-invariance field sentence.** -/
theorem zfc_proves_substitutionInvariantSet (n : ℕ) :
    𝗭𝗙𝗖 ⊢ substitutionInvariantSet n := by
  refine SetTheory.provable_of_models.{0} 𝗭𝗙𝗖
    (substitutionInvariantSet n) ?_
  intro W _ _ _
  show W↓[ℒₛₑₜ] ⊧ (toSet 0 (substitutionInvariantF n)).univCl
  refine models_iff_proposition.mpr fun f => ?_
  exact (eval_toSet (substitutionInvariantF n) 0 ![] f f
    (fun i => i.elim0) (fun j => by rw [Nat.zero_add])).mpr
    (sat_substitutionInvariantF zfcAxioms_of_models n f)

/-- **`𝗭𝗙𝗖` derives every axiom-soundness field sentence.** -/
theorem zfc_proves_axiomSoundSet (n : ℕ) : 𝗭𝗙𝗖 ⊢ axiomSoundSet n := by
  refine SetTheory.provable_of_models.{0} 𝗭𝗙𝗖 (axiomSoundSet n) ?_
  intro W _ _ _
  show W↓[ℒₛₑₜ] ⊧ (toSet 0 (axiomSoundF n)).univCl
  refine models_iff_proposition.mpr fun f => ?_
  exact (eval_toSet (axiomSoundF n) 0 ![] f f
    (fun i => i.elim0) (fun j => by rw [Nat.zero_add])).mpr
    (sat_axiomSoundF zfcAxioms_of_models n f)

/-- **`𝗭𝗙𝗖` derives every Tarski-elimination field sentence.** -/
theorem zfc_proves_tarskiElimSet (n : ℕ) : 𝗭𝗙𝗖 ⊢ tarskiElimSet n := by
  refine SetTheory.provable_of_models.{0} 𝗭𝗙𝗖 (tarskiElimSet n) ?_
  intro W _ _ _
  show W↓[ℒₛₑₜ] ⊧ (toSet 0 (tarskiElimF n)).univCl
  refine models_iff_proposition.mpr fun f => ?_
  exact (eval_toSet (tarskiElimF n) 0 ![] f f
    (fun i => i.elim0) (fun j => by rw [Nat.zero_add])).mpr
    (sat_tarskiElimF zfcAxioms_of_models n f)

/-- **`𝗭𝗙𝗖` derives every Tarski-introduction field sentence.** -/
theorem zfc_proves_tarskiIntroSet (n : ℕ) : 𝗭𝗙𝗖 ⊢ tarskiIntroSet n := by
  refine SetTheory.provable_of_models.{0} 𝗭𝗙𝗖 (tarskiIntroSet n) ?_
  intro W _ _ _
  show W↓[ℒₛₑₜ] ⊧ (toSet 0 (tarskiIntroF n)).univCl
  refine models_iff_proposition.mpr fun f => ?_
  exact (eval_toSet (tarskiIntroF n) 0 ![] f f
    (fun i => i.elim0) (fun j => by rw [Nat.zero_add])).mpr
    (sat_tarskiIntroF zfcAxioms_of_models n f)

end Provability

/-! ## Quotation of the field sentences

The field sentences are closed, so the universal closures are vacuous at
the level of codes — the `quote_conZFCSet` argument, once per field. -/

section Quotation

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem quote_univCl_of_closed {φ : SetTheory.Form}
    (hfree : ∀ i, ¬ SetTheory.Free i φ) :
    (⌜(toSet 0 φ).univCl⌝ : V) = ⌜toSet 0 φ⌝ := by
  have hfv : (toSet 0 φ).freeVariables = ∅ :=
    freeVariables_toSet φ 0 (fun i hi => absurd hi (hfree i))
  have h2 : ((toSet 0 φ).univCl : SetTheorySemiproposition 0) = toSet 0 φ := by
    rw [Semiformula.coe_univCl_eq_univCl', Semiformula.univCl'_eq_self_of _ hfv]
  show (⌜((toSet 0 φ).univCl : SetTheorySentence)⌝ : V) = _
  rw [Sentence.quote_def, h2]

/-- The local-step sentence's quote is the field builder's value. -/
theorem quote_localStepSet (n : ℕ) :
    (⌜localStepSet n⌝ : V) = localStepCode ((n : ℕ) : V) := by
  rw [localStepSet, quote_univCl_of_closed (not_free_localStepF n),
    localStepCode_natCast]

/-- The cross-level sentence's quote is the field builder's value. -/
theorem quote_crossLevelSet (n : ℕ) :
    (⌜crossLevelSet n⌝ : V) = crossLevelCode ((n : ℕ) : V) := by
  rw [crossLevelSet, quote_univCl_of_closed (not_free_crossLevelF n),
    crossLevelCode_natCast]

/-- The shift-invariance sentence's quote is the field builder's value. -/
theorem quote_shiftInvariantSet (n : ℕ) :
    (⌜shiftInvariantSet n⌝ : V) = shiftInvariantCode ((n : ℕ) : V) := by
  rw [shiftInvariantSet,
    quote_univCl_of_closed (not_free_shiftInvariantF n),
    shiftInvariantCode_natCast]

/-- The substitution-invariance sentence's quote is the field builder's
value. -/
theorem quote_substitutionInvariantSet (n : ℕ) :
    (⌜substitutionInvariantSet n⌝ : V) =
      substitutionInvariantCode ((n : ℕ) : V) := by
  rw [substitutionInvariantSet,
    quote_univCl_of_closed (not_free_substitutionInvariantF n),
    substitutionInvariantCode_natCast]

/-- The axiom-soundness sentence's quote is the field builder's value. -/
theorem quote_axiomSoundSet (n : ℕ) :
    (⌜axiomSoundSet n⌝ : V) = axiomSoundCode ((n : ℕ) : V) := by
  rw [axiomSoundSet, quote_univCl_of_closed (not_free_axiomSoundF n),
    axiomSoundCode_natCast]

/-- The Tarski-elimination sentence's quote is the field builder's value. -/
theorem quote_tarskiElimSet (n : ℕ) :
    (⌜tarskiElimSet n⌝ : V) = tarskiElimCode ((n : ℕ) : V) := by
  rw [tarskiElimSet, quote_univCl_of_closed (not_free_tarskiElimF n),
    tarskiElimCode_natCast]

/-- The Tarski-introduction sentence's quote is the field builder's
value. -/
theorem quote_tarskiIntroSet (n : ℕ) :
    (⌜tarskiIntroSet n⌝ : V) = tarskiIntroCode ((n : ℕ) : V) := by
  rw [tarskiIntroSet, quote_univCl_of_closed (not_free_tarskiIntroF n),
    tarskiIntroCode_natCast]

end Quotation

/-! ## The typed base proofs, by D1 -/

section BaseProofs

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

set_option backward.isDefEq.respectTransparency false in
/-- A typed internal `𝗭𝗙𝗖` proof of the local-step field at index `0`. -/
noncomputable def baseLocalStepProof :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢! localStepFormula (0 : V) := by
  have h := (internal_provable_of_outer_provable (V := V)
    (zfc_proves_localStepSet 0)).get
  have heq : (⌜localStepSet 0⌝ : Bootstrapping.Formula V ℒₛₑₜ) =
      localStepFormula 0 := by
    apply Semiformula.ext
    show (⌜localStepSet 0⌝ : V) = localStepCode (0 : V)
    rw [show (0 : V) = ((0 : ℕ) : V) by simp, quote_localStepSet]
  rw [← heq]
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- A typed internal `𝗭𝗙𝗖` proof of the cross-level field at index `0`. -/
noncomputable def baseCrossLevelProof :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢! crossLevelFormula (0 : V) := by
  have h := (internal_provable_of_outer_provable (V := V)
    (zfc_proves_crossLevelSet 0)).get
  have heq : (⌜crossLevelSet 0⌝ : Bootstrapping.Formula V ℒₛₑₜ) =
      crossLevelFormula 0 := by
    apply Semiformula.ext
    show (⌜crossLevelSet 0⌝ : V) = crossLevelCode (0 : V)
    rw [show (0 : V) = ((0 : ℕ) : V) by simp, quote_crossLevelSet]
  rw [← heq]
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- A typed internal `𝗭𝗙𝗖` proof of the shift-invariance field at index
`0`. -/
noncomputable def baseShiftInvariantProof :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢! shiftInvariantFormula (0 : V) := by
  have h := (internal_provable_of_outer_provable (V := V)
    (zfc_proves_shiftInvariantSet 0)).get
  have heq : (⌜shiftInvariantSet 0⌝ : Bootstrapping.Formula V ℒₛₑₜ) =
      shiftInvariantFormula 0 := by
    apply Semiformula.ext
    show (⌜shiftInvariantSet 0⌝ : V) = shiftInvariantCode (0 : V)
    rw [show (0 : V) = ((0 : ℕ) : V) by simp, quote_shiftInvariantSet]
  rw [← heq]
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- A typed internal `𝗭𝗙𝗖` proof of the substitution-invariance field at
index `0`. -/
noncomputable def baseSubstitutionInvariantProof :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      substitutionInvariantFormula (0 : V) := by
  have h := (internal_provable_of_outer_provable (V := V)
    (zfc_proves_substitutionInvariantSet 0)).get
  have heq : (⌜substitutionInvariantSet 0⌝ : Bootstrapping.Formula V ℒₛₑₜ) =
      substitutionInvariantFormula 0 := by
    apply Semiformula.ext
    show (⌜substitutionInvariantSet 0⌝ : V) =
      substitutionInvariantCode (0 : V)
    rw [show (0 : V) = ((0 : ℕ) : V) by simp,
      quote_substitutionInvariantSet]
  rw [← heq]
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- A typed internal `𝗭𝗙𝗖` proof of the axiom-soundness field at index
`0`. -/
noncomputable def baseAxiomSoundProof :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢! axiomSoundFormula (0 : V) := by
  have h := (internal_provable_of_outer_provable (V := V)
    (zfc_proves_axiomSoundSet 0)).get
  have heq : (⌜axiomSoundSet 0⌝ : Bootstrapping.Formula V ℒₛₑₜ) =
      axiomSoundFormula 0 := by
    apply Semiformula.ext
    show (⌜axiomSoundSet 0⌝ : V) = axiomSoundCode (0 : V)
    rw [show (0 : V) = ((0 : ℕ) : V) by simp, quote_axiomSoundSet]
  rw [← heq]
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- A typed internal `𝗭𝗙𝗖` proof of the Tarski-elimination field at index
`0`. -/
noncomputable def baseTarskiElimProof :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢! tarskiElimFormula (0 : V) := by
  have h := (internal_provable_of_outer_provable (V := V)
    (zfc_proves_tarskiElimSet 0)).get
  have heq : (⌜tarskiElimSet 0⌝ : Bootstrapping.Formula V ℒₛₑₜ) =
      tarskiElimFormula 0 := by
    apply Semiformula.ext
    show (⌜tarskiElimSet 0⌝ : V) = tarskiElimCode (0 : V)
    rw [show (0 : V) = ((0 : ℕ) : V) by simp, quote_tarskiElimSet]
  rw [← heq]
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- A typed internal `𝗭𝗙𝗖` proof of the Tarski-introduction field at index
`0`. -/
noncomputable def baseTarskiIntroProof :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢! tarskiIntroFormula (0 : V) := by
  have h := (internal_provable_of_outer_provable (V := V)
    (zfc_proves_tarskiIntroSet 0)).get
  have heq : (⌜tarskiIntroSet 0⌝ : Bootstrapping.Formula V ℒₛₑₜ) =
      tarskiIntroFormula 0 := by
    apply Semiformula.ext
    show (⌜tarskiIntroSet 0⌝ : V) = tarskiIntroCode (0 : V)
    rw [show (0 : V) = ((0 : ℕ) : V) by simp, quote_tarskiIntroSet]
  rw [← heq]
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- A typed internal `𝗭𝗙𝗖` proof of the forced final field at index `0`:
the internalized `Con₀(ZFC)`, by D1 from `zfc_proves_conZFCSet`.

Unlike the seven variable fields, this proof goes through the *raw*
provability predicate (`provable_conZFCSet_standard_point`) and rebuilds
the typed proof by the `toTProof` pattern: the quotation identity of the
sealed consistency sentence enters only as a propositional rewrite, never
as a definitional-equality claim the elaborator would have to check by
unfolding the sealed closure. -/
noncomputable def baseFinalConsistencyProof :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      conZFCSetFormula (0 : V) isFormula_conZFCSetCodeFun_zero := by
  have hp : Provable 𝗭𝗙𝗖 (conZFCSetCodeFun (0 : V)) := by
    rw [show (0 : V) = ((0 : ℕ) : V) by simp, conZFCSetCodeFun_natCast]
    exact provable_conZFCSet_standard_point 0
  exact ⟨hp.choose, by
    simpa [Proof, conZFCSetFormula] using hp.choose_spec⟩

/-! ## The assembled base master certificate -/

/-- **The base master certificate**: a typed internal `𝗭𝗙𝗖` proof of the
concrete family's complete eight-field sentence at level `0`. -/
noncomputable def baseZFCMasterCertificate :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      ((concreteZFCTruthCertificateFamily (V := V)).fields 0
        isFormula_conZFCSetCodeFun_zero).sentence :=
  ZFCTruthCertificateFields.intro _
    baseLocalStepProof baseCrossLevelProof baseShiftInvariantProof
    baseSubstitutionInvariantProof baseAxiomSoundProof
    baseTarskiElimProof baseTarskiIntroProof
    baseFinalConsistencyProof

end BaseProofs

/-! ## The exact remaining obligation -/

section Endpoint

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

set_option backward.isDefEq.respectTransparency false in
/-- **The complete reduction of the uniform internal-provability project
to the staged successor.**  With the concrete family, its `𝚺₁` field-code
graphs, and the base master certificate all in place, the model-internal
proof selector — and with it, by
`peano_proves_uniformZFCProvability_of_selectorInAllModels`, the sentence
`PA ⊢ ∀ n, Prov_ZFC(⌜Conₙ(ZFC)⌝)` — now needs exactly one further input:
a staged successor witness for this family at every model index.  (The
transparency option only identifies the public `ZFC_delta1` instance with
the instance stored by `Theory.internalize`; it does not choose or alter
any proof code.) -/
theorem zfcProofSelectorIn_of_concreteStagedSuccessor
    (successorTemplates :
      HasStagedSuccessor (concreteZFCTruthCertificateFamily (V := V))) :
    ZFCProofSelectorIn V :=
  zfcProofSelectorIn_of_stagedCertificates_and_fieldCodes
    (concreteZFCTruthCertificateFamily (V := V))
    concreteFamily_localStep_definable
    concreteFamily_crossLevel_definable
    concreteFamily_shiftInvariant_definable
    concreteFamily_substitutionInvariant_definable
    concreteFamily_axiomSound_definable
    concreteFamily_tarskiElim_definable
    concreteFamily_tarskiIntro_definable
    baseZFCMasterCertificate
    successorTemplates

end Endpoint

end ZFCinPA
end LeanProofs
