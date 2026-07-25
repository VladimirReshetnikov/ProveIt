import ZFCinPA.LevelCodeTower

/-!
# The five variable certificate fields of the concrete `𝗭𝗙𝗖` truth family

`ZFCinPA.CertificateFamily` fixes the shape of a level-indexed six-field
`𝗭𝗙𝗖` truth certificate: five variable truth-construction fields plus the
forced internalized `Conₓ(ZFC)`.  This module chooses the five fields.

## The field design

Goal 2 (`BoundedZFCConsistency`) derives `Conₙ(ZFC)` from four semantic
pillars at level `n`:

1. the local polarity laws of level-`n+1` truth — falsity is never
   Sigma-true (`sigmaTrue_bot`), and Sigma-truth excludes Pi-falsity
   (`sigmaTrue_not_piFalse`/`piTrue_of_sigmaTrue`);
2. the collapse/totality law — every internal form code whose quantifier
   complexity is bounded by the numeral of `n` is *decided* at level `n+1`
   (`sigmaTrue_or_piFalse`, the content of the level-collapse theorem);
3. the substitution lemmas — level-`n+1` truth is invariant under internal
   renaming along a variable map (`sigmaTrue_renames`/`piFalse_renames`),
   consumed by the calculus at the successor-shift and general instances;
4. axiom truth — every bounded internal ZFC axiom code is true at level
   `n+1` on both polarities (`axiomCodesTrueAt`).

The five family slots internalize exactly these statements at internal
index `x`, mirroring goal 1's slot discipline:

| slot                    | object-level content at index `x`             |
| ----------------------- | --------------------------------------------- |
| `localStep`             | the local polarity laws at level `x+1`        |
| `crossLevel`            | decidedness of `x`-bounded codes at `x+1`     |
| `shiftInvariant`        | truth invariance under the successor shift    |
| `substitutionInvariant` | truth invariance under arbitrary renaming     |
| `axiomSound`            | axiom-code truth at level `x+1`, bound `x`    |

Each field is a *sentence* of the repository's `ℒₛₑₜ` syntax (`Form`),
built so that every occurrence of the level-indexed truth predicates is
the **canonical instance** of `ZFCinPA.LevelCodeTower` — `fSigmaTrueF`,
`fPiFalseF`, `fPiTrueF` at slots `(1, 0)` — and every other leaf is a
fixed (`x`-independent) macro of goal 2.  The internal code builders then
splice the level towers `sigmaTrueCode (x+1)`/`piFalseCode (x+1)`/
`piTrueCode (x+1)` and the numeral chain `numChainCode x` into fixed
constructor spines, exactly the `UniformStatement`/`LevelCodeTower`
technique.

## The canonical-slot gadget

A truth leaf can only be canonical when the two innermost binders at its
position are (code, environment).  Where a field's quantifier prefix
places a pair elsewhere, the leaf is wrapped in the two-binder
re-quantification gadget `canonAtF ci ei φ` — "for all `a = slot ci` and
`b = slot ei`, `φ` at `(a, b)`" — whose two equality guards are fixed
atoms.  Every truth leaf below uses the gadget, uniformly, so a single
pair of quotation/satisfaction lemmas serves all five fields.

## Standard points

At a standard index `x = n` each field's built code is the quotation of
the named `Form`-level sentence at level `n` (`localStepF n`, …), each of
which goal 2's semantics proves true in every model of ZFC.  That is what
makes the base certificate (and the D1 transports of the staged compiler)
possible; the base itself lives in `ZFCinPA.BaseCertificate`.

## Disciplines

The module observes `LevelCodeTower`'s two disciplines.  *Parameter
firewall*: every `Defined` evaluation proof is stated with the fixed leaf
codes as variables, and the astronomically large concrete constants enter
only by instantiation — never through `simp`.  *Per-declaration freeMax
bounds*: each fixed macro leaf gets its own kernel-evaluated `freeMax`
bound in its own declaration, so no heartbeat budget is shared.
-/

set_option autoImplicit false

namespace LeanProofs
namespace ZFCinPA

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open BoundedZFCConsistency (fNumF fTripleMemF fUnivEnvF levelSatF
  fSigmaTrueF fPiFalseF fPiTrueF fIsFormCodeF fQuantBoundedF
  fZFCAxiomCodeF fTaggedEmptyF fVarMapF fRenamesF fCompF fEconsF
  fSuccMapF)

/-! ## Form-level definitions

The five field sentences, as metatheoretic `Form`s at external level `n`.
No model appears in this section. -/

section FormLevel

open SetTheory (Form Free fIff)

/-- **The canonical-slot gadget**: re-quantify the pair `(slot ci, slot ei)`
into the two innermost binders, guarded by two equality atoms, so that `φ`
may be written at the canonical slots `(1, 0)`. -/
def canonAtF (ci ei : ℕ) (φ : SetTheory.Form) : SetTheory.Form :=
  .fAll (.fAll (.fImp (.fEq 1 (ci + 2)) (.fImp (.fEq 0 (ei + 2)) φ)))

/-- Sigma-truth at level `n+1` of the pair `(slot ci, slot ei)`, through
the gadget: the payload is exactly the canonical tower instance. -/
def sigmaAtF (n ci ei : ℕ) : SetTheory.Form :=
  canonAtF ci ei (fSigmaTrueF (n + 1) 1 0)

/-- Pi-falsity at level `n+1` of the pair `(slot ci, slot ei)`. -/
def piFalseAtF (n ci ei : ℕ) : SetTheory.Form :=
  canonAtF ci ei (fPiFalseF (n + 1) 1 0)

/-- Pi-truth at level `n+1` of the pair `(slot ci, slot ei)`. -/
def piTrueAtF (n ci ei : ℕ) : SetTheory.Form :=
  canonAtF ci ei (fPiTrueF (n + 1) 1 0)

/-- "Slot `ci` is quantifier-bounded by the numeral of `n`": the numeral is
introduced by one existential, so the only `n`-dependent leaf is the
numeral chain `fNumF 0 n` already handled by `numChainCode`. -/
def boundedAtF (n ci : ℕ) : SetTheory.Form :=
  .fEx (.fAnd (fNumF 0 n) (fQuantBoundedF 0 (ci + 1)))

/-- **Field 1, `localStep`: the local polarity laws at level `n+1`.**

For every code `c` (slot `1`) and universe environment `E` (slot `0`):
the falsity code is not Sigma-true, and Sigma-truth of an internal form
code implies its Pi-truth (exclusivity).  Goal-2 counterparts:
`sigmaTrue_bot` and `piTrue_of_sigmaTrue`. -/
def localStepF (n : ℕ) : SetTheory.Form :=
  .fAll (.fAll (.fImp (fUnivEnvF 0)
    (.fAnd
      (.fImp (fTaggedEmptyF 1 2) (.fImp (sigmaAtF n 1 0) .fBot))
      (.fImp (fIsFormCodeF 1)
        (.fImp (sigmaAtF n 1 0) (piTrueAtF n 1 0))))))

/-- **Field 2, `crossLevel`: decidedness of bounded codes at level `n+1`.**

For every internal form code `c` (slot `1`) whose quantifier complexity is
bounded by the numeral of `n`, and every universe environment `E`
(slot `0`), the code is Sigma-true or Pi-false at level `n+1`.  This is
the object-level content of the level-collapse theorem; goal-2
counterpart: `sigmaTrue_or_piFalse`. -/
def crossLevelF (n : ℕ) : SetTheory.Form :=
  .fAll (.fAll (.fImp (fIsFormCodeF 1) (.fImp (fUnivEnvF 0)
    (.fImp (boundedAtF n 1)
      (.fOr (sigmaAtF n 1 0) (piFalseAtF n 1 0))))))

/-- **Field 3, `shiftInvariant`: the successor-shift substitution
instance at level `n+1`.**

Binders, outermost first: the code `c` (slot `3`), its shift `c'`
(slot `2`), the environment `E` (slot `1`), the shifted-in value `d`
(slot `0`), and then the extended environment `E'` bound with the guard
`E' = econs d E`.  If `c` is an internal form code and some successor map
renames `c` to `c'`, then Sigma-truth and Pi-falsity of `c'` at `E'`
agree with those of `c` at `E`.  Goal-2 counterparts:
`sigmaTrue_renames`/`piFalse_renames` at `succMap` with
`compV_succMapU`. -/
def shiftInvariantF (n : ℕ) : SetTheory.Form :=
  .fAll (.fAll (.fAll (.fAll
    (.fImp (fIsFormCodeF 3)
      (.fImp (.fEx (.fAnd (fSuccMapF 0) (fRenamesF 0 4 3)))
        (.fImp (fUnivEnvF 1)
          (.fAll
            (.fImp (fEconsF 0 1 2)
              (.fAnd
                (fIff (sigmaAtF n 3 0) (sigmaAtF n 4 2))
                (fIff (piFalseAtF n 3 0) (piFalseAtF n 4 2)))))))))))

/-- **Field 4, `substitutionInvariant`: the general substitution lemma at
level `n+1`.**

Binders, outermost first: the code `c` (slot `4`), the variable map `r`
(slot `3`), the renaming `c'` (slot `2`), the environment `E` (slot `1`),
and the composite `E₂` (slot `0`) guarded by `E₂ = compV E r`.  If `c` is
an internal form code, `r` a variable map renaming `c` to `c'`, and `E` a
universe environment, then Sigma-truth and Pi-falsity of `c'` at `E`
agree with those of `c` at `E₂`.  Goal-2 counterparts:
`sigmaTrue_renames`/`piFalse_renames`. -/
def substitutionInvariantF (n : ℕ) : SetTheory.Form :=
  .fAll (.fAll (.fAll (.fAll (.fAll
    (.fImp (fIsFormCodeF 4)
      (.fImp (fVarMapF 3)
        (.fImp (fRenamesF 3 4 2)
          (.fImp (fUnivEnvF 1)
            (.fImp (fCompF 0 1 3)
              (.fAnd
                (fIff (sigmaAtF n 2 1) (sigmaAtF n 4 0))
                (fIff (piFalseAtF n 2 1) (piFalseAtF n 4 0))))))))))))

/-- **Field 5, `axiomSound`: axiom-code truth at level `n+1`, bound `n`.**

For every internal ZFC axiom code `c` (slot `1`) whose quantifier
complexity is bounded by the numeral of `n`, and every universe
environment `E` (slot `0`), the code is true at level `n+1` on both
polarities.  The internal quantifier over codes covers the nonstandard
Separation and Replacement instances.  Goal-2 counterpart:
`axiomCodesTrueAt`. -/
def axiomSoundF (n : ℕ) : SetTheory.Form :=
  .fAll (.fAll (.fImp (fZFCAxiomCodeF 1) (.fImp (fUnivEnvF 0)
    (.fImp (boundedAtF n 1)
      (.fAnd (sigmaAtF n 1 0) (piTrueAtF n 1 0))))))

end FormLevel

/-! ## Free-slot bounds

Depth moves under quotation and the closedness of the five sentences both
reduce to per-leaf free-slot bounds: kernel-evaluated `freeMax` bounds for
the fixed macro leaves, structural walks for the level towers and the
gadgets. -/

section FreeBounds

open SetTheory (Form Free fIff)

/-! ### Kernel bounds for the fixed macro leaves -/

set_option maxHeartbeats 1000000 in
private theorem fb01 : freeMax (fUnivEnvF 0) ≤ 1 := by decide
set_option maxHeartbeats 1000000 in
private theorem fb02 : freeMax (fUnivEnvF 1) ≤ 2 := by decide
set_option maxHeartbeats 1000000 in
private theorem fb03 : freeMax (fTaggedEmptyF 1 2) ≤ 2 := by decide
set_option maxHeartbeats 1000000 in
private theorem fb04 : freeMax (fIsFormCodeF 1) ≤ 2 := by decide
set_option maxHeartbeats 1000000 in
private theorem fb05 : freeMax (fIsFormCodeF 3) ≤ 4 := by decide
set_option maxHeartbeats 1000000 in
private theorem fb06 : freeMax (fIsFormCodeF 4) ≤ 5 := by decide
set_option maxHeartbeats 1000000 in
private theorem fb07 : freeMax (fQuantBoundedF 0 2) ≤ 3 := by decide
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem fb08 : freeMax (fZFCAxiomCodeF 1) ≤ 2 := by decide
set_option maxHeartbeats 1000000 in
private theorem fb09 : freeMax (fSuccMapF 0) ≤ 1 := by decide
set_option maxHeartbeats 1000000 in
private theorem fb10 : freeMax (fRenamesF 0 4 3) ≤ 5 := by decide
set_option maxHeartbeats 1000000 in
private theorem fb11 : freeMax (fEconsF 0 1 2) ≤ 3 := by decide
set_option maxHeartbeats 1000000 in
private theorem fb12 : freeMax (fVarMapF 3) ≤ 4 := by decide
set_option maxHeartbeats 1000000 in
private theorem fb13 : freeMax (fRenamesF 3 4 2) ≤ 5 := by decide
set_option maxHeartbeats 1000000 in
private theorem fb14 : freeMax (fCompF 0 1 3) ≤ 4 := by decide
set_option maxHeartbeats 1000000 in
private theorem fb15 : freeMax (fTripleMemF 4 3 2 1) ≤ 5 := by decide
set_option maxHeartbeats 2000000 in
private theorem fb16 : freeMax (levelSatF 0 2 1 0) ≤ 3 := by decide

/-! ### Structural bounds for the level towers -/

/-- The canonical tower instance has free slots below `3`, at every level.
The base is the kernel bound above; the successor walks the unfolded
instance shape with `free_fNumF`, `free_closF`, and the membership-atom
bound. -/
theorem free_levelSatF_canonical :
    ∀ (n : ℕ) {i : ℕ}, Free i (levelSatF n 2 1 0) → i < 3 := by
  intro n
  cases n with
  | zero =>
      intro i h
      have h1 := free_lt_freeMax (levelSatF 0 2 1 0) i h
      have h2 := fb16
      omega
  | succ n =>
      intro i h
      rw [levelSatF_succ_canonical] at h
      simp only [lvlInstF, SetTheory.Free] at h
      rcases h with h | h | h
      · have := free_fNumF h
        omega
      · have := free_closF n h
        omega
      · have h2 := free_lt_freeMax _ _ h
        have h3 := fb15
        omega

/-- The canonical Sigma-truth wrapper has free slots below `2`. -/
theorem free_fSigmaTrueF_canonical {n i : ℕ}
    (h : Free i (fSigmaTrueF n 1 0)) : i < 2 := by
  simp only [BoundedZFCConsistency.fSigmaTrueF, SetTheory.Free] at h
  rcases h with h | h
  · have := free_fNumF h
    omega
  · have := free_levelSatF_canonical n h
    omega

/-- The canonical Pi-falsity wrapper has free slots below `2`. -/
theorem free_fPiFalseF_canonical {n i : ℕ}
    (h : Free i (fPiFalseF n 1 0)) : i < 2 := by
  simp only [BoundedZFCConsistency.fPiFalseF, SetTheory.Free] at h
  rcases h with h | h
  · have := free_fNumF h
    omega
  · have := free_levelSatF_canonical n h
    omega

/-- The canonical Pi-truth wrapper has free slots below `2`. -/
theorem free_fPiTrueF_canonical {n i : ℕ}
    (h : Free i (fPiTrueF n 1 0)) : i < 2 := by
  simp only [BoundedZFCConsistency.fPiTrueF, SetTheory.Free] at h
  rcases h with h | h
  · exact free_fPiFalseF_canonical h
  · cases h

/-! ### Bounds for the assembled gadgets -/

/-- The gadget's free slots are among the redirected pair, provided the
payload keeps to the canonical slots. -/
theorem free_canonAtF {ci ei i : ℕ} {φ : SetTheory.Form}
    (hφ : ∀ j, Free j φ → j < 2)
    (h : Free i (canonAtF ci ei φ)) : i = ci ∨ i = ei := by
  simp only [canonAtF, SetTheory.Free] at h
  rcases h with (h | h) | (h | h) | h
  · omega
  · exact Or.inl (by omega)
  · omega
  · exact Or.inr (by omega)
  · have := hφ _ h
    omega

/-- Free slots of the Sigma gadget. -/
theorem free_sigmaAtF {n ci ei i : ℕ} (h : Free i (sigmaAtF n ci ei)) :
    i = ci ∨ i = ei :=
  free_canonAtF (fun _ hj => free_fSigmaTrueF_canonical hj) h

/-- Free slots of the Pi-falsity gadget. -/
theorem free_piFalseAtF {n ci ei i : ℕ} (h : Free i (piFalseAtF n ci ei)) :
    i = ci ∨ i = ei :=
  free_canonAtF (fun _ hj => free_fPiFalseF_canonical hj) h

/-- Free slots of the Pi-truth gadget. -/
theorem free_piTrueAtF {n ci ei i : ℕ} (h : Free i (piTrueAtF n ci ei)) :
    i = ci ∨ i = ei :=
  free_canonAtF (fun _ hj => free_fPiTrueF_canonical hj) h

/-- Free slots of the boundedness gadget, at the only slot the fields
use.  (The kernel bound `fb07` is specific to `fQuantBoundedF 0 2`, so the
statement is deliberately not generalized over the slot.) -/
theorem free_boundedAt1F {n i : ℕ} (h : Free i (boundedAtF n 1)) :
    i < 2 := by
  simp only [boundedAtF, SetTheory.Free] at h
  rcases h with h | h
  · have := free_fNumF h
    omega
  · have h2 := free_lt_freeMax _ _ h
    have h3 : freeMax (fQuantBoundedF 0 (1 + 1)) ≤ 3 := fb07
    omega

/-- The free slots of an equality atom are its two arguments.  (This is
definitional; the named form keeps the depth-move side conditions
readable.) -/
theorem free_fEq {i j m : ℕ} (h : Free m (SetTheory.Form.fEq i j)) :
    m = i ∨ m = j := h

/-! ### Closedness of the five field sentences

Every field is a sentence: all leaves keep to slots the quantifier prefix
binds.  Each proof walks the disjunction `Free` assigns to the spine; the
fixed leaves are the kernel bounds above, the gadgets are the structural
bounds, and every case is a small linear problem. -/

/-- `localStepF n` is closed. -/
theorem not_free_localStepF (n : ℕ) : ∀ i, ¬ Free i (localStepF n) := by
  intro i h
  simp only [localStepF, SetTheory.Free] at h
  casesm* _ ∨ _
  all_goals
    first
    | exact ‹False›
    | (have h2 := free_lt_freeMax _ _ ‹_›
       first
       | (have h3 := fb01; omega)
       | (have h3 := fb03; omega)
       | (have h3 := fb04; omega))
    | (rcases free_sigmaAtF ‹_› with h2 | h2 <;> omega)
    | (rcases free_piTrueAtF ‹_› with h2 | h2 <;> omega)

/-- `crossLevelF n` is closed. -/
theorem not_free_crossLevelF (n : ℕ) : ∀ i, ¬ Free i (crossLevelF n) := by
  intro i h
  simp only [crossLevelF, SetTheory.Free] at h
  casesm* _ ∨ _
  all_goals
    first
    | (have h2 := free_boundedAt1F ‹_›; omega)
    | (have h2 := free_lt_freeMax _ _ ‹_›
       first
       | (have h3 := fb01; omega)
       | (have h3 := fb04; omega))
    | (rcases free_sigmaAtF ‹_› with h2 | h2 <;> omega)
    | (rcases free_piFalseAtF ‹_› with h2 | h2 <;> omega)

/-- `shiftInvariantF n` is closed. -/
theorem not_free_shiftInvariantF (n : ℕ) :
    ∀ i, ¬ Free i (shiftInvariantF n) := by
  intro i h
  simp only [shiftInvariantF, SetTheory.fIff, SetTheory.Free] at h
  casesm* _ ∨ _
  all_goals
    first
    | (have h2 := free_lt_freeMax _ _ ‹_›
       first
       | (have h3 := fb02; omega)
       | (have h3 := fb05; omega)
       | (have h3 := fb09; omega)
       | (have h3 := fb10; omega)
       | (have h3 := fb11; omega))
    | (rcases free_sigmaAtF ‹_› with h2 | h2 <;> omega)
    | (rcases free_piFalseAtF ‹_› with h2 | h2 <;> omega)

/-- `substitutionInvariantF n` is closed. -/
theorem not_free_substitutionInvariantF (n : ℕ) :
    ∀ i, ¬ Free i (substitutionInvariantF n) := by
  intro i h
  simp only [substitutionInvariantF, SetTheory.fIff, SetTheory.Free] at h
  casesm* _ ∨ _
  all_goals
    first
    | (have h2 := free_lt_freeMax _ _ ‹_›
       first
       | (have h3 := fb02; omega)
       | (have h3 := fb06; omega)
       | (have h3 := fb12; omega)
       | (have h3 := fb13; omega)
       | (have h3 := fb14; omega))
    | (rcases free_sigmaAtF ‹_› with h2 | h2 <;> omega)
    | (rcases free_piFalseAtF ‹_› with h2 | h2 <;> omega)

/-- `axiomSoundF n` is closed. -/
theorem not_free_axiomSoundF (n : ℕ) : ∀ i, ¬ Free i (axiomSoundF n) := by
  intro i h
  simp only [axiomSoundF, SetTheory.Free] at h
  casesm* _ ∨ _
  all_goals
    first
    | (have h2 := free_boundedAt1F ‹_›; omega)
    | (have h2 := free_lt_freeMax _ _ ‹_›
       first
       | (have h3 := fb01; omega)
       | (have h3 := fb08; omega))
    | (rcases free_sigmaAtF ‹_› with h2 | h2 <;> omega)
    | (rcases free_piTrueAtF ‹_› with h2 | h2 <;> omega)

end FreeBounds

/-! ## The fixed codes

The `x`-independent leaves of the five spines, as standard natural-number
codes at the exact translation depths where they occur.  Codes are names,
never numbers: nothing below evaluates one. -/

section FixedCodes

/-- Code of an equality guard.  The depth is the smallest that binds both
slots; every occurrence at a deeper ambient depth is reached by a depth
move (`quote_fEq_move`). -/
def eqGuardCode (i j : ℕ) : ℕ :=
  (toSet (max i j + 1) (SetTheory.Form.fEq i j)).toNat

/-- Code of `fUnivEnvF 0` at depth `2`. -/
def univEnv0D2Code : ℕ := (toSet 2 (fUnivEnvF 0)).toNat

/-- Code of `fUnivEnvF 1` at depth `4`. -/
def univEnv1D4Code : ℕ := (toSet 4 (fUnivEnvF 1)).toNat

/-- Code of `fUnivEnvF 1` at depth `5`. -/
def univEnv1D5Code : ℕ := (toSet 5 (fUnivEnvF 1)).toNat

/-- Code of the falsity-code guard `fTaggedEmptyF 1 2` at depth `2`. -/
def taggedEmptyD2Code : ℕ := (toSet 2 (fTaggedEmptyF 1 2)).toNat

/-- Code of `fIsFormCodeF 1` at depth `2`. -/
def isFormCode1D2Code : ℕ := (toSet 2 (fIsFormCodeF 1)).toNat

/-- Code of `fIsFormCodeF 3` at depth `4`. -/
def isFormCode3D4Code : ℕ := (toSet 4 (fIsFormCodeF 3)).toNat

/-- Code of `fIsFormCodeF 4` at depth `5`. -/
def isFormCode4D5Code : ℕ := (toSet 5 (fIsFormCodeF 4)).toNat

/-- Code of `fZFCAxiomCodeF 1` at depth `2`. -/
def zfcAxiomCodeD2Code : ℕ := (toSet 2 (fZFCAxiomCodeF 1)).toNat

/-- Code of `fQuantBoundedF 0 2` at depth `3`. -/
def quantBoundedD3Code : ℕ := (toSet 3 (fQuantBoundedF 0 2)).toNat

/-- Code of `fSuccMapF 0` at depth `5`. -/
def succMapD5Code : ℕ := (toSet 5 (fSuccMapF 0)).toNat

/-- Code of the shift-instance renaming atom `fRenamesF 0 4 3` at depth
`5`. -/
def renamesShiftD5Code : ℕ := (toSet 5 (fRenamesF 0 4 3)).toNat

/-- Code of the environment-extension guard `fEconsF 0 1 2` at depth `5`. -/
def econsD5Code : ℕ := (toSet 5 (fEconsF 0 1 2)).toNat

/-- Code of `fVarMapF 3` at depth `5`. -/
def varMap3D5Code : ℕ := (toSet 5 (fVarMapF 3)).toNat

/-- Code of the general renaming atom `fRenamesF 3 4 2` at depth `5`. -/
def renamesSubstD5Code : ℕ := (toSet 5 (fRenamesF 3 4 2)).toNat

/-- Code of the composition guard `fCompF 0 1 3` at depth `5`. -/
def compD5Code : ℕ := (toSet 5 (fCompF 0 1 3)).toNat

end FixedCodes

/-! ## The internal builders

Fixed constructor spines over the level towers, in the
`LevelCodeTower` pattern: every `Defined` evaluation proof is stated with
the fixed leaf codes as variables (the parameter firewall), and the
concrete constants enter only by instantiating the proved instance. -/

section InternalBuilder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The coded canonical-slot gadget: two coded universal quantifiers over
the two equality guards and the payload. -/
noncomputable def canonAtPart (e1 e0 : ℕ) (inner : V) : V :=
  ^∀ (^∀ (Bootstrapping.imp ℒₛₑₜ ↑e1 (Bootstrapping.imp ℒₛₑₜ ↑e0 inner)))

/-- Graph of `canonAtPart e1 e0`, argument order `(value, payload)`. -/
noncomputable def canonAtGraph (e1 e0 : ℕ) : 𝚺₁.Semisentence 2 := .mkSigma
  “y inner.
    ∃ b, !(Bootstrapping.impGraph ℒₛₑₜ) b ↑e0 inner ∧
    ∃ a, !(Bootstrapping.impGraph ℒₛₑₜ) a ↑e1 b ∧
    ∃ u, !qqAllDef u a ∧ !qqAllDef y u”

instance canonAtPart.defined (e1 e0 : ℕ) :
    𝚺₁-Function₁ (canonAtPart e1 e0 : V → V) via canonAtGraph e1 e0 :=
  .mk fun v ↦ by simp [canonAtGraph, canonAtPart, numeral_eq_natCast]

/-- The coded Sigma-truth gadget at pair `(ci, ei)`: the payload is the
canonical Sigma tower at the *successor* of the index. -/
noncomputable def sigmaAtCode (ci ei : ℕ) (x : V) : V :=
  canonAtPart (eqGuardCode 1 (ci + 2)) (eqGuardCode 0 (ei + 2))
    (sigmaTrueCode (x + 1))

/-- Graph of `sigmaAtCode ci ei`, argument order `(value, index)`. -/
noncomputable def sigmaAtGraph (ci ei : ℕ) : 𝚺₁.Semisentence 2 := .mkSigma
  “y x. ∃ s, !sigmaTrueGraph s (x + 1) ∧
    !(canonAtGraph (eqGuardCode 1 (ci + 2)) (eqGuardCode 0 (ei + 2))) y s”

instance sigmaAtCode.defined (ci ei : ℕ) :
    𝚺₁-Function₁ (sigmaAtCode ci ei : V → V) via sigmaAtGraph ci ei :=
  .mk fun v ↦ by simp [sigmaAtGraph, sigmaAtCode]

/-- The coded Pi-falsity gadget at pair `(ci, ei)`. -/
noncomputable def piFalseAtCode (ci ei : ℕ) (x : V) : V :=
  canonAtPart (eqGuardCode 1 (ci + 2)) (eqGuardCode 0 (ei + 2))
    (piFalseCode (x + 1))

/-- Graph of `piFalseAtCode ci ei`. -/
noncomputable def piFalseAtGraph (ci ei : ℕ) : 𝚺₁.Semisentence 2 := .mkSigma
  “y x. ∃ s, !piFalseGraph s (x + 1) ∧
    !(canonAtGraph (eqGuardCode 1 (ci + 2)) (eqGuardCode 0 (ei + 2))) y s”

instance piFalseAtCode.defined (ci ei : ℕ) :
    𝚺₁-Function₁ (piFalseAtCode ci ei : V → V) via piFalseAtGraph ci ei :=
  .mk fun v ↦ by simp [piFalseAtGraph, piFalseAtCode]

/-- The coded Pi-truth gadget at pair `(ci, ei)`. -/
noncomputable def piTrueAtCode (ci ei : ℕ) (x : V) : V :=
  canonAtPart (eqGuardCode 1 (ci + 2)) (eqGuardCode 0 (ei + 2))
    (piTrueCode (x + 1))

/-- Graph of `piTrueAtCode ci ei`. -/
noncomputable def piTrueAtGraph (ci ei : ℕ) : 𝚺₁.Semisentence 2 := .mkSigma
  “y x. ∃ s, !piTrueGraph s (x + 1) ∧
    !(canonAtGraph (eqGuardCode 1 (ci + 2)) (eqGuardCode 0 (ei + 2))) y s”

instance piTrueAtCode.defined (ci ei : ℕ) :
    𝚺₁-Function₁ (piTrueAtCode ci ei : V → V) via piTrueAtGraph ci ei :=
  .mk fun v ↦ by simp [piTrueAtGraph, piTrueAtCode]

/-- The coded boundedness gadget: one coded existential over the numeral
chain and the fixed quantifier-bound leaf. -/
noncomputable def boundedAtPart (qb : ℕ) (x : V) : V :=
  ^∃ (numChainCode x ^⋏ ↑qb)

/-- Graph of `boundedAtPart qb`. -/
noncomputable def boundedAtGraph (qb : ℕ) : 𝚺₁.Semisentence 2 := .mkSigma
  “y x. ∃ g, !numChainGraph g x ∧ ∃ a, !qqAndDef a g ↑qb ∧ !qqExsDef y a”

instance boundedAtPart.defined (qb : ℕ) :
    𝚺₁-Function₁ (boundedAtPart qb : V → V) via boundedAtGraph qb :=
  .mk fun v ↦ by simp [boundedAtGraph, boundedAtPart, numeral_eq_natCast]

/-! ### Field 1: the local polarity laws -/

/-- The coded local-step field, with the fixed leaf codes abstracted. -/
noncomputable def localStepPart (ue te ifc bot : ℕ) (x : V) : V :=
  ^∀ (^∀ (Bootstrapping.imp ℒₛₑₜ ↑ue
    ((Bootstrapping.imp ℒₛₑₜ ↑te
        (Bootstrapping.imp ℒₛₑₜ (sigmaAtCode 1 0 x) ↑bot)) ^⋏
     (Bootstrapping.imp ℒₛₑₜ ↑ifc
        (Bootstrapping.imp ℒₛₑₜ (sigmaAtCode 1 0 x) (piTrueAtCode 1 0 x))))))

/-- Graph of `localStepPart`. -/
noncomputable def localStepGraphPart (ue te ifc bot : ℕ) :
    𝚺₁.Semisentence 2 := .mkSigma
  “y x.
    ∃ s, !(sigmaAtGraph 1 0) s x ∧
    ∃ pt, !(piTrueAtGraph 1 0) pt x ∧
    ∃ i1, !(Bootstrapping.impGraph ℒₛₑₜ) i1 s ↑bot ∧
    ∃ i2, !(Bootstrapping.impGraph ℒₛₑₜ) i2 ↑te i1 ∧
    ∃ i3, !(Bootstrapping.impGraph ℒₛₑₜ) i3 s pt ∧
    ∃ i4, !(Bootstrapping.impGraph ℒₛₑₜ) i4 ↑ifc i3 ∧
    ∃ a, !qqAndDef a i2 i4 ∧
    ∃ i5, !(Bootstrapping.impGraph ℒₛₑₜ) i5 ↑ue a ∧
    ∃ u, !qqAllDef u i5 ∧ !qqAllDef y u”

instance localStepPart.defined (ue te ifc bot : ℕ) :
    𝚺₁-Function₁ (localStepPart ue te ifc bot : V → V)
      via localStepGraphPart ue te ifc bot :=
  .mk fun v ↦ by simp [localStepGraphPart, localStepPart, numeral_eq_natCast]

/-- The coded local-step field at the concrete leaf codes. -/
noncomputable def localStepCode : V → V :=
  localStepPart univEnv0D2Code taggedEmptyD2Code isFormCode1D2Code
    botCanonCode

/-- Graph of `localStepCode`. -/
noncomputable def localStepGraph : 𝚺₁.Semisentence 2 :=
  localStepGraphPart univEnv0D2Code taggedEmptyD2Code isFormCode1D2Code
    botCanonCode

instance localStepCode.defined :
    𝚺₁-Function₁ (localStepCode : V → V) via localStepGraph :=
  localStepPart.defined univEnv0D2Code taggedEmptyD2Code isFormCode1D2Code
    botCanonCode

/-! ### Field 2: decidedness of bounded codes -/

/-- The coded cross-level field, with the fixed leaf codes abstracted. -/
noncomputable def crossLevelPart (ifc ue qb : ℕ) (x : V) : V :=
  ^∀ (^∀ (Bootstrapping.imp ℒₛₑₜ ↑ifc
    (Bootstrapping.imp ℒₛₑₜ ↑ue
      (Bootstrapping.imp ℒₛₑₜ (boundedAtPart qb x)
        (sigmaAtCode 1 0 x ^⋎ piFalseAtCode 1 0 x)))))

/-- Graph of `crossLevelPart`. -/
noncomputable def crossLevelGraphPart (ifc ue qb : ℕ) :
    𝚺₁.Semisentence 2 := .mkSigma
  “y x.
    ∃ s, !(sigmaAtGraph 1 0) s x ∧
    ∃ pf, !(piFalseAtGraph 1 0) pf x ∧
    ∃ b, !(boundedAtGraph qb) b x ∧
    ∃ o, !qqOrDef o s pf ∧
    ∃ i1, !(Bootstrapping.impGraph ℒₛₑₜ) i1 b o ∧
    ∃ i2, !(Bootstrapping.impGraph ℒₛₑₜ) i2 ↑ue i1 ∧
    ∃ i3, !(Bootstrapping.impGraph ℒₛₑₜ) i3 ↑ifc i2 ∧
    ∃ u, !qqAllDef u i3 ∧ !qqAllDef y u”

instance crossLevelPart.defined (ifc ue qb : ℕ) :
    𝚺₁-Function₁ (crossLevelPart ifc ue qb : V → V)
      via crossLevelGraphPart ifc ue qb :=
  .mk fun v ↦ by simp [crossLevelGraphPart, crossLevelPart, numeral_eq_natCast]

/-- The coded cross-level field at the concrete leaf codes. -/
noncomputable def crossLevelCode : V → V :=
  crossLevelPart isFormCode1D2Code univEnv0D2Code quantBoundedD3Code

/-- Graph of `crossLevelCode`. -/
noncomputable def crossLevelGraph : 𝚺₁.Semisentence 2 :=
  crossLevelGraphPart isFormCode1D2Code univEnv0D2Code quantBoundedD3Code

instance crossLevelCode.defined :
    𝚺₁-Function₁ (crossLevelCode : V → V) via crossLevelGraph :=
  crossLevelPart.defined isFormCode1D2Code univEnv0D2Code quantBoundedD3Code

/-! ### Field 3: the successor-shift substitution instance -/

/-- The coded shift-invariance field, with the fixed leaf codes
abstracted. -/
noncomputable def shiftInvariantPart (ifc sm rn ue ec : ℕ) (x : V) : V :=
  ^∀ (^∀ (^∀ (^∀ (Bootstrapping.imp ℒₛₑₜ ↑ifc
    (Bootstrapping.imp ℒₛₑₜ (^∃ (↑sm ^⋏ ↑rn))
      (Bootstrapping.imp ℒₛₑₜ ↑ue
        (^∀ (Bootstrapping.imp ℒₛₑₜ ↑ec
          ((Bootstrapping.iff ℒₛₑₜ (sigmaAtCode 3 0 x) (sigmaAtCode 4 2 x)) ^⋏
           (Bootstrapping.iff ℒₛₑₜ (piFalseAtCode 3 0 x)
             (piFalseAtCode 4 2 x)))))))))))

/-- Graph of `shiftInvariantPart`. -/
noncomputable def shiftInvariantGraphPart (ifc sm rn ue ec : ℕ) :
    𝚺₁.Semisentence 2 := .mkSigma
  “y x.
    ∃ s30, !(sigmaAtGraph 3 0) s30 x ∧
    ∃ s42, !(sigmaAtGraph 4 2) s42 x ∧
    ∃ p30, !(piFalseAtGraph 3 0) p30 x ∧
    ∃ p42, !(piFalseAtGraph 4 2) p42 x ∧
    ∃ e1, !(Bootstrapping.iffGraph ℒₛₑₜ) e1 s30 s42 ∧
    ∃ e2, !(Bootstrapping.iffGraph ℒₛₑₜ) e2 p30 p42 ∧
    ∃ a1, !qqAndDef a1 e1 e2 ∧
    ∃ i1, !(Bootstrapping.impGraph ℒₛₑₜ) i1 ↑ec a1 ∧
    ∃ u1, !qqAllDef u1 i1 ∧
    ∃ i2, !(Bootstrapping.impGraph ℒₛₑₜ) i2 ↑ue u1 ∧
    ∃ a2, !qqAndDef a2 ↑sm ↑rn ∧
    ∃ x1, !qqExsDef x1 a2 ∧
    ∃ i3, !(Bootstrapping.impGraph ℒₛₑₜ) i3 x1 i2 ∧
    ∃ i4, !(Bootstrapping.impGraph ℒₛₑₜ) i4 ↑ifc i3 ∧
    ∃ u2, !qqAllDef u2 i4 ∧
    ∃ u3, !qqAllDef u3 u2 ∧
    ∃ u4, !qqAllDef u4 u3 ∧
    !qqAllDef y u4”

instance shiftInvariantPart.defined (ifc sm rn ue ec : ℕ) :
    𝚺₁-Function₁ (shiftInvariantPart ifc sm rn ue ec : V → V)
      via shiftInvariantGraphPart ifc sm rn ue ec :=
  .mk fun v ↦ by
    simp [shiftInvariantGraphPart, shiftInvariantPart, numeral_eq_natCast]

/-- The coded shift-invariance field at the concrete leaf codes. -/
noncomputable def shiftInvariantCode : V → V :=
  shiftInvariantPart isFormCode3D4Code succMapD5Code renamesShiftD5Code
    univEnv1D4Code econsD5Code

/-- Graph of `shiftInvariantCode`. -/
noncomputable def shiftInvariantGraph : 𝚺₁.Semisentence 2 :=
  shiftInvariantGraphPart isFormCode3D4Code succMapD5Code renamesShiftD5Code
    univEnv1D4Code econsD5Code

instance shiftInvariantCode.defined :
    𝚺₁-Function₁ (shiftInvariantCode : V → V) via shiftInvariantGraph :=
  shiftInvariantPart.defined isFormCode3D4Code succMapD5Code
    renamesShiftD5Code univEnv1D4Code econsD5Code

/-! ### Field 4: the general substitution lemma -/

/-- The coded substitution-invariance field, with the fixed leaf codes
abstracted. -/
noncomputable def substitutionInvariantPart (ifc vm rn ue cp : ℕ)
    (x : V) : V :=
  ^∀ (^∀ (^∀ (^∀ (^∀ (Bootstrapping.imp ℒₛₑₜ ↑ifc
    (Bootstrapping.imp ℒₛₑₜ ↑vm
      (Bootstrapping.imp ℒₛₑₜ ↑rn
        (Bootstrapping.imp ℒₛₑₜ ↑ue
          (Bootstrapping.imp ℒₛₑₜ ↑cp
            ((Bootstrapping.iff ℒₛₑₜ (sigmaAtCode 2 1 x)
                (sigmaAtCode 4 0 x)) ^⋏
             (Bootstrapping.iff ℒₛₑₜ (piFalseAtCode 2 1 x)
               (piFalseAtCode 4 0 x))))))))))))

/-- Graph of `substitutionInvariantPart`. -/
noncomputable def substitutionInvariantGraphPart (ifc vm rn ue cp : ℕ) :
    𝚺₁.Semisentence 2 := .mkSigma
  “y x.
    ∃ s21, !(sigmaAtGraph 2 1) s21 x ∧
    ∃ s40, !(sigmaAtGraph 4 0) s40 x ∧
    ∃ p21, !(piFalseAtGraph 2 1) p21 x ∧
    ∃ p40, !(piFalseAtGraph 4 0) p40 x ∧
    ∃ e1, !(Bootstrapping.iffGraph ℒₛₑₜ) e1 s21 s40 ∧
    ∃ e2, !(Bootstrapping.iffGraph ℒₛₑₜ) e2 p21 p40 ∧
    ∃ a1, !qqAndDef a1 e1 e2 ∧
    ∃ i1, !(Bootstrapping.impGraph ℒₛₑₜ) i1 ↑cp a1 ∧
    ∃ i2, !(Bootstrapping.impGraph ℒₛₑₜ) i2 ↑ue i1 ∧
    ∃ i3, !(Bootstrapping.impGraph ℒₛₑₜ) i3 ↑rn i2 ∧
    ∃ i4, !(Bootstrapping.impGraph ℒₛₑₜ) i4 ↑vm i3 ∧
    ∃ i5, !(Bootstrapping.impGraph ℒₛₑₜ) i5 ↑ifc i4 ∧
    ∃ u1, !qqAllDef u1 i5 ∧
    ∃ u2, !qqAllDef u2 u1 ∧
    ∃ u3, !qqAllDef u3 u2 ∧
    ∃ u4, !qqAllDef u4 u3 ∧
    !qqAllDef y u4”

instance substitutionInvariantPart.defined (ifc vm rn ue cp : ℕ) :
    𝚺₁-Function₁ (substitutionInvariantPart ifc vm rn ue cp : V → V)
      via substitutionInvariantGraphPart ifc vm rn ue cp :=
  .mk fun v ↦ by
    simp [substitutionInvariantGraphPart, substitutionInvariantPart,
      numeral_eq_natCast]

/-- The coded substitution-invariance field at the concrete leaf codes. -/
noncomputable def substitutionInvariantCode : V → V :=
  substitutionInvariantPart isFormCode4D5Code varMap3D5Code
    renamesSubstD5Code univEnv1D5Code compD5Code

/-- Graph of `substitutionInvariantCode`. -/
noncomputable def substitutionInvariantGraph : 𝚺₁.Semisentence 2 :=
  substitutionInvariantGraphPart isFormCode4D5Code varMap3D5Code
    renamesSubstD5Code univEnv1D5Code compD5Code

instance substitutionInvariantCode.defined :
    𝚺₁-Function₁ (substitutionInvariantCode : V → V)
      via substitutionInvariantGraph :=
  substitutionInvariantPart.defined isFormCode4D5Code varMap3D5Code
    renamesSubstD5Code univEnv1D5Code compD5Code

/-! ### Field 5: axiom-code truth -/

/-- The coded axiom-soundness field, with the fixed leaf codes
abstracted. -/
noncomputable def axiomSoundPart (ax ue qb : ℕ) (x : V) : V :=
  ^∀ (^∀ (Bootstrapping.imp ℒₛₑₜ ↑ax
    (Bootstrapping.imp ℒₛₑₜ ↑ue
      (Bootstrapping.imp ℒₛₑₜ (boundedAtPart qb x)
        (sigmaAtCode 1 0 x ^⋏ piTrueAtCode 1 0 x)))))

/-- Graph of `axiomSoundPart`. -/
noncomputable def axiomSoundGraphPart (ax ue qb : ℕ) :
    𝚺₁.Semisentence 2 := .mkSigma
  “y x.
    ∃ s, !(sigmaAtGraph 1 0) s x ∧
    ∃ pt, !(piTrueAtGraph 1 0) pt x ∧
    ∃ b, !(boundedAtGraph qb) b x ∧
    ∃ a, !qqAndDef a s pt ∧
    ∃ i1, !(Bootstrapping.impGraph ℒₛₑₜ) i1 b a ∧
    ∃ i2, !(Bootstrapping.impGraph ℒₛₑₜ) i2 ↑ue i1 ∧
    ∃ i3, !(Bootstrapping.impGraph ℒₛₑₜ) i3 ↑ax i2 ∧
    ∃ u, !qqAllDef u i3 ∧ !qqAllDef y u”

instance axiomSoundPart.defined (ax ue qb : ℕ) :
    𝚺₁-Function₁ (axiomSoundPart ax ue qb : V → V)
      via axiomSoundGraphPart ax ue qb :=
  .mk fun v ↦ by simp [axiomSoundGraphPart, axiomSoundPart, numeral_eq_natCast]

/-- The coded axiom-soundness field at the concrete leaf codes. -/
noncomputable def axiomSoundCode : V → V :=
  axiomSoundPart zfcAxiomCodeD2Code univEnv0D2Code quantBoundedD3Code

/-- Graph of `axiomSoundCode`. -/
noncomputable def axiomSoundGraph : 𝚺₁.Semisentence 2 :=
  axiomSoundGraphPart zfcAxiomCodeD2Code univEnv0D2Code quantBoundedD3Code

instance axiomSoundCode.defined :
    𝚺₁-Function₁ (axiomSoundCode : V → V) via axiomSoundGraph :=
  axiomSoundPart.defined zfcAxiomCodeD2Code univEnv0D2Code quantBoundedD3Code

end InternalBuilder

/-! ## Standard points

At a standard index `↑n` each builder computes exactly the quotation of
the corresponding field sentence at translation depth `0`.  All proofs are
`rw`-chains through generic quote-computation helpers with explicit result
depths — never `simp` over a spine containing a leaf that must stay
opaque — with the fixed leaves matched against their named codes by
`coe_toNat_eq_quote` alone. -/

section StandardPoints

open SetTheory (Form Free fIff)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Quotation computes through a translated universal quantifier.  The
result depth is explicit so that `rw`-chains keep literal depths. -/
theorem quote_toSet_fAll' {k d : ℕ} (h : k + 1 = d) (a : Form) :
    (⌜toSet k (.fAll a)⌝ : V) = ^∀ (⌜toSet d a⌝ : V) := by
  subst h
  simp [toSet]

/-- Quotation computes through a translated existential quantifier. -/
theorem quote_toSet_fEx' {k d : ℕ} (h : k + 1 = d) (a : Form) :
    (⌜toSet k (.fEx a)⌝ : V) = ^∃ (⌜toSet d a⌝ : V) := by
  subst h
  simp [toSet]

/-- Quotation computes through a translated conjunction. -/
theorem quote_toSet_fAnd (k : ℕ) (a b : Form) :
    (⌜toSet k (.fAnd a b)⌝ : V) = (⌜toSet k a⌝ : V) ^⋏ (⌜toSet k b⌝ : V) := by
  simp [toSet]

/-- Quotation computes through a translated disjunction. -/
theorem quote_toSet_fOr (k : ℕ) (a b : Form) :
    (⌜toSet k (.fOr a b)⌝ : V) = (⌜toSet k a⌝ : V) ^⋎ (⌜toSet k b⌝ : V) := by
  simp [toSet]

/-- Quotation renders `fIff` as the coded biconditional: both are the
conjunction of the two coded implications. -/
theorem quote_toSet_fIff (k : ℕ) (a b : Form) :
    (⌜toSet k (fIff a b)⌝ : V) =
      Bootstrapping.iff ℒₛₑₜ (⌜toSet k a⌝ : V) (⌜toSet k b⌝ : V) := by
  rw [show fIff a b = Form.fAnd (.fImp a b) (.fImp b a) from rfl,
    quote_toSet_fAnd, quote_toSet_fImp, quote_toSet_fImp]
  rfl

/-- An equality guard's quote at any binding depth is its named code. -/
theorem quote_fEq_move {i j k : ℕ} (hi : i < k) (hj : j < k) :
    (⌜toSet k (Form.fEq i j)⌝ : V) = ↑(eqGuardCode i j) := by
  have h : (⌜toSet k (Form.fEq i j)⌝ : V) =
      ⌜toSet (max i j + 1) (Form.fEq i j)⌝ :=
    quote_toSet_congr
      (fun m hm => by rcases free_fEq hm with rfl | rfl <;> omega)
      (fun m hm => by rcases free_fEq hm with rfl | rfl <;> omega)
  rw [h, ← coe_toNat_eq_quote (V := V) (toSet (max i j + 1) (Form.fEq i j))]
  rfl

/-- **Quotation of the canonical-slot gadget**: the coded gadget on the two
equality-guard codes and the payload's canonical-depth quote. -/
theorem quote_canonAtF {k : ℕ} (ci ei : ℕ) (hci : ci < k) (hei : ei < k)
    (φ : Form) (hφ : ∀ j, Free j φ → j < 2) :
    (⌜toSet k (canonAtF ci ei φ)⌝ : V) =
      canonAtPart (eqGuardCode 1 (ci + 2)) (eqGuardCode 0 (ei + 2))
        (⌜toSet 2 φ⌝ : V) := by
  have hφmove : (⌜toSet (k + 2) φ⌝ : V) = ⌜toSet 2 φ⌝ :=
    quote_toSet_congr (fun j hj => by have := hφ j hj; omega) hφ
  rw [show canonAtF ci ei φ =
        Form.fAll (.fAll (.fImp (.fEq 1 (ci + 2))
          (.fImp (.fEq 0 (ei + 2)) φ))) from rfl,
    quote_toSet_fAll' (show k + 1 = k + 1 from rfl),
    quote_toSet_fAll' (show k + 1 + 1 = k + 2 from rfl),
    quote_toSet_fImp, quote_toSet_fImp,
    quote_fEq_move (show 1 < k + 2 by omega) (show ci + 2 < k + 2 by omega),
    quote_fEq_move (show 0 < k + 2 by omega) (show ei + 2 < k + 2 by omega),
    hφmove]
  rfl

/-- The Sigma gadget's quote is the coded Sigma gadget at the cast index. -/
theorem quote_sigmaAtF (n : ℕ) {k : ℕ} (ci ei : ℕ)
    (hci : ci < k) (hei : ei < k) :
    (⌜toSet k (sigmaAtF n ci ei)⌝ : V) = sigmaAtCode ci ei ((n : ℕ) : V) := by
  rw [show sigmaAtF n ci ei = canonAtF ci ei (fSigmaTrueF (n + 1) 1 0)
      from rfl,
    quote_canonAtF ci ei hci hei _
      (fun j hj => free_fSigmaTrueF_canonical hj),
    ← sigmaTrueCode_natCast (V := V) (n + 1), Nat.cast_succ]
  rfl

/-- The Pi-falsity gadget's quote is the coded Pi-falsity gadget. -/
theorem quote_piFalseAtF (n : ℕ) {k : ℕ} (ci ei : ℕ)
    (hci : ci < k) (hei : ei < k) :
    (⌜toSet k (piFalseAtF n ci ei)⌝ : V) =
      piFalseAtCode ci ei ((n : ℕ) : V) := by
  rw [show piFalseAtF n ci ei = canonAtF ci ei (fPiFalseF (n + 1) 1 0)
      from rfl,
    quote_canonAtF ci ei hci hei _
      (fun j hj => free_fPiFalseF_canonical hj),
    ← piFalseCode_natCast (V := V) (n + 1), Nat.cast_succ]
  rfl

/-- The Pi-truth gadget's quote is the coded Pi-truth gadget. -/
theorem quote_piTrueAtF (n : ℕ) {k : ℕ} (ci ei : ℕ)
    (hci : ci < k) (hei : ei < k) :
    (⌜toSet k (piTrueAtF n ci ei)⌝ : V) =
      piTrueAtCode ci ei ((n : ℕ) : V) := by
  rw [show piTrueAtF n ci ei = canonAtF ci ei (fPiTrueF (n + 1) 1 0)
      from rfl,
    quote_canonAtF ci ei hci hei _
      (fun j hj => free_fPiTrueF_canonical hj),
    ← piTrueCode_natCast (V := V) (n + 1), Nat.cast_succ]
  rfl

/-- The boundedness gadget's quote at its (only) ambient depth. -/
theorem quote_boundedAtF (n : ℕ) :
    (⌜toSet 2 (boundedAtF n 1)⌝ : V) =
      boundedAtPart quantBoundedD3Code ((n : ℕ) : V) := by
  have hnum : (⌜toSet 3 (fNumF 0 n)⌝ : V) = ⌜toSet 1 (fNumF 0 n)⌝ :=
    quote_toSet_congr (fun i hi => by have := free_fNumF hi; omega)
      (fun i hi => by have := free_fNumF hi; omega)
  rw [show boundedAtF n 1 =
        Form.fEx (.fAnd (fNumF 0 n) (fQuantBoundedF 0 2)) from rfl,
    quote_toSet_fEx' (show 2 + 1 = 3 from rfl), quote_toSet_fAnd,
    hnum, ← numChainCode_natCast,
    ← coe_toNat_eq_quote (V := V) (toSet 3 (fQuantBoundedF 0 2))]
  rfl

/-! ### The five field builders at standard points -/

/-- **`localStepCode` agrees with the quotation of `localStepF`.** -/
theorem localStepCode_natCast (n : ℕ) :
    localStepCode ((n : ℕ) : V) = ⌜toSet 0 (localStepF n)⌝ := by
  rw [show localStepF n =
        Form.fAll (.fAll (.fImp (fUnivEnvF 0)
          (.fAnd
            (.fImp (fTaggedEmptyF 1 2) (.fImp (sigmaAtF n 1 0) .fBot))
            (.fImp (fIsFormCodeF 1)
              (.fImp (sigmaAtF n 1 0) (piTrueAtF n 1 0)))))) from rfl,
    quote_toSet_fAll' (show 0 + 1 = 1 from rfl),
    quote_toSet_fAll' (show 1 + 1 = 2 from rfl),
    quote_toSet_fImp, quote_toSet_fAnd,
    quote_toSet_fImp, quote_toSet_fImp, quote_toSet_fImp, quote_toSet_fImp,
    quote_sigmaAtF (V := V) n 1 0 (by omega) (by omega),
    quote_piTrueAtF (V := V) n 1 0 (by omega) (by omega),
    ← coe_toNat_eq_quote (V := V) (toSet 2 (fUnivEnvF 0)),
    ← coe_toNat_eq_quote (V := V) (toSet 2 (fTaggedEmptyF 1 2)),
    ← coe_toNat_eq_quote (V := V) (toSet 2 (fIsFormCodeF 1)),
    ← coe_toNat_eq_quote (V := V) (toSet 2 (Form.fBot))]
  rfl

/-- **`crossLevelCode` agrees with the quotation of `crossLevelF`.** -/
theorem crossLevelCode_natCast (n : ℕ) :
    crossLevelCode ((n : ℕ) : V) = ⌜toSet 0 (crossLevelF n)⌝ := by
  rw [show crossLevelF n =
        Form.fAll (.fAll (.fImp (fIsFormCodeF 1) (.fImp (fUnivEnvF 0)
          (.fImp (boundedAtF n 1)
            (.fOr (sigmaAtF n 1 0) (piFalseAtF n 1 0)))))) from rfl,
    quote_toSet_fAll' (show 0 + 1 = 1 from rfl),
    quote_toSet_fAll' (show 1 + 1 = 2 from rfl),
    quote_toSet_fImp, quote_toSet_fImp, quote_toSet_fImp, quote_toSet_fOr,
    quote_boundedAtF,
    quote_sigmaAtF (V := V) n 1 0 (by omega) (by omega),
    quote_piFalseAtF (V := V) n 1 0 (by omega) (by omega),
    ← coe_toNat_eq_quote (V := V) (toSet 2 (fIsFormCodeF 1)),
    ← coe_toNat_eq_quote (V := V) (toSet 2 (fUnivEnvF 0))]
  rfl

/-- **`shiftInvariantCode` agrees with the quotation of
`shiftInvariantF`.** -/
theorem shiftInvariantCode_natCast (n : ℕ) :
    shiftInvariantCode ((n : ℕ) : V) = ⌜toSet 0 (shiftInvariantF n)⌝ := by
  rw [show shiftInvariantF n =
        Form.fAll (.fAll (.fAll (.fAll
          (.fImp (fIsFormCodeF 3)
            (.fImp (.fEx (.fAnd (fSuccMapF 0) (fRenamesF 0 4 3)))
              (.fImp (fUnivEnvF 1)
                (.fAll
                  (.fImp (fEconsF 0 1 2)
                    (.fAnd
                      (fIff (sigmaAtF n 3 0) (sigmaAtF n 4 2))
                      (fIff (piFalseAtF n 3 0)
                        (piFalseAtF n 4 2))))))))))) from rfl,
    quote_toSet_fAll' (show 0 + 1 = 1 from rfl),
    quote_toSet_fAll' (show 1 + 1 = 2 from rfl),
    quote_toSet_fAll' (show 2 + 1 = 3 from rfl),
    quote_toSet_fAll' (show 3 + 1 = 4 from rfl),
    quote_toSet_fImp, quote_toSet_fImp, quote_toSet_fImp,
    quote_toSet_fEx' (show 4 + 1 = 5 from rfl), quote_toSet_fAnd,
    quote_toSet_fAll' (show 4 + 1 = 5 from rfl),
    quote_toSet_fImp, quote_toSet_fAnd,
    quote_toSet_fIff, quote_toSet_fIff,
    quote_sigmaAtF (V := V) n 3 0 (by omega) (by omega),
    quote_sigmaAtF (V := V) n 4 2 (by omega) (by omega),
    quote_piFalseAtF (V := V) n 3 0 (by omega) (by omega),
    quote_piFalseAtF (V := V) n 4 2 (by omega) (by omega),
    ← coe_toNat_eq_quote (V := V) (toSet 4 (fIsFormCodeF 3)),
    ← coe_toNat_eq_quote (V := V) (toSet 5 (fSuccMapF 0)),
    ← coe_toNat_eq_quote (V := V) (toSet 5 (fRenamesF 0 4 3)),
    ← coe_toNat_eq_quote (V := V) (toSet 4 (fUnivEnvF 1)),
    ← coe_toNat_eq_quote (V := V) (toSet 5 (fEconsF 0 1 2))]
  rfl

/-- **`substitutionInvariantCode` agrees with the quotation of
`substitutionInvariantF`.** -/
theorem substitutionInvariantCode_natCast (n : ℕ) :
    substitutionInvariantCode ((n : ℕ) : V) =
      ⌜toSet 0 (substitutionInvariantF n)⌝ := by
  rw [show substitutionInvariantF n =
        Form.fAll (.fAll (.fAll (.fAll (.fAll
          (.fImp (fIsFormCodeF 4)
            (.fImp (fVarMapF 3)
              (.fImp (fRenamesF 3 4 2)
                (.fImp (fUnivEnvF 1)
                  (.fImp (fCompF 0 1 3)
                    (.fAnd
                      (fIff (sigmaAtF n 2 1) (sigmaAtF n 4 0))
                      (fIff (piFalseAtF n 2 1)
                        (piFalseAtF n 4 0)))))))))))) from rfl,
    quote_toSet_fAll' (show 0 + 1 = 1 from rfl),
    quote_toSet_fAll' (show 1 + 1 = 2 from rfl),
    quote_toSet_fAll' (show 2 + 1 = 3 from rfl),
    quote_toSet_fAll' (show 3 + 1 = 4 from rfl),
    quote_toSet_fAll' (show 4 + 1 = 5 from rfl),
    quote_toSet_fImp, quote_toSet_fImp, quote_toSet_fImp, quote_toSet_fImp,
    quote_toSet_fImp, quote_toSet_fAnd,
    quote_toSet_fIff, quote_toSet_fIff,
    quote_sigmaAtF (V := V) n 2 1 (by omega) (by omega),
    quote_sigmaAtF (V := V) n 4 0 (by omega) (by omega),
    quote_piFalseAtF (V := V) n 2 1 (by omega) (by omega),
    quote_piFalseAtF (V := V) n 4 0 (by omega) (by omega),
    ← coe_toNat_eq_quote (V := V) (toSet 5 (fIsFormCodeF 4)),
    ← coe_toNat_eq_quote (V := V) (toSet 5 (fVarMapF 3)),
    ← coe_toNat_eq_quote (V := V) (toSet 5 (fRenamesF 3 4 2)),
    ← coe_toNat_eq_quote (V := V) (toSet 5 (fUnivEnvF 1)),
    ← coe_toNat_eq_quote (V := V) (toSet 5 (fCompF 0 1 3))]
  rfl

/-- **`axiomSoundCode` agrees with the quotation of `axiomSoundF`.** -/
theorem axiomSoundCode_natCast (n : ℕ) :
    axiomSoundCode ((n : ℕ) : V) = ⌜toSet 0 (axiomSoundF n)⌝ := by
  rw [show axiomSoundF n =
        Form.fAll (.fAll (.fImp (fZFCAxiomCodeF 1) (.fImp (fUnivEnvF 0)
          (.fImp (boundedAtF n 1)
            (.fAnd (sigmaAtF n 1 0) (piTrueAtF n 1 0)))))) from rfl,
    quote_toSet_fAll' (show 0 + 1 = 1 from rfl),
    quote_toSet_fAll' (show 1 + 1 = 2 from rfl),
    quote_toSet_fImp, quote_toSet_fImp, quote_toSet_fImp, quote_toSet_fAnd,
    quote_boundedAtF,
    quote_sigmaAtF (V := V) n 1 0 (by omega) (by omega),
    quote_piTrueAtF (V := V) n 1 0 (by omega) (by omega),
    ← coe_toNat_eq_quote (V := V) (toSet 2 (fZFCAxiomCodeF 1)),
    ← coe_toNat_eq_quote (V := V) (toSet 2 (fUnivEnvF 0))]
  rfl

end StandardPoints

end ZFCinPA
end LeanProofs
