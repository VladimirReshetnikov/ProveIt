import BoundedZFCConsistency.AxiomCode
import BoundedZFCConsistency.UniverseTruthLevel

/-!
# Renaming at a fixed truth level, and the shape of level soundness

`BoundedZFCConsistency.InternalSoundness` proves the substitution lemma for
internal satisfaction in a *set* structure: satisfaction of a renamed code under
an environment is satisfaction of the original code under the composed
environment.  `BoundedZFCConsistency.CodedDerivation` then turns that lemma,
together with the Tarski clauses of `SatIn`, into soundness of the seventeen-rule
coded calculus over a set structure.

Truth over the *universe* is not `SatIn` over a set, so neither result transfers.
This module supplies the substitution half of the replacement: the same lemma for
the externally indexed predicates `SigmaTrue` and `PiFalse` of
`BoundedZFCConsistency.UniverseTruthLevel`, at every fixed level.

## Two recursions, again

The proof combines the two mechanisms the truth hierarchy already combines, and
in the same way.

*Across* levels the recursion is external.  The universal head on the Sigma side
and the existential head on the Pi side are recorded by *delegation to the
previous level* under an oriented rank bound, so the substitution lemma at level
`n+1` consumes the substitution lemma at level `n`, both polarities.  The level
therefore has to be a metatheoretic `Nat` and the induction on it a metatheoretic
induction; nothing here is uniform in the level, and no formula of this module
has the level as a de Bruijn slot.

*Within* a level the recursion is over a possibly nonstandard code, so it is the
definability-relative code induction `isFormCodeSem_ind'`.  The property carried
is therefore a `Form` with parameters, assembled from `fSigmaTrueF n`,
`fPiFalseF n`, `fRenamesF`, `fVarMapF`, `fUnivEnvF` and `fCompF` — every
ingredient is already rendered, so the property is written rather than built.

Level zero is a separate, simpler code induction, over the quantifier-free codes
and against `QFTrue` directly.  It has to be separate: at level zero the Tarski
clauses of the two polarities are not biconditionals in the subcodes — a code is
Sigma-true at level zero only if it is quantifier-free, and quantifier-freeness
of a compound is not delivered by either subcode alone — so the connective cases
run against `qfTrue_imp`, `qfTrue_and` and `qfTrue_or` and their codehood
constructors instead.  The bridge back to `SigmaTrue H 0` and `PiFalse H 0` is
the observation that both are false at a code that is not quantifier-free, and
that a renaming of a code is quantifier-free only if the code is, which is
invariance of the internal rank under renaming.

## Carriers for universe environments

`compV` and its three composition identities are stated for `IsEnvOn H A e`, an
environment whose values lie in a fixed carrier.  A universe environment has no
carrier, but it does have one available: the double union of its graph collects
every value of a Kuratowski-pair graph, and one further set may be adjoined to
accommodate the value the binder cases shift in.  Every carrier-relative
composition fact is therefore reused rather than reproved, and the carrier never
appears in a statement of this module.

## What is proved, and what the soundness statement still owes

The substitution lemmas are proved outright, on both polarities, at every level,
together with the two instances the calculus consumes — the successor shift and
instantiation at an internal variable index.

Fixed-level soundness of the coded calculus and its falsity corollary are
*stated* here, as `LevelSoundnessAt` and `NoBoundedRefutationAtLevel`, and the
corollary is proved *from* the soundness statement together with the axiom-truth
premise `AxiomCodesTrueAt`.  Soundness itself is not proved, and the reason is
specific rather than a matter of effort: pushing truth through implication
elimination needs, at a positive level, one of the two facts about the hierarchy
that `BoundedZFCConsistency.UniverseTruthLevel` leaves open.

Read `SigmaTrue H (n+1) c E` as truth.  Implication elimination has
`SigmaTrue H (n+1) (imp a b) E` and `SigmaTrue H (n+1) a E`, and
`sigmaTrue_imp` turns the first into `PiFalse H (n+1) a E ∨ SigmaTrue H (n+1) b E`.
Discharging the left disjunct is exactly **exclusivity at a positive level**,
`SigmaTrue H (n+1) a E → ¬ PiFalse H (n+1) a E`, which is proved at level zero as
`sigmaTrue_not_piFalse_zero` and is open above it.

Read `PiTrue H (n+1) c E` as truth instead, and the same rule needs
`SigmaTrue H (n+1) a E` from `PiTrue H (n+1) a E`, which is **two-valuedness** at
a positive level and is a consequence of the level-collapse theorem.  Taking
truth to be the conjunction `SigmaTrue ∧ PiTrue` repairs implication elimination
but breaks disjunction elimination, where the two recorded disjuncts have to be
separated again.

The obligation is therefore named here as `LevelTwoValuedAt` and stated for the
codes a bounded derivation can mention.  With it, and with `AxiomCodesTrueAt`,
`LevelSoundnessAt` becomes the seventeen-case induction of `soundAt_step` with
`SatIn` replaced by fixed-level truth and the five binder rules replaced by the
substitution lemmas of this module.  Nothing below assumes it.

## Conventions

De Bruijn slots named `_i` are ABSOLUTE positions in the environment at the use
site, matching `ZF.Zf`, `BoundedZFCConsistency.InternalSat` and
`BoundedZFCConsistency.UniverseTruthLevel`.

Neither Powerset nor Regularity is used, matching the six axioms bundled in
`ZFAxioms`.
-/

namespace LeanProofs
namespace BoundedZFCConsistency

open SetTheory
open SetTheory.Form

universe u

section LevelSoundness

variable {V : Type u} {mem : V → V → Prop}

/-! ## A carrier for a universe environment

`IsUnivEnv H E` is `IsEnvOn H A E` with the value clause deleted, so the two
notions differ only by a set containing every value of `E`.  Such a set exists:
the graph of `E` consists of Kuratowski pairs, and the double union of a set of
Kuratowski pairs contains every second component.  Adjoining one further element
accommodates the value the binder cases shift in. -/

/-- A carrier for the universe environment `E`, with `d` adjoined. -/
noncomputable def envCarrier (H : ZFAxioms mem) (E d : V) : V :=
  vcup H (vunion H (vunion H E)) (vsingle H d)

/-- The adjoined element belongs to the carrier. -/
theorem mem_envCarrier (H : ZFAxioms mem) (E d : V) : mem d (envCarrier H E d) :=
  (vcup_spec H _ _ d).mpr (Or.inr ((vsingle_spec H d d).mpr rfl))

/-- **A universe environment is an environment over its own carrier.** -/
theorem isEnvOn_envCarrier (H : ZFAxioms mem) {E : V} (hE : IsUnivEnv H E)
    (d : V) : IsEnvOn H (envCarrier H E d) E := by
  refine ⟨hE, fun k y hk => ?_⟩
  refine (vcup_spec H _ _ y).mpr (Or.inl ?_)
  refine (vunion_spec H (vunion H E) y).mpr
    ⟨vpair H k y, (vpair_spec H k y y).mpr (Or.inr rfl), ?_⟩
  exact (vunion_spec H E (vpair H k y)).mpr
    ⟨kpair H k y, (kpair_mem H k y (vpair H k y)).mpr (Or.inr rfl), hk⟩

/-! ### The composition facts, restated over the universe

Each is the carrier-relative statement instantiated at `envCarrier`.  The
carrier is chosen at the point of use and never escapes. -/

/-- The composition of a universe environment with a variable map is a universe
environment. -/
theorem compV_isUnivEnv (H : ZFAxioms mem) {E r : V} (hE : IsUnivEnv H E)
    (hr : IsVarMap H r) : IsUnivEnv H (compV H E r) :=
  (compV_isEnvOn H (isEnvOn_envCarrier H hE (vempty H)) hr).1

/-- The composition evaluates as the composite. -/
theorem compV_applyU (H : ZFAxioms mem) {E r : V} (hE : IsUnivEnv H E)
    (hr : IsVarMap H r) {k : V} (hk : mem k (omegaV H)) :
    applyV H (compV H E r) k = applyV H E (applyV H r k) :=
  compV_apply H (isEnvOn_envCarrier H hE (vempty H)) hr hk

/-- **The binder identity over the universe.**  Composing a shifted environment
with a shifted variable map is the shift of the composition. -/
theorem compV_econs_upVU (H : ZFAxioms mem) {E r : V} (hE : IsUnivEnv H E)
    (hr : IsVarMap H r) (d : V) :
    compV H (econs H d E) (upV H r) = econs H d (compV H E r) :=
  compV_econs_upV H (isEnvOn_envCarrier H hE d) hr (mem_envCarrier H E d)

/-- **The shift identity over the universe.** -/
theorem compV_succMapU (H : ZFAxioms mem) {E : V} (hE : IsUnivEnv H E) (d : V) :
    compV H (econs H d E) (succMap H) = E :=
  compV_succMap H (isEnvOn_envCarrier H hE d) (mem_envCarrier H E d)

/-- **The instantiation identity over the universe.** -/
theorem compV_instMapU (H : ZFAxioms mem) {E k : V} (hE : IsUnivEnv H E)
    (hk : mem k (omegaV H)) :
    compV H E (instMap H k) = econs H (applyV H E k) E :=
  compV_instMap H (isEnvOn_envCarrier H hE (vempty H)) hk

/-- `fCompF` read against a universe environment. -/
theorem fCompF_specU (H : ZFAxioms mem) (ee : Nat → V) (i e_i r_i : Nat)
    (he : IsUnivEnv H (ee e_i)) (hr : IsVarMap H (ee r_i)) :
    Sat mem ee (fCompF i e_i r_i) ↔ ee i = compV H (ee e_i) (ee r_i) :=
  fCompF_spec H ee i e_i r_i (isEnvOn_envCarrier H he (vempty H)) hr

/-! ## The right-hand side of a substitution biconditional

Every property this module carries through a code induction has the shape "truth
of the renaming at the environment iff truth of the code at the composition".
The composition is not a term of the object language, so the right-hand side
introduces one binder for it; the slot layout is fixed once here and shared by
the three instances. -/

/-- The parameter block of the substitution properties: there are no parameters,
so the block is constant. -/
noncomputable def envLevelSubst (H : ZFAxioms mem) : Nat → V := fun _ => vempty H

/-- The right-hand side of a substitution biconditional, for any rendered binary
truth predicate.

| de Bruijn slot | contents                             |
| -------------- | ------------------------------------ |
| `0`            | the environment `e`                  |
| `1`            | the renaming `c'`                    |
| `2`            | the variable map `r`                 |
| `3`            | the code `c`                         |

Under the binder for the composed environment every slot above is shifted by
one. -/
theorem compRhs_spec (H : ZFAxioms mem) {F : Nat → Nat → Form}
    {P : V → V → Prop}
    (hF : ∀ (ee : Nat → V) (c_i e_i : Nat),
      Sat mem ee (F c_i e_i) ↔ P (ee c_i) (ee e_i))
    (ee : Nat → V) (hr : IsVarMap H (ee 2)) (he : IsUnivEnv H (ee 0)) :
    Sat mem ee (fEx (fAnd (fCompF 0 1 3) (F 4 0))) ↔
      P (ee 3) (compV H (ee 0) (ee 2)) := by
  constructor
  · rintro ⟨w, hw, hsat⟩
    have hw' : w = compV H (ee 0) (ee 2) :=
      (fCompF_specU H (scons w ee) 0 1 3 he hr).mp hw
    have hs := (hF (scons w ee) 4 0).mp hsat
    rw [hw'] at hs
    exact hs
  · intro hsat
    exact ⟨compV H (ee 0) (ee 2),
      (fCompF_specU H (scons (compV H (ee 0) (ee 2)) ee) 0 1 3 he hr).mpr rfl,
      (hF (scons (compV H (ee 0) (ee 2)) ee) 4 0).mpr hsat⟩

/-! ## Invariance of the oriented bounds under internal renaming

`BoundedZFCConsistency.CodedRank` proves that a renaming carries the ranks of a
code, and that the bound on the smaller rank descends from a renaming to its
source.  The polarity switch needs the two oriented bounds and needs them in both
directions, so the underlying rank equation is stated as a biconditional. -/

/-- **A renaming has exactly the ranks of its source.**  The forward direction is
`rankRen_of_isFormCodeSem`; the converse combines it with single-valuedness of
the ranks at the renaming. -/
theorem ranks_renames_iff (H : ZFAxioms mem) {r c c' s p : V}
    (hc : IsFormCodeSem H c) (hr : IsVarMap H r) (hren : Renames H r c c') :
    Ranks H c s p ↔ Ranks H c' s p := by
  constructor
  · intro h
    exact rankRen_of_isFormCodeSem H c hc r c' s p hr hren h
  · intro h
    obtain ⟨sa, pa, hra⟩ := rankTotal_of_isFormCodeSem H c hc
    have hra' : Ranks H c' sa pa :=
      rankRen_of_isFormCodeSem H c hc r c' sa pa hr hren hra
    obtain ⟨e1, e2⟩ :=
      rankUnique_of_isFormCodeSem H c'
        (renames_isFormCodeSem H hc hr hren) s p sa pa h hra'
    rw [e1, e2]
    exact hra

/-- **The Sigma-bound is invariant under internal renaming.** -/
theorem sigmaBounded_renames_iff (H : ZFAxioms mem) {b r c c' : V}
    (hc : IsFormCodeSem H c) (hr : IsVarMap H r) (hren : Renames H r c c') :
    SigmaBounded H b c ↔ SigmaBounded H b c' := by
  unfold SigmaBounded
  constructor
  · rintro ⟨s, p, hrk, hle⟩
    exact ⟨s, p, (ranks_renames_iff H hc hr hren).mp hrk, hle⟩
  · rintro ⟨s, p, hrk, hle⟩
    exact ⟨s, p, (ranks_renames_iff H hc hr hren).mpr hrk, hle⟩

/-- **The Pi-bound is invariant under internal renaming.** -/
theorem piBounded_renames_iff (H : ZFAxioms mem) {b r c c' : V}
    (hc : IsFormCodeSem H c) (hr : IsVarMap H r) (hren : Renames H r c c') :
    PiBounded H b c ↔ PiBounded H b c' := by
  unfold PiBounded
  constructor
  · rintro ⟨s, p, hrk, hle⟩
    exact ⟨s, p, (ranks_renames_iff H hc hr hren).mp hrk, hle⟩
  · rintro ⟨s, p, hrk, hle⟩
    exact ⟨s, p, (ranks_renames_iff H hc hr hren).mpr hrk, hle⟩

/-- **A renaming is quantifier-free only if its source is.**  This is the
rank-zero instance of the same invariance, and it is what makes both polarities
of level zero vanish at a code that is not quantifier-free. -/
theorem isQFCodeSem_of_renames (H : ZFAxioms mem) {r c c' : V}
    (hc : IsFormCodeSem H c) (hr : IsVarMap H r) (hren : Renames H r c c')
    (h : IsQFCodeSem H c') : IsQFCodeSem H c :=
  (isQFCodeSem_iff_quantBounded_zero H hc).mpr
    (quantBounded_of_renames H hc hr hren
      (quantBounded_zero_of_isQFCodeSem H h))

/-! ## Level zero

Both polarities of level zero read the truth bit of `QFTrue`, so the substitution
lemma there is a statement about `QFTrue` and a statement about
quantifier-freeness.  The code induction is the quantifier-free one, over six
clauses. -/

/-- The Pi side of level zero, spelled out: the code is quantifier-free and the
quantifier-free truth fails. -/
theorem piFalse_zero_iff (H : ZFAxioms mem) {c e : V} :
    PiFalse H 0 c e ↔ (IsQFCodeSem H c ∧ ¬ QFTrue H c e) := by
  constructor
  · rintro ⟨hq, hb⟩
    exact ⟨hq, (vbit_eq_zero H _).mp hb.symm⟩
  · rintro ⟨hq, ht⟩
    exact ⟨hq, (vbit_neg H ht).symm⟩

/-- **Renaming commutes with quantifier-free truth**, as the property the
quantifier-free code induction carries.  The property also carries
quantifier-freeness of every renaming, which the connective cases need and which
no inversion rule supplies. -/
def QFSubstOK (H : ZFAxioms mem) (c : V) : Prop :=
  IsQFCodeSem H c ∧
  ∀ r c' e, IsVarMap H r → IsUnivEnv H e → Renames H r c c' →
    (IsQFCodeSem H c' ∧ (QFTrue H c' e ↔ QFTrue H c (compV H e r)))

/-- `QFSubstOK` as a `Form`, with the code in slot `0` of the caller.

| de Bruijn slot | contents              |
| -------------- | --------------------- |
| `0`            | the environment `e`   |
| `1`            | the renaming `c'`     |
| `2`            | the variable map `r`  |
| `3`            | the code `c`          |
-/
def fQFSubstOKF : Form :=
  fAnd (fIsQFCodeF 0)
    (fAll (fAll (fAll (fImp (fVarMapF 2)
      (fImp (fUnivEnvF 0)
        (fImp (fRenamesF 2 3 1)
          (fAnd (fIsQFCodeF 1)
            (fIff (fQFTrueF 1 0)
              (fEx (fAnd (fCompF 0 1 3) (fQFTrueF 4 0)))))))))))

theorem fQFSubstOKF_spec (H : ZFAxioms mem) (y : V) :
    Sat mem (scons y (envLevelSubst H)) fQFSubstOKF ↔ QFSubstOK H y := by
  unfold QFSubstOK
  have hrhs : ∀ r c' e : V, IsVarMap H r → IsUnivEnv H e →
      (Sat mem (scons e (scons c' (scons r (scons y (envLevelSubst H)))))
          (fEx (fAnd (fCompF 0 1 3) (fQFTrueF 4 0))) ↔
        QFTrue H y (compV H e r)) := by
    intro r c' e hr he
    exact compRhs_spec H (fun ee c_i e_i => fQFTrueF_spec H ee c_i e_i)
      (scons e (scons c' (scons r (scons y (envLevelSubst H))))) hr he
  constructor
  · rintro ⟨hcode, h⟩
    refine ⟨(fIsQFCodeF_spec H (scons y (envLevelSubst H)) 0).mp hcode,
      fun r c' e hr he hren => ?_⟩
    have hbody := h r c' e
      ((fVarMapF_spec H
        (scons e (scons c' (scons r (scons y (envLevelSubst H))))) 2).mpr hr)
      ((fUnivEnvF_spec H
        (scons e (scons c' (scons r (scons y (envLevelSubst H))))) 0).mpr he)
      ((fRenamesF_spec H
        (scons e (scons c' (scons r (scons y (envLevelSubst H)))))
        2 3 1).mpr hren)
    refine ⟨(fIsQFCodeF_spec H
      (scons e (scons c' (scons r (scons y (envLevelSubst H))))) 1).mp hbody.1,
      ?_⟩
    have hiff := Sat_fIff.mp hbody.2
    exact ((fQFTrueF_spec H
      (scons e (scons c' (scons r (scons y (envLevelSubst H)))))
      1 0).symm.trans hiff).trans (hrhs r c' e hr he)
  · rintro ⟨hcode, h⟩
    refine ⟨(fIsQFCodeF_spec H (scons y (envLevelSubst H)) 0).mpr hcode,
      fun r c' e hr he hren => ?_⟩
    have hr' : IsVarMap H r :=
      (fVarMapF_spec H
        (scons e (scons c' (scons r (scons y (envLevelSubst H))))) 2).mp hr
    have he' : IsUnivEnv H e :=
      (fUnivEnvF_spec H
        (scons e (scons c' (scons r (scons y (envLevelSubst H))))) 0).mp he
    have hren' : Renames H r y c' :=
      (fRenamesF_spec H
        (scons e (scons c' (scons r (scons y (envLevelSubst H)))))
        2 3 1).mp hren
    obtain ⟨hq', hiff⟩ := h r c' e hr' he' hren'
    refine ⟨(fIsQFCodeF_spec H
      (scons e (scons c' (scons r (scons y (envLevelSubst H))))) 1).mpr hq', ?_⟩
    exact Sat_fIff.mpr (((fQFTrueF_spec H
      (scons e (scons c' (scons r (scons y (envLevelSubst H)))))
      1 0).trans hiff).trans (hrhs r c' e hr' he').symm)

/-- **The substitution lemma at level zero**, in the form the quantifier-free
code induction proves.  The atomic cases reduce both sides to the same fact about
the model, using `compV_applyU`; falsity is refuted on both sides; and the three
Boolean cases apply the induction hypothesis to the subcodes at the same map and
environment. -/
theorem qfSubstOK_of_isQFCodeSem (H : ZFAxioms mem) :
    ∀ c, IsQFCodeSem H c → QFSubstOK H c := by
  refine isQFCodeSem_ind H (QFSubstOK H) fQFSubstOKF (envLevelSubst H)
    (fun y => (fQFSubstOKF_spec H y).symm) ?_ ?_ ?_ ?_ ?_ ?_
  · intro i j hi hj
    refine ⟨isQFCodeSem_memAtom H hi hj, fun r c' e hr he hren => ?_⟩
    have hri := isVarMap_apply H hr hi
    have hrj := isVarMap_apply H hr hj
    rw [renames_memAtom_inv H hren]
    refine ⟨isQFCodeSem_memAtom H hri hrj, ?_⟩
    rw [qfTrue_memAtom H hri hrj he,
        qfTrue_memAtom H hi hj (compV_isUnivEnv H he hr),
        compV_applyU H he hr hi, compV_applyU H he hr hj]
  · intro i j hi hj
    refine ⟨isQFCodeSem_eqAtom H hi hj, fun r c' e hr he hren => ?_⟩
    have hri := isVarMap_apply H hr hi
    have hrj := isVarMap_apply H hr hj
    rw [renames_eqAtom_inv H hren]
    refine ⟨isQFCodeSem_eqAtom H hri hrj, ?_⟩
    rw [qfTrue_eqAtom H hri hrj he,
        qfTrue_eqAtom H hi hj (compV_isUnivEnv H he hr),
        compV_applyU H he hr hi, compV_applyU H he hr hj]
  · refine ⟨isQFCodeSem_bot H, fun r c' e hr he hren => ?_⟩
    rw [renames_bot_inv H hren]
    exact ⟨isQFCodeSem_bot H,
      ⟨fun h => absurd h (qfTrue_bot H), fun h => absurd h (qfTrue_bot H)⟩⟩
  · intro a b ha hb
    refine ⟨isQFCodeSem_imp H ha.1 hb.1, fun r c' e hr he hren => ?_⟩
    obtain ⟨a', b', hc', k1, k2⟩ := renames_imp_inv H hren
    obtain ⟨q1, t1⟩ := ha.2 r a' e hr he k1
    obtain ⟨q2, t2⟩ := hb.2 r b' e hr he k2
    subst hc'
    refine ⟨isQFCodeSem_imp H q1 q2, ?_⟩
    rw [qfTrue_imp H q1 q2 he,
        qfTrue_imp H ha.1 hb.1 (compV_isUnivEnv H he hr), t1, t2]
  · intro a b ha hb
    refine ⟨isQFCodeSem_and H ha.1 hb.1, fun r c' e hr he hren => ?_⟩
    obtain ⟨a', b', hc', k1, k2⟩ := renames_and_inv H hren
    obtain ⟨q1, t1⟩ := ha.2 r a' e hr he k1
    obtain ⟨q2, t2⟩ := hb.2 r b' e hr he k2
    subst hc'
    refine ⟨isQFCodeSem_and H q1 q2, ?_⟩
    rw [qfTrue_and H q1 q2 he,
        qfTrue_and H ha.1 hb.1 (compV_isUnivEnv H he hr), t1, t2]
  · intro a b ha hb
    refine ⟨isQFCodeSem_or H ha.1 hb.1, fun r c' e hr he hren => ?_⟩
    obtain ⟨a', b', hc', k1, k2⟩ := renames_or_inv H hren
    obtain ⟨q1, t1⟩ := ha.2 r a' e hr he k1
    obtain ⟨q2, t2⟩ := hb.2 r b' e hr he k2
    subst hc'
    refine ⟨isQFCodeSem_or H q1 q2, ?_⟩
    rw [qfTrue_or H q1 q2 he,
        qfTrue_or H ha.1 hb.1 (compV_isUnivEnv H he hr), t1, t2]

/-- **Renaming commutes with both polarities at level zero.**  At a code that is
not quantifier-free all four statements are false, and the renaming inherits that
by rank invariance. -/
theorem levelSubst_zero (H : ZFAxioms mem) {r c c' e : V}
    (hc : IsFormCodeSem H c) (hr : IsVarMap H r) (he : IsUnivEnv H e)
    (hren : Renames H r c c') :
    (SigmaTrue H 0 c' e ↔ SigmaTrue H 0 c (compV H e r)) ∧
      (PiFalse H 0 c' e ↔ PiFalse H 0 c (compV H e r)) := by
  by_cases hq : IsQFCodeSem H c
  · obtain ⟨-, hstep⟩ := qfSubstOK_of_isQFCodeSem H c hq
    obtain ⟨hq', hiff⟩ := hstep r c' e hr he hren
    constructor
    · rw [sigmaTrue_zero_iff, sigmaTrue_zero_iff]
      exact ⟨fun h => ⟨hq, hiff.mp h.2⟩, fun h => ⟨hq', hiff.mpr h.2⟩⟩
    · rw [piFalse_zero_iff, piFalse_zero_iff]
      exact ⟨fun h => ⟨hq, fun t => h.2 (hiff.mpr t)⟩,
        fun h => ⟨hq', fun t => h.2 (hiff.mp t)⟩⟩
  · have hq' : ¬ IsQFCodeSem H c' := fun h =>
      hq (isQFCodeSem_of_renames H hc hr hren h)
    constructor
    · rw [sigmaTrue_zero_iff, sigmaTrue_zero_iff]
      exact ⟨fun h => absurd h.1 hq', fun h => absurd h.1 hq⟩
    · rw [piFalse_zero_iff, piFalse_zero_iff]
      exact ⟨fun h => absurd h.1 hq', fun h => absurd h.1 hq⟩

/-! ## The Pi side of the atomic clauses

`BoundedZFCConsistency.UniverseTruthLevel` states the atomic Tarski clauses on
the Sigma side only, because nothing there needed the other polarity.  Both
inductions on the level are the same: at a tag below three the only applicable
row is delegation, so every level reads an atom exactly as level zero does. -/

/-- **Atomic membership on the Pi side**, at every level. -/
theorem piFalse_memAtom (H : ZFAxioms mem) :
    ∀ (n : Nat) {i j e : V}, mem i (omegaV H) → mem j (omegaV H) →
      IsUnivEnv H e →
      (PiFalse H n (kpair H (natV H 0) (kpair H i j)) e ↔
        ¬ mem (applyV H e i) (applyV H e j)) := by
  intro n
  induction n with
  | zero =>
      intro i j e hi hj he
      rw [piFalse_zero_iff]
      constructor
      · rintro ⟨-, ht⟩ h
        exact ht ((qfTrue_memAtom H hi hj he).mpr h)
      · intro h
        exact ⟨isQFCodeSem_memAtom H hi hj,
          fun ht => h ((qfTrue_memAtom H hi hj he).mp ht)⟩
  | succ n ih =>
      intro i j e hi hj he
      constructor
      · rintro ⟨C, hC, hmem⟩
        exact (ih hi hj he).mp
          (levelJustified_of_tag_low H (by omega) (hC _ _ _ hmem).2)
      · intro h
        exact levelSat_succ_of_levelSat H n he ((ih hi hj he).mpr h)

/-- **Atomic equality on the Pi side**, at every level. -/
theorem piFalse_eqAtom (H : ZFAxioms mem) :
    ∀ (n : Nat) {i j e : V}, mem i (omegaV H) → mem j (omegaV H) →
      IsUnivEnv H e →
      (PiFalse H n (kpair H (natV H 1) (kpair H i j)) e ↔
        applyV H e i ≠ applyV H e j) := by
  intro n
  induction n with
  | zero =>
      intro i j e hi hj he
      rw [piFalse_zero_iff]
      constructor
      · rintro ⟨-, ht⟩ h
        exact ht ((qfTrue_eqAtom H hi hj he).mpr h)
      · intro h
        exact ⟨isQFCodeSem_eqAtom H hi hj,
          fun ht => h ((qfTrue_eqAtom H hi hj he).mp ht)⟩
  | succ n ih =>
      intro i j e hi hj he
      constructor
      · rintro ⟨C, hC, hmem⟩
        exact (ih hi hj he).mp
          (levelJustified_of_tag_low H (by omega) (hC _ _ _ hmem).2)
      · intro h
        exact levelSat_succ_of_levelSat H n he ((ih hi hj he).mpr h)

/-! ## The substitution lemma at a fixed level

The property carried through the code induction is the pair of biconditionals,
one per polarity, universally quantified over the variable map, the renaming and
the environment.  Both polarities have to travel together: the Sigma clause of an
implication asks for Pi-falsity of the antecedent, and each polarity switch turns
one polarity at level `n+1` into the other at level `n`. -/

/-- **Renaming commutes with level-`n` truth**, as the property the code
induction carries. -/
def LevelSubstOK (H : ZFAxioms mem) (n : Nat) (c : V) : Prop :=
  IsFormCodeSem H c ∧
  ∀ r c' e, IsVarMap H r → IsUnivEnv H e → Renames H r c c' →
    ((SigmaTrue H n c' e ↔ SigmaTrue H n c (compV H e r)) ∧
      (PiFalse H n c' e ↔ PiFalse H n c (compV H e r)))

/-- `LevelSubstOK` as a `Form`, with the code in slot `0` of the caller and the
same slot layout as `fQFSubstOKF`.  The level is a metatheoretic argument
producing a different formula for each value, never a de Bruijn slot. -/
def fLevelSubstOKF (n : Nat) : Form :=
  fAnd (fIsFormCodeF 0)
    (fAll (fAll (fAll (fImp (fVarMapF 2)
      (fImp (fUnivEnvF 0)
        (fImp (fRenamesF 2 3 1)
          (fAnd
            (fIff (fSigmaTrueF n 1 0)
              (fEx (fAnd (fCompF 0 1 3) (fSigmaTrueF n 4 0))))
            (fIff (fPiFalseF n 1 0)
              (fEx (fAnd (fCompF 0 1 3) (fPiFalseF n 4 0)))))))))))

theorem fLevelSubstOKF_spec (H : ZFAxioms mem) (n : Nat) (y : V) :
    Sat mem (scons y (envLevelSubst H)) (fLevelSubstOKF n) ↔
      LevelSubstOK H n y := by
  unfold LevelSubstOK
  have hsig : ∀ r c' e : V, IsVarMap H r → IsUnivEnv H e →
      (Sat mem (scons e (scons c' (scons r (scons y (envLevelSubst H)))))
          (fEx (fAnd (fCompF 0 1 3) (fSigmaTrueF n 4 0))) ↔
        SigmaTrue H n y (compV H e r)) := by
    intro r c' e hr he
    exact compRhs_spec H (fun ee c_i e_i => fSigmaTrueF_spec H n ee c_i e_i)
      (scons e (scons c' (scons r (scons y (envLevelSubst H))))) hr he
  have hpi : ∀ r c' e : V, IsVarMap H r → IsUnivEnv H e →
      (Sat mem (scons e (scons c' (scons r (scons y (envLevelSubst H)))))
          (fEx (fAnd (fCompF 0 1 3) (fPiFalseF n 4 0))) ↔
        PiFalse H n y (compV H e r)) := by
    intro r c' e hr he
    exact compRhs_spec H (fun ee c_i e_i => fPiFalseF_spec H n ee c_i e_i)
      (scons e (scons c' (scons r (scons y (envLevelSubst H))))) hr he
  constructor
  · rintro ⟨hcode, h⟩
    refine ⟨(fIsFormCodeF_spec H (scons y (envLevelSubst H)) 0).mp hcode,
      fun r c' e hr he hren => ?_⟩
    have hbody := h r c' e
      ((fVarMapF_spec H
        (scons e (scons c' (scons r (scons y (envLevelSubst H))))) 2).mpr hr)
      ((fUnivEnvF_spec H
        (scons e (scons c' (scons r (scons y (envLevelSubst H))))) 0).mpr he)
      ((fRenamesF_spec H
        (scons e (scons c' (scons r (scons y (envLevelSubst H)))))
        2 3 1).mpr hren)
    refine ⟨?_, ?_⟩
    · exact ((fSigmaTrueF_spec H n
        (scons e (scons c' (scons r (scons y (envLevelSubst H)))))
        1 0).symm.trans (Sat_fIff.mp hbody.1)).trans (hsig r c' e hr he)
    · exact ((fPiFalseF_spec H n
        (scons e (scons c' (scons r (scons y (envLevelSubst H)))))
        1 0).symm.trans (Sat_fIff.mp hbody.2)).trans (hpi r c' e hr he)
  · rintro ⟨hcode, h⟩
    refine ⟨(fIsFormCodeF_spec H (scons y (envLevelSubst H)) 0).mpr hcode,
      fun r c' e hr he hren => ?_⟩
    have hr' : IsVarMap H r :=
      (fVarMapF_spec H
        (scons e (scons c' (scons r (scons y (envLevelSubst H))))) 2).mp hr
    have he' : IsUnivEnv H e :=
      (fUnivEnvF_spec H
        (scons e (scons c' (scons r (scons y (envLevelSubst H))))) 0).mp he
    have hren' : Renames H r y c' :=
      (fRenamesF_spec H
        (scons e (scons c' (scons r (scons y (envLevelSubst H)))))
        2 3 1).mp hren
    obtain ⟨hs, hp⟩ := h r c' e hr' he' hren'
    refine ⟨Sat_fIff.mpr ?_, Sat_fIff.mpr ?_⟩
    · exact ((fSigmaTrueF_spec H n
        (scons e (scons c' (scons r (scons y (envLevelSubst H)))))
        1 0).trans hs).trans (hsig r c' e hr' he').symm
    · exact ((fPiFalseF_spec H n
        (scons e (scons c' (scons r (scons y (envLevelSubst H)))))
        1 0).trans hp).trans (hpi r c' e hr' he').symm

/-- **The substitution lemma at every fixed level**, in the form the two
inductions prove.

The outer induction is on the metatheoretic level, and its base case is
`levelSubst_zero`.  The inner induction is the definability-relative code
induction.  The atomic cases and falsity read the clauses that hold at every
level; the three connective cases read the biconditional clauses, which hold at a
positive level; the existential head on the Sigma side and the universal head on
the Pi side read their positively recorded clauses at the shifted map and the
shifted environment, where `compV_econs_upVU` identifies the two ways of
shifting; and the two polarity switches consume the *previous* level on the
opposite polarity, together with invariance of the matching oriented bound under
renaming. -/
theorem levelSubstOK_of_isFormCodeSem (H : ZFAxioms mem) :
    ∀ (n : Nat) (c : V), IsFormCodeSem H c → LevelSubstOK H n c := by
  intro n
  induction n with
  | zero =>
      intro c hc
      exact ⟨hc, fun r c' e hr he hren => levelSubst_zero H hc hr he hren⟩
  | succ n ih =>
      refine isFormCodeSem_ind' H (LevelSubstOK H (n+1)) (fLevelSubstOKF (n+1))
        (envLevelSubst H) (fun y => (fLevelSubstOKF_spec H (n+1) y).symm)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · intro i j hi hj
        refine ⟨isFormCodeSem_memAtom H hi hj, fun r c' e hr he hren => ?_⟩
        have hri := isVarMap_apply H hr hi
        have hrj := isVarMap_apply H hr hj
        have hce := compV_isUnivEnv H he hr
        rw [renames_memAtom_inv H hren]
        constructor
        · rw [sigmaTrue_memAtom H (n+1) hri hrj he,
              sigmaTrue_memAtom H (n+1) hi hj hce,
              compV_applyU H he hr hi, compV_applyU H he hr hj]
        · rw [piFalse_memAtom H (n+1) hri hrj he,
              piFalse_memAtom H (n+1) hi hj hce,
              compV_applyU H he hr hi, compV_applyU H he hr hj]
      · intro i j hi hj
        refine ⟨isFormCodeSem_eqAtom H hi hj, fun r c' e hr he hren => ?_⟩
        have hri := isVarMap_apply H hr hi
        have hrj := isVarMap_apply H hr hj
        have hce := compV_isUnivEnv H he hr
        rw [renames_eqAtom_inv H hren]
        constructor
        · rw [sigmaTrue_eqAtom H (n+1) hri hrj he,
              sigmaTrue_eqAtom H (n+1) hi hj hce,
              compV_applyU H he hr hi, compV_applyU H he hr hj]
        · rw [piFalse_eqAtom H (n+1) hri hrj he,
              piFalse_eqAtom H (n+1) hi hj hce,
              compV_applyU H he hr hi, compV_applyU H he hr hj]
      · refine ⟨isFormCodeSem_bot H, fun r c' e hr he hren => ?_⟩
        have hce := compV_isUnivEnv H he hr
        rw [renames_bot_inv H hren]
        exact ⟨⟨fun h => absurd h (sigmaTrue_bot H (n+1)),
            fun h => absurd h (sigmaTrue_bot H (n+1))⟩,
          ⟨fun _ => piFalse_bot H (n+1) hce, fun _ => piFalse_bot H (n+1) he⟩⟩
      · intro a b ha hb
        refine ⟨isFormCodeSem_imp H ha.1 hb.1, fun r c' e hr he hren => ?_⟩
        obtain ⟨a', b', hc', k1, k2⟩ := renames_imp_inv H hren
        have ha' := renames_isFormCodeSem H ha.1 hr k1
        have hb' := renames_isFormCodeSem H hb.1 hr k2
        obtain ⟨s1, p1⟩ := ha.2 r a' e hr he k1
        obtain ⟨s2, p2⟩ := hb.2 r b' e hr he k2
        have hce := compV_isUnivEnv H he hr
        subst hc'
        constructor
        · rw [sigmaTrue_imp H n ha' hb' he, sigmaTrue_imp H n ha.1 hb.1 hce,
              p1, s2]
        · rw [piFalse_imp H n ha' hb' he, piFalse_imp H n ha.1 hb.1 hce, s1, p2]
      · intro a b ha hb
        refine ⟨isFormCodeSem_and H ha.1 hb.1, fun r c' e hr he hren => ?_⟩
        obtain ⟨a', b', hc', k1, k2⟩ := renames_and_inv H hren
        have ha' := renames_isFormCodeSem H ha.1 hr k1
        have hb' := renames_isFormCodeSem H hb.1 hr k2
        obtain ⟨s1, p1⟩ := ha.2 r a' e hr he k1
        obtain ⟨s2, p2⟩ := hb.2 r b' e hr he k2
        have hce := compV_isUnivEnv H he hr
        subst hc'
        constructor
        · rw [sigmaTrue_and H n ha' hb' he, sigmaTrue_and H n ha.1 hb.1 hce,
              s1, s2]
        · rw [piFalse_and H n ha' hb' he, piFalse_and H n ha.1 hb.1 hce, p1, p2]
      · intro a b ha hb
        refine ⟨isFormCodeSem_or H ha.1 hb.1, fun r c' e hr he hren => ?_⟩
        obtain ⟨a', b', hc', k1, k2⟩ := renames_or_inv H hren
        have ha' := renames_isFormCodeSem H ha.1 hr k1
        have hb' := renames_isFormCodeSem H hb.1 hr k2
        obtain ⟨s1, p1⟩ := ha.2 r a' e hr he k1
        obtain ⟨s2, p2⟩ := hb.2 r b' e hr he k2
        have hce := compV_isUnivEnv H he hr
        subst hc'
        constructor
        · rw [sigmaTrue_or H n ha' hb' he, sigmaTrue_or H n ha.1 hb.1 hce,
              s1, s2]
        · rw [piFalse_or H n ha' hb' he, piFalse_or H n ha.1 hb.1 hce, p1, p2]
      · intro a ha
        have hallc : IsFormCodeSem H (kpair H (natV H 6) a) :=
          isFormCodeSem_all H ha.1
        refine ⟨hallc, fun r c' e hr he hren => ?_⟩
        obtain ⟨a', hc', k⟩ := renames_all_inv H hren
        have hce := compV_isUnivEnv H he hr
        subst hc'
        have hprev := (ih _ hallc).2 r (kpair H (natV H 6) a') e hr he hren
        refine ⟨?_, ?_⟩
        · constructor
          · intro h
            rcases sigmaTrue_all_inv H n h with hesc | ⟨hb, hp⟩
            · exact sigmaTrue_mono H (Nat.le_succ n) hce (hprev.1.mp hesc)
            · refine sigmaTrue_all_of_piTrue H n hce
                ((piBounded_renames_iff H hallc hr hren).mpr hb) ?_
              exact fun hf => hp (hprev.2.mpr hf)
          · intro h
            rcases sigmaTrue_all_inv H n h with hesc | ⟨hb, hp⟩
            · exact sigmaTrue_mono H (Nat.le_succ n) he (hprev.1.mpr hesc)
            · refine sigmaTrue_all_of_piTrue H n he
                ((piBounded_renames_iff H hallc hr hren).mp hb) ?_
              exact fun hf => hp (hprev.2.mp hf)
        · constructor
          · intro h
            obtain ⟨d, hd⟩ := piFalse_all_elim H (n+1) he h
            refine piFalse_all_intro H n hce (d := d) ?_
            have hstep := (ha.2 (upV H r) a' (econs H d e) (upV_isVarMap H hr)
              (econs_isUnivEnv H he d) k).2.mp hd
            rwa [compV_econs_upVU H he hr d] at hstep
          · intro h
            obtain ⟨d, hd⟩ := piFalse_all_elim H (n+1) hce h
            refine piFalse_all_intro H n he (d := d) ?_
            refine (ha.2 (upV H r) a' (econs H d e) (upV_isVarMap H hr)
              (econs_isUnivEnv H he d) k).2.mpr ?_
            rw [compV_econs_upVU H he hr d]
            exact hd
      · intro a ha
        have hexc : IsFormCodeSem H (kpair H (natV H 7) a) :=
          isFormCodeSem_ex H ha.1
        refine ⟨hexc, fun r c' e hr he hren => ?_⟩
        obtain ⟨a', hc', k⟩ := renames_ex_inv H hren
        have hce := compV_isUnivEnv H he hr
        subst hc'
        have hprev := (ih _ hexc).2 r (kpair H (natV H 7) a') e hr he hren
        refine ⟨?_, ?_⟩
        · rw [sigmaTrue_ex H n he, sigmaTrue_ex H n hce]
          constructor
          · rintro ⟨d, hd⟩
            refine ⟨d, ?_⟩
            have hstep := (ha.2 (upV H r) a' (econs H d e) (upV_isVarMap H hr)
              (econs_isUnivEnv H he d) k).1.mp hd
            rwa [compV_econs_upVU H he hr d] at hstep
          · rintro ⟨d, hd⟩
            refine ⟨d, (ha.2 (upV H r) a' (econs H d e) (upV_isVarMap H hr)
              (econs_isUnivEnv H he d) k).1.mpr ?_⟩
            rw [compV_econs_upVU H he hr d]
            exact hd
        · constructor
          · intro h
            rcases piFalse_ex_inv H n h with hesc | ⟨hb, hp⟩
            · exact piFalse_mono H (Nat.le_succ n) hce (hprev.2.mp hesc)
            · refine piFalse_ex_of_not_sigmaTrue H n hce
                ((sigmaBounded_renames_iff H hexc hr hren).mpr hb) ?_
              exact fun hs => hp (hprev.1.mpr hs)
          · intro h
            rcases piFalse_ex_inv H n h with hesc | ⟨hb, hp⟩
            · exact piFalse_mono H (Nat.le_succ n) he (hprev.2.mpr hesc)
            · refine piFalse_ex_of_not_sigmaTrue H n he
                ((sigmaBounded_renames_iff H hexc hr hren).mp hb) ?_
              exact fun hs => hp (hprev.1.mp hs)

/-! ### The substitution lemma, and the instances the calculus consumes -/

/-- **The substitution lemma on the Sigma side.**  Sigma-truth of a renamed code
under an environment is Sigma-truth of the original under the composed
environment, at every level. -/
theorem sigmaTrue_renames (H : ZFAxioms mem) (n : Nat) {c c' r e : V}
    (hc : IsFormCodeSem H c) (hr : IsVarMap H r) (he : IsUnivEnv H e)
    (hren : Renames H r c c') :
    SigmaTrue H n c' e ↔ SigmaTrue H n c (compV H e r) :=
  ((levelSubstOK_of_isFormCodeSem H n c hc).2 r c' e hr he hren).1

/-- **The substitution lemma on the Pi side.** -/
theorem piFalse_renames (H : ZFAxioms mem) (n : Nat) {c c' r e : V}
    (hc : IsFormCodeSem H c) (hr : IsVarMap H r) (he : IsUnivEnv H e)
    (hren : Renames H r c c') :
    PiFalse H n c' e ↔ PiFalse H n c (compV H e r) :=
  ((levelSubstOK_of_isFormCodeSem H n c hc).2 r c' e hr he hren).2

/-- The Pi side stated on the true side. -/
theorem piTrue_renames (H : ZFAxioms mem) (n : Nat) {c c' r e : V}
    (hc : IsFormCodeSem H c) (hr : IsVarMap H r) (he : IsUnivEnv H e)
    (hren : Renames H r c c') :
    PiTrue H n c' e ↔ PiTrue H n c (compV H e r) :=
  not_congr (piFalse_renames H n hc hr he hren)

/-- The substitution lemma in operator form, Sigma side. -/
theorem sigmaTrue_renameV (H : ZFAxioms mem) (n : Nat) {c r e : V}
    (hc : IsFormCodeSem H c) (hr : IsVarMap H r) (he : IsUnivEnv H e) :
    SigmaTrue H n (renameV H r c) e ↔ SigmaTrue H n c (compV H e r) :=
  sigmaTrue_renames H n hc hr he (renames_renameV H hc hr)

/-- The substitution lemma in operator form, Pi side. -/
theorem piFalse_renameV (H : ZFAxioms mem) (n : Nat) {c r e : V}
    (hc : IsFormCodeSem H c) (hr : IsVarMap H r) (he : IsUnivEnv H e) :
    PiFalse H n (renameV H r c) e ↔ PiFalse H n c (compV H e r) :=
  piFalse_renames H n hc hr he (renames_renameV H hc hr)

/-- **The successor shift on the Sigma side.**  Renaming along the internal
successor map makes a code indifferent to the newly bound slot.  This is what the
eigenvariable rules `P_allI` and `P_exE` need. -/
theorem sigmaTrue_renameV_succMap (H : ZFAxioms mem) (n : Nat) {c e d : V}
    (hc : IsFormCodeSem H c) (he : IsUnivEnv H e) :
    SigmaTrue H n (renameV H (succMap H) c) (econs H d e) ↔
      SigmaTrue H n c e := by
  rw [sigmaTrue_renameV H n hc (succMap_isVarMap H) (econs_isUnivEnv H he d),
      compV_succMapU H he d]

/-- **The successor shift on the Pi side.** -/
theorem piFalse_renameV_succMap (H : ZFAxioms mem) (n : Nat) {c e d : V}
    (hc : IsFormCodeSem H c) (he : IsUnivEnv H e) :
    PiFalse H n (renameV H (succMap H) c) (econs H d e) ↔ PiFalse H n c e := by
  rw [piFalse_renameV H n hc (succMap_isVarMap H) (econs_isUnivEnv H he d),
      compV_succMapU H he d]

/-- **Instantiation at a variable, Sigma side.**  Renaming along the internal
instantiation map at the index `k` is evaluation with the binder filled by the
environment's value at `k`.  This is what `P_allE`, `P_exI` and `P_eqElim`
need. -/
theorem sigmaTrue_renameV_instMap (H : ZFAxioms mem) (n : Nat) {c e k : V}
    (hc : IsFormCodeSem H c) (he : IsUnivEnv H e) (hk : mem k (omegaV H)) :
    SigmaTrue H n (renameV H (instMap H k) c) e ↔
      SigmaTrue H n c (econs H (applyV H e k) e) := by
  rw [sigmaTrue_renameV H n hc (instMap_isVarMap H hk) he, compV_instMapU H he hk]

/-- **Instantiation at a variable, Pi side.** -/
theorem piFalse_renameV_instMap (H : ZFAxioms mem) (n : Nat) {c e k : V}
    (hc : IsFormCodeSem H c) (he : IsUnivEnv H e) (hk : mem k (omegaV H)) :
    PiFalse H n (renameV H (instMap H k) c) e ↔
      PiFalse H n c (econs H (applyV H e k) e) := by
  rw [piFalse_renameV H n hc (instMap_isVarMap H hk) he, compV_instMapU H he hk]

/-! ## The shape of fixed-level soundness

What follows is *stated* and not proved.  Each statement is a `Prop`-valued
definition, so that the remaining obligations are named objects rather than
prose, and so that nothing here can be mistaken for a theorem.

The level is `n+1` when the derivation's occurrences are bounded by the numeral
of `n`.  That is the level at which both polarities of every occurring code are
available: a universal code of Sigma-rank at most `n+1` is Pi-bounded at `n`, an
existential code of Pi-rank at most `n+1` is Sigma-bounded at `n`, and those two
guards are exactly what the polarity-switch rows of
`BoundedZFCConsistency.UniverseTruthLevel` require. -/

/-- Level-`n+1` truth of a code, on both polarities.  Only the Sigma side is
certified positively; the Pi side is the absence of a certificate. -/
def LevelTrue (H : ZFAxioms mem) (n : Nat) (c e : V) : Prop :=
  SigmaTrue H (n+1) c e ∧ PiTrue H (n+1) c e

/-- Every member of the coded context is true at level `n+1`. -/
def CtxLevelTrue (H : ZFAxioms mem) (n : Nat) (g e : V) : Prop :=
  ∀ x, MemCtx H x g → LevelTrue H n x e

/-- **The axiom-truth premise.**  This is the statement in which the content of
the ZFC axioms finally enters, and it is the only one of the remaining
obligations that is about the axioms rather than about the truth hierarchy.

Every internal ZFC axiom code whose quantifier complexity is bounded by the
numeral of `n` is true at level `n+1`, at every universe environment, on both
polarities.  The quantification over codes is internal, so it covers the
nonstandard Separation and Replacement instances that
`BoundedZFCConsistency.AxiomCode` deliberately admits — the internal axiom set is
properly larger than the quotations of the external one, and a bounded coded
derivation may cite any of it.

Nothing in this module discharges it. -/
def AxiomCodesTrueAt (H : ZFAxioms mem) (n : Nat) : Prop :=
  ∀ c E, IsZFCAxiomCode H c → QuantBounded H (natV H n) c → IsUnivEnv H E →
    LevelTrue H n c E

/-- **The two-valuedness obligation.**  At level zero the two polarities are the
two readings of one bit, so `sigmaTrue_not_piFalse_zero` and `piTrue_zero_iff`
settle both halves.  At a positive level neither half is available: exclusivity
is a code induction that
`BoundedZFCConsistency.UniverseTruthLevel` states only for level zero, and
completeness follows from the level-collapse theorem, which is open.

The statement is restricted to the codes a bounded derivation can mention,
because that is all soundness consumes and because the guards of the polarity
switch are unavailable without the bound. -/
def LevelTwoValuedAt (H : ZFAxioms mem) (n : Nat) : Prop :=
  ∀ c E, IsFormCodeSem H c → QuantBounded H (natV H n) c → IsUnivEnv H E →
    (SigmaTrue H (n+1) c E ↔ PiTrue H (n+1) c E)

/-- **Fixed-level soundness of the coded calculus**, as a statement.

A coded derivation all of whose occurrences are bounded by the numeral of `n`
transports level-`n+1` truth of every context member to level-`n+1` truth of the
conclusion.  The induction is the strong one over the derivation's internal rank,
exactly as `soundAt_step` and `derives_sound` do it for a set structure, and the
five rules that move a formula across a binder read the substitution lemmas of
this module instead of those of
`BoundedZFCConsistency.InternalSoundness`.

This is **not proved here**.  The obstruction is a single rule and a single
missing fact: implication elimination has `SigmaTrue H (n+1) (imp a b) E` and
`SigmaTrue H (n+1) a E`, and `sigmaTrue_imp` turns the first into
`PiFalse H (n+1) a E ∨ SigmaTrue H (n+1) b E`, whose left disjunct is discharged
only by `LevelTwoValuedAt`.  Reading truth as `PiTrue` instead moves the same
obligation to the other side of the same rule, and reading it as the conjunction
`LevelTrue` moves it to disjunction elimination.  No formulation of the rule
avoids it. -/
def LevelSoundnessAt (H : ZFAxioms mem) (n : Nat) : Prop :=
  ∀ d g c E, DerAllBounded H (natV H n) d → Derives H d g c → IsUnivEnv H E →
    CtxLevelTrue H n g E → LevelTrue H n c E

/-- No bounded coded derivation of falsity from a context of internal ZFC axiom
codes.  This is the semantic obligation
`zfcprov_conZFCForm_of_no_bounded_refutation` consumes, spelled for a single
model. -/
def NoBoundedRefutationAtLevel (H : ZFAxioms mem) (n : Nat) : Prop :=
  ¬ ∃ d g, CtxZFCAxioms H g ∧
    Derives H d g (kpair H (natV H 2) (vempty H)) ∧
    DerAllBounded H (natV H n) d

/-- **The falsity corollary.**  Fixed-level soundness together with the
axiom-truth premise rules out a bounded coded refutation, because falsity is
Sigma-true at no level.

The context of such a derivation is recorded by the certificate, so the
every-occurrence bound bounds each of its members, and the axiom-truth premise
applies to each; soundness then makes the falsity code true at level `n+1`, which
`sigmaTrue_bot` forbids.  The environment is supplied by `exists_isUnivEnv`,
which needs no nonemptiness hypothesis: the universe always contains the empty
set. -/
theorem noBoundedRefutation_of_levelSoundness (H : ZFAxioms mem) (n : Nat)
    (hax : AxiomCodesTrueAt H n) (hsound : LevelSoundnessAt H n) :
    NoBoundedRefutationAtLevel H n := by
  rintro ⟨d, g, hg, hder, hbnd⟩
  obtain ⟨E, hE⟩ := exists_isUnivEnv H
  have hctx : CtxLevelTrue H n g E := by
    obtain ⟨-, m, -, hmem⟩ := hder
    intro x hx
    exact hax x E (hg x hx) ((hbnd m g _ hmem).2 x hx) hE
  exact sigmaTrue_bot H (n+1)
    (hsound d g (kpair H (natV H 2) (vempty H)) E hbnd hder hE hctx).1

end LevelSoundness

end BoundedZFCConsistency
end LeanProofs
