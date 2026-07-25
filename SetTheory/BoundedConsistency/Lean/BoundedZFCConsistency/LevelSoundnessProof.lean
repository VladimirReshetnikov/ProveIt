import BoundedZFCConsistency.LevelCollapse

/-!
# Fixed-level soundness of the coded calculus

`BoundedZFCConsistency.LevelSoundness` names three obligations and proves the
substitution lemmas the first of them consumes.  This module discharges that
first obligation: `LevelSoundnessAt`, the statement that a coded derivation all
of whose occurrences are bounded by the numeral of `n` transports level-`n+1`
truth from its context to its conclusion.

The argument is the strong induction over the derivation's internal rank that
`BoundedZFCConsistency.CodedDerivation` runs for a set structure with `SatIn`,
with three substitutions.  `SatIn` is replaced by `LevelTrue H n`, truth on both
polarities at level `n+1`.  The Tarski clauses come from
`BoundedZFCConsistency.UniverseTruthLevel` and the polarity switches from
`BoundedZFCConsistency.LevelCollapse`.  And the five rules that move a formula
across a binder read the fixed-level substitution lemmas rather than the
set-structure ones.

## One polarity suffices

Level-`n+1` truth is the conjunction of Sigma-truth and Pi-truth, and both
halves have to be carried: the Sigma clause of an implication offers Pi-falsity
of the antecedent, and the Pi clause offers Sigma-truth of it.  But at a
*conclusion* the two halves are interchangeable, because a coded derivation
records only codes and the every-occurrence bound bounds every conclusion:
exclusivity turns Sigma-truth into Pi-truth with no bound at all, and totality
turns Pi-truth back into Sigma-truth under the bound.  Sixteen of the seventeen
cases therefore establish Sigma-truth of the conclusion and read Pi-truth off
it; universal introduction goes the other way, since the universal head is
recorded on the Pi side and delegated on the Sigma side.

That is also where two-valuedness is load-bearing rather than convenient.
Implication elimination has to discharge Pi-falsity of the antecedent against
Sigma-truth of it, and disjunction elimination has to turn Sigma-truth of a
recorded disjunct into the full level truth its subderivation's context asks
for.  Both are instances of `sigmaTrue_iff_piTrue`, applied to a *rule
parameter* rather than to the conclusion — which is exactly what
`DerStepBounded` makes available, by carrying the bound on every formula-valued
parameter and not merely on the conclusion.

## The rank induction is internal

The rank of a coded derivation is an element of the model's omega and may be
nonstandard, so the induction on it is the definability-relative one over
internal omega, exactly as in `CodedDerivation.soundBelow`.  The property it
carries — soundness at every rank strictly below the induction variable — is
therefore assembled as a `Form`, from the already rendered `fSigmaTrueF`,
`fPiTrueF`, `fMemCtxF`, `fTripleMemF` and `fUnivEnvF`.  The level `n` is a
metatheoretic argument of that assembly and never a de Bruijn slot.

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

section LevelSoundnessProof

variable {V : Type u} {mem : V → V → Prop}

/-! ## Reading one polarity off the other

Both directions are about a code, and only one of them needs the bound.
Exclusivity is `sigmaTrue_not_piFalse`, which holds at every code and every
level; totality is `sigmaTrue_or_piFalse`, which is available exactly at the
level above a bound. -/

/-- **Sigma-truth of a code is level truth.**  No bound is needed: the Pi half is
exclusivity. -/
theorem levelTrue_of_sigmaTrue (H : ZFAxioms mem) (n : Nat) {c E : V}
    (hc : IsFormCodeSem H c) (hE : IsUnivEnv H E)
    (h : SigmaTrue H (n+1) c E) : LevelTrue H n c E :=
  ⟨h, piTrue_of_sigmaTrue H (n+1) hc hE h⟩

/-- **Pi-truth of a bounded code is level truth.**  Here the bound is needed: the
Sigma half is totality. -/
theorem levelTrue_of_piTrue (H : ZFAxioms mem) (n : Nat) {c E : V}
    (hc : IsFormCodeSem H c) (hq : QuantBounded H (natV H n) c)
    (hE : IsUnivEnv H E) (h : PiTrue H (n+1) c E) : LevelTrue H n c E :=
  ⟨(sigmaTrue_iff_piTrue H n hc hq hE).mpr h, h⟩

/-- **Level truth is decided on bounded codes.**  A code that is not true at the
level is Pi-false there. -/
theorem piFalse_of_not_levelTrue (H : ZFAxioms mem) (n : Nat) {c E : V}
    (hc : IsFormCodeSem H c) (hq : QuantBounded H (natV H n) c)
    (hE : IsUnivEnv H E) (h : ¬ LevelTrue H n c E) : PiFalse H (n+1) c E := by
  rcases sigmaTrue_or_piFalse H n hc hq hE with hs | hp
  · exact absurd (levelTrue_of_sigmaTrue H n hc hE hs) h
  · exact hp

/-! ## Coded contexts at a fixed level

The two operations soundness performs on a context are the ones the calculus
performs: extending it by a formula an introduction rule discharges, and shifting
it across a binder at an eigenvariable rule. -/

/-- Extending a level-true context by a level-true formula. -/
theorem ctxLevelTrue_cons (H : ZFAxioms mem) (n : Nat) {g E a : V}
    (hg : CtxLevelTrue H n g E) (ha : LevelTrue H n a E) :
    CtxLevelTrue H n (ctxCons H a g) E := by
  intro x hx
  rcases memCtx_cons_inv H hx with rfl | hx
  · exact ha
  · exact hg x hx

/-- **The eigenvariable transfer at a fixed level.**  A successor shift of a
level-true context is level-true at the shifted environment: each of its members
is the successor renaming of a coded member of the original, and the fixed-level
substitution lemmas turn truth at `E` into truth at `econs H d E` through
`compV_succMapU`.

This is the analogue of `CodedDerivation.ctxSat_shift`, and like it, it needs
codehood of the *source* member, which `ShiftsCtx` carries because membership in
a coded context has no descent principle. -/
theorem ctxLevelTrue_shift (H : ZFAxioms mem) (n : Nat) {g g' E d : V}
    (hsh : ShiftsCtx H g g') (hE : IsUnivEnv H E)
    (hg : CtxLevelTrue H n g E) : CtxLevelTrue H n g' (econs H d E) := by
  intro x' hx'
  obtain ⟨x, hxc, hxm, hren⟩ := hsh x' hx'
  have hs := sigmaTrue_renames H (n+1) hxc (succMap_isVarMap H)
    (econs_isUnivEnv H hE d) hren
  have hp := piFalse_renames H (n+1) hxc (succMap_isVarMap H)
    (econs_isUnivEnv H hE d) hren
  rw [compV_succMapU H hE d] at hs hp
  obtain ⟨k1, k2⟩ := hg x hxm
  exact ⟨hs.mpr k1, fun hf => k2 (hp.mp hf)⟩

/-! ## Soundness at a single internal rank

The certificate and the level are fixed; the rank is the induction variable.
The bound on the certificate is not part of this property — it is a hypothesis of
the step, exactly as closure is. -/

/-- The certificate `D` is sound at the internal rank `m`, for level `n+1`
truth. -/
def LevelSoundAt (H : ZFAxioms mem) (n : Nat) (D m : V) : Prop :=
  ∀ g c E, mem (satTriple H m g c) D → IsUnivEnv H E →
    CtxLevelTrue H n g E → LevelTrue H n c E

/-! ### The property as a `Form`

Nothing here unfolds a rendered macro: each proof goes through the spec of its
constituents.  The level appears only as the metatheoretic argument `n`, which
selects a different formula for each value. -/

/-- "slot `c_i` is true at level `n+1` at slot `e_i`", on both polarities. -/
def fLevelTrueF (n c_i e_i : Nat) : Form :=
  fAnd (fSigmaTrueF (n+1) c_i e_i) (fPiTrueF (n+1) c_i e_i)

theorem fLevelTrueF_spec (H : ZFAxioms mem) (n : Nat) (ee : Nat → V)
    (c_i e_i : Nat) :
    Sat mem ee (fLevelTrueF n c_i e_i) ↔ LevelTrue H n (ee c_i) (ee e_i) := by
  unfold LevelTrue fLevelTrueF
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(fSigmaTrueF_spec H (n+1) ee c_i e_i).mp h1,
      (fPiTrueF_spec H (n+1) ee c_i e_i).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(fSigmaTrueF_spec H (n+1) ee c_i e_i).mpr h1,
      (fPiTrueF_spec H (n+1) ee c_i e_i).mpr h2⟩

/-- "every member of the context in slot `g_i` is true at level `n+1` at slot
`e_i`".

| de Bruijn slot | contents              |
| -------------- | --------------------- |
| `0`            | the member `x`        |
| `m+1`          | the caller's slot `m` |
-/
def fCtxLevelTrueF (n g_i e_i : Nat) : Form :=
  fAll (fImp (fMemCtxF 0 (g_i+1)) (fLevelTrueF n 0 (e_i+1)))

theorem fCtxLevelTrueF_spec (H : ZFAxioms mem) (n : Nat) (ee : Nat → V)
    (g_i e_i : Nat) :
    Sat mem ee (fCtxLevelTrueF n g_i e_i) ↔
      CtxLevelTrue H n (ee g_i) (ee e_i) := by
  unfold CtxLevelTrue
  constructor
  · intro h x hx
    exact (fLevelTrueF_spec H n (scons x ee) 0 (e_i+1)).mp
      (h x ((fMemCtxF_spec H (scons x ee) 0 (g_i+1)).mpr hx))
  · intro h x hx
    exact (fLevelTrueF_spec H n (scons x ee) 0 (e_i+1)).mpr
      (h x ((fMemCtxF_spec H (scons x ee) 0 (g_i+1)).mp hx))

/-- "the certificate in slot `d_i` is sound at the rank in slot `m_i`, for level
`n+1` truth".

| de Bruijn slot | contents              |
| -------------- | --------------------- |
| `0`            | the environment `E`   |
| `1`            | the conclusion `c`    |
| `2`            | the context `g`       |
| `m+3`          | the caller's slot `m` |
-/
def fLevelSoundAtF (n m_i d_i : Nat) : Form :=
  fAll (fAll (fAll (fImp (fTripleMemF (m_i+3) 2 1 (d_i+3))
    (fImp (fUnivEnvF 0)
      (fImp (fCtxLevelTrueF n 2 0) (fLevelTrueF n 1 0))))))

theorem fLevelSoundAtF_spec (H : ZFAxioms mem) (n : Nat) (ee : Nat → V)
    (m_i d_i : Nat) :
    Sat mem ee (fLevelSoundAtF n m_i d_i) ↔
      LevelSoundAt H n (ee d_i) (ee m_i) := by
  unfold LevelSoundAt
  constructor
  · intro h g c E hmem hE hg
    exact (fLevelTrueF_spec H n (scons E (scons c (scons g ee))) 1 0).mp
      (h g c E
        ((fTripleMemF_spec H (scons E (scons c (scons g ee)))
          (m_i+3) 2 1 (d_i+3)).mpr hmem)
        ((fUnivEnvF_spec H (scons E (scons c (scons g ee))) 0).mpr hE)
        ((fCtxLevelTrueF_spec H n (scons E (scons c (scons g ee))) 2 0).mpr hg))
  · intro h g c E hmem hE hg
    exact (fLevelTrueF_spec H n (scons E (scons c (scons g ee))) 1 0).mpr
      (h g c E
        ((fTripleMemF_spec H (scons E (scons c (scons g ee)))
          (m_i+3) 2 1 (d_i+3)).mp hmem)
        ((fUnivEnvF_spec H (scons E (scons c (scons g ee))) 0).mp hE)
        ((fCtxLevelTrueF_spec H n (scons E (scons c (scons g ee))) 2 0).mp hg))

/-- The parameter block of `fLevelSoundBelowF`: the certificate. -/
def envLevelSound (D : V) : Nat → V := fun _ => D

/-- The property the definable-induction schema carries: soundness at every rank
strictly below the induction variable.

| de Bruijn slot | contents               |
| -------------- | ---------------------- |
| `0`            | the smaller rank `m`   |
| `1`            | the induction variable |
| `2`            | the certificate        |
-/
def fLevelSoundBelowF (n : Nat) : Form :=
  fAll (fImp (fMem 0 1) (fLevelSoundAtF n 0 2))

theorem fLevelSoundBelowF_spec (H : ZFAxioms mem) (n : Nat) (D k : V) :
    Sat mem (scons k (envLevelSound D)) (fLevelSoundBelowF n) ↔
      ∀ m, mem m k → LevelSoundAt H n D m := by
  constructor
  · intro h m hm
    exact (fLevelSoundAtF_spec H n (scons m (scons k (envLevelSound D)))
      0 2).mp (h m hm)
  · intro h m hm
    exact (fLevelSoundAtF_spec H n (scons m (scons k (envLevelSound D)))
      0 2).mpr (h m hm)

/-! ## The seventeen cases

Given soundness at every rank below `m`, the certificate is sound at `m`.  This
is `CodedDerivation.soundAt_step` with `SatIn` replaced by `LevelTrue H n`.

The bound enters through `derStepBounded_of_derAllBounded`, which reads the rule
that justifies the node with every formula-valued parameter bounded.  Only four
cases consume a parameter bound — the two rules that case-split on a parameter
and the two that convert a parameter's Pi-truth into Sigma-truth — but none of
them could be done without it, since a rule parameter need not occur in the
conclusion at all. -/

/-- **Fixed-level soundness at one internal rank**, given soundness below it. -/
theorem levelSoundAt_step (H : ZFAxioms mem) (n : Nat) {D : V}
    (hD : DerClosed H D) (hb : DerAllBounded H (natV H n) D) {m : V}
    (ih : ∀ k, mem k m → LevelSoundAt H n D k) : LevelSoundAt H n D m := by
  intro g c E hmem hE hg
  obtain ⟨-, hc, hstep⟩ := hD m g c hmem
  have hbo : mem (natV H n) (omegaV H) := natV_mem_omega H n
  have hcq : QuantBounded H (natV H n) c := (hb m g c hmem).1
  have hstepB : DerStepBounded H (natV H n) D m g c :=
    derStepBounded_of_derAllBounded H hbo hb hmem hstep
  have use : ∀ g' c' E', DerCite H D m g' c' → IsUnivEnv H E' →
      CtxLevelTrue H n g' E' → LevelTrue H n c' E' := by
    rintro g' c' E' ⟨k, hk, hkm⟩ hE' hg'
    exact ih k hk g' c' E' hkm hE' hg'
  have code : ∀ g' c', DerCite H D m g' c' → IsFormCodeSem H c' := by
    rintro g' c' ⟨k, hk, hkm⟩
    exact (hD k g' c' hkm).2.1
  rcases hstepB with h | ⟨a, b, ha, haq, -, hce, h1⟩ | ⟨a, ha, -, h1, h2⟩ | h |
    ⟨a, ha, haq, hce⟩ | ⟨a, b, -, -, hce, h1, h2⟩ | ⟨b, hbc, -, h1⟩ |
    ⟨a, ha, -, h1⟩ | ⟨a, b, ha, hbc, -, -, hce, h1⟩ |
    ⟨a, b, ha, hbc, -, -, hce, h1⟩ | ⟨a, b, ha, hbc, -, -, h1, h2, h3⟩ |
    ⟨a, g', ha, -, hce, hsh, h1⟩ | ⟨a, k, ha, haq, hk, hren, h1⟩ |
    ⟨a, k, a', ha, -, -, hk, hce, hren, h1⟩ |
    ⟨a, g', c', ha, -, -, hsh, hren, h1, h2⟩ | ⟨k, hk, hce⟩ |
    ⟨i, j, a, ci, hi, hj, ha, -, -, hren1, hren2, h1, h2⟩
  · -- assumption
    exact hg c h
  · -- implication introduction
    subst hce
    refine levelTrue_of_sigmaTrue H n hc hE ?_
    rw [sigmaTrue_imp H n ha (code _ _ h1) hE]
    rcases sigmaTrue_or_piFalse H n ha haq hE with hs | hp
    · exact Or.inr (use _ b E h1 hE
        (ctxLevelTrue_cons H n hg (levelTrue_of_sigmaTrue H n ha hE hs))).1
    · exact Or.inl hp
  · -- implication elimination
    have s1 := (use g _ E h1 hE hg).1
    rw [sigmaTrue_imp H n ha hc hE] at s1
    rcases s1 with hp | hs
    · exact absurd hp (use g a E h2 hE hg).2
    · exact levelTrue_of_sigmaTrue H n hc hE hs
  · -- ex falso
    exact absurd (use g _ E h hE hg).1 (sigmaTrue_bot H (n+1))
  · -- excluded middle
    subst hce
    refine levelTrue_of_sigmaTrue H n hc hE ?_
    rw [sigmaTrue_or H n ha (isFormCodeSem_imp H ha (isFormCodeSem_bot H)) hE]
    rcases sigmaTrue_or_piFalse H n ha haq hE with hs | hp
    · exact Or.inl hs
    · exact Or.inr (sigmaTrue_imp_intro H n hE (Or.inl hp))
  · -- conjunction introduction
    subst hce
    refine levelTrue_of_sigmaTrue H n hc hE ?_
    rw [sigmaTrue_and H n (code _ _ h1) (code _ _ h2) hE]
    exact ⟨(use g a E h1 hE hg).1, (use g b E h2 hE hg).1⟩
  · -- first conjunction elimination
    have s := (use g _ E h1 hE hg).1
    rw [sigmaTrue_and H n hc hbc hE] at s
    exact levelTrue_of_sigmaTrue H n hc hE s.1
  · -- second conjunction elimination
    have s := (use g _ E h1 hE hg).1
    rw [sigmaTrue_and H n ha hc hE] at s
    exact levelTrue_of_sigmaTrue H n hc hE s.2
  · -- first disjunction introduction
    subst hce
    refine levelTrue_of_sigmaTrue H n hc hE ?_
    rw [sigmaTrue_or H n ha hbc hE]
    exact Or.inl (use g a E h1 hE hg).1
  · -- second disjunction introduction
    subst hce
    refine levelTrue_of_sigmaTrue H n hc hE ?_
    rw [sigmaTrue_or H n ha hbc hE]
    exact Or.inr (use g b E h1 hE hg).1
  · -- disjunction elimination
    have s := (use g _ E h1 hE hg).1
    rw [sigmaTrue_or H n ha hbc hE] at s
    rcases s with s | s
    · exact use _ c E h2 hE
        (ctxLevelTrue_cons H n hg (levelTrue_of_sigmaTrue H n ha hE s))
    · exact use _ c E h3 hE
        (ctxLevelTrue_cons H n hg (levelTrue_of_sigmaTrue H n hbc hE s))
  · -- universal introduction
    subst hce
    refine levelTrue_of_piTrue H n hc hcq hE ?_
    rw [piTrue_all H n hE]
    intro d
    exact (use g' a (econs H d E) h1 (econs_isUnivEnv H hE d)
      (ctxLevelTrue_shift H n hsh hE hg)).2
  · -- universal elimination
    have s := (use g _ E h1 hE hg).2
    rw [piTrue_all H n hE] at s
    refine levelTrue_of_sigmaTrue H n hc hE ?_
    rw [sigmaTrue_renames H (n+1) ha (instMap_isVarMap H hk) hE hren,
        compV_instMapU H hE hk]
    exact (sigmaTrue_iff_piTrue H n ha haq
      (econs_isUnivEnv H hE (applyV H E k))).mpr (s (applyV H E k))
  · -- existential introduction
    subst hce
    have s := (use g a' E h1 hE hg).1
    rw [sigmaTrue_renames H (n+1) ha (instMap_isVarMap H hk) hE hren,
        compV_instMapU H hE hk] at s
    refine levelTrue_of_sigmaTrue H n hc hE ?_
    rw [sigmaTrue_ex H n hE]
    exact ⟨applyV H E k, s⟩
  · -- existential elimination
    have s := (use g _ E h1 hE hg).1
    rw [sigmaTrue_ex H n hE] at s
    obtain ⟨d, hd⟩ := s
    have hEd : IsUnivEnv H (econs H d E) := econs_isUnivEnv H hE d
    have hbody := use _ c' (econs H d E) h2 hEd
      (ctxLevelTrue_cons H n (ctxLevelTrue_shift H n hsh hE hg)
        (levelTrue_of_sigmaTrue H n ha hEd hd))
    have hiff := sigmaTrue_renames H (n+1) hc (succMap_isVarMap H) hEd hren
    rw [compV_succMapU H hE d] at hiff
    exact levelTrue_of_sigmaTrue H n hc hE (hiff.mp hbody.1)
  · -- reflexivity of equality
    subst hce
    exact levelTrue_of_sigmaTrue H n hc hE
      ((sigmaTrue_eqAtom H (n+1) hk hk hE).mpr rfl)
  · -- the Leibniz rule
    have seq := (use g _ E h1 hE hg).1
    rw [sigmaTrue_eqAtom H (n+1) hi hj hE] at seq
    have sci := (use g ci E h2 hE hg).1
    rw [sigmaTrue_renames H (n+1) ha (instMap_isVarMap H hi) hE hren1,
        compV_instMapU H hE hi] at sci
    refine levelTrue_of_sigmaTrue H n hc hE ?_
    rw [sigmaTrue_renames H (n+1) ha (instMap_isVarMap H hj) hE hren2,
        compV_instMapU H hE hj, ← seq]
    exact sci

/-! ## The induction on the internal rank

The rank of a coded derivation is an element of the model's omega, so the
induction is the definable one over internal omega and the property it carries is
the assembled `Form` above.  The strong form is what a citation at a strictly
smaller rank needs, and it is the whole content of the ranking. -/

/-- **Soundness at every rank below a given internal natural.**  This is the form
the definable-induction schema proves; the successor step is a single application
of `levelSoundAt_step`. -/
theorem levelSoundBelow (H : ZFAxioms mem) (n : Nat) {D : V}
    (hD : DerClosed H D) (hb : DerAllBounded H (natV H n) D) :
    ∀ k, mem k (omegaV H) → ∀ m, mem m k → LevelSoundAt H n D m := by
  intro k hk
  refine (fLevelSoundBelowF_spec H n D k).mp ?_
  refine omega_ind H (fLevelSoundBelowF n) (envLevelSound D) ?_ ?_ k hk
  · refine (fLevelSoundBelowF_spec H n D (vempty H)).mpr (fun m hm => ?_)
    exact absurd hm (vempty_spec H m)
  · intro j hj hbelow
    have hbl := (fLevelSoundBelowF_spec H n D j).mp hbelow
    refine (fLevelSoundBelowF_spec H n D (vsucc H j)).mpr (fun m hm => ?_)
    rcases (vsucc_spec H j m).mp hm with hm | rfl
    · exact hbl m hm
    · exact levelSoundAt_step H n hD hb hbl

/-- Soundness at every rank of a bounded certificate. -/
theorem levelSoundAt_all (H : ZFAxioms mem) (n : Nat) {D : V}
    (hD : DerClosed H D) (hb : DerAllBounded H (natV H n) D) :
    ∀ k, mem k (omegaV H) → LevelSoundAt H n D k :=
  fun k hk =>
    levelSoundBelow H n hD hb (vsucc H k) (omega_succ H k hk) k (vsucc_self H k)

/-- **Fixed-level soundness of the coded calculus**, discharging the obligation
`BoundedZFCConsistency.LevelSoundness.LevelSoundnessAt`.

A coded derivation all of whose occurrences are bounded by the numeral of `n`
transports level-`n+1` truth of every context member to level-`n+1` truth of the
conclusion.  Nothing beyond the truth hierarchy is assumed: the axioms enter only
in the separate obligation `AxiomCodesTrueAt`, and the derivation may cite the
nonstandard axiom codes a nonstandard model contains. -/
theorem levelSoundnessAt (H : ZFAxioms mem) (n : Nat) : LevelSoundnessAt H n := by
  intro d g c E hbnd hder hE hg
  obtain ⟨hD, k, hk, hmem⟩ := hder
  exact levelSoundAt_all H n hD hbnd k hk g c E hmem hE hg

/-- **No bounded coded refutation from the internal ZFC axioms**, given that
those axioms are true at the level.  This is `LevelSoundness`'s falsity corollary
with its soundness premise discharged; the remaining premise is the axiom-truth
statement, which is about the axioms rather than about the hierarchy. -/
theorem noBoundedRefutationAtLevel (H : ZFAxioms mem) (n : Nat)
    (hax : AxiomCodesTrueAt H n) : NoBoundedRefutationAtLevel H n :=
  noBoundedRefutation_of_levelSoundness H n hax (levelSoundnessAt H n)

end LevelSoundnessProof

end BoundedZFCConsistency
end LeanProofs
