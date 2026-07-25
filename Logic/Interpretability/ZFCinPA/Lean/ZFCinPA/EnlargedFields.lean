import ZFCinPA.LocalStepDerivation
import ZFCinPA.TarskiFieldSemantics

/-!
# The enlarged certificate field set, checked semantically

The two field bundles themselves — `TarskiElim`, `TarskiIntro`, the
compound code shapes they are stated over, and their truth of goal 2's
real hierarchy at every level — live one module down, in
`ZFCinPA.TarskiFieldSemantics`, because `ZFCinPA.BaseCertificate` needs
them and sits below the countermodels used here.  Both files share this
namespace, so nothing about the naming changes.

`ZFCinPA.LocalStepDerivation` machine-checked that the **five**-field
successor obligation of `ZFCinPA.StagedSuccessor.ZFCSuccessorImplications`
is *false* relative to `Con(𝗭𝗙𝗖)`: `exclusivity_not_step_transferable`
exhibits a previous level `L` — an arbitrary interpretation of the two
placeholders — satisfying the five fields at level `x+1` for which
exclusivity fails at level `x+2`.

The diagnosis recorded there is that the missing content is the Tarski
**elimination** clauses together with the **adjacent-level collapse**, and
that the fix has to be an enlargement of `ZFCTruthCertificateFields`,
because at level `x+1` the closure relation is an opaque placeholder:
closed sets can be inspected but never constructed.

This module carries out the semantic half of that fix, in goal 2's own
abstract closure vocabulary (`BoundedZFCConsistency.LevelClosed`,
`LevelJustified`, with the previous level an arbitrary ternary relation
`L`), exactly as `exclusivity_not_step_transferable` is stated.  Nothing
here mentions the source language, and nothing here is assumed anywhere
else in the project.

## The enlargement

Two new fields are added to the five:

* **`tarskiElim`** (`EnlargedFields.TarskiElim`) — the six connective
  Tarski elimination clauses at level `x+1` (implication, conjunction,
  disjunction, on both polarities) together with two quantifier
  eliminations in their *strong*, side-condition-free form: Sigma-truth of
  `∀a` yields Sigma-truth of `a` at **every** extension of the
  environment, and dually for Pi-falsity of `∃a`.  Goal-2 counterparts:
  `sigmaTrue_imp_elim`, `piFalse_imp_elim`, `sigmaTrue_and_elim`,
  `piFalse_and_elim`, `sigmaTrue_or_elim`, `piFalse_or_elim`, and — for
  the two quantifier clauses — the composite of `sigmaTrue_all_inv'`,
  `sigmaTrue_or_piFalse` and `piFalse_collapse_le`.
* **`tarskiIntro`** (`EnlargedFields.TarskiIntro`) — Pi-falsity of the
  falsity code (`piFalse_bot`), the six connective introduction clauses,
  and the two quantifier introductions.  These hold *automatically* at any
  closure level — `levelClosed_insert` builds the certificate, see
  `impSigmaIntro_step` — but at an opaque placeholder level they are not
  available, which is exactly why they have to be certified.

The **collapse is not a field**.  Under the enlarged design it is derived,
one level up, from the two new fields and the old decidedness field; that
is the content of `StepGood`'s second and third conjuncts and of
`piFalse_collapse_step`/`sigmaTrue_collapse_step`.

## What is checked here

1. **Both refuting expansions die.**  `expansionA_fails_tarskiIntro` and
   `expansionB_fails_tarskiElim` show that the two definable expansions of
   `LocalStepDerivation`'s module header each violate one of the two new
   fields.  Expansion (A) — closure placeholder empty, so the previous
   level is the empty relation — fails `tarskiIntro` at its very first
   clause.  Expansion (B) — closure placeholder admitting only bit-`0`
   triples, so the previous level decides every code negatively — fails
   `tarskiElim` at the implication row on the Pi side, at the same witness
   `⊥ 🡒 ⊥` that `exclusivity_not_step_transferable` uses.  That (B)
   satisfies the *old* fields is recorded by `expansionB_satisfies_excl`
   and `expansionB_satisfies_decided`: the enlargement, not the old
   antecedent, is what excludes it.
2. **The enlarged set is step-transferable.**  `stepGood_of_levelLaws`
   proves, by one induction on internal formula codes, that the enlarged
   laws at `L` give exclusivity *and* the one-step collapse at the closure
   level over `L`.  The headline corollaries are `exclusivity_step` — the
   field whose five-field version is false — and
   `piFalse_collapse_step`/`sigmaTrue_collapse_step`.

## The two honest costs

* **The induction predicate mentions `L`.**  `StepGood` is not the
  two-set, placeholder-free predicate of `LocalStepDerivation`'s header:
  the collapse conjuncts mention the previous level.  In the source
  template `L` is definable (it is `∃ n C, Num n ∧ Clos n C ∧ ⟨c,e,b⟩ ∈ C`
  over the two placeholders), so the induction is still an instance of
  Separation — but of Separation *for a placeholder formula*, which
  `templateZFC` does not contain.  It is therefore supplied here as the
  explicit hypothesis `CodeInduction`, and downstream it has to be
  discharged after translation, where the placeholder formula has become
  an ordinary (possibly nonstandard) `ℒₛₑₜ` code, by
  `ZFCinPA.SeparationKernel`.  `codeInduction_of_definable` records that
  every `Form`-presented property has it.
* **The bound is an arbitrary internal natural.**  The two goal-2 lemmas
  the quantifier rows consume,
  `piBounded_of_sigmaBounded_all_succ` and
  `sigmaBounded_of_piBounded_ex_succ`, peel a successor off a `vsucc`
  bound at any element of `omegaV`, so the transfer below runs at
  `bnd = b ∈ ω`, `bnd⁺ = vsucc H b` — the shape a nonstandard successor
  step needs, with no external `m` anywhere.  The numeral instance
  `b = natV H m` is `natV_succ`, definitionally.
-/

set_option autoImplicit false

namespace LeanProofs
namespace ZFCinPA
namespace EnlargedFields

open BoundedZFCConsistency
open SetTheory (ZFAxioms vempty vsingle vcup vcup_spec vsingle_spec omegaV
  vsucc omega_succ)

universe u

variable {W : Type u} {mem : W → W → Prop}

local notation "kpair'" => _root_.SetTheory.kpair

/-! ## The two new fields, abstractly

Each clause is stated of an arbitrary ternary relation `L` standing for
level-`x+1` satisfaction, with `L c e (natV H 1)` reading "Sigma-true" and
`L c e (natV H 0)` reading "Pi-false", exactly as the source layer of
`ZFCinPA.SuccessorSources` specializes them. -/

/-- **The enlarged law bundle at one level.**  The two conjuncts of the old
`localStep` and `crossLevel` fields that the transfer consumes, plus the two
new fields.  The old `shiftInvariant`, `substitutionInvariant` and
`axiomSound` fields play no role in the transfer proved here and are
omitted. -/
structure LevelLaws (H : ZFAxioms mem) (L : W → W → W → Prop) (bnd : W) :
    Prop where
  /-- Old field 1, second conjunct: exclusivity at the level itself. -/
  excl : ∀ c e, IsFormCodeSem H c → IsUnivEnv H e →
    L c e (natV H 1) → ¬ L c e (natV H 0)
  /-- Old field 2: a code bounded by the level's numeral is decided. -/
  decided : ∀ c e, IsFormCodeSem H c → IsUnivEnv H e → QuantBounded H bnd c →
    L c e (natV H 1) ∨ L c e (natV H 0)
  /-- New field 6. -/
  elim : TarskiElim H L
  /-- New field 7. -/
  intr : TarskiIntro H L

/-! ## The two refuting expansions die

The expansions are those of `ZFCinPA.LocalStepDerivation`'s module header.
Both are recorded here through the property of the *induced previous level*
that the header derives from the placeholder values, so that no reading of
the source syntax is needed:

* expansion (A) sets the closure placeholder to `∅`, so
  `LS₁ c e b :≡ ∃ n C, Num n ∧ Clos n C ∧ ⟨c,e,b⟩ ∈ C` is the empty
  relation;
* expansion (B) lets the closure placeholder admit exactly the sets of
  bit-`0` triples, so `LS₁ c e b ↔ b = natV H 0`.
-/

/-- **Expansion (A) fails the new introduction field.**  Its previous level
is empty, and `tarskiIntro`'s first clause asks for the falsity code to be
Pi-false. -/
theorem expansionA_fails_tarskiIntro (H : ZFAxioms mem) {L : W → W → W → Prop}
    (hL : ∀ c e b, ¬ L c e b) {e : W} (he : IsUnivEnv H e) :
    ¬ TarskiIntro H L :=
  fun h => hL _ _ _ (h.botPi e he)

/-- **Expansion (B) fails the new elimination field**, at the implication row
on the Pi side, at the witness `⊥ 🡒 ⊥` of
`ZFCinPA.LocalStepDerivation.exclusivity_not_step_transferable`: that code is
Pi-false in (B), so the clause demands Sigma-truth of its antecedent, and
(B)'s Sigma side is empty. -/
theorem expansionB_fails_tarskiElim (H : ZFAxioms mem) {L : W → W → W → Prop}
    (hL1 : ∀ c e, ¬ L c e (natV H 1)) (hL0 : ∀ c e, L c e (natV H 0))
    {e : W} (he : IsUnivEnv H e) :
    ¬ TarskiElim H L :=
  fun h => hL1 _ _
    (h.impPi (botC H) (botC H) e (isFormCodeSem_bot H) (isFormCodeSem_bot H)
      he (hL0 _ _)).1

/-- **Expansion (B) satisfies the old exclusivity conjunct**, vacuously: its
Sigma side is empty. -/
theorem expansionB_satisfies_excl (H : ZFAxioms mem) {L : W → W → W → Prop}
    (hL1 : ∀ c e, ¬ L c e (natV H 1)) :
    ∀ c e, IsFormCodeSem H c → IsUnivEnv H e →
      L c e (natV H 1) → ¬ L c e (natV H 0) :=
  fun _ _ _ _ h => absurd h (hL1 _ _)

/-- **Expansion (B) satisfies the old decidedness field**, trivially: its Pi
side is total.  So the five-field antecedent does not exclude (B); the
enlargement does. -/
theorem expansionB_satisfies_decided (H : ZFAxioms mem) {L : W → W → W → Prop}
    (hL0 : ∀ c e, L c e (natV H 0)) (bnd : W) :
    ∀ c e, IsFormCodeSem H c → IsUnivEnv H e → QuantBounded H bnd c →
      L c e (natV H 1) ∨ L c e (natV H 0) :=
  fun _ _ _ _ _ => Or.inr (hL0 _ _)

/-! ## The successor level -/

/-- **The closure level over `L` at bound `bnd`.**  This is the
specialization of `BoundedZFCConsistency.LevelSat` at a successor index when
the previous level is an arbitrary relation; it is what the source-template
successor step has to reason about. -/
def Step (H : ZFAxioms mem) (L : W → W → W → Prop) (bnd : W) :
    W → W → W → Prop :=
  fun c e b => ∃ C, LevelClosed H L bnd C ∧ mem (satTriple H c e b) C

/-- **The previous level embeds into the successor level**, by the delegation
row.  Available for *any* `L`: the one-record certificate is built by
`levelClosed_insert`. -/
theorem step_of_level (H : ZFAxioms mem) {L : W → W → W → Prop} {bnd c e b : W}
    (he : IsUnivEnv H e) (h : L c e b) : Step H L bnd c e b :=
  ⟨vcup H (vempty H) (vsingle H (satTriple H c e b)),
    levelClosed_insert H (levelClosed_empty H L bnd) he (Or.inl h),
    (vcup_spec H _ _ _).mpr (Or.inr ((vsingle_spec H _ _).mpr rfl))⟩

/-! ### The elimination field transfers, illustrated at the implication row

The general pattern: a record of a step-closed set is justified, and the
justification either delegates — where the field at `L` applies and
`step_of_level` lifts the result back — or is the structural row, whose
premises are memberships of the same set and therefore already `Step` facts.
Neither branch constructs a closed set over the placeholder level. -/

/-- Implication, Sigma side, one level up. -/
theorem impSigmaElim_step (H : ZFAxioms mem) {L : W → W → W → Prop}
    {bnd a b e : W} (hE : TarskiElim H L) (hca : IsFormCodeSem H a)
    (hcb : IsFormCodeSem H b) (he : IsUnivEnv H e)
    (h : Step H L bnd (impC H a b) e (natV H 1)) :
    Step H L bnd a e (natV H 0) ∨ Step H L bnd b e (natV H 1) := by
  obtain ⟨C, hC, hmem⟩ := h
  rcases levelJustified_imp H (hC _ _ _ hmem).2 with hd | hcase
  · rcases hE.impSigma a b e hca hcb he hd with k | k
    · exact Or.inl (step_of_level H he k)
    · exact Or.inr (step_of_level H he k)
  · rcases hcase with ⟨-, hm | hm⟩ | ⟨hb0, -⟩
    · exact Or.inl ⟨C, hC, hm⟩
    · exact Or.inr ⟨C, hC, hm⟩
    · exact absurd hb0 (natV_ne H (by decide))

/-- Implication, Pi side, one level up. -/
theorem impPiElim_step (H : ZFAxioms mem) {L : W → W → W → Prop}
    {bnd a b e : W} (hE : TarskiElim H L) (hca : IsFormCodeSem H a)
    (hcb : IsFormCodeSem H b) (he : IsUnivEnv H e)
    (h : Step H L bnd (impC H a b) e (natV H 0)) :
    Step H L bnd a e (natV H 1) ∧ Step H L bnd b e (natV H 0) := by
  obtain ⟨C, hC, hmem⟩ := h
  rcases levelJustified_imp H (hC _ _ _ hmem).2 with hd | hcase
  · obtain ⟨k1, k2⟩ := hE.impPi a b e hca hcb he hd
    exact ⟨step_of_level H he k1, step_of_level H he k2⟩
  · rcases hcase with ⟨hb1, -⟩ | ⟨-, m1, m2⟩
    · exact absurd hb1 (natV_ne H (by decide))
    · exact ⟨⟨C, hC, m1⟩, ⟨C, hC, m2⟩⟩

/-- Implication, Sigma side, introduction one level up — with no hypothesis
on `L` at all, because a closure level always has its introduction rules.
This is why `tarskiIntro` is a *certificate field* rather than a successor
obligation. -/
theorem impSigmaIntro_step (H : ZFAxioms mem) {L : W → W → W → Prop}
    {bnd a b e : W} (he : IsUnivEnv H e)
    (h : Step H L bnd a e (natV H 0) ∨ Step H L bnd b e (natV H 1)) :
    Step H L bnd (impC H a b) e (natV H 1) := by
  rcases h with ⟨C, hC, hm⟩ | ⟨C, hC, hm⟩
  · exact ⟨_, levelClosed_insert H hC he
      (Or.inr (Or.inl ⟨a, b, rfl, Or.inl ⟨rfl, Or.inl hm⟩⟩)),
      (vcup_spec H _ _ _).mpr (Or.inr ((vsingle_spec H _ _).mpr rfl))⟩
  · exact ⟨_, levelClosed_insert H hC he
      (Or.inr (Or.inl ⟨a, b, rfl, Or.inl ⟨rfl, Or.inr hm⟩⟩)),
      (vcup_spec H _ _ _).mpr (Or.inr ((vsingle_spec H _ _).mpr rfl))⟩

/-! ## The induction principle on formula codes, as an explicit hypothesis

`BoundedZFCConsistency.FormulaClosedSet.isFormCodeSem_ind'` needs the
property to be presented by a `Form` with parameters.  The property below
mentions `L`, so in the source template the corresponding instance is
Separation for a *placeholder* formula, which `templateZFC` does not
contain.  It is therefore carried as a hypothesis. -/

/-- The internal induction principle on formula codes, at one property. -/
def CodeInduction (H : ZFAxioms mem) (P : W → Prop) : Prop :=
  (∀ a b, mem a (omegaV H) → mem b (omegaV H) →
      P (kpair' H (natV H 0) (kpair' H a b))) →
  (∀ a b, mem a (omegaV H) → mem b (omegaV H) →
      P (kpair' H (natV H 1) (kpair' H a b))) →
  P (botC H) →
  (∀ a b, P a → P b → P (impC H a b)) →
  (∀ a b, P a → P b → P (andC H a b)) →
  (∀ a b, P a → P b → P (orC H a b)) →
  (∀ a, P a → P (allC H a)) →
  (∀ a, P a → P (exC H a)) →
  ∀ x, IsFormCodeSem H x → P x

/-- Every property presented by a `Form` with parameters has the induction
principle.  This is `isFormCodeSem_ind'`, repackaged. -/
theorem codeInduction_of_definable (H : ZFAxioms mem) (P : W → Prop)
    (phi : SetTheory.Form) (ee : Nat → W)
    (hdef : ∀ y, P y ↔ SetTheory.Sat mem (SetTheory.scons y ee) phi) :
    CodeInduction H P :=
  fun h1 h2 h3 h4 h5 h6 h7 h8 =>
    isFormCodeSem_ind' H P phi ee hdef h1 h2 h3 h4 h5 h6 h7 h8

/-! ## The transfer

`StepGood` bundles the three statements the induction has to carry at once:
exclusivity of the two polarities of "delegated or recorded in `C`", and the
two oriented halves of the adjacent-level collapse into `L`.  The collapse
conjuncts are what the two quantifier rows of `LevelJustified` consume, and
they are the reason the predicate cannot be taken placeholder-free. -/

/-- **The induction property.**  `C` is one step-closed certificate over the
previous level `L` at bound `bnd`; `L c e b ∨ ⟨c,e,b⟩ ∈ C` is the reading of
"true at the successor level, as witnessed by `C` or delegated". -/
def StepGood (H : ZFAxioms mem) (L : W → W → W → Prop) (bnd C c : W) : Prop :=
  IsFormCodeSem H c ∧ ∀ e, IsUnivEnv H e →
    (¬ ((L c e (natV H 1) ∨ mem (satTriple H c e (natV H 1)) C) ∧
        (L c e (natV H 0) ∨ mem (satTriple H c e (natV H 0)) C))) ∧
    (PiBounded H bnd c → mem (satTriple H c e (natV H 0)) C →
      L c e (natV H 0)) ∧
    (SigmaBounded H bnd c → mem (satTriple H c e (natV H 1)) C →
      L c e (natV H 1))

section Transfer

variable (H : ZFAxioms mem)

/-- At a tag below three only the delegation row survives, so the successor
reading collapses to the previous level with no bound at all. -/
private theorem sl_tag_low {L : W → W → W → Prop} {bnd C : W}
    (hC : LevelClosed H L bnd C) {t : Nat} (ht : t < 3) {x e b : W}
    (h : L (kpair' H (natV H t) x) e b ∨
      mem (satTriple H (kpair' H (natV H t) x) e b) C) :
    L (kpair' H (natV H t) x) e b := by
  rcases h with h | h
  · exact h
  · exact levelJustified_of_tag_low H ht (hC _ _ _ h).2

/-- The atomic and falsity cases of the induction, uniformly. -/
private theorem stepGood_tag_low {L : W → W → W → Prop} {bnd C : W}
    (hexcl : ∀ c e, IsFormCodeSem H c → IsUnivEnv H e →
      L c e (natV H 1) → ¬ L c e (natV H 0))
    (hC : LevelClosed H L bnd C) {t : Nat} (ht : t < 3) {x : W}
    (hc : IsFormCodeSem H (kpair' H (natV H t) x)) :
    StepGood H L bnd C (kpair' H (natV H t) x) :=
  ⟨hc, fun e he =>
    ⟨fun h => hexcl _ e hc he (sl_tag_low H hC ht h.1) (sl_tag_low H hC ht h.2),
     fun _ h => sl_tag_low H hC ht (Or.inr h),
     fun _ h => sl_tag_low H hC ht (Or.inr h)⟩⟩

set_option maxHeartbeats 1000000 in
/-- **The enlarged laws transfer to the closure level.**  One induction on
internal formula codes proves exclusivity and the adjacent-level collapse at
the successor level simultaneously.

The connective cases use the elimination clauses at `L` on the delegated
branch and the structural row on the other, and close by the introduction
clauses at `L`.  The two quantifier cases are where the design is decided:
the polarity-switch row supplies `¬ L c e (natV H 0)` together with a
`Pi`-bound at the successor numeral, the collapse conjunct at the matrix
turns a recorded counterexample into a counterexample at `L`, and the
quantifier introduction at `L` closes the contradiction.  The old
decidedness field is consumed exactly twice: at the two rows whose bound
peels a successor. -/
theorem stepGood_of_levelLaws {L : W → W → W → Prop} {b : W}
    (hb : mem b (omegaV H)) (hL : LevelLaws H L b) {C : W}
    (hC : LevelClosed H L (vsucc H b) C)
    (hind : CodeInduction H (StepGood H L (vsucc H b) C)) :
    ∀ c, IsFormCodeSem H c → StepGood H L (vsucc H b) C c := by
  have hom : mem (vsucc H b) (omegaV H) := omega_succ H b hb
  refine hind ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun a b ha hb =>
      stepGood_tag_low H hL.excl hC (t := 0) (by omega)
        (isFormCodeSem_memAtom H ha hb)
  · exact fun a b ha hb =>
      stepGood_tag_low H hL.excl hC (t := 1) (by omega)
        (isFormCodeSem_eqAtom H ha hb)
  · exact stepGood_tag_low H hL.excl hC (t := 2) (by omega)
      (isFormCodeSem_bot H)
  -- implication
  · rintro a b ⟨hca, iha⟩ ⟨hcb, ihb⟩
    refine ⟨isFormCodeSem_imp H hca hcb, fun e he => ⟨?_, ?_, ?_⟩⟩
    · rintro ⟨h1, h0⟩
      have k1 : (L a e (natV H 0) ∨ mem (satTriple H a e (natV H 0)) C) ∨
          (L b e (natV H 1) ∨ mem (satTriple H b e (natV H 1)) C) := by
        rcases h1 with h1 | h1
        · rcases hL.elim.impSigma a b e hca hcb he h1 with k | k
          · exact Or.inl (Or.inl k)
          · exact Or.inr (Or.inl k)
        · rcases levelJustified_imp H (hC _ _ _ h1).2 with hd | hcase
          · rcases hL.elim.impSigma a b e hca hcb he hd with k | k
            · exact Or.inl (Or.inl k)
            · exact Or.inr (Or.inl k)
          · rcases hcase with ⟨-, hm | hm⟩ | ⟨hb0, -⟩
            · exact Or.inl (Or.inr hm)
            · exact Or.inr (Or.inr hm)
            · exact absurd hb0 (natV_ne H (by decide))
      have k0 : (L a e (natV H 1) ∨ mem (satTriple H a e (natV H 1)) C) ∧
          (L b e (natV H 0) ∨ mem (satTriple H b e (natV H 0)) C) := by
        rcases h0 with h0 | h0
        · obtain ⟨j1, j2⟩ := hL.elim.impPi a b e hca hcb he h0
          exact ⟨Or.inl j1, Or.inl j2⟩
        · rcases levelJustified_imp H (hC _ _ _ h0).2 with hd | hcase
          · obtain ⟨j1, j2⟩ := hL.elim.impPi a b e hca hcb he hd
            exact ⟨Or.inl j1, Or.inl j2⟩
          · rcases hcase with ⟨hb1, -⟩ | ⟨-, m1, m2⟩
            · exact absurd hb1 (natV_ne H (by decide))
            · exact ⟨Or.inr m1, Or.inr m2⟩
      rcases k1 with ka | kb
      · exact (iha e he).1 ⟨k0.1, ka⟩
      · exact (ihb e he).1 ⟨kb, k0.2⟩
    · intro hbd hmem
      rcases levelJustified_imp H (hC _ _ _ hmem).2 with hd | hcase
      · exact hd
      · rcases hcase with ⟨hb1, -⟩ | ⟨-, m1, m2⟩
        · exact absurd hb1 (natV_ne H (by decide))
        · obtain ⟨ba, bb⟩ := piBounded_imp H hom hbd
          exact hL.intr.impPi a b e hca hcb he ((iha e he).2.2 ba m1)
            ((ihb e he).2.1 bb m2)
    · intro hbd hmem
      rcases levelJustified_imp H (hC _ _ _ hmem).2 with hd | hcase
      · exact hd
      · rcases hcase with ⟨-, hm | hm⟩ | ⟨hb0, -⟩
        · obtain ⟨ba, -⟩ := sigmaBounded_imp H hom hbd
          exact hL.intr.impSigma a b e hca hcb he
            (Or.inl ((iha e he).2.1 ba hm))
        · obtain ⟨-, bb⟩ := sigmaBounded_imp H hom hbd
          exact hL.intr.impSigma a b e hca hcb he
            (Or.inr ((ihb e he).2.2 bb hm))
        · exact absurd hb0 (natV_ne H (by decide))
  -- conjunction
  · rintro a b ⟨hca, iha⟩ ⟨hcb, ihb⟩
    refine ⟨isFormCodeSem_and H hca hcb, fun e he => ⟨?_, ?_, ?_⟩⟩
    · rintro ⟨h1, h0⟩
      have k1 : (L a e (natV H 1) ∨ mem (satTriple H a e (natV H 1)) C) ∧
          (L b e (natV H 1) ∨ mem (satTriple H b e (natV H 1)) C) := by
        rcases h1 with h1 | h1
        · obtain ⟨j1, j2⟩ := hL.elim.andSigma a b e hca hcb he h1
          exact ⟨Or.inl j1, Or.inl j2⟩
        · rcases levelJustified_and H (hC _ _ _ h1).2 with hd | hcase
          · obtain ⟨j1, j2⟩ := hL.elim.andSigma a b e hca hcb he hd
            exact ⟨Or.inl j1, Or.inl j2⟩
          · rcases hcase with ⟨-, m1, m2⟩ | ⟨hb0, -⟩
            · exact ⟨Or.inr m1, Or.inr m2⟩
            · exact absurd hb0 (natV_ne H (by decide))
      have k0 : (L a e (natV H 0) ∨ mem (satTriple H a e (natV H 0)) C) ∨
          (L b e (natV H 0) ∨ mem (satTriple H b e (natV H 0)) C) := by
        rcases h0 with h0 | h0
        · rcases hL.elim.andPi a b e hca hcb he h0 with k | k
          · exact Or.inl (Or.inl k)
          · exact Or.inr (Or.inl k)
        · rcases levelJustified_and H (hC _ _ _ h0).2 with hd | hcase
          · rcases hL.elim.andPi a b e hca hcb he hd with k | k
            · exact Or.inl (Or.inl k)
            · exact Or.inr (Or.inl k)
          · rcases hcase with ⟨hb1, -⟩ | ⟨-, hm | hm⟩
            · exact absurd hb1 (natV_ne H (by decide))
            · exact Or.inl (Or.inr hm)
            · exact Or.inr (Or.inr hm)
      rcases k0 with ka | kb
      · exact (iha e he).1 ⟨k1.1, ka⟩
      · exact (ihb e he).1 ⟨k1.2, kb⟩
    · intro hbd hmem
      rcases levelJustified_and H (hC _ _ _ hmem).2 with hd | hcase
      · exact hd
      · rcases hcase with ⟨hb1, -⟩ | ⟨-, hm | hm⟩
        · exact absurd hb1 (natV_ne H (by decide))
        · obtain ⟨ba, -⟩ := piBounded_and H hom hbd
          exact hL.intr.andPi a b e hca hcb he (Or.inl ((iha e he).2.1 ba hm))
        · obtain ⟨-, bb⟩ := piBounded_and H hom hbd
          exact hL.intr.andPi a b e hca hcb he (Or.inr ((ihb e he).2.1 bb hm))
    · intro hbd hmem
      rcases levelJustified_and H (hC _ _ _ hmem).2 with hd | hcase
      · exact hd
      · rcases hcase with ⟨-, m1, m2⟩ | ⟨hb0, -⟩
        · obtain ⟨ba, bb⟩ := sigmaBounded_and H hom hbd
          exact hL.intr.andSigma a b e hca hcb he ((iha e he).2.2 ba m1)
            ((ihb e he).2.2 bb m2)
        · exact absurd hb0 (natV_ne H (by decide))
  -- disjunction
  · rintro a b ⟨hca, iha⟩ ⟨hcb, ihb⟩
    refine ⟨isFormCodeSem_or H hca hcb, fun e he => ⟨?_, ?_, ?_⟩⟩
    · rintro ⟨h1, h0⟩
      have k1 : (L a e (natV H 1) ∨ mem (satTriple H a e (natV H 1)) C) ∨
          (L b e (natV H 1) ∨ mem (satTriple H b e (natV H 1)) C) := by
        rcases h1 with h1 | h1
        · rcases hL.elim.orSigma a b e hca hcb he h1 with k | k
          · exact Or.inl (Or.inl k)
          · exact Or.inr (Or.inl k)
        · rcases levelJustified_or H (hC _ _ _ h1).2 with hd | hcase
          · rcases hL.elim.orSigma a b e hca hcb he hd with k | k
            · exact Or.inl (Or.inl k)
            · exact Or.inr (Or.inl k)
          · rcases hcase with ⟨-, hm | hm⟩ | ⟨hb0, -⟩
            · exact Or.inl (Or.inr hm)
            · exact Or.inr (Or.inr hm)
            · exact absurd hb0 (natV_ne H (by decide))
      have k0 : (L a e (natV H 0) ∨ mem (satTriple H a e (natV H 0)) C) ∧
          (L b e (natV H 0) ∨ mem (satTriple H b e (natV H 0)) C) := by
        rcases h0 with h0 | h0
        · obtain ⟨j1, j2⟩ := hL.elim.orPi a b e hca hcb he h0
          exact ⟨Or.inl j1, Or.inl j2⟩
        · rcases levelJustified_or H (hC _ _ _ h0).2 with hd | hcase
          · obtain ⟨j1, j2⟩ := hL.elim.orPi a b e hca hcb he hd
            exact ⟨Or.inl j1, Or.inl j2⟩
          · rcases hcase with ⟨hb1, -⟩ | ⟨-, m1, m2⟩
            · exact absurd hb1 (natV_ne H (by decide))
            · exact ⟨Or.inr m1, Or.inr m2⟩
      rcases k1 with ka | kb
      · exact (iha e he).1 ⟨ka, k0.1⟩
      · exact (ihb e he).1 ⟨kb, k0.2⟩
    · intro hbd hmem
      rcases levelJustified_or H (hC _ _ _ hmem).2 with hd | hcase
      · exact hd
      · rcases hcase with ⟨hb1, -⟩ | ⟨-, m1, m2⟩
        · exact absurd hb1 (natV_ne H (by decide))
        · obtain ⟨ba, bb⟩ := piBounded_or H hom hbd
          exact hL.intr.orPi a b e hca hcb he ((iha e he).2.1 ba m1)
            ((ihb e he).2.1 bb m2)
    · intro hbd hmem
      rcases levelJustified_or H (hC _ _ _ hmem).2 with hd | hcase
      · exact hd
      · rcases hcase with ⟨-, hm | hm⟩ | ⟨hb0, -⟩
        · obtain ⟨ba, -⟩ := sigmaBounded_or H hom hbd
          exact hL.intr.orSigma a b e hca hcb he
            (Or.inl ((iha e he).2.2 ba hm))
        · obtain ⟨-, bb⟩ := sigmaBounded_or H hom hbd
          exact hL.intr.orSigma a b e hca hcb he
            (Or.inr ((ihb e he).2.2 bb hm))
        · exact absurd hb0 (natV_ne H (by decide))
  -- universal quantifier
  · rintro a ⟨hca, iha⟩
    refine ⟨isFormCodeSem_all H hca, fun e he => ⟨?_, ?_, ?_⟩⟩
    · rintro ⟨h1, h0⟩
      have k1 : L (allC H a) e (natV H 1) ∨
          (PiBounded H (vsucc H b) (allC H a) ∧
            ¬ L (allC H a) e (natV H 0)) := by
        rcases h1 with h1 | h1
        · exact Or.inl h1
        · rcases levelJustified_all H (hC _ _ _ h1).2 with hd | hcase
          · exact Or.inl hd
          · rcases hcase with ⟨-, hpb, hnp⟩ | ⟨hb0, -⟩
            · exact Or.inr ⟨hpb, hnp⟩
            · exact absurd hb0 (natV_ne H (by decide))
      have k0 : L (allC H a) e (natV H 0) ∨
          ∃ d, mem (satTriple H a (econs H d e) (natV H 0)) C := by
        rcases h0 with h0 | h0
        · exact Or.inl h0
        · rcases levelJustified_all H (hC _ _ _ h0).2 with hd | hcase
          · exact Or.inl hd
          · rcases hcase with ⟨hb1, -⟩ | ⟨-, hex⟩
            · exact absurd hb1 (natV_ne H (by decide))
            · exact Or.inr hex
      rcases k1 with k1 | ⟨hpb, hnp⟩
      · rcases k0 with k0 | ⟨d, hd⟩
        · exact hL.excl _ e (isFormCodeSem_all H hca) he k1 k0
        · exact (iha (econs H d e) (econs_isUnivEnv H he d)).1
            ⟨Or.inl (hL.elim.allSigma a e d hca he k1), Or.inr hd⟩
      · rcases k0 with k0 | ⟨d, hd⟩
        · exact hnp k0
        · exact hnp (hL.intr.allPi a e d hca he
            ((iha (econs H d e) (econs_isUnivEnv H he d)).2.1
              (piBounded_all H hom hpb) hd))
    · intro hbd hmem
      rcases levelJustified_all H (hC _ _ _ hmem).2 with hd | hcase
      · exact hd
      · rcases hcase with ⟨hb1, -⟩ | ⟨-, d, hd⟩
        · exact absurd hb1 (natV_ne H (by decide))
        · exact hL.intr.allPi a e d hca he
            ((iha (econs H d e) (econs_isUnivEnv H he d)).2.1
              (piBounded_all H hom hbd) hd)
    · intro hbd hmem
      rcases levelJustified_all H (hC _ _ _ hmem).2 with hd | hcase
      · exact hd
      · rcases hcase with ⟨-, -, hnp⟩ | ⟨hb0, -⟩
        · rcases hL.decided _ e (isFormCodeSem_all H hca) he
            (quantBounded_of_piBounded H hb
              (piBounded_of_sigmaBounded_all_succ H hb hbd)) with k | k
          · exact k
          · exact absurd k hnp
        · exact absurd hb0 (natV_ne H (by decide))
  -- existential quantifier
  · rintro a ⟨hca, iha⟩
    refine ⟨isFormCodeSem_ex H hca, fun e he => ⟨?_, ?_, ?_⟩⟩
    · rintro ⟨h1, h0⟩
      have k1 : L (exC H a) e (natV H 1) ∨
          ∃ d, mem (satTriple H a (econs H d e) (natV H 1)) C := by
        rcases h1 with h1 | h1
        · exact Or.inl h1
        · rcases levelJustified_ex H (hC _ _ _ h1).2 with hd | hcase
          · exact Or.inl hd
          · rcases hcase with ⟨-, hex⟩ | ⟨hb0, -⟩
            · exact Or.inr hex
            · exact absurd hb0 (natV_ne H (by decide))
      have k0 : L (exC H a) e (natV H 0) ∨
          (SigmaBounded H (vsucc H b) (exC H a) ∧
            ¬ L (exC H a) e (natV H 1)) := by
        rcases h0 with h0 | h0
        · exact Or.inl h0
        · rcases levelJustified_ex H (hC _ _ _ h0).2 with hd | hcase
          · exact Or.inl hd
          · rcases hcase with ⟨hb1, -⟩ | ⟨-, hsb, hns⟩
            · exact absurd hb1 (natV_ne H (by decide))
            · exact Or.inr ⟨hsb, hns⟩
      rcases k0 with k0 | ⟨hsb, hns⟩
      · rcases k1 with k1 | ⟨d, hd⟩
        · exact hL.excl _ e (isFormCodeSem_ex H hca) he k1 k0
        · exact (iha (econs H d e) (econs_isUnivEnv H he d)).1
            ⟨Or.inr hd, Or.inl (hL.elim.exPi a e d hca he k0)⟩
      · rcases k1 with k1 | ⟨d, hd⟩
        · exact hns k1
        · exact hns (hL.intr.exSigma a e d hca he
            ((iha (econs H d e) (econs_isUnivEnv H he d)).2.2
              (sigmaBounded_ex H hom hsb) hd))
    · intro hbd hmem
      rcases levelJustified_ex H (hC _ _ _ hmem).2 with hd | hcase
      · exact hd
      · rcases hcase with ⟨hb1, -⟩ | ⟨-, -, hns⟩
        · exact absurd hb1 (natV_ne H (by decide))
        · rcases hL.decided _ e (isFormCodeSem_ex H hca) he
            (quantBounded_of_sigmaBounded H hb
              (sigmaBounded_of_piBounded_ex_succ H hb hbd)) with k | k
          · exact absurd k hns
          · exact k
    · intro hbd hmem
      rcases levelJustified_ex H (hC _ _ _ hmem).2 with hd | hcase
      · exact hd
      · rcases hcase with ⟨-, d, hd⟩ | ⟨hb0, -⟩
        · exact hL.intr.exSigma a e d hca he
            ((iha (econs H d e) (econs_isUnivEnv H he d)).2.2
              (sigmaBounded_ex H hom hbd) hd)
        · exact absurd hb0 (natV_ne H (by decide))

/-! ### The three headline corollaries -/

/-- **Exclusivity transfers under the enlarged field set.**  This is the
positive counterpart of
`ZFCinPA.LocalStepDerivation.exclusivity_not_step_transferable`: the same
statement about the same closure level, now derivable, with the two new
fields in the antecedent.

The two witnessing certificates are merged by `levelClosed_cup` before the
induction runs, which is what lets the induction predicate speak about a
single set. -/
theorem exclusivity_step {L : W → W → W → Prop} {b : W}
    (hb : mem b (omegaV H)) (hL : LevelLaws H L b)
    (hind : ∀ C, LevelClosed H L (vsucc H b) C →
      CodeInduction H (StepGood H L (vsucc H b) C))
    {c e : W} (hc : IsFormCodeSem H c) (he : IsUnivEnv H e)
    (h1 : Step H L (vsucc H b) c e (natV H 1)) :
    ¬ Step H L (vsucc H b) c e (natV H 0) := by
  rintro ⟨C0, hC0, mem0⟩
  obtain ⟨C1, hC1, mem1⟩ := h1
  have hCu : LevelClosed H L (vsucc H b) (vcup H C1 C0) :=
    levelClosed_cup H hC1 hC0
  exact ((stepGood_of_levelLaws H hb hL hCu (hind _ hCu) c hc).2 e he).1
    ⟨Or.inr ((vcup_spec H _ _ _).mpr (Or.inl mem1)),
     Or.inr ((vcup_spec H _ _ _).mpr (Or.inr mem0))⟩

/-- **The adjacent-level collapse, Pi side, is derived and not a field.**
Goal-2 counterpart: `piFalse_collapse`. -/
theorem piFalse_collapse_step {L : W → W → W → Prop} {b : W}
    (hb : mem b (omegaV H)) (hL : LevelLaws H L b)
    (hind : ∀ C, LevelClosed H L (vsucc H b) C →
      CodeInduction H (StepGood H L (vsucc H b) C))
    {c e : W} (hc : IsFormCodeSem H c) (he : IsUnivEnv H e)
    (hbd : PiBounded H (vsucc H b) c)
    (h : Step H L (vsucc H b) c e (natV H 0)) : L c e (natV H 0) := by
  obtain ⟨C, hC, hm⟩ := h
  exact ((stepGood_of_levelLaws H hb hL hC (hind _ hC) c hc).2 e he).2.1
    hbd hm

/-- **The adjacent-level collapse, Sigma side.**  Goal-2 counterpart:
`sigmaTrue_collapse`. -/
theorem sigmaTrue_collapse_step {L : W → W → W → Prop} {b : W}
    (hb : mem b (omegaV H)) (hL : LevelLaws H L b)
    (hind : ∀ C, LevelClosed H L (vsucc H b) C →
      CodeInduction H (StepGood H L (vsucc H b) C))
    {c e : W} (hc : IsFormCodeSem H c) (he : IsUnivEnv H e)
    (hbd : SigmaBounded H (vsucc H b) c)
    (h : Step H L (vsucc H b) c e (natV H 1)) : L c e (natV H 1) := by
  obtain ⟨C, hC, hm⟩ := h
  exact ((stepGood_of_levelLaws H hb hL hC (hind _ hC) c hc).2 e he).2.2
    hbd hm

end Transfer

/-! ## Soundness of the enlarged fields

Everything above is conditional on the enlarged laws holding at the
previous level.  This section discharges that unconditionally for goal 2's
*actual* hierarchy, at every level, so that the enlargement is sound: a
field set that defeats the two countermodels but is not true would be
worthless.  These are also exactly the statements
`ZFCinPA.BaseCertificate` needs, externally at every standard index.

Fifteen of the seventeen clauses are goal-2 exports.  The two quantifier
eliminations are not: goal 2 records the quantifier clauses only in the
`inv` form, whose conclusion descends a level.  They are proved here from
`sigmaTrue_all_inv'`, totality (`sigmaTrue_or_piFalse`) and the collapse
(`piFalse_collapse_le`), which is why the strong form is legitimate. -/

section Soundness

variable (H : ZFAxioms mem)

/-- **The abstract successor level is goal 2's successor level.**  The
`Step` of this module is not an approximation of `LevelSat`; it is its
definitional unfolding with the previous level abstracted. -/
theorem step_levelSat (n : Nat) :
    Step H (LevelSat H (n + 1)) (natV H (n + 1)) = LevelSat H (n + 2) := rfl

/-- **The whole enlarged bundle is true**: level `n+1` with bound the
numeral of `n`, which is the pairing the certificate family uses at index
`n`.  Nothing in the enlargement is vacuous or unprovable. -/
theorem levelLaws_levelSat (n : Nat) :
    LevelLaws H (LevelSat H (n + 1)) (natV H n) where
  excl := fun c e hc he => sigmaTrue_not_piFalse H (n + 1) c e hc he
  decided := fun _ _ hc he hq => sigmaTrue_or_piFalse H n hc hq he
  elim := tarskiElim_levelSat H (n + 1)
  intr := tarskiIntro_levelSat H n

end Soundness

end EnlargedFields
end ZFCinPA
end LeanProofs
