import BoundedZFCConsistency.LevelSoundness

/-!
# The level-collapse theorem, and two-valuedness

`BoundedZFCConsistency.UniverseTruthLevel` builds the externally indexed truth
predicates and proves every Tarski clause except the elimination halves of the
two polarity-switch rows, whose inversions leave a disjunct reading "the
previous level already certified this record".  Discharging that disjunct is the
**level-collapse theorem**:

```text
truth at level n+1, on a code whose oriented rank is bounded at n,
already holds at level n.
```

The orientation is not cosmetic.  The Sigma side collapses under a Sigma-bound
and the Pi side under a Pi-bound, because the step table guards the delegated
row of a universal head by `PiBounded` and that of an existential head by
`SigmaBounded`, and because the two ranks of a compound mix the two ranks of its
parts: an implication's Sigma-rank dominates its antecedent's *Pi*-rank.  A
single unoriented bound is therefore not enough to run the induction, and the
oriented descent lemmas below are what make the connective cases go through.

## What the collapse buys

Three consequences, in increasing order of what they cost the project.

* The polarity switches become biconditionals: a universal code is Sigma-true at
  level `n+1` exactly when it is Pi-true at level `n`, and dually.
* `PiTrue` becomes monotone in the level on Pi-bounded codes, upgrading the
  antitonicity that `piTrue_anti` records.  The two directions are the same
  statement about `PiFalse` read from opposite sides, and only the collapse
  supplies the missing one.
* **Two-valuedness**, `LevelSoundness.LevelTwoValuedAt`: on the codes a bounded
  derivation can mention, `SigmaTrue (n+1)` and `PiTrue (n+1)` agree.  This is
  what implication elimination needs, and it is discharged outright at the end of
  this module.

## Three inductions, and why they are separate

*Collapse* is an induction over codes at a fixed level, and it splits on whether
that level is zero.  At a positive level each connective case is one application
of the corresponding introduction lemma; at level zero the introduction lemmas
are unavailable — level zero is not a certificate level — and the case is closed
instead by the quantifier-free Tarski clauses of
`BoundedZFCConsistency.UniverseTruthZero`, the oriented bound having forced the
code to be quantifier-free.  The quantifier cases at level zero are vacuous,
since no quantified code has complexity zero.

*Exclusivity* — that no code is both Sigma-true and Pi-false at the same level —
is an induction on the level with an induction over codes inside it.  It needs
no bound on the code.  Its quantifier cases are where the collapse is consumed:
a Sigma-true universal code at level `n` was delegated at some *earlier* level
`k`, and the Pi-false certificate at level `n` has to be brought down to `k`
before the two can be compared.

*Totality* — that a bounded code is Sigma-true or Pi-false — is an induction over
codes that consumes neither of the other two.  Its quantifier cases use only the
polarity-switch introductions, which is why the oriented bound appears in the
statement and no induction hypothesis is needed there.

Exclusivity and totality together are two-valuedness.

## Codes, not quotations

As everywhere in this project, a code is an arbitrary internal one and never
assumed to be the quotation of an external formula.  `IsFormCodeSem` has no
inversion, so codehood of a compound never yields codehood of its parts, and
every code induction below carries codehood as a conjunct of its property so
that the parts arrive with it.

Neither Powerset nor Regularity is used.
-/

namespace LeanProofs
namespace BoundedZFCConsistency

open SetTheory
open SetTheory.Form

universe u

section LevelCollapse

variable {V : Type u} {mem : V → V → Prop}

/-! ## The oriented bounds: weakening and descent

`BoundedZFCConsistency.CodedRank` proves descent for `QuantBounded`, the bound on
the *smaller* rank.  The collapse needs the two ranks separately, and the
subcode a bound descends to depends on the polarity: the Sigma-rank of an
implication is the larger of the antecedent's Pi-rank and the consequent's
Sigma-rank, so a Sigma-bound on the implication is a Pi-bound on the antecedent.
-/

/-- Weakening an oriented bound. -/
theorem sigmaBounded_le (H : ZFAxioms mem) {b b' c : V}
    (hb' : mem b' (omegaV H)) (h : SigmaBounded H b c) (hle : LeN H b b') :
    SigmaBounded H b' c := by
  obtain ⟨s, p, hr, h1⟩ := h
  exact ⟨s, p, hr, leN_trans H hb' h1 hle⟩

theorem piBounded_le (H : ZFAxioms mem) {b b' c : V}
    (hb' : mem b' (omegaV H)) (h : PiBounded H b c) (hle : LeN H b b') :
    PiBounded H b' c := by
  obtain ⟨s, p, hr, h1⟩ := h
  exact ⟨s, p, hr, leN_trans H hb' h1 hle⟩

/-- Weakening along the external order on numerals. -/
theorem sigmaBounded_natV_le (H : ZFAxioms mem) {j k : Nat} (hjk : j ≤ k)
    {c : V} (h : SigmaBounded H (natV H j) c) : SigmaBounded H (natV H k) c :=
  sigmaBounded_le H (natV_mem_omega H k) h ((leN_natV_iff H j k).mpr hjk)

theorem piBounded_natV_le (H : ZFAxioms mem) {j k : Nat} (hjk : j ≤ k) {c : V}
    (h : PiBounded H (natV H j) c) : PiBounded H (natV H k) c :=
  piBounded_le H (natV_mem_omega H k) h ((leN_natV_iff H j k).mpr hjk)

/-- **A bound on the smaller rank is a bound on one of the two.**  The minimum
of two internal naturals is one of them, so the unoriented bound the every-
occurrence restriction supplies always orients itself in at least one way. -/
theorem sigmaBounded_or_piBounded (H : ZFAxioms mem) {b c : V}
    (h : QuantBounded H b c) : SigmaBounded H b c ∨ PiBounded H b c := by
  obtain ⟨s, p, hr, hle⟩ := h
  rcases Classical.em (mem s p) with hm | hm
  · rw [vminN_of_mem H hm] at hle
    exact Or.inl ⟨s, p, hr, hle⟩
  · rw [vminN_of_not_mem H hm] at hle
    exact Or.inr ⟨s, p, hr, hle⟩

/-- **The Sigma-bound of an implication descends with the polarity flipped on
the antecedent.** -/
theorem sigmaBounded_imp (H : ZFAxioms mem) {b a a' : V}
    (hb : mem b (omegaV H))
    (h : SigmaBounded H b (kpair H (natV H 3) (kpair H a a'))) :
    PiBounded H b a ∧ SigmaBounded H b a' := by
  obtain ⟨s, p, hr, hle⟩ := h
  obtain ⟨sa, pa, sb, pb, ha, hb', hs, hp⟩ := ranks_imp_inv H hr
  obtain ⟨hsa, hpa⟩ := Ranks.mem_omega H ha
  obtain ⟨hsb, hpb⟩ := Ranks.mem_omega H hb'
  subst hs
  exact ⟨⟨sa, pa, ha, leN_trans H hb (leN_vmaxN_left H hpa hsb) hle⟩,
    ⟨sb, pb, hb', leN_trans H hb (leN_vmaxN_right H hpa hsb) hle⟩⟩

/-- **The Pi-bound of an implication descends with the polarity flipped on the
antecedent.** -/
theorem piBounded_imp (H : ZFAxioms mem) {b a a' : V} (hb : mem b (omegaV H))
    (h : PiBounded H b (kpair H (natV H 3) (kpair H a a'))) :
    SigmaBounded H b a ∧ PiBounded H b a' := by
  obtain ⟨s, p, hr, hle⟩ := h
  obtain ⟨sa, pa, sb, pb, ha, hb', hs, hp⟩ := ranks_imp_inv H hr
  obtain ⟨hsa, hpa⟩ := Ranks.mem_omega H ha
  obtain ⟨hsb, hpb⟩ := Ranks.mem_omega H hb'
  subst hp
  exact ⟨⟨sa, pa, ha, leN_trans H hb (leN_vmaxN_left H hsa hpb) hle⟩,
    ⟨sb, pb, hb', leN_trans H hb (leN_vmaxN_right H hsa hpb) hle⟩⟩

/-- Conjunction preserves the polarity on both parts. -/
theorem sigmaBounded_and (H : ZFAxioms mem) {b a a' : V}
    (hb : mem b (omegaV H))
    (h : SigmaBounded H b (kpair H (natV H 4) (kpair H a a'))) :
    SigmaBounded H b a ∧ SigmaBounded H b a' := by
  obtain ⟨s, p, hr, hle⟩ := h
  obtain ⟨sa, pa, sb, pb, ha, hb', hs, hp⟩ := ranks_and_inv H hr
  obtain ⟨hsa, hpa⟩ := Ranks.mem_omega H ha
  obtain ⟨hsb, hpb⟩ := Ranks.mem_omega H hb'
  subst hs
  exact ⟨⟨sa, pa, ha, leN_trans H hb (leN_vmaxN_left H hsa hsb) hle⟩,
    ⟨sb, pb, hb', leN_trans H hb (leN_vmaxN_right H hsa hsb) hle⟩⟩

theorem piBounded_and (H : ZFAxioms mem) {b a a' : V} (hb : mem b (omegaV H))
    (h : PiBounded H b (kpair H (natV H 4) (kpair H a a'))) :
    PiBounded H b a ∧ PiBounded H b a' := by
  obtain ⟨s, p, hr, hle⟩ := h
  obtain ⟨sa, pa, sb, pb, ha, hb', hs, hp⟩ := ranks_and_inv H hr
  obtain ⟨hsa, hpa⟩ := Ranks.mem_omega H ha
  obtain ⟨hsb, hpb⟩ := Ranks.mem_omega H hb'
  subst hp
  exact ⟨⟨sa, pa, ha, leN_trans H hb (leN_vmaxN_left H hpa hpb) hle⟩,
    ⟨sb, pb, hb', leN_trans H hb (leN_vmaxN_right H hpa hpb) hle⟩⟩

/-- Disjunction behaves as conjunction does on both ranks. -/
theorem sigmaBounded_or (H : ZFAxioms mem) {b a a' : V} (hb : mem b (omegaV H))
    (h : SigmaBounded H b (kpair H (natV H 5) (kpair H a a'))) :
    SigmaBounded H b a ∧ SigmaBounded H b a' := by
  obtain ⟨s, p, hr, hle⟩ := h
  obtain ⟨sa, pa, sb, pb, ha, hb', hs, hp⟩ := ranks_or_inv H hr
  obtain ⟨hsa, hpa⟩ := Ranks.mem_omega H ha
  obtain ⟨hsb, hpb⟩ := Ranks.mem_omega H hb'
  subst hs
  exact ⟨⟨sa, pa, ha, leN_trans H hb (leN_vmaxN_left H hsa hsb) hle⟩,
    ⟨sb, pb, hb', leN_trans H hb (leN_vmaxN_right H hsa hsb) hle⟩⟩

theorem piBounded_or (H : ZFAxioms mem) {b a a' : V} (hb : mem b (omegaV H))
    (h : PiBounded H b (kpair H (natV H 5) (kpair H a a'))) :
    PiBounded H b a ∧ PiBounded H b a' := by
  obtain ⟨s, p, hr, hle⟩ := h
  obtain ⟨sa, pa, sb, pb, ha, hb', hs, hp⟩ := ranks_or_inv H hr
  obtain ⟨hsa, hpa⟩ := Ranks.mem_omega H ha
  obtain ⟨hsb, hpb⟩ := Ranks.mem_omega H hb'
  subst hp
  exact ⟨⟨sa, pa, ha, leN_trans H hb (leN_vmaxN_left H hpa hpb) hle⟩,
    ⟨sb, pb, hb', leN_trans H hb (leN_vmaxN_right H hpa hpb) hle⟩⟩

/-- **The Pi-bound of a universal code descends to its matrix.**  This is the
positively recorded polarity at a universal head, and it is the only descent the
quantifier cases need: the other polarity is delegated rather than recorded. -/
theorem piBounded_all (H : ZFAxioms mem) {b a : V} (hb : mem b (omegaV H))
    (h : PiBounded H b (kpair H (natV H 6) a)) : PiBounded H b a := by
  obtain ⟨s, p, hr, hle⟩ := h
  obtain ⟨sa, pa, ha, hs, hp⟩ := ranks_all_inv H hr
  obtain ⟨hsa, hpa⟩ := Ranks.mem_omega H ha
  subst hp
  exact ⟨sa, pa, ha,
    leN_trans H hb (leN_vmaxN_right H (natV_mem_omega H 1) hpa) hle⟩

/-- **The Sigma-bound of an existential code descends to its matrix.** -/
theorem sigmaBounded_ex (H : ZFAxioms mem) {b a : V} (hb : mem b (omegaV H))
    (h : SigmaBounded H b (kpair H (natV H 7) a)) : SigmaBounded H b a := by
  obtain ⟨s, p, hr, hle⟩ := h
  obtain ⟨sa, pa, ha, hs, hp⟩ := ranks_ex_inv H hr
  obtain ⟨hsa, hpa⟩ := Ranks.mem_omega H ha
  subst hs
  exact ⟨sa, pa, ha,
    leN_trans H hb (leN_vmaxN_right H (natV_mem_omega H 1) hsa) hle⟩

/-! ### The successor step at a quantifier head

A universal code's Sigma-rank is the successor of its Pi-rank, and an
existential code's Pi-rank the successor of its Sigma-rank.  A bound of `n+1` on
the larger rank is therefore a bound of `n` on the smaller — which is exactly the
guard the delegated row asks for one level down.  This is the internal reading of
`sigmaRank (fAll a) = piRank (fAll a) + 1`. -/

/-- Peeling one successor off a numeral bound. -/
private theorem leN_pred_of_succ (H : ZFAxioms mem) {x : V} {m : Nat}
    (h : LeN H (vsucc H x) (natV H (m+1))) : LeN H x (natV H m) :=
  succ_le_lt H (natV H (m+1)) (natV_mem_omega H (m+1)) x
    ((leN_iff H (vsucc H x) (natV H (m+1))).mp h)

/-- **A universal code Sigma-bounded at `m+1` is Pi-bounded at `m`.** -/
theorem piBounded_of_sigmaBounded_all (H : ZFAxioms mem) {a : V} {m : Nat}
    (h : SigmaBounded H (natV H (m+1)) (kpair H (natV H 6) a)) :
    PiBounded H (natV H m) (kpair H (natV H 6) a) := by
  obtain ⟨s, p, hr, hle⟩ := h
  obtain ⟨sa, pa, ha, hs, hp⟩ := ranks_all_inv H hr
  subst hs
  subst hp
  exact ⟨_, _, hr, leN_pred_of_succ H hle⟩

/-- **An existential code Pi-bounded at `m+1` is Sigma-bounded at `m`.** -/
theorem sigmaBounded_of_piBounded_ex (H : ZFAxioms mem) {a : V} {m : Nat}
    (h : PiBounded H (natV H (m+1)) (kpair H (natV H 7) a)) :
    SigmaBounded H (natV H m) (kpair H (natV H 7) a) := by
  obtain ⟨s, p, hr, hle⟩ := h
  obtain ⟨sa, pa, ha, hs, hp⟩ := ranks_ex_inv H hr
  subst hs
  subst hp
  exact ⟨_, _, hr, leN_pred_of_succ H hle⟩

/-- **No universal code is Sigma-bounded by zero**, the companion of
`not_piBounded_zero_all`. -/
theorem not_sigmaBounded_zero_all (H : ZFAxioms mem) {a : V} :
    ¬ SigmaBounded H (natV H 0) (kpair H (natV H 6) a) := fun h =>
  not_quantBounded_zero_all H
    (quantBounded_of_sigmaBounded H (natV_mem_omega H 0) h)

/-- **No existential code is Pi-bounded by zero.** -/
theorem not_piBounded_zero_ex (H : ZFAxioms mem) {a : V} :
    ¬ PiBounded H (natV H 0) (kpair H (natV H 7) a) := fun h =>
  not_quantBounded_zero_ex H (quantBounded_of_piBounded H (natV_mem_omega H 0) h)

/-! ## Level zero as a target

The introduction halves of the Tarski clauses are stated at a positive level,
because that is where a certificate exists to adjoin a record to.  The collapse
into level zero has to rebuild them from the quantifier-free clauses, which the
oriented bound makes available: a code bounded by zero on either polarity has
complexity zero, hence is quantifier-free. -/

theorem sigmaTrue_zero_imp_intro (H : ZFAxioms mem) {c1 c2 e : V}
    (q1 : IsQFCodeSem H c1) (q2 : IsQFCodeSem H c2) (he : IsUnivEnv H e)
    (k : PiFalse H 0 c1 e ∨ SigmaTrue H 0 c2 e) :
    SigmaTrue H 0 (kpair H (natV H 3) (kpair H c1 c2)) e := by
  refine (sigmaTrue_zero_iff H).mpr ⟨isQFCodeSem_imp H q1 q2, ?_⟩
  refine (qfTrue_imp H q1 q2 he).mpr fun t1 => ?_
  rcases k with hk | hk
  · exact absurd t1 ((piFalse_zero_iff H).mp hk).2
  · exact ((sigmaTrue_zero_iff H).mp hk).2

theorem piFalse_zero_imp_intro (H : ZFAxioms mem) {c1 c2 e : V}
    (q1 : IsQFCodeSem H c1) (q2 : IsQFCodeSem H c2) (he : IsUnivEnv H e)
    (k1 : SigmaTrue H 0 c1 e) (k2 : PiFalse H 0 c2 e) :
    PiFalse H 0 (kpair H (natV H 3) (kpair H c1 c2)) e := by
  refine (piFalse_zero_iff H).mpr ⟨isQFCodeSem_imp H q1 q2, fun ht => ?_⟩
  exact ((piFalse_zero_iff H).mp k2).2
    ((qfTrue_imp H q1 q2 he).mp ht ((sigmaTrue_zero_iff H).mp k1).2)

theorem sigmaTrue_zero_and_intro (H : ZFAxioms mem) {c1 c2 e : V}
    (q1 : IsQFCodeSem H c1) (q2 : IsQFCodeSem H c2) (he : IsUnivEnv H e)
    (k1 : SigmaTrue H 0 c1 e) (k2 : SigmaTrue H 0 c2 e) :
    SigmaTrue H 0 (kpair H (natV H 4) (kpair H c1 c2)) e :=
  (sigmaTrue_zero_iff H).mpr ⟨isQFCodeSem_and H q1 q2,
    (qfTrue_and H q1 q2 he).mpr
      ⟨((sigmaTrue_zero_iff H).mp k1).2, ((sigmaTrue_zero_iff H).mp k2).2⟩⟩

theorem piFalse_zero_and_intro (H : ZFAxioms mem) {c1 c2 e : V}
    (q1 : IsQFCodeSem H c1) (q2 : IsQFCodeSem H c2) (he : IsUnivEnv H e)
    (k : PiFalse H 0 c1 e ∨ PiFalse H 0 c2 e) :
    PiFalse H 0 (kpair H (natV H 4) (kpair H c1 c2)) e := by
  refine (piFalse_zero_iff H).mpr ⟨isQFCodeSem_and H q1 q2, fun ht => ?_⟩
  obtain ⟨t1, t2⟩ := (qfTrue_and H q1 q2 he).mp ht
  rcases k with hk | hk
  · exact ((piFalse_zero_iff H).mp hk).2 t1
  · exact ((piFalse_zero_iff H).mp hk).2 t2

theorem sigmaTrue_zero_or_intro (H : ZFAxioms mem) {c1 c2 e : V}
    (q1 : IsQFCodeSem H c1) (q2 : IsQFCodeSem H c2) (he : IsUnivEnv H e)
    (k : SigmaTrue H 0 c1 e ∨ SigmaTrue H 0 c2 e) :
    SigmaTrue H 0 (kpair H (natV H 5) (kpair H c1 c2)) e := by
  refine (sigmaTrue_zero_iff H).mpr ⟨isQFCodeSem_or H q1 q2, ?_⟩
  rcases k with hk | hk
  · exact (qfTrue_or H q1 q2 he).mpr (Or.inl ((sigmaTrue_zero_iff H).mp hk).2)
  · exact (qfTrue_or H q1 q2 he).mpr (Or.inr ((sigmaTrue_zero_iff H).mp hk).2)

theorem piFalse_zero_or_intro (H : ZFAxioms mem) {c1 c2 e : V}
    (q1 : IsQFCodeSem H c1) (q2 : IsQFCodeSem H c2) (he : IsUnivEnv H e)
    (k1 : PiFalse H 0 c1 e) (k2 : PiFalse H 0 c2 e) :
    PiFalse H 0 (kpair H (natV H 5) (kpair H c1 c2)) e := by
  refine (piFalse_zero_iff H).mpr ⟨isQFCodeSem_or H q1 q2, fun ht => ?_⟩
  rcases (qfTrue_or H q1 q2 he).mp ht with t | t
  · exact ((piFalse_zero_iff H).mp k1).2 t
  · exact ((piFalse_zero_iff H).mp k2).2 t

/-! ## The collapse property and its definability

The induction runs over codes at a level fixed outside it, so the property has
to be a `Form` with the numeral of the level as its only parameter.  Codehood is
carried as a conjunct because `IsFormCodeSem` has no inversion: without it the
connective cases would not know that their subcodes are codes, and neither the
Tarski eliminations nor the quantifier-free descent would apply. -/

/-- **The collapse property at a code.**  Both polarities, uniformly in the
environment, each guarded by its own oriented bound. -/
def CollapseAt (H : ZFAxioms mem) (n : Nat) (c : V) : Prop :=
  IsFormCodeSem H c ∧ ∀ e, IsUnivEnv H e →
    ((SigmaBounded H (natV H n) c → SigmaTrue H (n+1) c e → SigmaTrue H n c e) ∧
      (PiBounded H (natV H n) c → PiFalse H (n+1) c e → PiFalse H n c e))

/-- The collapse property as a `Form`.

| de Bruijn slot | contents                        |
| -------------- | ------------------------------- |
| `0`            | the environment `e`             |
| `1`            | the code                        |
| `2`            | the numeral of the level        |
-/
def collapseF (n : Nat) : Form :=
  fAnd (fIsFormCodeF 0)
    (fAll (fImp (fUnivEnvF 0)
      (fAnd (fImp (fSigmaBoundedF 2 1)
              (fImp (fSigmaTrueF (n+1) 1 0) (fSigmaTrueF n 1 0)))
            (fImp (fPiBoundedF 2 1)
              (fImp (fPiFalseF (n+1) 1 0) (fPiFalseF n 1 0))))))

/-- The parameter block: the numeral of the level. -/
noncomputable def envCollapse (H : ZFAxioms mem) (n : Nat) : Nat → V :=
  scons (natV H n) (fun _ => vempty H)

theorem collapseF_spec (H : ZFAxioms mem) (n : Nat) (y : V) :
    Sat mem (scons y (envCollapse H n)) (collapseF n) ↔ CollapseAt H n y := by
  unfold CollapseAt
  constructor
  · rintro ⟨hcode, h⟩
    refine ⟨(fIsFormCodeF_spec H (scons y (envCollapse H n)) 0).mp hcode, ?_⟩
    intro e he
    have h' := h e ((fUnivEnvF_spec H
      (scons e (scons y (envCollapse H n))) 0).mpr he)
    refine ⟨fun hbd hs => ?_, fun hbd hs => ?_⟩
    · exact (fSigmaTrueF_spec H n (scons e (scons y (envCollapse H n))) 1 0).mp
        (h'.1 ((fSigmaBoundedF_spec H
            (scons e (scons y (envCollapse H n))) 2 1).mpr hbd)
          ((fSigmaTrueF_spec H (n+1)
            (scons e (scons y (envCollapse H n))) 1 0).mpr hs))
    · exact (fPiFalseF_spec H n (scons e (scons y (envCollapse H n))) 1 0).mp
        (h'.2 ((fPiBoundedF_spec H
            (scons e (scons y (envCollapse H n))) 2 1).mpr hbd)
          ((fPiFalseF_spec H (n+1)
            (scons e (scons y (envCollapse H n))) 1 0).mpr hs))
  · rintro ⟨hcode, h⟩
    refine ⟨(fIsFormCodeF_spec H (scons y (envCollapse H n)) 0).mpr hcode, ?_⟩
    intro e hue
    have h' := h e ((fUnivEnvF_spec H
      (scons e (scons y (envCollapse H n))) 0).mp hue)
    refine ⟨fun hbd hs => ?_, fun hbd hs => ?_⟩
    · exact (fSigmaTrueF_spec H n (scons e (scons y (envCollapse H n))) 1 0).mpr
        (h'.1 ((fSigmaBoundedF_spec H
            (scons e (scons y (envCollapse H n))) 2 1).mp hbd)
          ((fSigmaTrueF_spec H (n+1)
            (scons e (scons y (envCollapse H n))) 1 0).mp hs))
    · exact (fPiFalseF_spec H n (scons e (scons y (envCollapse H n))) 1 0).mpr
        (h'.2 ((fPiBoundedF_spec H
            (scons e (scons y (envCollapse H n))) 2 1).mp hbd)
          ((fPiFalseF_spec H (n+1)
            (scons e (scons y (envCollapse H n))) 1 0).mp hs))

/-- At a tag below three the level-`n+1` certificate carries no row but
delegation, so the record descends to level `n` on either polarity and with no
bound at all. -/
theorem levelSat_collapse_tag_low (H : ZFAxioms mem) {n : Nat} {e b x : V}
    {t : Nat} (ht : t < 3)
    (h : LevelSat H (n+1) (kpair H (natV H t) x) e b) :
    LevelSat H n (kpair H (natV H t) x) e b := by
  obtain ⟨C, hC, hmem⟩ := h
  exact levelJustified_of_tag_low H ht (hC _ _ _ hmem).2

/-! ## The collapse into level zero

A code bounded by zero on either polarity is quantifier-free, so the target is
the quantifier-free reading and the two quantifier cases are vacuous. -/

theorem collapse_zero (H : ZFAxioms mem) :
    ∀ c, IsFormCodeSem H c → CollapseAt H 0 c := by
  refine isFormCodeSem_ind' H (CollapseAt H 0) (collapseF 0) (envCollapse H 0)
    (fun y => (collapseF_spec H 0 y).symm) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a b ha hb
    exact ⟨isFormCodeSem_memAtom H ha hb, fun _ _ =>
      ⟨fun _ h => levelSat_collapse_tag_low H (by omega) h,
       fun _ h => levelSat_collapse_tag_low H (by omega) h⟩⟩
  · intro a b ha hb
    exact ⟨isFormCodeSem_eqAtom H ha hb, fun _ _ =>
      ⟨fun _ h => levelSat_collapse_tag_low H (by omega) h,
       fun _ h => levelSat_collapse_tag_low H (by omega) h⟩⟩
  · exact ⟨isFormCodeSem_bot H, fun _ _ =>
      ⟨fun _ h => levelSat_collapse_tag_low H (by omega) h,
       fun _ h => levelSat_collapse_tag_low H (by omega) h⟩⟩
  · rintro a b ⟨hca, iha⟩ ⟨hcb, ihb⟩
    refine ⟨isFormCodeSem_imp H hca hcb, fun e he => ⟨?_, ?_⟩⟩
    · intro hbd h1
      obtain ⟨ba, bb⟩ := sigmaBounded_imp H (natV_mem_omega H 0) hbd
      have qa : IsQFCodeSem H a := isQFCodeSem_of_quantBounded_zero H a hca
        (quantBounded_of_piBounded H (natV_mem_omega H 0) ba)
      have qb : IsQFCodeSem H b := isQFCodeSem_of_quantBounded_zero H b hcb
        (quantBounded_of_sigmaBounded H (natV_mem_omega H 0) bb)
      rcases sigmaTrue_imp_elim H 1 hca hcb he h1 with k | k
      · exact sigmaTrue_zero_imp_intro H qa qb he (Or.inl ((iha e he).2 ba k))
      · exact sigmaTrue_zero_imp_intro H qa qb he (Or.inr ((ihb e he).1 bb k))
    · intro hbd h1
      obtain ⟨ba, bb⟩ := piBounded_imp H (natV_mem_omega H 0) hbd
      have qa : IsQFCodeSem H a := isQFCodeSem_of_quantBounded_zero H a hca
        (quantBounded_of_sigmaBounded H (natV_mem_omega H 0) ba)
      have qb : IsQFCodeSem H b := isQFCodeSem_of_quantBounded_zero H b hcb
        (quantBounded_of_piBounded H (natV_mem_omega H 0) bb)
      obtain ⟨k1, k2⟩ := piFalse_imp_elim H 1 hca hcb he h1
      exact piFalse_zero_imp_intro H qa qb he ((iha e he).1 ba k1)
        ((ihb e he).2 bb k2)
  · rintro a b ⟨hca, iha⟩ ⟨hcb, ihb⟩
    refine ⟨isFormCodeSem_and H hca hcb, fun e he => ⟨?_, ?_⟩⟩
    · intro hbd h1
      obtain ⟨ba, bb⟩ := sigmaBounded_and H (natV_mem_omega H 0) hbd
      have qa : IsQFCodeSem H a := isQFCodeSem_of_quantBounded_zero H a hca
        (quantBounded_of_sigmaBounded H (natV_mem_omega H 0) ba)
      have qb : IsQFCodeSem H b := isQFCodeSem_of_quantBounded_zero H b hcb
        (quantBounded_of_sigmaBounded H (natV_mem_omega H 0) bb)
      obtain ⟨k1, k2⟩ := sigmaTrue_and_elim H 1 hca hcb he h1
      exact sigmaTrue_zero_and_intro H qa qb he ((iha e he).1 ba k1)
        ((ihb e he).1 bb k2)
    · intro hbd h1
      obtain ⟨ba, bb⟩ := piBounded_and H (natV_mem_omega H 0) hbd
      have qa : IsQFCodeSem H a := isQFCodeSem_of_quantBounded_zero H a hca
        (quantBounded_of_piBounded H (natV_mem_omega H 0) ba)
      have qb : IsQFCodeSem H b := isQFCodeSem_of_quantBounded_zero H b hcb
        (quantBounded_of_piBounded H (natV_mem_omega H 0) bb)
      rcases piFalse_and_elim H 1 hca hcb he h1 with k | k
      · exact piFalse_zero_and_intro H qa qb he (Or.inl ((iha e he).2 ba k))
      · exact piFalse_zero_and_intro H qa qb he (Or.inr ((ihb e he).2 bb k))
  · rintro a b ⟨hca, iha⟩ ⟨hcb, ihb⟩
    refine ⟨isFormCodeSem_or H hca hcb, fun e he => ⟨?_, ?_⟩⟩
    · intro hbd h1
      obtain ⟨ba, bb⟩ := sigmaBounded_or H (natV_mem_omega H 0) hbd
      have qa : IsQFCodeSem H a := isQFCodeSem_of_quantBounded_zero H a hca
        (quantBounded_of_sigmaBounded H (natV_mem_omega H 0) ba)
      have qb : IsQFCodeSem H b := isQFCodeSem_of_quantBounded_zero H b hcb
        (quantBounded_of_sigmaBounded H (natV_mem_omega H 0) bb)
      rcases sigmaTrue_or_elim H 1 hca hcb he h1 with k | k
      · exact sigmaTrue_zero_or_intro H qa qb he (Or.inl ((iha e he).1 ba k))
      · exact sigmaTrue_zero_or_intro H qa qb he (Or.inr ((ihb e he).1 bb k))
    · intro hbd h1
      obtain ⟨ba, bb⟩ := piBounded_or H (natV_mem_omega H 0) hbd
      have qa : IsQFCodeSem H a := isQFCodeSem_of_quantBounded_zero H a hca
        (quantBounded_of_piBounded H (natV_mem_omega H 0) ba)
      have qb : IsQFCodeSem H b := isQFCodeSem_of_quantBounded_zero H b hcb
        (quantBounded_of_piBounded H (natV_mem_omega H 0) bb)
      obtain ⟨k1, k2⟩ := piFalse_or_elim H 1 hca hcb he h1
      exact piFalse_zero_or_intro H qa qb he ((iha e he).2 ba k1)
        ((ihb e he).2 bb k2)
  · rintro a ⟨hca, -⟩
    exact ⟨isFormCodeSem_all H hca, fun _ _ =>
      ⟨fun hbd _ => absurd hbd (not_sigmaBounded_zero_all H),
       fun hbd _ => absurd hbd (not_piBounded_zero_all H)⟩⟩
  · rintro a ⟨hca, -⟩
    exact ⟨isFormCodeSem_ex H hca, fun _ _ =>
      ⟨fun hbd _ => absurd hbd (not_sigmaBounded_zero_ex H),
       fun hbd _ => absurd hbd (not_piBounded_zero_ex H)⟩⟩

/-! ## The collapse into a positive level

Here each connective case is one application of the corresponding introduction
lemma, and the two quantifier cases are the ones the theorem exists for.  At a
universal head on the Sigma side the level-`n+1` certificate delegates to level
`n` under a Pi-bound at `n`; the Sigma-bound at `n` in the hypothesis is a
Pi-bound at `n-1`, and `PiTrue` is antitone, so the same delegation is available
one level down.  The existential head on the Pi side is dual, using
monotonicity of `SigmaTrue` on the negated side. -/

theorem collapse_succ (H : ZFAxioms mem) (m : Nat) :
    ∀ c, IsFormCodeSem H c → CollapseAt H (m+1) c := by
  refine isFormCodeSem_ind' H (CollapseAt H (m+1)) (collapseF (m+1))
    (envCollapse H (m+1)) (fun y => (collapseF_spec H (m+1) y).symm)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a b ha hb
    exact ⟨isFormCodeSem_memAtom H ha hb, fun _ _ =>
      ⟨fun _ h => levelSat_collapse_tag_low H (by omega) h,
       fun _ h => levelSat_collapse_tag_low H (by omega) h⟩⟩
  · intro a b ha hb
    exact ⟨isFormCodeSem_eqAtom H ha hb, fun _ _ =>
      ⟨fun _ h => levelSat_collapse_tag_low H (by omega) h,
       fun _ h => levelSat_collapse_tag_low H (by omega) h⟩⟩
  · exact ⟨isFormCodeSem_bot H, fun _ _ =>
      ⟨fun _ h => levelSat_collapse_tag_low H (by omega) h,
       fun _ h => levelSat_collapse_tag_low H (by omega) h⟩⟩
  · rintro a b ⟨hca, iha⟩ ⟨hcb, ihb⟩
    refine ⟨isFormCodeSem_imp H hca hcb, fun e he => ⟨?_, ?_⟩⟩
    · intro hbd h1
      obtain ⟨ba, bb⟩ := sigmaBounded_imp H (natV_mem_omega H (m+1)) hbd
      rcases sigmaTrue_imp_elim H (m+1+1) hca hcb he h1 with k | k
      · exact sigmaTrue_imp_intro H m he (Or.inl ((iha e he).2 ba k))
      · exact sigmaTrue_imp_intro H m he (Or.inr ((ihb e he).1 bb k))
    · intro hbd h1
      obtain ⟨ba, bb⟩ := piBounded_imp H (natV_mem_omega H (m+1)) hbd
      obtain ⟨k1, k2⟩ := piFalse_imp_elim H (m+1+1) hca hcb he h1
      exact piFalse_imp_intro H m he ((iha e he).1 ba k1) ((ihb e he).2 bb k2)
  · rintro a b ⟨hca, iha⟩ ⟨hcb, ihb⟩
    refine ⟨isFormCodeSem_and H hca hcb, fun e he => ⟨?_, ?_⟩⟩
    · intro hbd h1
      obtain ⟨ba, bb⟩ := sigmaBounded_and H (natV_mem_omega H (m+1)) hbd
      obtain ⟨k1, k2⟩ := sigmaTrue_and_elim H (m+1+1) hca hcb he h1
      exact sigmaTrue_and_intro H m he ((iha e he).1 ba k1) ((ihb e he).1 bb k2)
    · intro hbd h1
      obtain ⟨ba, bb⟩ := piBounded_and H (natV_mem_omega H (m+1)) hbd
      rcases piFalse_and_elim H (m+1+1) hca hcb he h1 with k | k
      · exact piFalse_and_intro H m he (Or.inl ((iha e he).2 ba k))
      · exact piFalse_and_intro H m he (Or.inr ((ihb e he).2 bb k))
  · rintro a b ⟨hca, iha⟩ ⟨hcb, ihb⟩
    refine ⟨isFormCodeSem_or H hca hcb, fun e he => ⟨?_, ?_⟩⟩
    · intro hbd h1
      obtain ⟨ba, bb⟩ := sigmaBounded_or H (natV_mem_omega H (m+1)) hbd
      rcases sigmaTrue_or_elim H (m+1+1) hca hcb he h1 with k | k
      · exact sigmaTrue_or_intro H m he (Or.inl ((iha e he).1 ba k))
      · exact sigmaTrue_or_intro H m he (Or.inr ((ihb e he).1 bb k))
    · intro hbd h1
      obtain ⟨ba, bb⟩ := piBounded_or H (natV_mem_omega H (m+1)) hbd
      obtain ⟨k1, k2⟩ := piFalse_or_elim H (m+1+1) hca hcb he h1
      exact piFalse_or_intro H m he ((iha e he).2 ba k1) ((ihb e he).2 bb k2)
  · rintro a ⟨hca, iha⟩
    refine ⟨isFormCodeSem_all H hca, fun e he => ⟨?_, ?_⟩⟩
    · intro hbd h1
      rcases sigmaTrue_all_inv H (m+1) h1 with k | ⟨-, hpt⟩
      · exact k
      · exact sigmaTrue_all_of_piTrue H m he
          (piBounded_of_sigmaBounded_all H hbd)
          (piTrue_anti H (Nat.le_succ m) he hpt)
    · intro hbd h1
      obtain ⟨d, hd⟩ := piFalse_all_elim H (m+1+1) he h1
      exact piFalse_all_intro H m he
        ((iha (econs H d e) (econs_isUnivEnv H he d)).2
          (piBounded_all H (natV_mem_omega H (m+1)) hbd) hd)
  · rintro a ⟨hca, iha⟩
    refine ⟨isFormCodeSem_ex H hca, fun e he => ⟨?_, ?_⟩⟩
    · intro hbd h1
      obtain ⟨d, hd⟩ := sigmaTrue_ex_elim H (m+1+1) he h1
      exact sigmaTrue_ex_intro H m he
        ((iha (econs H d e) (econs_isUnivEnv H he d)).1
          (sigmaBounded_ex H (natV_mem_omega H (m+1)) hbd) hd)
    · intro hbd h1
      rcases piFalse_ex_inv H (m+1) h1 with k | ⟨-, hns⟩
      · exact k
      · exact piFalse_ex_of_not_sigmaTrue H m he
          (sigmaBounded_of_piBounded_ex H hbd)
          (fun hs => hns (sigmaTrue_mono H (Nat.le_succ m) he hs))

/-! ## The theorem

The two inductions above differ only in how a connective case is closed, so the
statement is uniform in the level. -/

theorem collapseAt_of_isFormCodeSem (H : ZFAxioms mem) (n : Nat) :
    ∀ c, IsFormCodeSem H c → CollapseAt H n c := by
  cases n with
  | zero => exact collapse_zero H
  | succ m => exact collapse_succ H m

/-- **The level-collapse theorem, Sigma side.**  A Sigma-bounded code that is
Sigma-true at level `n+1` is already Sigma-true at level `n`. -/
theorem sigmaTrue_collapse (H : ZFAxioms mem) (n : Nat) {c e : V}
    (hc : IsFormCodeSem H c) (he : IsUnivEnv H e)
    (hb : SigmaBounded H (natV H n) c) (h : SigmaTrue H (n+1) c e) :
    SigmaTrue H n c e :=
  ((collapseAt_of_isFormCodeSem H n c hc).2 e he).1 hb h

/-- **The level-collapse theorem, Pi side.**  A Pi-bounded code that is Pi-false
at level `n+1` is already Pi-false at level `n`. -/
theorem piFalse_collapse (H : ZFAxioms mem) (n : Nat) {c e : V}
    (hc : IsFormCodeSem H c) (he : IsUnivEnv H e)
    (hb : PiBounded H (natV H n) c) (h : PiFalse H (n+1) c e) :
    PiFalse H n c e :=
  ((collapseAt_of_isFormCodeSem H n c hc).2 e he).2 hb h

/-- **The collapse iterated.**  A bound at `k` is a bound at every larger level,
so the one-step collapse composes all the way down to `k`. -/
theorem sigmaTrue_collapse_le (H : ZFAxioms mem) {k : Nat} {c e : V}
    (hc : IsFormCodeSem H c) (he : IsUnivEnv H e)
    (hb : SigmaBounded H (natV H k) c) :
    ∀ n, k ≤ n → SigmaTrue H n c e → SigmaTrue H k c e := by
  intro n
  induction n with
  | zero =>
      intro hkn h
      have hk : k = 0 := Nat.le_zero.mp hkn
      subst hk
      exact h
  | succ n ih =>
      intro hkn h
      by_cases hk : k = n+1
      · subst hk
        exact h
      · have hkn' : k ≤ n := by omega
        exact ih hkn' (sigmaTrue_collapse H n hc he
          (sigmaBounded_natV_le H hkn' hb) h)

theorem piFalse_collapse_le (H : ZFAxioms mem) {k : Nat} {c e : V}
    (hc : IsFormCodeSem H c) (he : IsUnivEnv H e)
    (hb : PiBounded H (natV H k) c) :
    ∀ n, k ≤ n → PiFalse H n c e → PiFalse H k c e := by
  intro n
  induction n with
  | zero =>
      intro hkn h
      have hk : k = 0 := Nat.le_zero.mp hkn
      subst hk
      exact h
  | succ n ih =>
      intro hkn h
      by_cases hk : k = n+1
      · subst hk
        exact h
      · have hkn' : k ≤ n := by omega
        exact ih hkn' (piFalse_collapse H n hc he
          (piBounded_natV_le H hkn' hb) h)

/-- **Sigma-truth is level-invariant on Sigma-bounded codes**, and dually for
Pi-falsity.  Monotonicity supplies one direction and the collapse the other. -/
theorem sigmaTrue_collapse_iff (H : ZFAxioms mem) {k n : Nat} (hkn : k ≤ n)
    {c e : V} (hc : IsFormCodeSem H c) (he : IsUnivEnv H e)
    (hb : SigmaBounded H (natV H k) c) :
    SigmaTrue H n c e ↔ SigmaTrue H k c e :=
  ⟨sigmaTrue_collapse_le H hc he hb n hkn, sigmaTrue_mono H hkn he⟩

theorem piFalse_collapse_iff (H : ZFAxioms mem) {k n : Nat} (hkn : k ≤ n)
    {c e : V} (hc : IsFormCodeSem H c) (he : IsUnivEnv H e)
    (hb : PiBounded H (natV H k) c) :
    PiFalse H n c e ↔ PiFalse H k c e :=
  ⟨piFalse_collapse_le H hc he hb n hkn, piFalse_mono H hkn he⟩

/-- **Pi-truth is monotone in the level on Pi-bounded codes.**  This is the
upgrade of `piTrue_anti`: the antitone direction is monotonicity of the
certified notion `PiFalse`, and the missing direction is exactly the collapse. -/
theorem piTrue_mono (H : ZFAxioms mem) {k n : Nat} (hkn : k ≤ n) {c e : V}
    (hc : IsFormCodeSem H c) (he : IsUnivEnv H e)
    (hb : PiBounded H (natV H k) c) (h : PiTrue H k c e) : PiTrue H n c e :=
  fun hf => h (piFalse_collapse_le H hc he hb n hkn hf)

/-! ## Where a quantified code entered the hierarchy

A universal code is never recorded on the Sigma side; it can only have been
delegated, at some level strictly below the one in question, under a Pi-bound
there.  Iterating the inversion locates that level.  The bound is what makes the
collapse applicable at the quantifier cases of exclusivity, and it is not
recoverable from the level-`n` statement alone. -/

/-- **A Sigma-true universal code was delegated at an earlier level.** -/
theorem sigmaTrue_all_inv' (H : ZFAxioms mem) :
    ∀ (n : Nat) {c1 e : V}, SigmaTrue H n (kpair H (natV H 6) c1) e →
      ∃ k, k < n ∧ PiBounded H (natV H k) (kpair H (natV H 6) c1) ∧
        PiTrue H k (kpair H (natV H 6) c1) e := by
  intro n
  induction n with
  | zero =>
      intro c1 e h
      rw [sigmaTrue_zero_iff] at h
      exact absurd (quantBounded_zero_of_isQFCodeSem H h.1)
        (not_quantBounded_zero_all H)
  | succ m ihm =>
      intro c1 e h
      rcases sigmaTrue_all_inv H m h with k | ⟨hb, hp⟩
      · obtain ⟨j, hj, hbj, hpj⟩ := ihm k
        exact ⟨j, by omega, hbj, hpj⟩
      · exact ⟨m, by omega, hb, hp⟩

/-- **A Pi-false existential code was delegated at an earlier level.** -/
theorem piFalse_ex_inv' (H : ZFAxioms mem) :
    ∀ (n : Nat) {c1 e : V}, PiFalse H n (kpair H (natV H 7) c1) e →
      ∃ k, k < n ∧ SigmaBounded H (natV H k) (kpair H (natV H 7) c1) ∧
        ¬ SigmaTrue H k (kpair H (natV H 7) c1) e := by
  intro n
  induction n with
  | zero =>
      intro c1 e h
      exact absurd (quantBounded_zero_of_isQFCodeSem H h.1)
        (not_quantBounded_zero_ex H)
  | succ m ihm =>
      intro c1 e h
      rcases piFalse_ex_inv H m h with k | ⟨hb, hp⟩
      · obtain ⟨j, hj, hbj, hpj⟩ := ihm k
        exact ⟨j, by omega, hbj, hpj⟩
      · exact ⟨m, by omega, hb, hp⟩

/-! ## Exclusivity

No code is both Sigma-true and Pi-false at the same level.  The statement needs
no bound: the connective cases descend to subcodes at the same level, the atomic
cases descend to the previous level, and the two quantifier cases consume the
collapse at the level the delegation happened.

`BoundedZFCConsistency.UniverseTruthLevel` proves the level-zero instance from
the fact that both polarities read one bit of one proposition; the induction
below bottoms out there. -/

/-- The exclusivity property at a code. -/
def ExclAt (H : ZFAxioms mem) (n : Nat) (c : V) : Prop :=
  IsFormCodeSem H c ∧ ∀ e, IsUnivEnv H e → SigmaTrue H n c e → ¬ PiFalse H n c e

/-- Exclusivity as a `Form`.

| de Bruijn slot | contents            |
| -------------- | ------------------- |
| `0`            | the environment `e` |
| `1`            | the code            |
-/
def exclF (n : Nat) : Form :=
  fAnd (fIsFormCodeF 0)
    (fAll (fImp (fUnivEnvF 0)
      (fImp (fSigmaTrueF n 1 0) (fImp (fPiFalseF n 1 0) fBot))))

/-- The exclusivity property needs no parameters. -/
noncomputable def envExcl (H : ZFAxioms mem) : Nat → V := fun _ => vempty H

theorem exclF_spec (H : ZFAxioms mem) (n : Nat) (y : V) :
    Sat mem (scons y (envExcl H)) (exclF n) ↔ ExclAt H n y := by
  unfold ExclAt
  constructor
  · rintro ⟨hcode, h⟩
    refine ⟨(fIsFormCodeF_spec H (scons y (envExcl H)) 0).mp hcode, ?_⟩
    intro e he hs hp
    exact h e ((fUnivEnvF_spec H (scons e (scons y (envExcl H))) 0).mpr he)
      ((fSigmaTrueF_spec H n (scons e (scons y (envExcl H))) 1 0).mpr hs)
      ((fPiFalseF_spec H n (scons e (scons y (envExcl H))) 1 0).mpr hp)
  · rintro ⟨hcode, h⟩
    refine ⟨(fIsFormCodeF_spec H (scons y (envExcl H)) 0).mpr hcode, ?_⟩
    intro e hue hs hp
    exact h e ((fUnivEnvF_spec H (scons e (scons y (envExcl H))) 0).mp hue)
      ((fSigmaTrueF_spec H n (scons e (scons y (envExcl H))) 1 0).mp hs)
      ((fPiFalseF_spec H n (scons e (scons y (envExcl H))) 1 0).mp hp)

/-- **Sigma-truth and Pi-falsity are exclusive at every level.**  The two
polarity-switch rows are the only places where the argument leaves the level it
starts at, and they are exactly where the collapse is used. -/
theorem sigmaTrue_not_piFalse (H : ZFAxioms mem) :
    ∀ (n : Nat) (c e : V), IsFormCodeSem H c → IsUnivEnv H e →
      SigmaTrue H n c e → ¬ PiFalse H n c e := by
  intro n
  induction n with
  | zero =>
      intro c e _ _ hs hp
      exact sigmaTrue_not_piFalse_zero H hs hp
  | succ m ih =>
      have key : ∀ c, IsFormCodeSem H c → ExclAt H (m+1) c := by
        refine isFormCodeSem_ind' H (ExclAt H (m+1)) (exclF (m+1)) (envExcl H)
          (fun y => (exclF_spec H (m+1) y).symm) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · intro a b ha hb
          refine ⟨isFormCodeSem_memAtom H ha hb, fun e he hs hp => ?_⟩
          exact ih _ e (isFormCodeSem_memAtom H ha hb) he
            (levelSat_collapse_tag_low H (by omega) hs)
            (levelSat_collapse_tag_low H (by omega) hp)
        · intro a b ha hb
          refine ⟨isFormCodeSem_eqAtom H ha hb, fun e he hs hp => ?_⟩
          exact ih _ e (isFormCodeSem_eqAtom H ha hb) he
            (levelSat_collapse_tag_low H (by omega) hs)
            (levelSat_collapse_tag_low H (by omega) hp)
        · exact ⟨isFormCodeSem_bot H,
            fun _ _ hs _ => absurd hs (sigmaTrue_bot H (m+1))⟩
        · rintro a b ⟨hca, iha⟩ ⟨hcb, ihb⟩
          refine ⟨isFormCodeSem_imp H hca hcb, fun e he hs hp => ?_⟩
          obtain ⟨k1, k2⟩ := piFalse_imp_elim H (m+1) hca hcb he hp
          rcases sigmaTrue_imp_elim H (m+1) hca hcb he hs with k | k
          · exact iha e he k1 k
          · exact ihb e he k k2
        · rintro a b ⟨hca, iha⟩ ⟨hcb, ihb⟩
          refine ⟨isFormCodeSem_and H hca hcb, fun e he hs hp => ?_⟩
          obtain ⟨k1, k2⟩ := sigmaTrue_and_elim H (m+1) hca hcb he hs
          rcases piFalse_and_elim H (m+1) hca hcb he hp with k | k
          · exact iha e he k1 k
          · exact ihb e he k2 k
        · rintro a b ⟨hca, iha⟩ ⟨hcb, ihb⟩
          refine ⟨isFormCodeSem_or H hca hcb, fun e he hs hp => ?_⟩
          obtain ⟨k1, k2⟩ := piFalse_or_elim H (m+1) hca hcb he hp
          rcases sigmaTrue_or_elim H (m+1) hca hcb he hs with k | k
          · exact iha e he k k1
          · exact ihb e he k k2
        · rintro a ⟨hca, -⟩
          refine ⟨isFormCodeSem_all H hca, fun e he hs hp => ?_⟩
          obtain ⟨k, hk, hpb, hpt⟩ := sigmaTrue_all_inv' H (m+1) hs
          exact hpt (piFalse_collapse_le H (isFormCodeSem_all H hca) he hpb
            (m+1) (Nat.le_of_lt hk) hp)
        · rintro a ⟨hca, -⟩
          refine ⟨isFormCodeSem_ex H hca, fun e he hs hp => ?_⟩
          obtain ⟨k, hk, hsb, hns⟩ := piFalse_ex_inv' H (m+1) hp
          exact hns (sigmaTrue_collapse_le H (isFormCodeSem_ex H hca) he hsb
            (m+1) (Nat.le_of_lt hk) hs)
      intro c e hc he hs hp
      exact (key c hc).2 e he hs hp

/-- **Sigma-truth implies Pi-truth at every level**, the readable form of
exclusivity. -/
theorem piTrue_of_sigmaTrue (H : ZFAxioms mem) (n : Nat) {c e : V}
    (hc : IsFormCodeSem H c) (he : IsUnivEnv H e) (h : SigmaTrue H n c e) :
    PiTrue H n c e :=
  sigmaTrue_not_piFalse H n c e hc he h

/-! ## Totality

The complement of exclusivity: a bounded code is Sigma-true or Pi-false at the
level above its bound.  The two statements are proved separately because they
have nothing in common — totality needs the bound and no collapse, exclusivity
needs the collapse and no bound.

The oriented bound is what makes the quantifier cases immediate rather than
inductive: at a universal head the delegated row is *available* under a Pi-bound,
so excluded middle on the previous level's Pi-falsity already decides the
code. -/

/-- A Sigma-bound at a universal head is a Pi-bound one level down, and the
level is positive. -/
theorem exists_pred_piBounded_of_sigmaBounded_all (H : ZFAxioms mem) {a : V}
    {n : Nat} (h : SigmaBounded H (natV H n) (kpair H (natV H 6) a)) :
    ∃ m, n = m + 1 ∧ PiBounded H (natV H m) (kpair H (natV H 6) a) := by
  cases n with
  | zero => exact absurd h (not_sigmaBounded_zero_all H)
  | succ m => exact ⟨m, rfl, piBounded_of_sigmaBounded_all H h⟩

/-- A Pi-bound at an existential head is a Sigma-bound one level down. -/
theorem exists_pred_sigmaBounded_of_piBounded_ex (H : ZFAxioms mem) {a : V}
    {n : Nat} (h : PiBounded H (natV H n) (kpair H (natV H 7) a)) :
    ∃ m, n = m + 1 ∧ SigmaBounded H (natV H m) (kpair H (natV H 7) a) := by
  cases n with
  | zero => exact absurd h (not_piBounded_zero_ex H)
  | succ m => exact ⟨m, rfl, sigmaBounded_of_piBounded_ex H h⟩

/-- A false membership atom is Pi-false at every level. -/
theorem piFalse_memAtom_of_not (H : ZFAxioms mem) (n : Nat) {i j e : V}
    (hi : mem i (omegaV H)) (hj : mem j (omegaV H)) (he : IsUnivEnv H e)
    (hm : ¬ mem (applyV H e i) (applyV H e j)) :
    PiFalse H n (kpair H (natV H 0) (kpair H i j)) e :=
  piFalse_mono H (Nat.zero_le n) he ((piFalse_zero_iff H).mpr
    ⟨isQFCodeSem_memAtom H hi hj,
      fun ht => hm ((qfTrue_memAtom H hi hj he).mp ht)⟩)

/-- A false equality atom is Pi-false at every level. -/
theorem piFalse_eqAtom_of_ne (H : ZFAxioms mem) (n : Nat) {i j e : V}
    (hi : mem i (omegaV H)) (hj : mem j (omegaV H)) (he : IsUnivEnv H e)
    (hm : applyV H e i ≠ applyV H e j) :
    PiFalse H n (kpair H (natV H 1) (kpair H i j)) e :=
  piFalse_mono H (Nat.zero_le n) he ((piFalse_zero_iff H).mpr
    ⟨isQFCodeSem_eqAtom H hi hj,
      fun ht => hm ((qfTrue_eqAtom H hi hj he).mp ht)⟩)

/-- The connective steps of totality, isolated because each is used on both
polarities of the bound and the two uses differ only in which oriented descent
supplied the premises. -/
theorem imp_total_step (H : ZFAxioms mem) (n : Nat) {a b e : V}
    (he : IsUnivEnv H e)
    (ka : SigmaTrue H (n+1) a e ∨ PiFalse H (n+1) a e)
    (kb : SigmaTrue H (n+1) b e ∨ PiFalse H (n+1) b e) :
    SigmaTrue H (n+1) (kpair H (natV H 3) (kpair H a b)) e ∨
      PiFalse H (n+1) (kpair H (natV H 3) (kpair H a b)) e := by
  rcases ka with ka | ka
  · rcases kb with kb | kb
    · exact Or.inl (sigmaTrue_imp_intro H n he (Or.inr kb))
    · exact Or.inr (piFalse_imp_intro H n he ka kb)
  · exact Or.inl (sigmaTrue_imp_intro H n he (Or.inl ka))

theorem and_total_step (H : ZFAxioms mem) (n : Nat) {a b e : V}
    (he : IsUnivEnv H e)
    (ka : SigmaTrue H (n+1) a e ∨ PiFalse H (n+1) a e)
    (kb : SigmaTrue H (n+1) b e ∨ PiFalse H (n+1) b e) :
    SigmaTrue H (n+1) (kpair H (natV H 4) (kpair H a b)) e ∨
      PiFalse H (n+1) (kpair H (natV H 4) (kpair H a b)) e := by
  rcases ka with ka | ka
  · rcases kb with kb | kb
    · exact Or.inl (sigmaTrue_and_intro H n he ka kb)
    · exact Or.inr (piFalse_and_intro H n he (Or.inr kb))
  · exact Or.inr (piFalse_and_intro H n he (Or.inl ka))

theorem or_total_step (H : ZFAxioms mem) (n : Nat) {a b e : V}
    (he : IsUnivEnv H e)
    (ka : SigmaTrue H (n+1) a e ∨ PiFalse H (n+1) a e)
    (kb : SigmaTrue H (n+1) b e ∨ PiFalse H (n+1) b e) :
    SigmaTrue H (n+1) (kpair H (natV H 5) (kpair H a b)) e ∨
      PiFalse H (n+1) (kpair H (natV H 5) (kpair H a b)) e := by
  rcases ka with ka | ka
  · exact Or.inl (sigmaTrue_or_intro H n he (Or.inl ka))
  · rcases kb with kb | kb
    · exact Or.inl (sigmaTrue_or_intro H n he (Or.inr kb))
    · exact Or.inr (piFalse_or_intro H n he ka kb)

/-- **The totality property at a code**, on both orientations of the bound. -/
def TotalAt (H : ZFAxioms mem) (n : Nat) (c : V) : Prop :=
  IsFormCodeSem H c ∧ ∀ e, IsUnivEnv H e →
    ((SigmaBounded H (natV H n) c →
        SigmaTrue H (n+1) c e ∨ PiFalse H (n+1) c e) ∧
      (PiBounded H (natV H n) c →
        SigmaTrue H (n+1) c e ∨ PiFalse H (n+1) c e))

/-- Totality as a `Form`, with the slot table of `collapseF`. -/
def totalF (n : Nat) : Form :=
  fAnd (fIsFormCodeF 0)
    (fAll (fImp (fUnivEnvF 0)
      (fAnd (fImp (fSigmaBoundedF 2 1)
              (fOr (fSigmaTrueF (n+1) 1 0) (fPiFalseF (n+1) 1 0)))
            (fImp (fPiBoundedF 2 1)
              (fOr (fSigmaTrueF (n+1) 1 0) (fPiFalseF (n+1) 1 0))))))

theorem totalF_spec (H : ZFAxioms mem) (n : Nat) (y : V) :
    Sat mem (scons y (envCollapse H n)) (totalF n) ↔ TotalAt H n y := by
  unfold TotalAt
  constructor
  · rintro ⟨hcode, h⟩
    refine ⟨(fIsFormCodeF_spec H (scons y (envCollapse H n)) 0).mp hcode, ?_⟩
    intro e he
    have h' := h e ((fUnivEnvF_spec H
      (scons e (scons y (envCollapse H n))) 0).mpr he)
    constructor
    · intro hbd
      rcases h'.1 ((fSigmaBoundedF_spec H
          (scons e (scons y (envCollapse H n))) 2 1).mpr hbd) with k | k
      · exact Or.inl ((fSigmaTrueF_spec H (n+1)
          (scons e (scons y (envCollapse H n))) 1 0).mp k)
      · exact Or.inr ((fPiFalseF_spec H (n+1)
          (scons e (scons y (envCollapse H n))) 1 0).mp k)
    · intro hbd
      rcases h'.2 ((fPiBoundedF_spec H
          (scons e (scons y (envCollapse H n))) 2 1).mpr hbd) with k | k
      · exact Or.inl ((fSigmaTrueF_spec H (n+1)
          (scons e (scons y (envCollapse H n))) 1 0).mp k)
      · exact Or.inr ((fPiFalseF_spec H (n+1)
          (scons e (scons y (envCollapse H n))) 1 0).mp k)
  · rintro ⟨hcode, h⟩
    refine ⟨(fIsFormCodeF_spec H (scons y (envCollapse H n)) 0).mpr hcode, ?_⟩
    intro e hue
    have h' := h e ((fUnivEnvF_spec H
      (scons e (scons y (envCollapse H n))) 0).mp hue)
    constructor
    · intro hbd
      rcases h'.1 ((fSigmaBoundedF_spec H
          (scons e (scons y (envCollapse H n))) 2 1).mp hbd) with k | k
      · exact Or.inl ((fSigmaTrueF_spec H (n+1)
          (scons e (scons y (envCollapse H n))) 1 0).mpr k)
      · exact Or.inr ((fPiFalseF_spec H (n+1)
          (scons e (scons y (envCollapse H n))) 1 0).mpr k)
    · intro hbd
      rcases h'.2 ((fPiBoundedF_spec H
          (scons e (scons y (envCollapse H n))) 2 1).mp hbd) with k | k
      · exact Or.inl ((fSigmaTrueF_spec H (n+1)
          (scons e (scons y (envCollapse H n))) 1 0).mpr k)
      · exact Or.inr ((fPiFalseF_spec H (n+1)
          (scons e (scons y (envCollapse H n))) 1 0).mpr k)

theorem totalAt_of_isFormCodeSem (H : ZFAxioms mem) (n : Nat) :
    ∀ c, IsFormCodeSem H c → TotalAt H n c := by
  refine isFormCodeSem_ind' H (TotalAt H n) (totalF n) (envCollapse H n)
    (fun y => (totalF_spec H n y).symm) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a b ha hb
    refine ⟨isFormCodeSem_memAtom H ha hb, fun e he => ?_⟩
    have hd : SigmaTrue H (n+1) (kpair H (natV H 0) (kpair H a b)) e ∨
        PiFalse H (n+1) (kpair H (natV H 0) (kpair H a b)) e := by
      rcases Classical.em (mem (applyV H e a) (applyV H e b)) with hm | hm
      · exact Or.inl ((sigmaTrue_memAtom H (n+1) ha hb he).mpr hm)
      · exact Or.inr (piFalse_memAtom_of_not H (n+1) ha hb he hm)
    exact ⟨fun _ => hd, fun _ => hd⟩
  · intro a b ha hb
    refine ⟨isFormCodeSem_eqAtom H ha hb, fun e he => ?_⟩
    have hd : SigmaTrue H (n+1) (kpair H (natV H 1) (kpair H a b)) e ∨
        PiFalse H (n+1) (kpair H (natV H 1) (kpair H a b)) e := by
      rcases Classical.em (applyV H e a = applyV H e b) with hm | hm
      · exact Or.inl ((sigmaTrue_eqAtom H (n+1) ha hb he).mpr hm)
      · exact Or.inr (piFalse_eqAtom_of_ne H (n+1) ha hb he hm)
    exact ⟨fun _ => hd, fun _ => hd⟩
  · exact ⟨isFormCodeSem_bot H, fun e he =>
      ⟨fun _ => Or.inr (piFalse_bot H (n+1) he),
       fun _ => Or.inr (piFalse_bot H (n+1) he)⟩⟩
  · rintro a b ⟨hca, iha⟩ ⟨hcb, ihb⟩
    refine ⟨isFormCodeSem_imp H hca hcb, fun e he => ⟨?_, ?_⟩⟩
    · intro hbd
      obtain ⟨ba, bb⟩ := sigmaBounded_imp H (natV_mem_omega H n) hbd
      exact imp_total_step H n he ((iha e he).2 ba) ((ihb e he).1 bb)
    · intro hbd
      obtain ⟨ba, bb⟩ := piBounded_imp H (natV_mem_omega H n) hbd
      exact imp_total_step H n he ((iha e he).1 ba) ((ihb e he).2 bb)
  · rintro a b ⟨hca, iha⟩ ⟨hcb, ihb⟩
    refine ⟨isFormCodeSem_and H hca hcb, fun e he => ⟨?_, ?_⟩⟩
    · intro hbd
      obtain ⟨ba, bb⟩ := sigmaBounded_and H (natV_mem_omega H n) hbd
      exact and_total_step H n he ((iha e he).1 ba) ((ihb e he).1 bb)
    · intro hbd
      obtain ⟨ba, bb⟩ := piBounded_and H (natV_mem_omega H n) hbd
      exact and_total_step H n he ((iha e he).2 ba) ((ihb e he).2 bb)
  · rintro a b ⟨hca, iha⟩ ⟨hcb, ihb⟩
    refine ⟨isFormCodeSem_or H hca hcb, fun e he => ⟨?_, ?_⟩⟩
    · intro hbd
      obtain ⟨ba, bb⟩ := sigmaBounded_or H (natV_mem_omega H n) hbd
      exact or_total_step H n he ((iha e he).1 ba) ((ihb e he).1 bb)
    · intro hbd
      obtain ⟨ba, bb⟩ := piBounded_or H (natV_mem_omega H n) hbd
      exact or_total_step H n he ((iha e he).2 ba) ((ihb e he).2 bb)
  · rintro a ⟨hca, -⟩
    refine ⟨isFormCodeSem_all H hca, fun e he => ⟨?_, ?_⟩⟩
    · intro hbd
      obtain ⟨m, rfl, hpb⟩ := exists_pred_piBounded_of_sigmaBounded_all H hbd
      rcases Classical.em (PiFalse H m (kpair H (natV H 6) a) e) with hf | hf
      · exact Or.inr (piFalse_mono H (by omega) he hf)
      · exact Or.inl (sigmaTrue_mono H (by omega) he
          (sigmaTrue_all_of_piTrue H m he hpb hf))
    · intro hbd
      rcases Classical.em (PiFalse H n (kpair H (natV H 6) a) e) with hf | hf
      · exact Or.inr (piFalse_mono H (Nat.le_succ n) he hf)
      · exact Or.inl (sigmaTrue_all_of_piTrue H n he hbd hf)
  · rintro a ⟨hca, -⟩
    refine ⟨isFormCodeSem_ex H hca, fun e he => ⟨?_, ?_⟩⟩
    · intro hbd
      rcases Classical.em (SigmaTrue H n (kpair H (natV H 7) a) e) with hs | hs
      · exact Or.inl (sigmaTrue_mono H (Nat.le_succ n) he hs)
      · exact Or.inr (piFalse_ex_of_not_sigmaTrue H n he hbd hs)
    · intro hbd
      obtain ⟨m, rfl, hsb⟩ := exists_pred_sigmaBounded_of_piBounded_ex H hbd
      rcases Classical.em (SigmaTrue H m (kpair H (natV H 7) a) e) with hs | hs
      · exact Or.inl (sigmaTrue_mono H (by omega) he hs)
      · exact Or.inr (piFalse_mono H (by omega) he
          (piFalse_ex_of_not_sigmaTrue H m he hsb hs))

/-! ## Two-valuedness

Totality and exclusivity together.  The unoriented bound the every-occurrence
restriction supplies orients itself in at least one way, and either orientation
gives totality; exclusivity needs no bound at all. -/

/-- **A bounded code is decided at the level above its bound.** -/
theorem sigmaTrue_or_piFalse (H : ZFAxioms mem) (n : Nat) {c e : V}
    (hc : IsFormCodeSem H c) (hq : QuantBounded H (natV H n) c)
    (he : IsUnivEnv H e) :
    SigmaTrue H (n+1) c e ∨ PiFalse H (n+1) c e := by
  rcases sigmaBounded_or_piBounded H hq with hb | hb
  · exact ((totalAt_of_isFormCodeSem H n c hc).2 e he).1 hb
  · exact ((totalAt_of_isFormCodeSem H n c hc).2 e he).2 hb

/-- **The two polarities agree on bounded codes.**  This is what implication
elimination consumes: the Sigma reading of an implication offers Pi-falsity of
the antecedent, and only this identification turns it back into the Sigma
reading soundness is carrying. -/
theorem sigmaTrue_iff_piTrue (H : ZFAxioms mem) (n : Nat) {c e : V}
    (hc : IsFormCodeSem H c) (hq : QuantBounded H (natV H n) c)
    (he : IsUnivEnv H e) :
    SigmaTrue H (n+1) c e ↔ PiTrue H (n+1) c e := by
  constructor
  · exact piTrue_of_sigmaTrue H (n+1) hc he
  · intro h
    rcases sigmaTrue_or_piFalse H n hc hq he with k | k
    · exact k
    · exact absurd k h

/-- **The two-valuedness obligation of `BoundedZFCConsistency.LevelSoundness`,
discharged.**  With it, the only remaining premise of fixed-level soundness is
`AxiomCodesTrueAt`, which is about the axioms rather than about the hierarchy. -/
theorem levelTwoValuedAt (H : ZFAxioms mem) (n : Nat) : LevelTwoValuedAt H n :=
  fun _ _ hc hq hE => sigmaTrue_iff_piTrue H n hc hq hE

/-! ## The polarity switches as biconditionals

The inversions of `BoundedZFCConsistency.UniverseTruthLevel` leave a disjunct
saying that the previous level already certified the record.  Exclusivity
discharges it — a record certified at the previous level is Sigma-true there,
hence Pi-true there — so the elimination halves need no bound at all; the bound
returns only for the introduction halves, where the delegated row is being
built. -/

/-- **Elimination at a universal head on the Sigma side**, with no bound. -/
theorem sigmaTrue_all_elim (H : ZFAxioms mem) (n : Nat) {c1 e : V}
    (hc : IsFormCodeSem H (kpair H (natV H 6) c1)) (he : IsUnivEnv H e)
    (h : SigmaTrue H (n+1) (kpair H (natV H 6) c1) e) :
    PiTrue H n (kpair H (natV H 6) c1) e := by
  rcases sigmaTrue_all_inv H n h with k | ⟨-, hp⟩
  · exact piTrue_of_sigmaTrue H n hc he k
  · exact hp

/-- **The polarity switch at a universal head**, as a biconditional. -/
theorem sigmaTrue_all (H : ZFAxioms mem) (n : Nat) {c1 e : V}
    (hc : IsFormCodeSem H (kpair H (natV H 6) c1)) (he : IsUnivEnv H e)
    (hb : PiBounded H (natV H n) (kpair H (natV H 6) c1)) :
    SigmaTrue H (n+1) (kpair H (natV H 6) c1) e ↔
      PiTrue H n (kpair H (natV H 6) c1) e :=
  ⟨sigmaTrue_all_elim H n hc he, sigmaTrue_all_of_piTrue H n he hb⟩

/-- **Elimination at an existential head on the Pi side**, with no bound. -/
theorem piFalse_ex_elim (H : ZFAxioms mem) (n : Nat) {c1 e : V}
    (hc : IsFormCodeSem H (kpair H (natV H 7) c1)) (he : IsUnivEnv H e)
    (h : PiFalse H (n+1) (kpair H (natV H 7) c1) e) :
    ¬ SigmaTrue H n (kpair H (natV H 7) c1) e := by
  rcases piFalse_ex_inv H n h with k | ⟨-, hp⟩
  · exact fun hs => sigmaTrue_not_piFalse H n _ e hc he hs k
  · exact hp

/-- **The polarity switch at an existential head**, as a biconditional. -/
theorem piFalse_ex (H : ZFAxioms mem) (n : Nat) {c1 e : V}
    (hc : IsFormCodeSem H (kpair H (natV H 7) c1)) (he : IsUnivEnv H e)
    (hb : SigmaBounded H (natV H n) (kpair H (natV H 7) c1)) :
    PiFalse H (n+1) (kpair H (natV H 7) c1) e ↔
      ¬ SigmaTrue H n (kpair H (natV H 7) c1) e :=
  ⟨piFalse_ex_elim H n hc he, piFalse_ex_of_not_sigmaTrue H n he hb⟩

end LevelCollapse

end BoundedZFCConsistency
end LeanProofs
