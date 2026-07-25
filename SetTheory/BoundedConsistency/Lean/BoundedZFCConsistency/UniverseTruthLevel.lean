import BoundedZFCConsistency.UniverseTruthZero

/-!
# The externally indexed partial truth predicates over the universe

`BoundedZFCConsistency.UniverseTruthZero` interprets a quantifier-free code
over the whole universe.  This module builds the positive levels of the
hierarchy on top of it: for every metatheoretic `n` a relation `SigmaTrue H n`
and its dual `PiTrue H n`, each of them a `Form` of the object language
together with an exact satisfaction spec.

## Why the level is external, and what that buys

The recursion is on the **metatheoretic** natural `n`, so `SigmaTrue H n` is a
*different* Lean definition, and `levelSatF n` a *different* object-language
formula, for every `n`.  Nothing here defines truth uniformly in the level: the
level appears only as the length of an external recursion producing the
formula, and no `Form` of this file has the level as a free variable.  That is
what keeps Tarski's theorem satisfied, and it is visible in the types —
`levelSatF : Nat → (Nat → Nat → Nat → Form)` takes a metatheoretic `Nat` and
returns a formula, whereas a uniform truth definition would have to take the
level as a de Bruijn slot and would be a single formula.

## The clauses, and why they are one-sided

A record is the evaluation triple `⟨c, e, b⟩` of
`BoundedZFCConsistency.InternalSat`, with the bit read as a *polarity*: bit `1`
asserts Sigma-truth of `c` at `e`, bit `0` asserts Pi-falsity.  A certificate is
a set of records, each locally justified by the certificate itself:

| tag | bit | justification                                                     |
| --- | --- | ------------------------------------------------------------------ |
| any | any | the previous level already certifies the record                     |
| `3` | `1` | the antecedent is recorded false, or the consequent recorded true   |
| `3` | `0` | the antecedent is recorded true and the consequent recorded false   |
| `4` | `1` | both conjuncts are recorded true                                    |
| `4` | `0` | some conjunct is recorded false                                     |
| `5` | `1` | some disjunct is recorded true                                      |
| `5` | `0` | both disjuncts are recorded false                                   |
| `6` | `0` | some shift records the matrix false — a counterexample              |
| `7` | `1` | some shift records the matrix true — a witness                      |
| `6` | `1` | the code is Pi-bounded at the previous level and Pi-true there      |
| `7` | `0` | the code is Sigma-bounded at the previous level and Sigma-false there |

The last two rows are the **polarity switch**, and the asymmetry of the table
is forced rather than chosen.  A witness for an existential, or a
counterexample to a universal, is a single element and can be recorded; the
*absence* of one is a statement about the whole universe and cannot be, since a
certificate is a set while the values range over a proper class.  So each
quantifier head is recorded positively on exactly one polarity and delegated to
the previous level on the other.  The delegation is legitimate precisely
because of the polarity ranks of `BoundedZFCConsistency.Basic`: a universal
code whose Sigma-rank is at most `n+1` has Pi-rank at most `n`, and an
existential code whose Pi-rank is at most `n+1` has Sigma-rank at most `n`.
The guards `PiBounded` and `SigmaBounded` say exactly that, and without them
the delegated row would be vacuously available at every code the previous level
says nothing about.

`SigmaTrue H n c e` and `PiFalse H n c e` are therefore the two readings of one
relation `LevelSat H n c e b`, and `PiTrue H n c e` is the complement of
`PiFalse H n c e`.  Only the Sigma side is certified positively; the falsity of
a Sigma statement is a metatheoretic negation, never a certificate, which is
why no certificate is ever asked to enumerate the universe.

## The base case

Level zero is the quantifier-free fragment: `LevelSat H 0 c e b` says that `c`
is a quantifier-free code and that `b` is the truth bit of `QFTrue H c e`.
Both `SigmaTrue H 0` and `PiTrue H 0` therefore agree with `QFTrue` on
quantifier-free codes, which is the base case of the polarity ranks: at level
zero the Sigma and Pi sides coincide.

## What is proved and what is not

The introduction half of every clause holds at every positive level, and the
elimination half at every level — the latter by induction on the level, because
the delegation row is never excluded by a tag.  The two polarity-switch rows
are the exception: their elimination halves are given as inversion lemmas whose
first disjunct is "the previous level already said so", and discharging that
disjunct in general is the level-collapse theorem
(`SigmaTrue (n+1) c e → SigmaTrue n c e` on codes bounded at level `n`), which
is a separate induction over codes and is not proved here.  At level one the
disjunct is discharged outright, which is what `not_sigmaTrue_one_all` and
`not_piFalse_one_ex` record.

## Codes, not quotations

Nothing below assumes that a code is the quotation of an external formula; the
codes are arbitrary internal ones, and in a nonstandard model the existential
block a Sigma-1 code carries may have nonstandard length.  That is why the
within-level recursion is carried by an internal certificate instead of by an
external recursion on a parse tree, and why `IsFormCodeSem` appears as a
hypothesis wherever a subcode has to be recognized: `IsFormCodeSem` has no
inversion principle, so codehood of a compound never yields codehood of its
parts.

## De Bruijn bookkeeping

Every formula below carries a table of its de Bruijn slots.  Slot arguments
named `_i` are ABSOLUTE positions in the environment at the use site.  The
convention matches `ZF.Zf` and `BoundedZFCConsistency.InternalSat`.

Neither Powerset nor Regularity is used, matching the six axioms bundled in
`ZFAxioms`.
-/

namespace LeanProofs
namespace BoundedZFCConsistency

open SetTheory
open SetTheory.Form

universe u

section UniverseTruthLevel

variable {V : Type u} {mem : V → V → Prop}

/-! ## The shift on environments over the universe

`BoundedZFCConsistency.InternalSat` states the shift lemmas for `IsEnvOn`, an
environment whose values lie in a fixed carrier.  A universe environment has no
carrier clause, so the three lemmas are restated here against `IsUnivEnv`.
Only the function part of `econs_isEnvOn` transfers; the value clause has no
counterpart and needs none, since any set may be shifted in. -/

/-- **The shift of a universe environment is a universe environment.**  Unlike
the carrier version this needs no hypothesis on the shifted-in value: there is
nothing for it to belong to. -/
theorem econs_isUnivEnv (H : ZFAxioms mem) {E : V} (hE : IsUnivEnv H E) (d : V) :
    IsUnivEnv H (econs H d E) := by
  have hfun := hE.1
  refine ⟨econs_functional H hfun d, ?_, ?_⟩
  · intro x hx
    rcases nat_zero_or_succ H x hx with hx0 | ⟨m, hm, hx0⟩
    · exact ⟨d, (econs_spec H hfun d (kpair H x d)).mpr (Or.inl (by rw [hx0]))⟩
    · obtain ⟨y, hy⟩ := hE.2.1 m hm
      exact ⟨y, (econs_spec H hfun d (kpair H x y)).mpr
        (Or.inr ⟨m, hm, y, hy, by rw [hx0]⟩)⟩
  · intro p hp
    rcases (econs_spec H hfun d p).mp hp with h | ⟨n, hn, y, _, h⟩
    · exact ⟨vempty H, d, vempty_in_omega H, h⟩
    · exact ⟨vsucc H n, y, omega_succ H n hn, h⟩

/-- The shifted environment takes the shifted-in value at the internal zero. -/
theorem econs_apply_zero (H : ZFAxioms mem) {E : V} (hE : IsUnivEnv H E) (d : V) :
    applyV H (econs H d E) (vempty H) = d :=
  econs_zero H hE.1 d

/-- The shifted environment reproduces the old values at successors. -/
theorem econs_apply_succ (H : ZFAxioms mem) {E : V} (hE : IsUnivEnv H E) (d : V)
    {n : V} (hn : mem n (omegaV H)) :
    applyV H (econs H d E) (vsucc H n) = applyV H E n :=
  applyV_eq H (econs_functional H hE.1 d)
    ((econs_spec H hE.1 d (kpair H (vsucc H n) (applyV H E n))).mpr
      (Or.inr ⟨n, hn, applyV H E n, applyV_mem H (hE.2.1 n hn), rfl⟩))

/-! ## The two oriented bounds on codes

`BoundedZFCConsistency.CodedRank` bounds the *smaller* of a code's two internal
ranks, which is the right notion for the every-occurrence restriction.  The
truth hierarchy needs the two ranks separately, because the polarity switch
concerns one of them at a time. -/

/-- **The Sigma-rank of `c` is at most `b`.** -/
def SigmaBounded (H : ZFAxioms mem) (b c : V) : Prop :=
  ∃ s p, Ranks H c s p ∧ LeN H s b

/-- **The Pi-rank of `c` is at most `b`.** -/
def PiBounded (H : ZFAxioms mem) (b c : V) : Prop :=
  ∃ s p, Ranks H c s p ∧ LeN H p b

/-- `SigmaBounded` as a `Form`.

| de Bruijn slot | contents              |
| -------------- | --------------------- |
| `0`            | the pi rank `p`       |
| `1`            | the sigma rank `s`    |
| `m+2`          | the caller's slot `m` |
-/
def fSigmaBoundedF (b_i c_i : Nat) : Form :=
  fEx (fEx (fAnd (fRanksF (c_i+2) 1 0) (fLeF 1 (b_i+2))))

theorem fSigmaBoundedF_spec (H : ZFAxioms mem) (ee : Nat → V) (b_i c_i : Nat) :
    Sat mem ee (fSigmaBoundedF b_i c_i) ↔ SigmaBounded H (ee b_i) (ee c_i) := by
  unfold SigmaBounded
  constructor
  · rintro ⟨s, p, hr, hle⟩
    exact ⟨s, p, (fRanksF_spec H (scons p (scons s ee)) (c_i+2) 1 0).mp hr,
      (fLeF_spec H (scons p (scons s ee)) 1 (b_i+2)).mp hle⟩
  · rintro ⟨s, p, hr, hle⟩
    exact ⟨s, p, (fRanksF_spec H (scons p (scons s ee)) (c_i+2) 1 0).mpr hr,
      (fLeF_spec H (scons p (scons s ee)) 1 (b_i+2)).mpr hle⟩

/-- `PiBounded` as a `Form`, with the same slot table. -/
def fPiBoundedF (b_i c_i : Nat) : Form :=
  fEx (fEx (fAnd (fRanksF (c_i+2) 1 0) (fLeF 0 (b_i+2))))

theorem fPiBoundedF_spec (H : ZFAxioms mem) (ee : Nat → V) (b_i c_i : Nat) :
    Sat mem ee (fPiBoundedF b_i c_i) ↔ PiBounded H (ee b_i) (ee c_i) := by
  unfold PiBounded
  constructor
  · rintro ⟨s, p, hr, hle⟩
    exact ⟨s, p, (fRanksF_spec H (scons p (scons s ee)) (c_i+2) 1 0).mp hr,
      (fLeF_spec H (scons p (scons s ee)) 0 (b_i+2)).mp hle⟩
  · rintro ⟨s, p, hr, hle⟩
    exact ⟨s, p, (fRanksF_spec H (scons p (scons s ee)) (c_i+2) 1 0).mpr hr,
      (fLeF_spec H (scons p (scons s ee)) 0 (b_i+2)).mpr hle⟩

/-- Either oriented bound implies the bound on the smaller rank. -/
theorem quantBounded_of_sigmaBounded (H : ZFAxioms mem) {b c : V}
    (hb : mem b (omegaV H)) (h : SigmaBounded H b c) : QuantBounded H b c := by
  obtain ⟨s, p, hr, hle⟩ := h
  obtain ⟨hs, hp⟩ := Ranks.mem_omega H hr
  exact ⟨s, p, hr, leN_trans H hb (vminN_leN_left H hs hp) hle⟩

theorem quantBounded_of_piBounded (H : ZFAxioms mem) {b c : V}
    (hb : mem b (omegaV H)) (h : PiBounded H b c) : QuantBounded H b c := by
  obtain ⟨s, p, hr, hle⟩ := h
  obtain ⟨hs, hp⟩ := Ranks.mem_omega H hr
  exact ⟨s, p, hr, leN_trans H hb (vminN_leN_right H hs hp) hle⟩

/-- On quotations the internal Sigma-bound is the metatheoretic one. -/
theorem sigmaBounded_formCode_iff (H : ZFAxioms mem) (n : Nat) (phi : Form) :
    SigmaBounded H (natV H n) (formCode H phi) ↔ sigmaRank phi ≤ n := by
  unfold SigmaBounded
  constructor
  · rintro ⟨s, p, hr, hle⟩
    obtain ⟨rfl, rfl⟩ := (ranks_formCode_iff H phi s p).mp hr
    exact (leN_natV_iff H (sigmaRank phi) n).mp hle
  · intro h
    exact ⟨natV H (sigmaRank phi), natV H (piRank phi), ranks_formCode H phi,
      (leN_natV_iff H (sigmaRank phi) n).mpr h⟩

/-- On quotations the internal Pi-bound is the metatheoretic one. -/
theorem piBounded_formCode_iff (H : ZFAxioms mem) (n : Nat) (phi : Form) :
    PiBounded H (natV H n) (formCode H phi) ↔ piRank phi ≤ n := by
  unfold PiBounded
  constructor
  · rintro ⟨s, p, hr, hle⟩
    obtain ⟨rfl, rfl⟩ := (ranks_formCode_iff H phi s p).mp hr
    exact (leN_natV_iff H (piRank phi) n).mp hle
  · intro h
    exact ⟨natV H (sigmaRank phi), natV H (piRank phi), ranks_formCode H phi,
      (leN_natV_iff H (piRank phi) n).mpr h⟩

/-- **A universally quantified code is never Pi-bounded by zero.**  Its Pi-rank
dominates the numeral one.  This is what makes the polarity switch unavailable
at level one, and hence what makes level one a genuine Sigma-1 predicate rather
than a collapse of the hierarchy. -/
theorem not_piBounded_zero_all (H : ZFAxioms mem) {a : V} :
    ¬ PiBounded H (natV H 0) (kpair H (natV H 6) a) := by
  rintro ⟨s, p, hr, hle⟩
  obtain ⟨sa, pa, ha, hs, hp⟩ := ranks_all_inv H hr
  obtain ⟨hsa, hpa⟩ := Ranks.mem_omega H ha
  subst hs
  subst hp
  have h1 : LeN H (natV H 1) (vmaxN H (natV H 1) pa) :=
    leN_vmaxN_left H (natV_mem_omega H 1) hpa
  have h2 : LeN H (natV H 1) (natV H 0) :=
    leN_trans H (natV_mem_omega H 0) h1 hle
  exact absurd ((leN_natV_iff H 1 0).mp h2) (by omega)

/-- **An existentially quantified code is never Sigma-bounded by zero.** -/
theorem not_sigmaBounded_zero_ex (H : ZFAxioms mem) {a : V} :
    ¬ SigmaBounded H (natV H 0) (kpair H (natV H 7) a) := by
  rintro ⟨s, p, hr, hle⟩
  obtain ⟨sa, pa, ha, hs, hp⟩ := ranks_ex_inv H hr
  obtain ⟨hsa, hpa⟩ := Ranks.mem_omega H ha
  subst hs
  subst hp
  have h1 : LeN H (natV H 1) (vmaxN H (natV H 1) sa) :=
    leN_vmaxN_left H (natV_mem_omega H 1) hsa
  have h2 : LeN H (natV H 1) (natV H 0) :=
    leN_trans H (natV_mem_omega H 0) h1 hle
  exact absurd ((leN_natV_iff H 1 0).mp h2) (by omega)

/-! ## Quantifier-free truth as a `Form`

`UniverseTruthZero` proves the base predicate's Tarski clauses but never
renders it as a formula, because nothing there needed to.  The level recursion
does: level zero is the first argument of the recursion producing
`levelSatF`. -/

/-- "quantifier-free truth of slot `c_i` at slot `e_i`".

| de Bruijn slot | contents              |
| -------------- | --------------------- |
| `0`            | the numeral one       |
| `1`            | the certificate `S`   |
| `m+2`          | the caller's slot `m` |
-/
def fQFTrueF (c_i e_i : Nat) : Form :=
  fEx (fEx (fAnd (fNumF 0 1)
    (fAnd (fQFSatClosedF 1) (fTripleMemF (c_i+2) (e_i+2) 0 1))))

theorem fQFTrueF_spec (H : ZFAxioms mem) (ee : Nat → V) (c_i e_i : Nat) :
    Sat mem ee (fQFTrueF c_i e_i) ↔ QFTrue H (ee c_i) (ee e_i) := by
  unfold QFTrue
  constructor
  · rintro ⟨S, one, hone, hcl, hmem⟩
    have hone' : one = natV H 1 :=
      (fNumF_spec H 1 0 (scons one (scons S ee))).mp hone
    refine ⟨S, (fQFSatClosedF_spec H (scons one (scons S ee)) 1).mp hcl, ?_⟩
    have hm := (fTripleMemF_spec H (scons one (scons S ee))
      (c_i+2) (e_i+2) 0 1).mp hmem
    rw [hone'] at hm
    exact hm
  · rintro ⟨S, hcl, hmem⟩
    refine ⟨S, natV H 1,
      (fNumF_spec H 1 0 (scons (natV H 1) (scons S ee))).mpr rfl,
      (fQFSatClosedF_spec H (scons (natV H 1) (scons S ee)) 1).mpr hcl, ?_⟩
    exact (fTripleMemF_spec H (scons (natV H 1) (scons S ee))
      (c_i+2) (e_i+2) 0 1).mpr hmem

/-! ## The local step

`LevelJustified H L bnd S c e b` is the eleven-row table of the module header,
parametrized by the *previous level* `L` and by the numeral `bnd` of the
previous level.  It is local: it mentions the certificate `S` only through
membership assertions, and the previous level only through `L`, never through
the relation being defined. -/

/-- The record `⟨c, e, b⟩` is justified by the records of `S`, over the previous
level `L` with bound `bnd`. -/
def LevelJustified (H : ZFAxioms mem) (L : V → V → V → Prop) (bnd S c e b : V) :
    Prop :=
  L c e b ∨
  (∃ c1 c2, c = kpair H (natV H 3) (kpair H c1 c2) ∧
    ((b = natV H 1 ∧ (mem (satTriple H c1 e (natV H 0)) S ∨
                      mem (satTriple H c2 e (natV H 1)) S)) ∨
     (b = natV H 0 ∧ mem (satTriple H c1 e (natV H 1)) S ∧
                     mem (satTriple H c2 e (natV H 0)) S))) ∨
  (∃ c1 c2, c = kpair H (natV H 4) (kpair H c1 c2) ∧
    ((b = natV H 1 ∧ mem (satTriple H c1 e (natV H 1)) S ∧
                     mem (satTriple H c2 e (natV H 1)) S) ∨
     (b = natV H 0 ∧ (mem (satTriple H c1 e (natV H 0)) S ∨
                      mem (satTriple H c2 e (natV H 0)) S)))) ∨
  (∃ c1 c2, c = kpair H (natV H 5) (kpair H c1 c2) ∧
    ((b = natV H 1 ∧ (mem (satTriple H c1 e (natV H 1)) S ∨
                      mem (satTriple H c2 e (natV H 1)) S)) ∨
     (b = natV H 0 ∧ mem (satTriple H c1 e (natV H 0)) S ∧
                     mem (satTriple H c2 e (natV H 0)) S))) ∨
  (∃ c1, c = kpair H (natV H 6) c1 ∧
    ((b = natV H 1 ∧ PiBounded H bnd c ∧ ¬ L c e (natV H 0)) ∨
     (b = natV H 0 ∧ ∃ d, mem (satTriple H c1 (econs H d e) (natV H 0)) S))) ∨
  (∃ c1, c = kpair H (natV H 7) c1 ∧
    ((b = natV H 1 ∧ ∃ d, mem (satTriple H c1 (econs H d e) (natV H 1)) S) ∨
     (b = natV H 0 ∧ SigmaBounded H bnd c ∧ ¬ L c e (natV H 1))))

/-! ### The clauses as formulas

The three Boolean rows share a shape and are rendered separately rather than
through one macro, because their two polarities distribute the subrecords
differently.  Each takes two extra slots `z_i` and `o_i` holding the numerals
`0` and `1`; the caller binds them once, so that a subrecord's bit is a slot
and `fTripleMemF` applies. -/

/-- The implication clause.

| de Bruijn slot | contents              |
| -------------- | --------------------- |
| `0`            | the consequent `c2`   |
| `1`            | the antecedent `c1`   |
| `m+2`          | the caller's slot `m` |
-/
def fLevelImpF (c_i e_i b_i s_i z_i o_i : Nat) : Form :=
  fEx (fEx (fAnd (fTagPairF (c_i+2) 3 1 0)
    (fOr (fAnd (fEq (b_i+2) (o_i+2))
               (fOr (fTripleMemF 1 (e_i+2) (z_i+2) (s_i+2))
                    (fTripleMemF 0 (e_i+2) (o_i+2) (s_i+2))))
         (fAnd (fEq (b_i+2) (z_i+2))
               (fAnd (fTripleMemF 1 (e_i+2) (o_i+2) (s_i+2))
                     (fTripleMemF 0 (e_i+2) (z_i+2) (s_i+2)))))))

theorem fLevelImpF_spec (H : ZFAxioms mem) (ee : Nat → V)
    (c_i e_i b_i s_i z_i o_i : Nat) :
    Sat mem ee (fLevelImpF c_i e_i b_i s_i z_i o_i) ↔
      ∃ c1 c2, ee c_i = kpair H (natV H 3) (kpair H c1 c2) ∧
        ((ee b_i = ee o_i ∧
            (mem (satTriple H c1 (ee e_i) (ee z_i)) (ee s_i) ∨
             mem (satTriple H c2 (ee e_i) (ee o_i)) (ee s_i))) ∨
         (ee b_i = ee z_i ∧
            mem (satTriple H c1 (ee e_i) (ee o_i)) (ee s_i) ∧
            mem (satTriple H c2 (ee e_i) (ee z_i)) (ee s_i))) := by
  constructor
  · rintro ⟨c1, c2, hc, hcase⟩
    refine ⟨c1, c2,
      (fTagPairF_spec H (scons c2 (scons c1 ee)) (c_i+2) 3 1 0).mp hc, ?_⟩
    rcases hcase with ⟨hb, hsub⟩ | ⟨hb, h1, h2⟩
    · refine Or.inl ⟨hb, ?_⟩
      rcases hsub with h | h
      · exact Or.inl ((fTripleMemF_spec H (scons c2 (scons c1 ee))
          1 (e_i+2) (z_i+2) (s_i+2)).mp h)
      · exact Or.inr ((fTripleMemF_spec H (scons c2 (scons c1 ee))
          0 (e_i+2) (o_i+2) (s_i+2)).mp h)
    · exact Or.inr ⟨hb,
        (fTripleMemF_spec H (scons c2 (scons c1 ee))
          1 (e_i+2) (o_i+2) (s_i+2)).mp h1,
        (fTripleMemF_spec H (scons c2 (scons c1 ee))
          0 (e_i+2) (z_i+2) (s_i+2)).mp h2⟩
  · rintro ⟨c1, c2, hc, hcase⟩
    refine ⟨c1, c2,
      (fTagPairF_spec H (scons c2 (scons c1 ee)) (c_i+2) 3 1 0).mpr hc, ?_⟩
    rcases hcase with ⟨hb, hsub⟩ | ⟨hb, h1, h2⟩
    · refine Or.inl ⟨hb, ?_⟩
      rcases hsub with h | h
      · exact Or.inl ((fTripleMemF_spec H (scons c2 (scons c1 ee))
          1 (e_i+2) (z_i+2) (s_i+2)).mpr h)
      · exact Or.inr ((fTripleMemF_spec H (scons c2 (scons c1 ee))
          0 (e_i+2) (o_i+2) (s_i+2)).mpr h)
    · exact Or.inr ⟨hb,
        (fTripleMemF_spec H (scons c2 (scons c1 ee))
          1 (e_i+2) (o_i+2) (s_i+2)).mpr h1,
        (fTripleMemF_spec H (scons c2 (scons c1 ee))
          0 (e_i+2) (z_i+2) (s_i+2)).mpr h2⟩

/-- The conjunction clause, with the slot table of `fLevelImpF`. -/
def fLevelAndF (c_i e_i b_i s_i z_i o_i : Nat) : Form :=
  fEx (fEx (fAnd (fTagPairF (c_i+2) 4 1 0)
    (fOr (fAnd (fEq (b_i+2) (o_i+2))
               (fAnd (fTripleMemF 1 (e_i+2) (o_i+2) (s_i+2))
                     (fTripleMemF 0 (e_i+2) (o_i+2) (s_i+2))))
         (fAnd (fEq (b_i+2) (z_i+2))
               (fOr (fTripleMemF 1 (e_i+2) (z_i+2) (s_i+2))
                    (fTripleMemF 0 (e_i+2) (z_i+2) (s_i+2)))))))

theorem fLevelAndF_spec (H : ZFAxioms mem) (ee : Nat → V)
    (c_i e_i b_i s_i z_i o_i : Nat) :
    Sat mem ee (fLevelAndF c_i e_i b_i s_i z_i o_i) ↔
      ∃ c1 c2, ee c_i = kpair H (natV H 4) (kpair H c1 c2) ∧
        ((ee b_i = ee o_i ∧
            mem (satTriple H c1 (ee e_i) (ee o_i)) (ee s_i) ∧
            mem (satTriple H c2 (ee e_i) (ee o_i)) (ee s_i)) ∨
         (ee b_i = ee z_i ∧
            (mem (satTriple H c1 (ee e_i) (ee z_i)) (ee s_i) ∨
             mem (satTriple H c2 (ee e_i) (ee z_i)) (ee s_i)))) := by
  constructor
  · rintro ⟨c1, c2, hc, hcase⟩
    refine ⟨c1, c2,
      (fTagPairF_spec H (scons c2 (scons c1 ee)) (c_i+2) 4 1 0).mp hc, ?_⟩
    rcases hcase with ⟨hb, h1, h2⟩ | ⟨hb, hsub⟩
    · exact Or.inl ⟨hb,
        (fTripleMemF_spec H (scons c2 (scons c1 ee))
          1 (e_i+2) (o_i+2) (s_i+2)).mp h1,
        (fTripleMemF_spec H (scons c2 (scons c1 ee))
          0 (e_i+2) (o_i+2) (s_i+2)).mp h2⟩
    · refine Or.inr ⟨hb, ?_⟩
      rcases hsub with h | h
      · exact Or.inl ((fTripleMemF_spec H (scons c2 (scons c1 ee))
          1 (e_i+2) (z_i+2) (s_i+2)).mp h)
      · exact Or.inr ((fTripleMemF_spec H (scons c2 (scons c1 ee))
          0 (e_i+2) (z_i+2) (s_i+2)).mp h)
  · rintro ⟨c1, c2, hc, hcase⟩
    refine ⟨c1, c2,
      (fTagPairF_spec H (scons c2 (scons c1 ee)) (c_i+2) 4 1 0).mpr hc, ?_⟩
    rcases hcase with ⟨hb, h1, h2⟩ | ⟨hb, hsub⟩
    · exact Or.inl ⟨hb,
        (fTripleMemF_spec H (scons c2 (scons c1 ee))
          1 (e_i+2) (o_i+2) (s_i+2)).mpr h1,
        (fTripleMemF_spec H (scons c2 (scons c1 ee))
          0 (e_i+2) (o_i+2) (s_i+2)).mpr h2⟩
    · refine Or.inr ⟨hb, ?_⟩
      rcases hsub with h | h
      · exact Or.inl ((fTripleMemF_spec H (scons c2 (scons c1 ee))
          1 (e_i+2) (z_i+2) (s_i+2)).mpr h)
      · exact Or.inr ((fTripleMemF_spec H (scons c2 (scons c1 ee))
          0 (e_i+2) (z_i+2) (s_i+2)).mpr h)

/-- The disjunction clause, with the slot table of `fLevelImpF`. -/
def fLevelOrF (c_i e_i b_i s_i z_i o_i : Nat) : Form :=
  fEx (fEx (fAnd (fTagPairF (c_i+2) 5 1 0)
    (fOr (fAnd (fEq (b_i+2) (o_i+2))
               (fOr (fTripleMemF 1 (e_i+2) (o_i+2) (s_i+2))
                    (fTripleMemF 0 (e_i+2) (o_i+2) (s_i+2))))
         (fAnd (fEq (b_i+2) (z_i+2))
               (fAnd (fTripleMemF 1 (e_i+2) (z_i+2) (s_i+2))
                     (fTripleMemF 0 (e_i+2) (z_i+2) (s_i+2)))))))

theorem fLevelOrF_spec (H : ZFAxioms mem) (ee : Nat → V)
    (c_i e_i b_i s_i z_i o_i : Nat) :
    Sat mem ee (fLevelOrF c_i e_i b_i s_i z_i o_i) ↔
      ∃ c1 c2, ee c_i = kpair H (natV H 5) (kpair H c1 c2) ∧
        ((ee b_i = ee o_i ∧
            (mem (satTriple H c1 (ee e_i) (ee o_i)) (ee s_i) ∨
             mem (satTriple H c2 (ee e_i) (ee o_i)) (ee s_i))) ∨
         (ee b_i = ee z_i ∧
            mem (satTriple H c1 (ee e_i) (ee z_i)) (ee s_i) ∧
            mem (satTriple H c2 (ee e_i) (ee z_i)) (ee s_i))) := by
  constructor
  · rintro ⟨c1, c2, hc, hcase⟩
    refine ⟨c1, c2,
      (fTagPairF_spec H (scons c2 (scons c1 ee)) (c_i+2) 5 1 0).mp hc, ?_⟩
    rcases hcase with ⟨hb, hsub⟩ | ⟨hb, h1, h2⟩
    · refine Or.inl ⟨hb, ?_⟩
      rcases hsub with h | h
      · exact Or.inl ((fTripleMemF_spec H (scons c2 (scons c1 ee))
          1 (e_i+2) (o_i+2) (s_i+2)).mp h)
      · exact Or.inr ((fTripleMemF_spec H (scons c2 (scons c1 ee))
          0 (e_i+2) (o_i+2) (s_i+2)).mp h)
    · exact Or.inr ⟨hb,
        (fTripleMemF_spec H (scons c2 (scons c1 ee))
          1 (e_i+2) (z_i+2) (s_i+2)).mp h1,
        (fTripleMemF_spec H (scons c2 (scons c1 ee))
          0 (e_i+2) (z_i+2) (s_i+2)).mp h2⟩
  · rintro ⟨c1, c2, hc, hcase⟩
    refine ⟨c1, c2,
      (fTagPairF_spec H (scons c2 (scons c1 ee)) (c_i+2) 5 1 0).mpr hc, ?_⟩
    rcases hcase with ⟨hb, hsub⟩ | ⟨hb, h1, h2⟩
    · refine Or.inl ⟨hb, ?_⟩
      rcases hsub with h | h
      · exact Or.inl ((fTripleMemF_spec H (scons c2 (scons c1 ee))
          1 (e_i+2) (o_i+2) (s_i+2)).mpr h)
      · exact Or.inr ((fTripleMemF_spec H (scons c2 (scons c1 ee))
          0 (e_i+2) (o_i+2) (s_i+2)).mpr h)
    · exact Or.inr ⟨hb,
        (fTripleMemF_spec H (scons c2 (scons c1 ee))
          1 (e_i+2) (z_i+2) (s_i+2)).mpr h1,
        (fTripleMemF_spec H (scons c2 (scons c1 ee))
          0 (e_i+2) (z_i+2) (s_i+2)).mpr h2⟩

/-- The universal clause: a counterexample is recorded on the false side, and
the true side is delegated to the previous level under the Pi-bound.

| de Bruijn slot | contents                                  |
| -------------- | ----------------------------------------- |
| `0`            | the matrix `c1`, then the shifted value   |
| `1`            | under the inner binder: the matrix `c1`   |
| `m+1`, `m+2`   | the caller's slot `m`                     |
-/
def fLevelAllF (lF : Nat → Nat → Nat → Form)
    (c_i e_i b_i s_i z_i o_i bnd_i : Nat) : Form :=
  fEx (fAnd (fTagUnF (c_i+1) 6 0)
    (fOr (fAnd (fEq (b_i+1) (o_i+1))
               (fAnd (fPiBoundedF (bnd_i+1) (c_i+1))
                     (fImp (lF (c_i+1) (e_i+1) (z_i+1)) fBot)))
         (fAnd (fEq (b_i+1) (z_i+1))
               (fEx (fShiftTripleMemF 1 0 (e_i+2) (s_i+2) 0)))))

theorem fLevelAllF_spec (H : ZFAxioms mem) (lF : Nat → Nat → Nat → Form)
    (L : V → V → V → Prop)
    (hl : ∀ (ee' : Nat → V) (c e b : Nat),
      Sat mem ee' (lF c e b) ↔ L (ee' c) (ee' e) (ee' b))
    (ee : Nat → V) (c_i e_i b_i s_i z_i o_i bnd_i : Nat)
    (hfun : ∀ x y y', mem (kpair H x y) (ee e_i) →
      mem (kpair H x y') (ee e_i) → y = y') :
    Sat mem ee (fLevelAllF lF c_i e_i b_i s_i z_i o_i bnd_i) ↔
      ∃ c1, ee c_i = kpair H (natV H 6) c1 ∧
        ((ee b_i = ee o_i ∧ PiBounded H (ee bnd_i) (ee c_i) ∧
            ¬ L (ee c_i) (ee e_i) (ee z_i)) ∨
         (ee b_i = ee z_i ∧
            ∃ d, mem (satTriple H c1 (econs H d (ee e_i)) (natV H 0))
              (ee s_i))) := by
  constructor
  · rintro ⟨c1, hc, hcase⟩
    refine ⟨c1, (fTagUnF_spec H (scons c1 ee) (c_i+1) 6 0).mp hc, ?_⟩
    rcases hcase with ⟨hb, hbd, hnot⟩ | ⟨hb, d, hd⟩
    · refine Or.inl ⟨hb,
        (fPiBoundedF_spec H (scons c1 ee) (bnd_i+1) (c_i+1)).mp hbd, ?_⟩
      intro hL
      exact hnot ((hl (scons c1 ee) (c_i+1) (e_i+1) (z_i+1)).mpr hL)
    · exact Or.inr ⟨hb, d,
        (fShiftTripleMemF_spec H (scons d (scons c1 ee))
          1 0 (e_i+2) (s_i+2) 0 hfun).mp hd⟩
  · rintro ⟨c1, hc, hcase⟩
    refine ⟨c1, (fTagUnF_spec H (scons c1 ee) (c_i+1) 6 0).mpr hc, ?_⟩
    rcases hcase with ⟨hb, hbd, hnot⟩ | ⟨hb, d, hd⟩
    · refine Or.inl ⟨hb,
        (fPiBoundedF_spec H (scons c1 ee) (bnd_i+1) (c_i+1)).mpr hbd, ?_⟩
      intro hL
      exact hnot ((hl (scons c1 ee) (c_i+1) (e_i+1) (z_i+1)).mp hL)
    · exact Or.inr ⟨hb, d,
        (fShiftTripleMemF_spec H (scons d (scons c1 ee))
          1 0 (e_i+2) (s_i+2) 0 hfun).mpr hd⟩

/-- The existential clause: a witness is recorded on the true side, and the
false side is delegated to the previous level under the Sigma-bound. -/
def fLevelExF (lF : Nat → Nat → Nat → Form)
    (c_i e_i b_i s_i z_i o_i bnd_i : Nat) : Form :=
  fEx (fAnd (fTagUnF (c_i+1) 7 0)
    (fOr (fAnd (fEq (b_i+1) (o_i+1))
               (fEx (fShiftTripleMemF 1 0 (e_i+2) (s_i+2) 1)))
         (fAnd (fEq (b_i+1) (z_i+1))
               (fAnd (fSigmaBoundedF (bnd_i+1) (c_i+1))
                     (fImp (lF (c_i+1) (e_i+1) (o_i+1)) fBot)))))

theorem fLevelExF_spec (H : ZFAxioms mem) (lF : Nat → Nat → Nat → Form)
    (L : V → V → V → Prop)
    (hl : ∀ (ee' : Nat → V) (c e b : Nat),
      Sat mem ee' (lF c e b) ↔ L (ee' c) (ee' e) (ee' b))
    (ee : Nat → V) (c_i e_i b_i s_i z_i o_i bnd_i : Nat)
    (hfun : ∀ x y y', mem (kpair H x y) (ee e_i) →
      mem (kpair H x y') (ee e_i) → y = y') :
    Sat mem ee (fLevelExF lF c_i e_i b_i s_i z_i o_i bnd_i) ↔
      ∃ c1, ee c_i = kpair H (natV H 7) c1 ∧
        ((ee b_i = ee o_i ∧
            ∃ d, mem (satTriple H c1 (econs H d (ee e_i)) (natV H 1))
              (ee s_i)) ∨
         (ee b_i = ee z_i ∧ SigmaBounded H (ee bnd_i) (ee c_i) ∧
            ¬ L (ee c_i) (ee e_i) (ee o_i))) := by
  constructor
  · rintro ⟨c1, hc, hcase⟩
    refine ⟨c1, (fTagUnF_spec H (scons c1 ee) (c_i+1) 7 0).mp hc, ?_⟩
    rcases hcase with ⟨hb, d, hd⟩ | ⟨hb, hbd, hnot⟩
    · exact Or.inl ⟨hb, d,
        (fShiftTripleMemF_spec H (scons d (scons c1 ee))
          1 0 (e_i+2) (s_i+2) 1 hfun).mp hd⟩
    · refine Or.inr ⟨hb,
        (fSigmaBoundedF_spec H (scons c1 ee) (bnd_i+1) (c_i+1)).mp hbd, ?_⟩
      intro hL
      exact hnot ((hl (scons c1 ee) (c_i+1) (e_i+1) (o_i+1)).mpr hL)
  · rintro ⟨c1, hc, hcase⟩
    refine ⟨c1, (fTagUnF_spec H (scons c1 ee) (c_i+1) 7 0).mpr hc, ?_⟩
    rcases hcase with ⟨hb, d, hd⟩ | ⟨hb, hbd, hnot⟩
    · exact Or.inl ⟨hb, d,
        (fShiftTripleMemF_spec H (scons d (scons c1 ee))
          1 0 (e_i+2) (s_i+2) 1 hfun).mpr hd⟩
    · refine Or.inr ⟨hb,
        (fSigmaBoundedF_spec H (scons c1 ee) (bnd_i+1) (c_i+1)).mpr hbd, ?_⟩
      intro hL
      exact hnot ((hl (scons c1 ee) (c_i+1) (e_i+1) (o_i+1)).mp hL)

/-- **The step relation as a `Form`.**  The two outermost binders hold the
numerals `0` and `1`, so that a subrecord's bit is a slot.

| de Bruijn slot | contents              |
| -------------- | --------------------- |
| `0`            | the numeral one       |
| `1`            | the numeral zero      |
| `m+2`          | the caller's slot `m` |
-/
def fLevelJustifiedF (lF : Nat → Nat → Nat → Form)
    (c_i e_i b_i s_i bnd_i : Nat) : Form :=
  fEx (fEx (fAnd (fAnd (fNumF 1 0) (fNumF 0 1))
    (fOr (lF (c_i+2) (e_i+2) (b_i+2))
    (fOr (fLevelImpF (c_i+2) (e_i+2) (b_i+2) (s_i+2) 1 0)
    (fOr (fLevelAndF (c_i+2) (e_i+2) (b_i+2) (s_i+2) 1 0)
    (fOr (fLevelOrF (c_i+2) (e_i+2) (b_i+2) (s_i+2) 1 0)
    (fOr (fLevelAllF lF (c_i+2) (e_i+2) (b_i+2) (s_i+2) 1 0 (bnd_i+2))
         (fLevelExF lF (c_i+2) (e_i+2) (b_i+2) (s_i+2) 1 0 (bnd_i+2)))))))))

theorem fLevelJustifiedF_spec (H : ZFAxioms mem) (lF : Nat → Nat → Nat → Form)
    (L : V → V → V → Prop)
    (hl : ∀ (ee' : Nat → V) (c e b : Nat),
      Sat mem ee' (lF c e b) ↔ L (ee' c) (ee' e) (ee' b))
    (ee : Nat → V) (c_i e_i b_i s_i bnd_i : Nat)
    (hE : IsUnivEnv H (ee e_i)) :
    Sat mem ee (fLevelJustifiedF lF c_i e_i b_i s_i bnd_i) ↔
      LevelJustified H L (ee bnd_i) (ee s_i) (ee c_i) (ee e_i) (ee b_i) := by
  unfold LevelJustified
  constructor
  · rintro ⟨z, o, ⟨hz, ho⟩, hbody⟩
    have hz' : z = natV H 0 :=
      (fNumF_spec H 0 1 (scons o (scons z ee))).mp hz
    have ho' : o = natV H 1 :=
      (fNumF_spec H 1 0 (scons o (scons z ee))).mp ho
    subst hz'
    subst ho'
    rcases hbody with h | h | h | h | h | h
    · exact Or.inl ((hl (scons (natV H 1) (scons (natV H 0) ee))
        (c_i+2) (e_i+2) (b_i+2)).mp h)
    · exact Or.inr (Or.inl ((fLevelImpF_spec H
        (scons (natV H 1) (scons (natV H 0) ee))
        (c_i+2) (e_i+2) (b_i+2) (s_i+2) 1 0).mp h))
    · exact Or.inr (Or.inr (Or.inl ((fLevelAndF_spec H
        (scons (natV H 1) (scons (natV H 0) ee))
        (c_i+2) (e_i+2) (b_i+2) (s_i+2) 1 0).mp h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ((fLevelOrF_spec H
        (scons (natV H 1) (scons (natV H 0) ee))
        (c_i+2) (e_i+2) (b_i+2) (s_i+2) 1 0).mp h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((fLevelAllF_spec H lF L hl
        (scons (natV H 1) (scons (natV H 0) ee))
        (c_i+2) (e_i+2) (b_i+2) (s_i+2) 1 0 (bnd_i+2) hE.1).mp h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((fLevelExF_spec H lF L hl
        (scons (natV H 1) (scons (natV H 0) ee))
        (c_i+2) (e_i+2) (b_i+2) (s_i+2) 1 0 (bnd_i+2) hE.1).mp h)))))
  · intro h
    refine ⟨natV H 0, natV H 1,
      ⟨(fNumF_spec H 0 1 (scons (natV H 1) (scons (natV H 0) ee))).mpr rfl,
       (fNumF_spec H 1 0 (scons (natV H 1) (scons (natV H 0) ee))).mpr rfl⟩, ?_⟩
    rcases h with h | h | h | h | h | h
    · exact Or.inl ((hl (scons (natV H 1) (scons (natV H 0) ee))
        (c_i+2) (e_i+2) (b_i+2)).mpr h)
    · exact Or.inr (Or.inl ((fLevelImpF_spec H
        (scons (natV H 1) (scons (natV H 0) ee))
        (c_i+2) (e_i+2) (b_i+2) (s_i+2) 1 0).mpr h))
    · exact Or.inr (Or.inr (Or.inl ((fLevelAndF_spec H
        (scons (natV H 1) (scons (natV H 0) ee))
        (c_i+2) (e_i+2) (b_i+2) (s_i+2) 1 0).mpr h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ((fLevelOrF_spec H
        (scons (natV H 1) (scons (natV H 0) ee))
        (c_i+2) (e_i+2) (b_i+2) (s_i+2) 1 0).mpr h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((fLevelAllF_spec H lF L hl
        (scons (natV H 1) (scons (natV H 0) ee))
        (c_i+2) (e_i+2) (b_i+2) (s_i+2) 1 0 (bnd_i+2) hE.1).mpr h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((fLevelExF_spec H lF L hl
        (scons (natV H 1) (scons (natV H 0) ee))
        (c_i+2) (e_i+2) (b_i+2) (s_i+2) 1 0 (bnd_i+2) hE.1).mpr h)))))

/-! ### Monotonicity, two-valuedness, and inversion at a known tag -/

/-- **The step relation is monotone in the certificate.**  Every occurrence of
the certificate is a positive membership assertion; the previous level does not
mention it at all. -/
theorem levelJustified_mono (H : ZFAxioms mem) {L : V → V → V → Prop}
    {bnd S S' c e b : V} (hsub : ∀ x, mem x S → mem x S')
    (h : LevelJustified H L bnd S c e b) : LevelJustified H L bnd S' c e b := by
  unfold LevelJustified at h ⊢
  rcases h with h | ⟨c1, c2, hc, hcase⟩ | ⟨c1, c2, hc, hcase⟩ |
    ⟨c1, c2, hc, hcase⟩ | ⟨c1, hc, hcase⟩ | ⟨c1, hc, hcase⟩
  · exact Or.inl h
  · refine Or.inr (Or.inl ⟨c1, c2, hc, ?_⟩)
    rcases hcase with ⟨hb, h1 | h1⟩ | ⟨hb, h1, h2⟩
    · exact Or.inl ⟨hb, Or.inl (hsub _ h1)⟩
    · exact Or.inl ⟨hb, Or.inr (hsub _ h1)⟩
    · exact Or.inr ⟨hb, hsub _ h1, hsub _ h2⟩
  · refine Or.inr (Or.inr (Or.inl ⟨c1, c2, hc, ?_⟩))
    rcases hcase with ⟨hb, h1, h2⟩ | ⟨hb, h1 | h1⟩
    · exact Or.inl ⟨hb, hsub _ h1, hsub _ h2⟩
    · exact Or.inr ⟨hb, Or.inl (hsub _ h1)⟩
    · exact Or.inr ⟨hb, Or.inr (hsub _ h1)⟩
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨c1, c2, hc, ?_⟩)))
    rcases hcase with ⟨hb, h1 | h1⟩ | ⟨hb, h1, h2⟩
    · exact Or.inl ⟨hb, Or.inl (hsub _ h1)⟩
    · exact Or.inl ⟨hb, Or.inr (hsub _ h1)⟩
    · exact Or.inr ⟨hb, hsub _ h1, hsub _ h2⟩
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c1, hc, ?_⟩))))
    rcases hcase with ⟨hb, hbd, hnot⟩ | ⟨hb, d, hd⟩
    · exact Or.inl ⟨hb, hbd, hnot⟩
    · exact Or.inr ⟨hb, d, hsub _ hd⟩
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨c1, hc, ?_⟩))))
    rcases hcase with ⟨hb, d, hd⟩ | ⟨hb, hbd, hnot⟩
    · exact Or.inl ⟨hb, d, hsub _ hd⟩
    · exact Or.inr ⟨hb, hbd, hnot⟩

/-- **A justified bit is the numeral `0` or the numeral `1`**, provided the
previous level assigns only such bits.  Every row of the table fixes the bit
outright. -/
theorem levelJustified_bit (H : ZFAxioms mem) {L : V → V → V → Prop}
    (hL : ∀ c e b, L c e b → b = natV H 0 ∨ b = natV H 1)
    {bnd S c e b : V} (h : LevelJustified H L bnd S c e b) :
    b = natV H 0 ∨ b = natV H 1 := by
  unfold LevelJustified at h
  rcases h with h | ⟨_, _, _, hcase⟩ | ⟨_, _, _, hcase⟩ | ⟨_, _, _, hcase⟩ |
    ⟨_, _, hcase⟩ | ⟨_, _, hcase⟩
  · exact hL _ _ _ h
  · rcases hcase with ⟨hb, _⟩ | ⟨hb, _⟩
    · exact Or.inr hb
    · exact Or.inl hb
  · rcases hcase with ⟨hb, _⟩ | ⟨hb, _⟩
    · exact Or.inr hb
    · exact Or.inl hb
  · rcases hcase with ⟨hb, _⟩ | ⟨hb, _⟩
    · exact Or.inr hb
    · exact Or.inl hb
  · rcases hcase with ⟨hb, _⟩ | ⟨hb, _⟩
    · exact Or.inr hb
    · exact Or.inl hb
  · rcases hcase with ⟨hb, _⟩ | ⟨hb, _⟩
    · exact Or.inr hb
    · exact Or.inl hb

/-! Codes carrying different tags are different sets, so at a code of known
shape at most two of the six rows can apply.  Each lemma discards the others by
`formCode_tag_ne`.  The delegation row is never discarded, since it constrains
no tag; that is what makes the elimination halves of the Tarski clauses
inductions on the level. -/

/-- At an atomic or falsity tag only the delegation row survives. -/
theorem levelJustified_of_tag_low (H : ZFAxioms mem) {L : V → V → V → Prop}
    {bnd S e b x : V} {t : Nat} (ht : t < 3)
    (h : LevelJustified H L bnd S (kpair H (natV H t) x) e b) :
    L (kpair H (natV H t) x) e b := by
  unfold LevelJustified at h
  rcases h with h | ⟨_, _, hc, _⟩ | ⟨_, _, hc, _⟩ | ⟨_, _, hc, _⟩ |
    ⟨_, hc, _⟩ | ⟨_, hc, _⟩
  · exact h
  · exact absurd hc (formCode_tag_ne H (by omega) _ _)
  · exact absurd hc (formCode_tag_ne H (by omega) _ _)
  · exact absurd hc (formCode_tag_ne H (by omega) _ _)
  · exact absurd hc (formCode_tag_ne H (by omega) _ _)
  · exact absurd hc (formCode_tag_ne H (by omega) _ _)

theorem levelJustified_imp (H : ZFAxioms mem) {L : V → V → V → Prop}
    {bnd S e b c1 c2 : V}
    (h : LevelJustified H L bnd S (kpair H (natV H 3) (kpair H c1 c2)) e b) :
    L (kpair H (natV H 3) (kpair H c1 c2)) e b ∨
      ((b = natV H 1 ∧ (mem (satTriple H c1 e (natV H 0)) S ∨
                        mem (satTriple H c2 e (natV H 1)) S)) ∨
       (b = natV H 0 ∧ mem (satTriple H c1 e (natV H 1)) S ∧
                       mem (satTriple H c2 e (natV H 0)) S)) := by
  unfold LevelJustified at h
  rcases h with h | ⟨d1, d2, hc, hcase⟩ | ⟨_, _, hc, _⟩ | ⟨_, _, hc, _⟩ |
    ⟨_, hc, _⟩ | ⟨_, hc, _⟩
  · exact Or.inl h
  · obtain ⟨-, hp⟩ := kpair_inj H _ _ _ _ hc
    obtain ⟨h1, h2⟩ := kpair_inj H _ _ _ _ hp
    rw [← h1, ← h2] at hcase
    exact Or.inr hcase
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)

theorem levelJustified_and (H : ZFAxioms mem) {L : V → V → V → Prop}
    {bnd S e b c1 c2 : V}
    (h : LevelJustified H L bnd S (kpair H (natV H 4) (kpair H c1 c2)) e b) :
    L (kpair H (natV H 4) (kpair H c1 c2)) e b ∨
      ((b = natV H 1 ∧ mem (satTriple H c1 e (natV H 1)) S ∧
                       mem (satTriple H c2 e (natV H 1)) S) ∨
       (b = natV H 0 ∧ (mem (satTriple H c1 e (natV H 0)) S ∨
                        mem (satTriple H c2 e (natV H 0)) S))) := by
  unfold LevelJustified at h
  rcases h with h | ⟨_, _, hc, _⟩ | ⟨d1, d2, hc, hcase⟩ | ⟨_, _, hc, _⟩ |
    ⟨_, hc, _⟩ | ⟨_, hc, _⟩
  · exact Or.inl h
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · obtain ⟨-, hp⟩ := kpair_inj H _ _ _ _ hc
    obtain ⟨h1, h2⟩ := kpair_inj H _ _ _ _ hp
    rw [← h1, ← h2] at hcase
    exact Or.inr hcase
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)

theorem levelJustified_or (H : ZFAxioms mem) {L : V → V → V → Prop}
    {bnd S e b c1 c2 : V}
    (h : LevelJustified H L bnd S (kpair H (natV H 5) (kpair H c1 c2)) e b) :
    L (kpair H (natV H 5) (kpair H c1 c2)) e b ∨
      ((b = natV H 1 ∧ (mem (satTriple H c1 e (natV H 1)) S ∨
                        mem (satTriple H c2 e (natV H 1)) S)) ∨
       (b = natV H 0 ∧ mem (satTriple H c1 e (natV H 0)) S ∧
                       mem (satTriple H c2 e (natV H 0)) S)) := by
  unfold LevelJustified at h
  rcases h with h | ⟨_, _, hc, _⟩ | ⟨_, _, hc, _⟩ | ⟨d1, d2, hc, hcase⟩ |
    ⟨_, hc, _⟩ | ⟨_, hc, _⟩
  · exact Or.inl h
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · obtain ⟨-, hp⟩ := kpair_inj H _ _ _ _ hc
    obtain ⟨h1, h2⟩ := kpair_inj H _ _ _ _ hp
    rw [← h1, ← h2] at hcase
    exact Or.inr hcase
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)

theorem levelJustified_all (H : ZFAxioms mem) {L : V → V → V → Prop}
    {bnd S e b c1 : V}
    (h : LevelJustified H L bnd S (kpair H (natV H 6) c1) e b) :
    L (kpair H (natV H 6) c1) e b ∨
      ((b = natV H 1 ∧ PiBounded H bnd (kpair H (natV H 6) c1) ∧
          ¬ L (kpair H (natV H 6) c1) e (natV H 0)) ∨
       (b = natV H 0 ∧
          ∃ d, mem (satTriple H c1 (econs H d e) (natV H 0)) S)) := by
  unfold LevelJustified at h
  rcases h with h | ⟨_, _, hc, _⟩ | ⟨_, _, hc, _⟩ | ⟨_, _, hc, _⟩ |
    ⟨d1, hc, hcase⟩ | ⟨_, hc, _⟩
  · exact Or.inl h
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · obtain ⟨-, h1⟩ := kpair_inj H _ _ _ _ hc
    rw [← h1] at hcase
    exact Or.inr hcase
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)

theorem levelJustified_ex (H : ZFAxioms mem) {L : V → V → V → Prop}
    {bnd S e b c1 : V}
    (h : LevelJustified H L bnd S (kpair H (natV H 7) c1) e b) :
    L (kpair H (natV H 7) c1) e b ∨
      ((b = natV H 1 ∧
          ∃ d, mem (satTriple H c1 (econs H d e) (natV H 1)) S) ∨
       (b = natV H 0 ∧ SigmaBounded H bnd (kpair H (natV H 7) c1) ∧
          ¬ L (kpair H (natV H 7) c1) e (natV H 1))) := by
  unfold LevelJustified at h
  rcases h with h | ⟨_, _, hc, _⟩ | ⟨_, _, hc, _⟩ | ⟨_, _, hc, _⟩ |
    ⟨_, hc, _⟩ | ⟨d1, hc, hcase⟩
  · exact Or.inl h
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · obtain ⟨-, h1⟩ := kpair_inj H _ _ _ _ hc
    rw [← h1] at hcase
    exact Or.inr hcase

/-! ## Certificates

A set is **step-closed** when every record it carries is justified by the set
itself and its environment is a genuine universe environment.  The environment
clause is not decoration: without it the object-language reading of the shift
in the quantifier clauses would be unavailable. -/

/-- Every record of `C` is justified by `C`, over genuine environments. -/
def LevelClosed (H : ZFAxioms mem) (L : V → V → V → Prop) (bnd C : V) : Prop :=
  ∀ c e b, mem (satTriple H c e b) C →
    (IsUnivEnv H e ∧ LevelJustified H L bnd C c e b)

/-- "slot `s_i` is step-closed for the previous level `lF` with bound slot
`bnd_i`".

| de Bruijn slot | contents              |
| -------------- | --------------------- |
| `0`            | the bit `b`           |
| `1`            | the environment `e`   |
| `2`            | the code `c`          |
| `m+3`          | the caller's slot `m` |
-/
def fLevelClosedF (lF : Nat → Nat → Nat → Form) (bnd_i s_i : Nat) : Form :=
  fAll (fAll (fAll (fImp (fTripleMemF 2 1 0 (s_i+3))
    (fAnd (fUnivEnvF 1) (fLevelJustifiedF lF 2 1 0 (s_i+3) (bnd_i+3))))))

theorem fLevelClosedF_spec (H : ZFAxioms mem) (lF : Nat → Nat → Nat → Form)
    (L : V → V → V → Prop)
    (hl : ∀ (ee' : Nat → V) (c e b : Nat),
      Sat mem ee' (lF c e b) ↔ L (ee' c) (ee' e) (ee' b))
    (ee : Nat → V) (bnd_i s_i : Nat) :
    Sat mem ee (fLevelClosedF lF bnd_i s_i) ↔
      LevelClosed H L (ee bnd_i) (ee s_i) := by
  unfold LevelClosed
  constructor
  · intro h c e b hmem
    obtain ⟨h1, h2⟩ := h c e b
      ((fTripleMemF_spec H (scons b (scons e (scons c ee)))
        2 1 0 (s_i+3)).mpr hmem)
    have henv : IsUnivEnv H e :=
      (fUnivEnvF_spec H (scons b (scons e (scons c ee))) 1).mp h1
    exact ⟨henv, (fLevelJustifiedF_spec H lF L hl
      (scons b (scons e (scons c ee))) 2 1 0 (s_i+3) (bnd_i+3) henv).mp h2⟩
  · intro h c e b hsat
    obtain ⟨henv, hj⟩ := h c e b
      ((fTripleMemF_spec H (scons b (scons e (scons c ee)))
        2 1 0 (s_i+3)).mp hsat)
    exact ⟨(fUnivEnvF_spec H (scons b (scons e (scons c ee))) 1).mpr henv,
      (fLevelJustifiedF_spec H lF L hl
        (scons b (scons e (scons c ee))) 2 1 0 (s_i+3) (bnd_i+3) henv).mpr hj⟩

/-! ### Building step-closed sets

The empty set is step-closed vacuously, a union of step-closed sets is
step-closed by monotonicity, and a single justified record may always be
adjoined.  Those three operations are all the constructions below need: each
quantifier clause records exactly one witness or one counterexample, so a
compound certificate is a union plus one record. -/

theorem levelClosed_empty (H : ZFAxioms mem) (L : V → V → V → Prop) (bnd : V) :
    LevelClosed H L bnd (vempty H) :=
  fun _ _ _ h => absurd h (vempty_spec H _)

theorem levelClosed_cup (H : ZFAxioms mem) {L : V → V → V → Prop} {bnd C1 C2 : V}
    (h1 : LevelClosed H L bnd C1) (h2 : LevelClosed H L bnd C2) :
    LevelClosed H L bnd (vcup H C1 C2) := by
  have hsub1 : ∀ x, mem x C1 → mem x (vcup H C1 C2) :=
    fun x hx => (vcup_spec H C1 C2 x).mpr (Or.inl hx)
  have hsub2 : ∀ x, mem x C2 → mem x (vcup H C1 C2) :=
    fun x hx => (vcup_spec H C1 C2 x).mpr (Or.inr hx)
  intro c e b hmem
  rcases (vcup_spec H C1 C2 _).mp hmem with h | h
  · exact ⟨(h1 c e b h).1, levelJustified_mono H hsub1 (h1 c e b h).2⟩
  · exact ⟨(h2 c e b h).1, levelJustified_mono H hsub2 (h2 c e b h).2⟩

theorem levelClosed_insert (H : ZFAxioms mem) {L : V → V → V → Prop}
    {bnd C c e b : V} (hC : LevelClosed H L bnd C) (he : IsUnivEnv H e)
    (hj : LevelJustified H L bnd C c e b) :
    LevelClosed H L bnd (vcup H C (vsingle H (satTriple H c e b))) := by
  have hsub : ∀ x, mem x C → mem x (vcup H C (vsingle H (satTriple H c e b))) :=
    fun x hx => (vcup_spec H _ _ x).mpr (Or.inl hx)
  intro c0 e0 b0 hmem
  rcases (vcup_spec H C (vsingle H (satTriple H c e b)) _).mp hmem with h | h
  · exact ⟨(hC c0 e0 b0 h).1, levelJustified_mono H hsub (hC c0 e0 b0 h).2⟩
  · obtain ⟨q1, q2, q3⟩ :=
      satTriple_inj H ((vsingle_spec H (satTriple H c e b) _).mp h)
    rw [q1, q2, q3]
    exact ⟨he, levelJustified_mono H hsub hj⟩

/-! ## The externally indexed family

`LevelSat H n c e b` is the level-`n` reading of the record `⟨c, e, b⟩`.  The
recursion is on the metatheoretic `n`; there is no internal recursion on the
level and no formula with the level as a free variable. -/

/-- **Level-`n` satisfaction of a record.**  At level zero the code must be
quantifier-free and the bit is the truth bit of `QFTrue`; at a positive level
the record must carry a certificate built over the previous level. -/
def LevelSat (H : ZFAxioms mem) : Nat → (V → V → V → Prop)
  | 0 => fun c e b => IsQFCodeSem H c ∧ b = vbit H (QFTrue H c e)
  | n+1 => fun c e b => ∃ C, LevelClosed H (LevelSat H n) (natV H n) C ∧
      mem (satTriple H c e b) C

theorem levelSat_zero_iff (H : ZFAxioms mem) (c e b : V) :
    LevelSat H 0 c e b ↔ (IsQFCodeSem H c ∧ b = vbit H (QFTrue H c e)) :=
  Iff.rfl

theorem levelSat_succ_iff (H : ZFAxioms mem) (n : Nat) (c e b : V) :
    LevelSat H (n+1) c e b ↔
      ∃ C, LevelClosed H (LevelSat H n) (natV H n) C ∧
        mem (satTriple H c e b) C :=
  Iff.rfl

/-- **The level-`n` record predicate as a `Form`.**  The external `Nat` is the
length of the recursion producing the formula, never a slot of it.

| de Bruijn slot | contents                          |
| -------------- | --------------------------------- |
| `0`            | the numeral of the previous level |
| `1`            | the certificate `C`               |
| `m+2`          | the caller's slot `m`             |
-/
def levelSatF : Nat → (Nat → Nat → Nat → Form)
  | 0 => fun c_i e_i b_i =>
      fAnd (fIsQFCodeF c_i) (fBitOfF b_i (fQFTrueF c_i e_i))
  | n+1 => fun c_i e_i b_i =>
      fEx (fEx (fAnd (fNumF 0 n)
        (fAnd (fLevelClosedF (levelSatF n) 0 1)
              (fTripleMemF (c_i+2) (e_i+2) (b_i+2) 1))))

/-- **The exact satisfaction spec, at every fixed level.**  The proof is an
external induction on the level; each step feeds the previous level's spec to
`fLevelClosedF_spec` as its definability hypothesis. -/
theorem levelSatF_spec (H : ZFAxioms mem) :
    ∀ (n : Nat) (ee : Nat → V) (c_i e_i b_i : Nat),
      Sat mem ee (levelSatF n c_i e_i b_i) ↔
        LevelSat H n (ee c_i) (ee e_i) (ee b_i) := by
  intro n
  induction n with
  | zero =>
      intro ee c_i e_i b_i
      constructor
      · rintro ⟨hq, hb⟩
        refine ⟨(fIsQFCodeF_spec H ee c_i).mp hq, ?_⟩
        have hb' := (fBitOfF_spec H ee b_i (fQFTrueF c_i e_i)).mp hb
        rw [hb']
        exact vbit_congr H (fQFTrueF_spec H ee c_i e_i)
      · rintro ⟨hq, hb⟩
        refine ⟨(fIsQFCodeF_spec H ee c_i).mpr hq, ?_⟩
        refine (fBitOfF_spec H ee b_i (fQFTrueF c_i e_i)).mpr ?_
        rw [hb]
        exact (vbit_congr H (fQFTrueF_spec H ee c_i e_i)).symm
  | succ n ih =>
      intro ee c_i e_i b_i
      constructor
      · rintro ⟨C, bd, hbd, hcl, hmem⟩
        have hbd' : bd = natV H n :=
          (fNumF_spec H n 0 (scons bd (scons C ee))).mp hbd
        have hcl' := (fLevelClosedF_spec H (levelSatF n) (LevelSat H n)
          (fun ee' c e b => ih ee' c e b) (scons bd (scons C ee)) 0 1).mp hcl
        rw [hbd'] at hcl'
        exact ⟨C, hcl', (fTripleMemF_spec H (scons bd (scons C ee))
          (c_i+2) (e_i+2) (b_i+2) 1).mp hmem⟩
      · rintro ⟨C, hcl, hmem⟩
        refine ⟨C, natV H n,
          (fNumF_spec H n 0 (scons (natV H n) (scons C ee))).mpr rfl, ?_, ?_⟩
        · exact (fLevelClosedF_spec H (levelSatF n) (LevelSat H n)
            (fun ee' c e b => ih ee' c e b)
            (scons (natV H n) (scons C ee)) 0 1).mpr hcl
        · exact (fTripleMemF_spec H (scons (natV H n) (scons C ee))
            (c_i+2) (e_i+2) (b_i+2) 1).mpr hmem

/-! ### The two readings of a record -/

/-- **Sigma-truth at level `n`**: the record with bit one is certified. -/
def SigmaTrue (H : ZFAxioms mem) (n : Nat) (c e : V) : Prop :=
  LevelSat H n c e (natV H 1)

/-- **Pi-falsity at level `n`**: the record with bit zero is certified.  This is
the positively certified notion; `PiTrue` is its complement. -/
def PiFalse (H : ZFAxioms mem) (n : Nat) (c e : V) : Prop :=
  LevelSat H n c e (natV H 0)

/-- **Pi-truth at level `n`**: no certificate makes the code false.  A Pi
statement's truth is never certified positively, which is what keeps every
certificate a set. -/
def PiTrue (H : ZFAxioms mem) (n : Nat) (c e : V) : Prop :=
  ¬ PiFalse H n c e

/-- "Sigma-truth of slot `c_i` at slot `e_i`, at level `n`". -/
def fSigmaTrueF (n c_i e_i : Nat) : Form :=
  fEx (fAnd (fNumF 0 1) (levelSatF n (c_i+1) (e_i+1) 0))

theorem fSigmaTrueF_spec (H : ZFAxioms mem) (n : Nat) (ee : Nat → V)
    (c_i e_i : Nat) :
    Sat mem ee (fSigmaTrueF n c_i e_i) ↔ SigmaTrue H n (ee c_i) (ee e_i) := by
  unfold SigmaTrue
  constructor
  · rintro ⟨o, ho, hs⟩
    have ho' : o = natV H 1 := (fNumF_spec H 1 0 (scons o ee)).mp ho
    have hs' := (levelSatF_spec H n (scons o ee) (c_i+1) (e_i+1) 0).mp hs
    rw [ho'] at hs'
    exact hs'
  · intro h
    exact ⟨natV H 1, (fNumF_spec H 1 0 (scons (natV H 1) ee)).mpr rfl,
      (levelSatF_spec H n (scons (natV H 1) ee) (c_i+1) (e_i+1) 0).mpr h⟩

/-- "Pi-falsity of slot `c_i` at slot `e_i`, at level `n`". -/
def fPiFalseF (n c_i e_i : Nat) : Form :=
  fEx (fAnd (fNumF 0 0) (levelSatF n (c_i+1) (e_i+1) 0))

theorem fPiFalseF_spec (H : ZFAxioms mem) (n : Nat) (ee : Nat → V)
    (c_i e_i : Nat) :
    Sat mem ee (fPiFalseF n c_i e_i) ↔ PiFalse H n (ee c_i) (ee e_i) := by
  unfold PiFalse
  constructor
  · rintro ⟨z, hz, hs⟩
    have hz' : z = natV H 0 := (fNumF_spec H 0 0 (scons z ee)).mp hz
    have hs' := (levelSatF_spec H n (scons z ee) (c_i+1) (e_i+1) 0).mp hs
    rw [hz'] at hs'
    exact hs'
  · intro h
    exact ⟨natV H 0, (fNumF_spec H 0 0 (scons (natV H 0) ee)).mpr rfl,
      (levelSatF_spec H n (scons (natV H 0) ee) (c_i+1) (e_i+1) 0).mpr h⟩

/-- "Pi-truth of slot `c_i` at slot `e_i`, at level `n`". -/
def fPiTrueF (n c_i e_i : Nat) : Form := fImp (fPiFalseF n c_i e_i) fBot

theorem fPiTrueF_spec (H : ZFAxioms mem) (n : Nat) (ee : Nat → V)
    (c_i e_i : Nat) :
    Sat mem ee (fPiTrueF n c_i e_i) ↔ PiTrue H n (ee c_i) (ee e_i) := by
  unfold PiTrue
  constructor
  · intro h hp
    exact h ((fPiFalseF_spec H n ee c_i e_i).mpr hp)
  · intro h hp
    exact h ((fPiFalseF_spec H n ee c_i e_i).mp hp)

/-! ## Adjoining a record, and the subsumption of lower levels -/

/-- A justified record over a step-closed set is certified by adjoining it.
This is the only way certificates are built below. -/
theorem levelSat_succ_of_justified (H : ZFAxioms mem) (n : Nat) {C c e b : V}
    (hC : LevelClosed H (LevelSat H n) (natV H n) C) (he : IsUnivEnv H e)
    (hj : LevelJustified H (LevelSat H n) (natV H n) C c e b) :
    LevelSat H (n+1) c e b :=
  ⟨vcup H C (vsingle H (satTriple H c e b)),
   levelClosed_insert H hC he hj,
   (vcup_spec H _ _ _).mpr (Or.inr ((vsingle_spec H _ _).mpr rfl))⟩

/-- **Each level subsumes the one below.**  The delegation row applies to any
record the previous level certifies, so a one-record certificate suffices; no
property of the code is needed. -/
theorem levelSat_succ_of_levelSat (H : ZFAxioms mem) (n : Nat) {c e b : V}
    (he : IsUnivEnv H e) (h : LevelSat H n c e b) : LevelSat H (n+1) c e b :=
  levelSat_succ_of_justified H n (levelClosed_empty H _ _) he (Or.inl h)

/-- Subsumption along any weakening of the level. -/
theorem levelSat_mono (H : ZFAxioms mem) {m n : Nat} (hmn : m ≤ n) {c e b : V}
    (he : IsUnivEnv H e) (h : LevelSat H m c e b) : LevelSat H n c e b := by
  induction n with
  | zero =>
      have hm : m = 0 := Nat.le_zero.mp hmn
      subst hm
      exact h
  | succ n ih =>
      by_cases hme : m = n + 1
      · subst hme
        exact h
      · exact levelSat_succ_of_levelSat H n he (ih (by omega))

/-- **Sigma-truth is monotone in the level.** -/
theorem sigmaTrue_mono (H : ZFAxioms mem) {m n : Nat} (hmn : m ≤ n) {c e : V}
    (he : IsUnivEnv H e) (h : SigmaTrue H m c e) : SigmaTrue H n c e :=
  levelSat_mono H hmn he h

/-- **Pi-falsity is monotone in the level.**  Pi-truth is therefore antitone,
and the two statements are the same statement: `PiTrue` is the complement of the
certified notion, so upward coherence on the Pi side is upward monotonicity of
`PiFalse`.  Turning it into upward monotonicity of `PiTrue` on codes bounded at
the lower level is the level-collapse theorem, which is not proved here. -/
theorem piFalse_mono (H : ZFAxioms mem) {m n : Nat} (hmn : m ≤ n) {c e : V}
    (he : IsUnivEnv H e) (h : PiFalse H m c e) : PiFalse H n c e :=
  levelSat_mono H hmn he h

theorem piTrue_anti (H : ZFAxioms mem) {m n : Nat} (hmn : m ≤ n) {c e : V}
    (he : IsUnivEnv H e) (h : PiTrue H n c e) : PiTrue H m c e :=
  fun hp => h (piFalse_mono H hmn he hp)

/-! ## Two-valuedness and the level-zero complement -/

/-- **A certified bit is the numeral `0` or the numeral `1`** at every level. -/
theorem levelSat_bit (H : ZFAxioms mem) :
    ∀ (n : Nat) (c e b : V), LevelSat H n c e b →
      (b = natV H 0 ∨ b = natV H 1) := by
  intro n
  induction n with
  | zero =>
      rintro c e b ⟨-, hb⟩
      rw [hb]
      exact vbit_zero_or_one H _
  | succ n ih =>
      rintro c e b ⟨C, hC, hmem⟩
      exact levelJustified_bit H (fun c' e' b' h => ih c' e' b' h)
        (hC c e b hmem).2

/-- **Level zero agrees with quantifier-free truth on the Sigma side.** -/
theorem sigmaTrue_zero_iff (H : ZFAxioms mem) {c e : V} :
    SigmaTrue H 0 c e ↔ (IsQFCodeSem H c ∧ QFTrue H c e) := by
  constructor
  · rintro ⟨hq, hb⟩
    exact ⟨hq, (vbit_eq_one H _).mp hb.symm⟩
  · rintro ⟨hq, ht⟩
    exact ⟨hq, (vbit_pos H ht).symm⟩

/-- **Level zero agrees with quantifier-free truth on the Pi side too.**  At
level zero the two polarities coincide, which is the base case of the polarity
ranks. -/
theorem piTrue_zero_iff (H : ZFAxioms mem) {c e : V} (hq : IsQFCodeSem H c) :
    PiTrue H 0 c e ↔ QFTrue H c e := by
  unfold PiTrue PiFalse
  constructor
  · intro h
    rcases Classical.em (QFTrue H c e) with ht | ht
    · exact ht
    · exact absurd
        (show LevelSat H 0 c e (natV H 0) from ⟨hq, (vbit_neg H ht).symm⟩) h
  · rintro ht ⟨-, hb⟩
    exact (vbit_eq_zero H _).mp hb.symm ht

/-- **Sigma-truth and Pi-falsity are exclusive at level zero.**  Both read the
same bit of the same proposition.  The corresponding statement at a positive
level is consistency of certificates and is a separate theorem, proved by
induction over codes rather than over the level. -/
theorem sigmaTrue_not_piFalse_zero (H : ZFAxioms mem) {c e : V}
    (h : SigmaTrue H 0 c e) : ¬ PiFalse H 0 c e := by
  rintro ⟨-, h0⟩
  obtain ⟨-, h1⟩ := h
  exact natV_ne H (by decide) (h0.trans h1.symm)

/-! ## Descent of quantifier-free codehood

`IsQFCodeSem` has no inversion, but complexity zero does descend through a
binary tag, and a code of complexity zero is quantifier-free.  These three
lemmas are what make the level-zero cases of the connective clauses go
through. -/

private theorem isQFCodeSem_imp_parts (H : ZFAxioms mem) {c1 c2 : V}
    (h1 : IsFormCodeSem H c1) (h2 : IsFormCodeSem H c2)
    (hq : IsQFCodeSem H (kpair H (natV H 3) (kpair H c1 c2))) :
    IsQFCodeSem H c1 ∧ IsQFCodeSem H c2 := by
  obtain ⟨k1, k2⟩ := quantBounded_imp H (natV_mem_omega H 0)
    (quantBounded_zero_of_isQFCodeSem H hq)
  exact ⟨isQFCodeSem_of_quantBounded_zero H c1 h1 k1,
    isQFCodeSem_of_quantBounded_zero H c2 h2 k2⟩

private theorem isQFCodeSem_and_parts (H : ZFAxioms mem) {c1 c2 : V}
    (h1 : IsFormCodeSem H c1) (h2 : IsFormCodeSem H c2)
    (hq : IsQFCodeSem H (kpair H (natV H 4) (kpair H c1 c2))) :
    IsQFCodeSem H c1 ∧ IsQFCodeSem H c2 := by
  obtain ⟨k1, k2⟩ := quantBounded_and H (natV_mem_omega H 0)
    (quantBounded_zero_of_isQFCodeSem H hq)
  exact ⟨isQFCodeSem_of_quantBounded_zero H c1 h1 k1,
    isQFCodeSem_of_quantBounded_zero H c2 h2 k2⟩

private theorem isQFCodeSem_or_parts (H : ZFAxioms mem) {c1 c2 : V}
    (h1 : IsFormCodeSem H c1) (h2 : IsFormCodeSem H c2)
    (hq : IsQFCodeSem H (kpair H (natV H 5) (kpair H c1 c2))) :
    IsQFCodeSem H c1 ∧ IsQFCodeSem H c2 := by
  obtain ⟨k1, k2⟩ := quantBounded_or H (natV_mem_omega H 0)
    (quantBounded_zero_of_isQFCodeSem H hq)
  exact ⟨isQFCodeSem_of_quantBounded_zero H c1 h1 k1,
    isQFCodeSem_of_quantBounded_zero H c2 h2 k2⟩

/-! ## The Tarski clauses

Each clause has an introduction half, valid at every positive level and proved
by adjoining one record, and an elimination half, valid at every level and
proved by inverting a certificate.  The elimination halves are inductions on the
level, because the delegation row is never excluded by a tag; the induction
bottoms out at level zero in the corresponding clause of
`BoundedZFCConsistency.UniverseTruthZero`. -/

/-! ### Atoms and falsity

At a tag below three the only applicable row is delegation, so every level reads
an atom exactly as level zero does. -/

theorem sigmaTrue_memAtom (H : ZFAxioms mem) :
    ∀ (n : Nat) {i j e : V}, mem i (omegaV H) → mem j (omegaV H) →
      IsUnivEnv H e →
      (SigmaTrue H n (kpair H (natV H 0) (kpair H i j)) e ↔
        mem (applyV H e i) (applyV H e j)) := by
  intro n
  induction n with
  | zero =>
      intro i j e hi hj he
      rw [sigmaTrue_zero_iff]
      constructor
      · rintro ⟨-, ht⟩
        exact (qfTrue_memAtom H hi hj he).mp ht
      · intro h
        exact ⟨isQFCodeSem_memAtom H hi hj, (qfTrue_memAtom H hi hj he).mpr h⟩
  | succ n ih =>
      intro i j e hi hj he
      constructor
      · rintro ⟨C, hC, hmem⟩
        exact (ih hi hj he).mp
          (levelJustified_of_tag_low H (by omega) (hC _ _ _ hmem).2)
      · intro h
        exact levelSat_succ_of_levelSat H n he ((ih hi hj he).mpr h)

theorem sigmaTrue_eqAtom (H : ZFAxioms mem) :
    ∀ (n : Nat) {i j e : V}, mem i (omegaV H) → mem j (omegaV H) →
      IsUnivEnv H e →
      (SigmaTrue H n (kpair H (natV H 1) (kpair H i j)) e ↔
        applyV H e i = applyV H e j) := by
  intro n
  induction n with
  | zero =>
      intro i j e hi hj he
      rw [sigmaTrue_zero_iff]
      constructor
      · rintro ⟨-, ht⟩
        exact (qfTrue_eqAtom H hi hj he).mp ht
      · intro h
        exact ⟨isQFCodeSem_eqAtom H hi hj, (qfTrue_eqAtom H hi hj he).mpr h⟩
  | succ n ih =>
      intro i j e hi hj he
      constructor
      · rintro ⟨C, hC, hmem⟩
        exact (ih hi hj he).mp
          (levelJustified_of_tag_low H (by omega) (hC _ _ _ hmem).2)
      · intro h
        exact levelSat_succ_of_levelSat H n he ((ih hi hj he).mpr h)

/-- **Falsity is never Sigma-true**, at any level. -/
theorem sigmaTrue_bot (H : ZFAxioms mem) :
    ∀ (n : Nat) {e : V}, ¬ SigmaTrue H n (kpair H (natV H 2) (vempty H)) e := by
  intro n
  induction n with
  | zero =>
      intro e h
      rw [sigmaTrue_zero_iff] at h
      exact qfTrue_bot H h.2
  | succ n ih =>
      rintro e ⟨C, hC, hmem⟩
      exact ih (levelJustified_of_tag_low H (by omega) (hC _ _ _ hmem).2)

/-- **Falsity is Pi-false at every level**, over a genuine environment. -/
theorem piFalse_bot (H : ZFAxioms mem) (n : Nat) {e : V} (he : IsUnivEnv H e) :
    PiFalse H n (kpair H (natV H 2) (vempty H)) e :=
  levelSat_mono H (Nat.zero_le n) he
    ⟨isQFCodeSem_bot H, (vbit_neg H (qfTrue_bot H)).symm⟩

/-! ### The three connectives -/

/-- Conjunction, Sigma side: elimination. -/
theorem sigmaTrue_and_elim (H : ZFAxioms mem) :
    ∀ (n : Nat) {c1 c2 e : V}, IsFormCodeSem H c1 → IsFormCodeSem H c2 →
      IsUnivEnv H e →
      SigmaTrue H n (kpair H (natV H 4) (kpair H c1 c2)) e →
      (SigmaTrue H n c1 e ∧ SigmaTrue H n c2 e) := by
  intro n
  induction n with
  | zero =>
      intro c1 c2 e h1 h2 he h
      rw [sigmaTrue_zero_iff] at h
      obtain ⟨hq, ht⟩ := h
      obtain ⟨q1, q2⟩ := isQFCodeSem_and_parts H h1 h2 hq
      obtain ⟨t1, t2⟩ := (qfTrue_and H q1 q2 he).mp ht
      exact ⟨(sigmaTrue_zero_iff H).mpr ⟨q1, t1⟩,
        (sigmaTrue_zero_iff H).mpr ⟨q2, t2⟩⟩
  | succ n ih =>
      rintro c1 c2 e h1 h2 he ⟨C, hC, hmem⟩
      rcases levelJustified_and H (hC _ _ _ hmem).2 with hesc | hcase
      · obtain ⟨k1, k2⟩ := ih h1 h2 he hesc
        exact ⟨levelSat_succ_of_levelSat H n he k1,
          levelSat_succ_of_levelSat H n he k2⟩
      · rcases hcase with ⟨-, m1, m2⟩ | ⟨hb, -⟩
        · exact ⟨⟨C, hC, m1⟩, ⟨C, hC, m2⟩⟩
        · exact absurd hb (natV_ne H (by decide))

/-- Conjunction, Sigma side: introduction. -/
theorem sigmaTrue_and_intro (H : ZFAxioms mem) (n : Nat) {c1 c2 e : V}
    (he : IsUnivEnv H e) (k1 : SigmaTrue H (n+1) c1 e)
    (k2 : SigmaTrue H (n+1) c2 e) :
    SigmaTrue H (n+1) (kpair H (natV H 4) (kpair H c1 c2)) e := by
  obtain ⟨C1, hC1, m1⟩ := k1
  obtain ⟨C2, hC2, m2⟩ := k2
  refine levelSat_succ_of_justified H n (levelClosed_cup H hC1 hC2) he ?_
  exact Or.inr (Or.inr (Or.inl ⟨c1, c2, rfl, Or.inl ⟨rfl,
    (vcup_spec H C1 C2 _).mpr (Or.inl m1),
    (vcup_spec H C1 C2 _).mpr (Or.inr m2)⟩⟩))

/-- **Conjunction on the Sigma side.** -/
theorem sigmaTrue_and (H : ZFAxioms mem) (n : Nat) {c1 c2 e : V}
    (h1 : IsFormCodeSem H c1) (h2 : IsFormCodeSem H c2) (he : IsUnivEnv H e) :
    SigmaTrue H (n+1) (kpair H (natV H 4) (kpair H c1 c2)) e ↔
      (SigmaTrue H (n+1) c1 e ∧ SigmaTrue H (n+1) c2 e) :=
  ⟨sigmaTrue_and_elim H (n+1) h1 h2 he,
    fun h => sigmaTrue_and_intro H n he h.1 h.2⟩

/-- Conjunction, Pi side: elimination. -/
theorem piFalse_and_elim (H : ZFAxioms mem) :
    ∀ (n : Nat) {c1 c2 e : V}, IsFormCodeSem H c1 → IsFormCodeSem H c2 →
      IsUnivEnv H e →
      PiFalse H n (kpair H (natV H 4) (kpair H c1 c2)) e →
      (PiFalse H n c1 e ∨ PiFalse H n c2 e) := by
  intro n
  induction n with
  | zero =>
      intro c1 c2 e h1 h2 he h
      obtain ⟨hq, hb⟩ := h
      obtain ⟨q1, q2⟩ := isQFCodeSem_and_parts H h1 h2 hq
      have hnt : ¬ QFTrue H (kpair H (natV H 4) (kpair H c1 c2)) e :=
        (vbit_eq_zero H _).mp hb.symm
      by_cases t1 : QFTrue H c1 e
      · by_cases t2 : QFTrue H c2 e
        · exact absurd ((qfTrue_and H q1 q2 he).mpr ⟨t1, t2⟩) hnt
        · exact Or.inr ⟨q2, (vbit_neg H t2).symm⟩
      · exact Or.inl ⟨q1, (vbit_neg H t1).symm⟩
  | succ n ih =>
      rintro c1 c2 e h1 h2 he ⟨C, hC, hmem⟩
      rcases levelJustified_and H (hC _ _ _ hmem).2 with hesc | hcase
      · rcases ih h1 h2 he hesc with k | k
        · exact Or.inl (levelSat_succ_of_levelSat H n he k)
        · exact Or.inr (levelSat_succ_of_levelSat H n he k)
      · rcases hcase with ⟨hb, -⟩ | ⟨-, m | m⟩
        · exact absurd hb (natV_ne H (by decide))
        · exact Or.inl ⟨C, hC, m⟩
        · exact Or.inr ⟨C, hC, m⟩

/-- Conjunction, Pi side: introduction. -/
theorem piFalse_and_intro (H : ZFAxioms mem) (n : Nat) {c1 c2 e : V}
    (he : IsUnivEnv H e)
    (k : PiFalse H (n+1) c1 e ∨ PiFalse H (n+1) c2 e) :
    PiFalse H (n+1) (kpair H (natV H 4) (kpair H c1 c2)) e := by
  rcases k with ⟨C, hC, m⟩ | ⟨C, hC, m⟩
  · exact levelSat_succ_of_justified H n hC he
      (Or.inr (Or.inr (Or.inl ⟨c1, c2, rfl, Or.inr ⟨rfl, Or.inl m⟩⟩)))
  · exact levelSat_succ_of_justified H n hC he
      (Or.inr (Or.inr (Or.inl ⟨c1, c2, rfl, Or.inr ⟨rfl, Or.inr m⟩⟩)))

/-- **Conjunction on the Pi side.** -/
theorem piFalse_and (H : ZFAxioms mem) (n : Nat) {c1 c2 e : V}
    (h1 : IsFormCodeSem H c1) (h2 : IsFormCodeSem H c2) (he : IsUnivEnv H e) :
    PiFalse H (n+1) (kpair H (natV H 4) (kpair H c1 c2)) e ↔
      (PiFalse H (n+1) c1 e ∨ PiFalse H (n+1) c2 e) :=
  ⟨piFalse_and_elim H (n+1) h1 h2 he, piFalse_and_intro H n he⟩

/-- Disjunction, Sigma side: elimination. -/
theorem sigmaTrue_or_elim (H : ZFAxioms mem) :
    ∀ (n : Nat) {c1 c2 e : V}, IsFormCodeSem H c1 → IsFormCodeSem H c2 →
      IsUnivEnv H e →
      SigmaTrue H n (kpair H (natV H 5) (kpair H c1 c2)) e →
      (SigmaTrue H n c1 e ∨ SigmaTrue H n c2 e) := by
  intro n
  induction n with
  | zero =>
      intro c1 c2 e h1 h2 he h
      rw [sigmaTrue_zero_iff] at h
      obtain ⟨hq, ht⟩ := h
      obtain ⟨q1, q2⟩ := isQFCodeSem_or_parts H h1 h2 hq
      rcases (qfTrue_or H q1 q2 he).mp ht with t | t
      · exact Or.inl ((sigmaTrue_zero_iff H).mpr ⟨q1, t⟩)
      · exact Or.inr ((sigmaTrue_zero_iff H).mpr ⟨q2, t⟩)
  | succ n ih =>
      rintro c1 c2 e h1 h2 he ⟨C, hC, hmem⟩
      rcases levelJustified_or H (hC _ _ _ hmem).2 with hesc | hcase
      · rcases ih h1 h2 he hesc with k | k
        · exact Or.inl (levelSat_succ_of_levelSat H n he k)
        · exact Or.inr (levelSat_succ_of_levelSat H n he k)
      · rcases hcase with ⟨-, m | m⟩ | ⟨hb, -⟩
        · exact Or.inl ⟨C, hC, m⟩
        · exact Or.inr ⟨C, hC, m⟩
        · exact absurd hb (natV_ne H (by decide))

/-- Disjunction, Sigma side: introduction. -/
theorem sigmaTrue_or_intro (H : ZFAxioms mem) (n : Nat) {c1 c2 e : V}
    (he : IsUnivEnv H e)
    (k : SigmaTrue H (n+1) c1 e ∨ SigmaTrue H (n+1) c2 e) :
    SigmaTrue H (n+1) (kpair H (natV H 5) (kpair H c1 c2)) e := by
  rcases k with ⟨C, hC, m⟩ | ⟨C, hC, m⟩
  · exact levelSat_succ_of_justified H n hC he
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨c1, c2, rfl, Or.inl ⟨rfl, Or.inl m⟩⟩))))
  · exact levelSat_succ_of_justified H n hC he
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨c1, c2, rfl, Or.inl ⟨rfl, Or.inr m⟩⟩))))

/-- **Disjunction on the Sigma side.** -/
theorem sigmaTrue_or (H : ZFAxioms mem) (n : Nat) {c1 c2 e : V}
    (h1 : IsFormCodeSem H c1) (h2 : IsFormCodeSem H c2) (he : IsUnivEnv H e) :
    SigmaTrue H (n+1) (kpair H (natV H 5) (kpair H c1 c2)) e ↔
      (SigmaTrue H (n+1) c1 e ∨ SigmaTrue H (n+1) c2 e) :=
  ⟨sigmaTrue_or_elim H (n+1) h1 h2 he, sigmaTrue_or_intro H n he⟩

/-- Disjunction, Pi side: elimination. -/
theorem piFalse_or_elim (H : ZFAxioms mem) :
    ∀ (n : Nat) {c1 c2 e : V}, IsFormCodeSem H c1 → IsFormCodeSem H c2 →
      IsUnivEnv H e →
      PiFalse H n (kpair H (natV H 5) (kpair H c1 c2)) e →
      (PiFalse H n c1 e ∧ PiFalse H n c2 e) := by
  intro n
  induction n with
  | zero =>
      intro c1 c2 e h1 h2 he h
      obtain ⟨hq, hb⟩ := h
      obtain ⟨q1, q2⟩ := isQFCodeSem_or_parts H h1 h2 hq
      have hnt : ¬ QFTrue H (kpair H (natV H 5) (kpair H c1 c2)) e :=
        (vbit_eq_zero H _).mp hb.symm
      exact ⟨⟨q1, (vbit_neg H (fun t => hnt
          ((qfTrue_or H q1 q2 he).mpr (Or.inl t)))).symm⟩,
        ⟨q2, (vbit_neg H (fun t => hnt
          ((qfTrue_or H q1 q2 he).mpr (Or.inr t)))).symm⟩⟩
  | succ n ih =>
      rintro c1 c2 e h1 h2 he ⟨C, hC, hmem⟩
      rcases levelJustified_or H (hC _ _ _ hmem).2 with hesc | hcase
      · obtain ⟨k1, k2⟩ := ih h1 h2 he hesc
        exact ⟨levelSat_succ_of_levelSat H n he k1,
          levelSat_succ_of_levelSat H n he k2⟩
      · rcases hcase with ⟨hb, -⟩ | ⟨-, m1, m2⟩
        · exact absurd hb (natV_ne H (by decide))
        · exact ⟨⟨C, hC, m1⟩, ⟨C, hC, m2⟩⟩

/-- Disjunction, Pi side: introduction. -/
theorem piFalse_or_intro (H : ZFAxioms mem) (n : Nat) {c1 c2 e : V}
    (he : IsUnivEnv H e) (k1 : PiFalse H (n+1) c1 e)
    (k2 : PiFalse H (n+1) c2 e) :
    PiFalse H (n+1) (kpair H (natV H 5) (kpair H c1 c2)) e := by
  obtain ⟨C1, hC1, m1⟩ := k1
  obtain ⟨C2, hC2, m2⟩ := k2
  refine levelSat_succ_of_justified H n (levelClosed_cup H hC1 hC2) he ?_
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨c1, c2, rfl, Or.inr ⟨rfl,
    (vcup_spec H C1 C2 _).mpr (Or.inl m1),
    (vcup_spec H C1 C2 _).mpr (Or.inr m2)⟩⟩)))

/-- **Disjunction on the Pi side.** -/
theorem piFalse_or (H : ZFAxioms mem) (n : Nat) {c1 c2 e : V}
    (h1 : IsFormCodeSem H c1) (h2 : IsFormCodeSem H c2) (he : IsUnivEnv H e) :
    PiFalse H (n+1) (kpair H (natV H 5) (kpair H c1 c2)) e ↔
      (PiFalse H (n+1) c1 e ∧ PiFalse H (n+1) c2 e) :=
  ⟨piFalse_or_elim H (n+1) h1 h2 he, fun h => piFalse_or_intro H n he h.1 h.2⟩

/-- Implication, Sigma side: elimination.  The antecedent changes polarity, so
the Sigma row of an implication asks for Pi-falsity of the antecedent. -/
theorem sigmaTrue_imp_elim (H : ZFAxioms mem) :
    ∀ (n : Nat) {c1 c2 e : V}, IsFormCodeSem H c1 → IsFormCodeSem H c2 →
      IsUnivEnv H e →
      SigmaTrue H n (kpair H (natV H 3) (kpair H c1 c2)) e →
      (PiFalse H n c1 e ∨ SigmaTrue H n c2 e) := by
  intro n
  induction n with
  | zero =>
      intro c1 c2 e h1 h2 he h
      rw [sigmaTrue_zero_iff] at h
      obtain ⟨hq, ht⟩ := h
      obtain ⟨q1, q2⟩ := isQFCodeSem_imp_parts H h1 h2 hq
      by_cases t1 : QFTrue H c1 e
      · exact Or.inr ((sigmaTrue_zero_iff H).mpr
          ⟨q2, (qfTrue_imp H q1 q2 he).mp ht t1⟩)
      · exact Or.inl ⟨q1, (vbit_neg H t1).symm⟩
  | succ n ih =>
      rintro c1 c2 e h1 h2 he ⟨C, hC, hmem⟩
      rcases levelJustified_imp H (hC _ _ _ hmem).2 with hesc | hcase
      · rcases ih h1 h2 he hesc with k | k
        · exact Or.inl (levelSat_succ_of_levelSat H n he k)
        · exact Or.inr (levelSat_succ_of_levelSat H n he k)
      · rcases hcase with ⟨-, m | m⟩ | ⟨hb, -, -⟩
        · exact Or.inl ⟨C, hC, m⟩
        · exact Or.inr ⟨C, hC, m⟩
        · exact absurd hb (natV_ne H (by decide))

/-- Implication, Sigma side: introduction. -/
theorem sigmaTrue_imp_intro (H : ZFAxioms mem) (n : Nat) {c1 c2 e : V}
    (he : IsUnivEnv H e)
    (k : PiFalse H (n+1) c1 e ∨ SigmaTrue H (n+1) c2 e) :
    SigmaTrue H (n+1) (kpair H (natV H 3) (kpair H c1 c2)) e := by
  rcases k with ⟨C, hC, m⟩ | ⟨C, hC, m⟩
  · exact levelSat_succ_of_justified H n hC he
      (Or.inr (Or.inl ⟨c1, c2, rfl, Or.inl ⟨rfl, Or.inl m⟩⟩))
  · exact levelSat_succ_of_justified H n hC he
      (Or.inr (Or.inl ⟨c1, c2, rfl, Or.inl ⟨rfl, Or.inr m⟩⟩))

/-- **Implication on the Sigma side.** -/
theorem sigmaTrue_imp (H : ZFAxioms mem) (n : Nat) {c1 c2 e : V}
    (h1 : IsFormCodeSem H c1) (h2 : IsFormCodeSem H c2) (he : IsUnivEnv H e) :
    SigmaTrue H (n+1) (kpair H (natV H 3) (kpair H c1 c2)) e ↔
      (PiFalse H (n+1) c1 e ∨ SigmaTrue H (n+1) c2 e) :=
  ⟨sigmaTrue_imp_elim H (n+1) h1 h2 he, sigmaTrue_imp_intro H n he⟩

/-- Implication, Pi side: elimination. -/
theorem piFalse_imp_elim (H : ZFAxioms mem) :
    ∀ (n : Nat) {c1 c2 e : V}, IsFormCodeSem H c1 → IsFormCodeSem H c2 →
      IsUnivEnv H e →
      PiFalse H n (kpair H (natV H 3) (kpair H c1 c2)) e →
      (SigmaTrue H n c1 e ∧ PiFalse H n c2 e) := by
  intro n
  induction n with
  | zero =>
      intro c1 c2 e h1 h2 he h
      obtain ⟨hq, hb⟩ := h
      obtain ⟨q1, q2⟩ := isQFCodeSem_imp_parts H h1 h2 hq
      have hnt : ¬ QFTrue H (kpair H (natV H 3) (kpair H c1 c2)) e :=
        (vbit_eq_zero H _).mp hb.symm
      by_cases t1 : QFTrue H c1 e
      · refine ⟨(sigmaTrue_zero_iff H).mpr ⟨q1, t1⟩, ⟨q2, ?_⟩⟩
        exact (vbit_neg H (fun t2 =>
          hnt ((qfTrue_imp H q1 q2 he).mpr (fun _ => t2)))).symm
      · exact absurd ((qfTrue_imp H q1 q2 he).mpr (fun t => absurd t t1)) hnt
  | succ n ih =>
      rintro c1 c2 e h1 h2 he ⟨C, hC, hmem⟩
      rcases levelJustified_imp H (hC _ _ _ hmem).2 with hesc | hcase
      · obtain ⟨k1, k2⟩ := ih h1 h2 he hesc
        exact ⟨levelSat_succ_of_levelSat H n he k1,
          levelSat_succ_of_levelSat H n he k2⟩
      · rcases hcase with ⟨hb, -⟩ | ⟨-, m1, m2⟩
        · exact absurd hb (natV_ne H (by decide))
        · exact ⟨⟨C, hC, m1⟩, ⟨C, hC, m2⟩⟩

/-- Implication, Pi side: introduction. -/
theorem piFalse_imp_intro (H : ZFAxioms mem) (n : Nat) {c1 c2 e : V}
    (he : IsUnivEnv H e) (k1 : SigmaTrue H (n+1) c1 e)
    (k2 : PiFalse H (n+1) c2 e) :
    PiFalse H (n+1) (kpair H (natV H 3) (kpair H c1 c2)) e := by
  obtain ⟨C1, hC1, m1⟩ := k1
  obtain ⟨C2, hC2, m2⟩ := k2
  refine levelSat_succ_of_justified H n (levelClosed_cup H hC1 hC2) he ?_
  exact Or.inr (Or.inl ⟨c1, c2, rfl, Or.inr ⟨rfl,
    (vcup_spec H C1 C2 _).mpr (Or.inl m1),
    (vcup_spec H C1 C2 _).mpr (Or.inr m2)⟩⟩)

/-- **Implication on the Pi side.** -/
theorem piFalse_imp (H : ZFAxioms mem) (n : Nat) {c1 c2 e : V}
    (h1 : IsFormCodeSem H c1) (h2 : IsFormCodeSem H c2) (he : IsUnivEnv H e) :
    PiFalse H (n+1) (kpair H (natV H 3) (kpair H c1 c2)) e ↔
      (SigmaTrue H (n+1) c1 e ∧ PiFalse H (n+1) c2 e) :=
  ⟨piFalse_imp_elim H (n+1) h1 h2 he, fun h => piFalse_imp_intro H n he h.1 h.2⟩

/-! ### The quantifier heads

The existential head on the Sigma side and the universal head on the Pi side are
the two positively recorded quantifier clauses.  Each quantifies over the whole
universe on the outside, which is exactly what a certificate cannot do and what
the record's single witness makes unnecessary. -/

/-- Existential head, Sigma side: elimination. -/
theorem sigmaTrue_ex_elim (H : ZFAxioms mem) :
    ∀ (n : Nat) {c1 e : V}, IsUnivEnv H e →
      SigmaTrue H n (kpair H (natV H 7) c1) e →
      ∃ d, SigmaTrue H n c1 (econs H d e) := by
  intro n
  induction n with
  | zero =>
      intro c1 e he h
      rw [sigmaTrue_zero_iff] at h
      exact absurd (quantBounded_zero_of_isQFCodeSem H h.1)
        (not_quantBounded_zero_ex H)
  | succ n ih =>
      rintro c1 e he ⟨C, hC, hmem⟩
      rcases levelJustified_ex H (hC _ _ _ hmem).2 with hesc | hcase
      · obtain ⟨d, hd⟩ := ih he hesc
        exact ⟨d, levelSat_succ_of_levelSat H n (econs_isUnivEnv H he d) hd⟩
      · rcases hcase with ⟨-, d, hd⟩ | ⟨hb, -, -⟩
        · exact ⟨d, ⟨C, hC, hd⟩⟩
        · exact absurd hb (natV_ne H (by decide))

/-- Existential head, Sigma side: introduction.  One witness is recorded. -/
theorem sigmaTrue_ex_intro (H : ZFAxioms mem) (n : Nat) {c1 e d : V}
    (he : IsUnivEnv H e) (h : SigmaTrue H (n+1) c1 (econs H d e)) :
    SigmaTrue H (n+1) (kpair H (natV H 7) c1) e := by
  obtain ⟨C, hC, m⟩ := h
  exact levelSat_succ_of_justified H n hC he
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨c1, rfl, Or.inl ⟨rfl, d, m⟩⟩)))))

/-- **The existential head on the Sigma side.**  The quantifier ranges over the
whole universe. -/
theorem sigmaTrue_ex (H : ZFAxioms mem) (n : Nat) {c1 e : V}
    (he : IsUnivEnv H e) :
    SigmaTrue H (n+1) (kpair H (natV H 7) c1) e ↔
      ∃ d, SigmaTrue H (n+1) c1 (econs H d e) :=
  ⟨sigmaTrue_ex_elim H (n+1) he,
    fun h => h.elim (fun _ hd => sigmaTrue_ex_intro H n he hd)⟩

/-- Universal head, Pi side: elimination. -/
theorem piFalse_all_elim (H : ZFAxioms mem) :
    ∀ (n : Nat) {c1 e : V}, IsUnivEnv H e →
      PiFalse H n (kpair H (natV H 6) c1) e →
      ∃ d, PiFalse H n c1 (econs H d e) := by
  intro n
  induction n with
  | zero =>
      intro c1 e he h
      exact absurd (quantBounded_zero_of_isQFCodeSem H h.1)
        (not_quantBounded_zero_all H)
  | succ n ih =>
      rintro c1 e he ⟨C, hC, hmem⟩
      rcases levelJustified_all H (hC _ _ _ hmem).2 with hesc | hcase
      · obtain ⟨d, hd⟩ := ih he hesc
        exact ⟨d, levelSat_succ_of_levelSat H n (econs_isUnivEnv H he d) hd⟩
      · rcases hcase with ⟨hb, -, -⟩ | ⟨-, d, hd⟩
        · exact absurd hb (natV_ne H (by decide))
        · exact ⟨d, ⟨C, hC, hd⟩⟩

/-- Universal head, Pi side: introduction.  One counterexample is recorded. -/
theorem piFalse_all_intro (H : ZFAxioms mem) (n : Nat) {c1 e d : V}
    (he : IsUnivEnv H e) (h : PiFalse H (n+1) c1 (econs H d e)) :
    PiFalse H (n+1) (kpair H (natV H 6) c1) e := by
  obtain ⟨C, hC, m⟩ := h
  exact levelSat_succ_of_justified H n hC he
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨c1, rfl, Or.inr ⟨rfl, d, m⟩⟩)))))

/-- **The universal head on the Pi side**, stated on the true side: a universal
code is Pi-true exactly when its matrix is Pi-true at every shift.  This is the
De Morgan reading of the counterexample clause, and the quantifier ranges over
the whole universe. -/
theorem piTrue_all (H : ZFAxioms mem) (n : Nat) {c1 e : V}
    (he : IsUnivEnv H e) :
    PiTrue H (n+1) (kpair H (natV H 6) c1) e ↔
      ∀ d, PiTrue H (n+1) c1 (econs H d e) := by
  constructor
  · intro h d hd
    exact h (piFalse_all_intro H n he hd)
  · intro h hf
    obtain ⟨d, hd⟩ := piFalse_all_elim H (n+1) he hf
    exact h d hd

/-! ### The polarity switch

At a universal head on the Sigma side, and at an existential head on the Pi
side, no certificate can record the quantifier: the row delegates to the
previous level under the matching oriented bound.  This is where the external
index does its work, and it is the only place where two levels meet. -/

/-- **The polarity switch at a universal head.**  A universal code that is
Pi-bounded at level `n` and Pi-true there is Sigma-true at level `n+1`.  The
bound is not decoration: without it the delegated row would be vacuously
available at every code the previous level says nothing about. -/
theorem sigmaTrue_all_of_piTrue (H : ZFAxioms mem) (n : Nat) {c1 e : V}
    (he : IsUnivEnv H e)
    (hb : PiBounded H (natV H n) (kpair H (natV H 6) c1))
    (hp : PiTrue H n (kpair H (natV H 6) c1) e) :
    SigmaTrue H (n+1) (kpair H (natV H 6) c1) e :=
  levelSat_succ_of_justified H n (levelClosed_empty H _ _) he
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c1, rfl, Or.inl ⟨rfl, hb, hp⟩⟩)))))

/-- **The polarity switch at an existential head.**  An existential code that is
Sigma-bounded at level `n` and Sigma-false there is Pi-false at level `n+1`. -/
theorem piFalse_ex_of_not_sigmaTrue (H : ZFAxioms mem) (n : Nat) {c1 e : V}
    (he : IsUnivEnv H e)
    (hb : SigmaBounded H (natV H n) (kpair H (natV H 7) c1))
    (hp : ¬ SigmaTrue H n (kpair H (natV H 7) c1) e) :
    PiFalse H (n+1) (kpair H (natV H 7) c1) e :=
  levelSat_succ_of_justified H n (levelClosed_empty H _ _) he
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨c1, rfl, Or.inr ⟨rfl, hb, hp⟩⟩)))))

/-- **Inverting the switch.**  A Sigma-true universal code at level `n+1` is
either already Sigma-true at level `n`, or Pi-bounded and Pi-true there.
Discharging the first disjunct in general is the level-collapse theorem and is
not proved here; at level one it is discharged outright, below. -/
theorem sigmaTrue_all_inv (H : ZFAxioms mem) (n : Nat) {c1 e : V}
    (h : SigmaTrue H (n+1) (kpair H (natV H 6) c1) e) :
    SigmaTrue H n (kpair H (natV H 6) c1) e ∨
      (PiBounded H (natV H n) (kpair H (natV H 6) c1) ∧
        PiTrue H n (kpair H (natV H 6) c1) e) := by
  obtain ⟨C, hC, hmem⟩ := h
  rcases levelJustified_all H (hC _ _ _ hmem).2 with hesc | hcase
  · exact Or.inl hesc
  · rcases hcase with ⟨-, hb, hp⟩ | ⟨hb, -⟩
    · exact Or.inr ⟨hb, hp⟩
    · exact absurd hb (natV_ne H (by decide))

/-- **Level one carries no universal code on the Sigma side.**  Both rows of the
inversion fail: level zero recognizes no quantified code, and no universal code
is Pi-bounded by the numeral zero.  This is the internal counterpart of
`sigmaRank (fAll a) ≥ 2`, and it is the check that level one is a genuine
Sigma-1 predicate rather than a collapse of the hierarchy. -/
theorem not_sigmaTrue_one_all (H : ZFAxioms mem) {c1 e : V} :
    ¬ SigmaTrue H 1 (kpair H (natV H 6) c1) e := by
  intro h
  rcases sigmaTrue_all_inv H 0 h with hesc | ⟨hb, -⟩
  · rw [sigmaTrue_zero_iff] at hesc
    exact absurd (quantBounded_zero_of_isQFCodeSem H hesc.1)
      (not_quantBounded_zero_all H)
  · exact not_piBounded_zero_all H hb

/-- **Inverting the switch on the Pi side.** -/
theorem piFalse_ex_inv (H : ZFAxioms mem) (n : Nat) {c1 e : V}
    (h : PiFalse H (n+1) (kpair H (natV H 7) c1) e) :
    PiFalse H n (kpair H (natV H 7) c1) e ∨
      (SigmaBounded H (natV H n) (kpair H (natV H 7) c1) ∧
        ¬ SigmaTrue H n (kpair H (natV H 7) c1) e) := by
  obtain ⟨C, hC, hmem⟩ := h
  rcases levelJustified_ex H (hC _ _ _ hmem).2 with hesc | hcase
  · exact Or.inl hesc
  · rcases hcase with ⟨hb, -⟩ | ⟨-, hb, hp⟩
    · exact absurd hb (natV_ne H (by decide))
    · exact Or.inr ⟨hb, hp⟩

/-- **Level one carries no existential code on the Pi-false side**, for the dual
reason. -/
theorem not_piFalse_one_ex (H : ZFAxioms mem) {c1 e : V} :
    ¬ PiFalse H 1 (kpair H (natV H 7) c1) e := by
  intro h
  rcases piFalse_ex_inv H 0 h with hesc | ⟨hb, -⟩
  · exact absurd (quantBounded_zero_of_isQFCodeSem H hesc.1)
      (not_quantBounded_zero_ex H)
  · exact not_sigmaBounded_zero_ex H hb

/-! ## Agreement with the metatheory

The quotation bridge of `UniverseTruthZero` identifies both polarities at level
zero, and subsumption carries each of them upward.  A quantifier-free external
formula therefore has its metatheoretic truth value read correctly at every
level; the converse readings at a positive level would need the level-collapse
theorem and are not stated. -/

/-- **Level zero agrees with the metatheory on quotations**, on both
polarities. -/
theorem levelSat_formCode_zero (H : ZFAxioms mem) {E : V} (hE : IsUnivEnv H E)
    (phi : Form) (hphi : IsQuantFree phi) :
    (SigmaTrue H 0 (formCode H phi) E ↔
        Sat mem (fun k => applyV H E (natV H k)) phi) ∧
      (PiFalse H 0 (formCode H phi) E ↔
        ¬ Sat mem (fun k => applyV H E (natV H k)) phi) := by
  have hq : IsQFCodeSem H (formCode H phi) := formCode_isQFCodeSem H phi hphi
  have hbridge := qfTrue_formCode_iff_apply H hE phi hphi
  constructor
  · rw [sigmaTrue_zero_iff]
    exact ⟨fun h => hbridge.mp h.2, fun h => ⟨hq, hbridge.mpr h⟩⟩
  · constructor
    · rintro ⟨-, hb⟩ h
      exact (vbit_eq_zero H _).mp hb.symm (hbridge.mpr h)
    · intro h
      exact ⟨hq, (vbit_neg H (fun ht => h (hbridge.mp ht))).symm⟩

/-- **A true quantifier-free quotation is Sigma-true at every level.** -/
theorem sigmaTrue_formCode_of_sat (H : ZFAxioms mem) (n : Nat) {E : V}
    (hE : IsUnivEnv H E) (phi : Form) (hphi : IsQuantFree phi)
    (h : Sat mem (fun k => applyV H E (natV H k)) phi) :
    SigmaTrue H n (formCode H phi) E :=
  levelSat_mono H (Nat.zero_le n) hE
    ((levelSat_formCode_zero H hE phi hphi).1.mpr h)

/-- **A false quantifier-free quotation is Pi-false at every level.** -/
theorem piFalse_formCode_of_not_sat (H : ZFAxioms mem) (n : Nat) {E : V}
    (hE : IsUnivEnv H E) (phi : Form) (hphi : IsQuantFree phi)
    (h : ¬ Sat mem (fun k => applyV H E (natV H k)) phi) :
    PiFalse H n (formCode H phi) E :=
  levelSat_mono H (Nat.zero_le n) hE
    ((levelSat_formCode_zero H hE phi hphi).2.mpr h)

end UniverseTruthLevel

end BoundedZFCConsistency
end LeanProofs
