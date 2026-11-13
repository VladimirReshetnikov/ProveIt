import BoundedZFCConsistency.CodedRank

/-!
# Quantifier-free truth over the universe

`BoundedZFCConsistency.InternalSatTotality` interprets a code in a **set**
structure `(A, R)`: the quantifiers range over the carrier `A` and the
membership symbol is interpreted by the set `R`.  What the partial-satisfaction
route needs instead is truth over the **universe** — quantifiers ranging over
all sets, the membership symbol interpreted by the model's own `mem`, and
equality by the model's own equality.  Tarski's theorem forbids a single
formula defining that for all codes, which is why the eventual hierarchy is
indexed by an *external* level.  This module is its base case, and is confined
to the quantifier-free fragment, where no such obstruction exists: nothing
below quantifies over a carrier, so the truth of a quantifier-free code is
determined by finitely many atoms of a set-sized environment.

Because this syntax has no primitive bounded quantifier, the base case is
quantifier-free truth rather than `Delta_0` truth: atoms, falsity and the three
Boolean connectives, and nothing else.

## Environments

An environment is an internal **function on the whole internal omega**, in the
sense of `IsFunctionOn`/`applyV`:

```text
IsUnivEnv H E  :=  IsFunctionOn H E (omegaV H)
```

Two choices are being made here and both are forced.

*The domain is the internal omega, not a numeral.*  A code is an arbitrary
element of the model, so in a nonstandard model its variable indices are
arbitrary internal naturals; an environment defined only on a numeral would
leave those atoms uninterpreted.  Totality on `omegaV H` is exactly what makes
the atomic clauses unconditional.

*The values are unrestricted, so there is no carrier clause.*  This is the
whole difference from `IsEnvOn`: an environment for universe truth may take any
sets as values.  It is still a **set** — an element of the model, a set of
Kuratowski pairs — which is what lets it appear as an argument of an internal
relation and be quantified over inside the object language.  Nothing weaker
would do: a metatheoretic valuation `Nat → V` is not an object of the model.

## The quantifier-free code domain

`IsQFCodeSem` is the intersection presentation of `CodePredicate` with the two
quantifier clauses deleted: `x` belongs to every set that contains the atoms
and falsity and is closed under implication, conjunction and disjunction.  Its
induction principle needs no existence hypothesis, because a formula-closed set
— which `FormulaClosedSet.exists_formulaClosed` produces — is in particular
quantifier-free-closed.

The syntactic domain **agrees exactly with internal rank zero**:

```text
IsFormCodeSem H c → (IsQFCodeSem H c ↔ QuantBounded H (natV H 0) c)
```

The forward direction is `Ranks H c 0 0` by quantifier-free induction; the
converse is code induction, using the descent lemmas of
`BoundedZFCConsistency.CodedRank` at the three Boolean tags and, at the two
quantifier tags, the fact that both ranks of a quantified code are at least
one.  The codehood hypothesis is needed only for the converse, and cannot be
dropped there: `QuantBounded` says nothing about a set that is not a code.

## Truth by certificates

The architecture is that of `InternalSat`, with the eight clauses cut to six
and the carrier and relation slots removed:

| tag | clause | bit                                                        |
| --- | ------ | ---------------------------------------------------------- |
| `0` | `fMem` | `1` exactly when `e i ∈ e j` **in the model**              |
| `1` | `fEq`  | `1` exactly when `e i = e j` **in the model**              |
| `2` | `fBot` | always `0`                                                 |
| `3` | `fImp` | `1` exactly when the first subbit is `0` or the second `1` |
| `4` | `fAnd` | `1` exactly when both subbits are `1`                      |
| `5` | `fOr`  | `1` exactly when some subbit is `1`                        |

Deleting the quantifier clauses simplifies totality considerably.  For
`SatIn` the induction hypothesis had to be strengthened to be uniform over a
whole *set* of environments, because a quantifier clause needs a certificate
for each carrier element and a definable choice is unavailable.  Here no clause
quantifies over anything, so — exactly as for internal renaming — a compound
certificate is a union of two certificates plus one new triple, and the plain
existential form of totality goes through.

## Agreement on quotations

`qfTrue_formCode_iff` closes the loop with the metatheory: for an externally
quantifier-free `phi` and an internal environment `E`,

```text
QFTrue H (formCode H phi) E ↔ Sat mem (fun k => applyV H E (natV H k)) phi.
```

The valuation is read off the environment rather than the other way round.
That direction is the available one: an arbitrary metatheoretic valuation
`Nat → V` need not be the trace of any set, since it is not definable, whereas
every internal environment does induce a valuation.  Since a quantifier-free
formula's satisfaction depends on the valuation alone, this is the form in
which the truth of quantifier-free axiom instances will eventually be read.

Nothing below assumes that a code is the quotation of an external formula; the
converse of quotation soundness is false in nonstandard models, and every
statement about codes here is about arbitrary internal ones.

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

section UniverseTruthZero

variable {V : Type u} {mem : V → V → Prop}

/-! ## Environments over the universe -/

/-- An environment for universe truth: an internal function defined on the
whole internal omega, with unrestricted values.  It is a set of the model, so
it can be quantified over internally. -/
def IsUnivEnv (H : ZFAxioms mem) (E : V) : Prop :=
  IsFunctionOn H E (omegaV H)

/-- The value of an environment at an internal index is recorded in the
environment itself. -/
theorem isUnivEnv_mem (H : ZFAxioms mem) {E : V} (hE : IsUnivEnv H E) {n : V}
    (hn : mem n (omegaV H)) : mem (kpair H n (applyV H E n)) E :=
  applyV_mem H (hE.2.1 n hn)

/-- **Environments exist.**  Unlike the set-structure case this needs no
nonemptiness hypothesis: the universe is never empty, since it contains the
empty set. -/
theorem exists_isUnivEnv (H : ZFAxioms mem) : ∃ E, IsUnivEnv H E :=
  ⟨constEnv H (vempty H),
    (constEnv_isEnvOn H ((vsingle_spec H (vempty H) (vempty H)).mpr rfl)).1⟩

/-- "slot `e_i` is an environment over the universe".  The domain is not a
slot: membership in the internal omega is written with `fNatF`, which uses the
pure intersection characterization. -/
def fUnivEnvF (e_i : Nat) : Form := fFunOnOmegaF e_i

theorem fUnivEnvF_spec (H : ZFAxioms mem) (ee : Nat → V) (e_i : Nat) :
    Sat mem ee (fUnivEnvF e_i) ↔ IsUnivEnv H (ee e_i) :=
  fFunOnOmegaF_spec H ee e_i

/-! ## The quantifier-free code domain

The presentation is the intersection one of
`BoundedZFCConsistency.CodePredicate` with the `fAll` and `fEx` clauses
deleted.  As there, the atomic clauses range over the *internal* omega, so in a
nonstandard model the domain contains quantifier-free codes with nonstandard
variable indices; that is intended, and is why the notion is internal. -/

/-- A set is **quantifier-free-closed** when it contains every atomic code and
the code of falsity and is closed under the three binary connectives. -/
structure QFClosed (H : ZFAxioms mem) (C : V) : Prop where
  /-- Codes of atomic membership formulas, with internal variable indices. -/
  memAtom : ∀ a b, mem a (omegaV H) → mem b (omegaV H) →
    mem (kpair H (natV H 0) (kpair H a b)) C
  /-- Codes of atomic equations, with internal variable indices. -/
  eqAtom : ∀ a b, mem a (omegaV H) → mem b (omegaV H) →
    mem (kpair H (natV H 1) (kpair H a b)) C
  /-- The code of falsity. -/
  bot : mem (kpair H (natV H 2) (vempty H)) C
  /-- Closure under the implication constructor. -/
  imp : ∀ a b, mem a C → mem b C → mem (kpair H (natV H 3) (kpair H a b)) C
  /-- Closure under the conjunction constructor. -/
  conj : ∀ a b, mem a C → mem b C → mem (kpair H (natV H 4) (kpair H a b)) C
  /-- Closure under the disjunction constructor. -/
  disj : ∀ a b, mem a C → mem b C → mem (kpair H (natV H 5) (kpair H a b)) C

/-- A formula-closed set is quantifier-free-closed: it satisfies six of the
eight clauses and the other two are not asked for. -/
theorem qfClosed_of_formulaClosed (H : ZFAxioms mem) {C : V}
    (hC : FormulaClosed H C) : QFClosed H C :=
  ⟨hC.memAtom, hC.eqAtom, hC.bot, hC.imp, hC.conj, hC.disj⟩

/-- A quantifier-free-closed set exists, inherited from the formula-closed set
constructed in `BoundedZFCConsistency.FormulaClosedSet`.  This is what makes
the induction principle below unconditional. -/
theorem exists_qfClosed (H : ZFAxioms mem) : ∃ C, QFClosed H C := by
  obtain ⟨C, hC⟩ := exists_formulaClosed H
  exact ⟨C, qfClosed_of_formulaClosed H hC⟩

/-- **"`x` codes a quantifier-free formula", semantically**: `x` belongs to
every quantifier-free-closed set. -/
def IsQFCodeSem (H : ZFAxioms mem) (x : V) : Prop :=
  ∀ C, QFClosed H C → mem x C

/-- A quantifier-free code is a code.  The converse is false: a code with a
quantifier at any node is not quantifier-free. -/
theorem isFormCodeSem_of_isQFCodeSem (H : ZFAxioms mem) {x : V}
    (h : IsQFCodeSem H x) : IsFormCodeSem H x :=
  fun C hC => h C (qfClosed_of_formulaClosed H hC)

/-! ### The introduction rules -/

theorem isQFCodeSem_memAtom (H : ZFAxioms mem) {a b : V}
    (ha : mem a (omegaV H)) (hb : mem b (omegaV H)) :
    IsQFCodeSem H (kpair H (natV H 0) (kpair H a b)) :=
  fun _ hC => hC.memAtom a b ha hb

theorem isQFCodeSem_eqAtom (H : ZFAxioms mem) {a b : V}
    (ha : mem a (omegaV H)) (hb : mem b (omegaV H)) :
    IsQFCodeSem H (kpair H (natV H 1) (kpair H a b)) :=
  fun _ hC => hC.eqAtom a b ha hb

theorem isQFCodeSem_bot (H : ZFAxioms mem) :
    IsQFCodeSem H (kpair H (natV H 2) (vempty H)) :=
  fun _ hC => hC.bot

theorem isQFCodeSem_imp (H : ZFAxioms mem) {a b : V} (ha : IsQFCodeSem H a)
    (hb : IsQFCodeSem H b) :
    IsQFCodeSem H (kpair H (natV H 3) (kpair H a b)) :=
  fun C hC => hC.imp a b (ha C hC) (hb C hC)

theorem isQFCodeSem_and (H : ZFAxioms mem) {a b : V} (ha : IsQFCodeSem H a)
    (hb : IsQFCodeSem H b) :
    IsQFCodeSem H (kpair H (natV H 4) (kpair H a b)) :=
  fun C hC => hC.conj a b (ha C hC) (hb C hC)

theorem isQFCodeSem_or (H : ZFAxioms mem) {a b : V} (ha : IsQFCodeSem H a)
    (hb : IsQFCodeSem H b) :
    IsQFCodeSem H (kpair H (natV H 5) (kpair H a b)) :=
  fun C hC => hC.disj a b (ha C hC) (hb C hC)

/-! ### The object-language predicate -/

/-- "slot `c` is quantifier-free-closed" — the six clauses, reusing the closure
macros of `BoundedZFCConsistency.CodePredicate`. -/
def fQFClosedF (c : Nat) : Form :=
  fAnd (fClAtomF c 0)
    (fAnd (fClAtomF c 1)
      (fAnd (fTagEmptyMemF c 2)
        (fAnd (fClBinF c 3) (fAnd (fClBinF c 4) (fClBinF c 5)))))

theorem fQFClosedF_spec (H : ZFAxioms mem) (ee : Nat → V) (c : Nat) :
    Sat mem ee (fQFClosedF c) ↔ QFClosed H (ee c) := by
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩
    exact
      ⟨(fClAtomF_spec H ee c 0).mp h0,
       (fClAtomF_spec H ee c 1).mp h1,
       (fTagEmptyMemF_spec H ee c 2).mp h2,
       (fClBinF_spec H ee c 3).mp h3,
       (fClBinF_spec H ee c 4).mp h4,
       (fClBinF_spec H ee c 5).mp h5⟩
  · intro h
    exact
      ⟨(fClAtomF_spec H ee c 0).mpr h.memAtom,
       (fClAtomF_spec H ee c 1).mpr h.eqAtom,
       (fTagEmptyMemF_spec H ee c 2).mpr h.bot,
       (fClBinF_spec H ee c 3).mpr h.imp,
       (fClBinF_spec H ee c 4).mpr h.conj,
       (fClBinF_spec H ee c 5).mpr h.disj⟩

/-- **"slot `i` codes a quantifier-free formula", as a `Form`**.

| de Bruijn slot | contents                                 |
| -------------- | ---------------------------------------- |
| `0`            | the bound quantifier-free-closed set `C` |
| `m+1`          | the caller's slot `m`                    |
-/
def fIsQFCodeF (i : Nat) : Form :=
  fAll (fImp (fQFClosedF 0) (fMem (i+1) 0))

theorem fIsQFCodeF_spec (H : ZFAxioms mem) (ee : Nat → V) (i : Nat) :
    Sat mem ee (fIsQFCodeF i) ↔ IsQFCodeSem H (ee i) := by
  constructor
  · intro h C hC
    exact h C ((fQFClosedF_spec H (scons C ee) 0).mpr hC)
  · intro h C hC
    exact h C ((fQFClosedF_spec H (scons C ee) 0).mp hC)

/-! ### The induction principle

The instance of the intersection that does the work is the subset of a given
quantifier-free-closed set carved out by the property.  Separation supplies it
whenever the property is definable — which remains a genuine hypothesis, since
Separation carves subsets by a `Form` with parameters and not by an arbitrary
Lean predicate.  The existence hypothesis that `CodePredicate` had to carry is
discharged here at once by `exists_qfClosed`. -/

/-- **Induction on quantifier-free codes, as a definable schema.**  The
property is `phi` with parameters `e` in its free slots beyond slot `0`, in the
style of `omega_ind`. -/
theorem isQFCodeSem_ind_form (H : ZFAxioms mem) (phi : Form) (e : Nat → V)
    (hMemAtom : ∀ a b, mem a (omegaV H) → mem b (omegaV H) →
      Sat mem (scons (kpair H (natV H 0) (kpair H a b)) e) phi)
    (hEqAtom : ∀ a b, mem a (omegaV H) → mem b (omegaV H) →
      Sat mem (scons (kpair H (natV H 1) (kpair H a b)) e) phi)
    (hBot : Sat mem (scons (kpair H (natV H 2) (vempty H)) e) phi)
    (hImp : ∀ a b, Sat mem (scons a e) phi → Sat mem (scons b e) phi →
      Sat mem (scons (kpair H (natV H 3) (kpair H a b)) e) phi)
    (hAnd : ∀ a b, Sat mem (scons a e) phi → Sat mem (scons b e) phi →
      Sat mem (scons (kpair H (natV H 4) (kpair H a b)) e) phi)
    (hOr : ∀ a b, Sat mem (scons a e) phi → Sat mem (scons b e) phi →
      Sat mem (scons (kpair H (natV H 5) (kpair H a b)) e) phi) :
    ∀ x, IsQFCodeSem H x → Sat mem (scons x e) phi := by
  intro x hx
  obtain ⟨C0, hC0⟩ := exists_qfClosed H
  have hD : ∀ y, mem y (sepD H phi e C0) ↔
      (mem y C0 ∧ Sat mem (scons y e) phi) :=
    fun y => sepD_spec H phi e C0 y
  have hclosed : QFClosed H (sepD H phi e C0) := by
    refine
      ⟨fun a b ha hb => (hD _).mpr ⟨hC0.memAtom a b ha hb, hMemAtom a b ha hb⟩,
       fun a b ha hb => (hD _).mpr ⟨hC0.eqAtom a b ha hb, hEqAtom a b ha hb⟩,
       (hD _).mpr ⟨hC0.bot, hBot⟩, ?_, ?_, ?_⟩
    · intro a b ha hb
      obtain ⟨ha0, ha1⟩ := (hD a).mp ha
      obtain ⟨hb0, hb1⟩ := (hD b).mp hb
      exact (hD _).mpr ⟨hC0.imp a b ha0 hb0, hImp a b ha1 hb1⟩
    · intro a b ha hb
      obtain ⟨ha0, ha1⟩ := (hD a).mp ha
      obtain ⟨hb0, hb1⟩ := (hD b).mp hb
      exact (hD _).mpr ⟨hC0.conj a b ha0 hb0, hAnd a b ha1 hb1⟩
    · intro a b ha hb
      obtain ⟨ha0, ha1⟩ := (hD a).mp ha
      obtain ⟨hb0, hb1⟩ := (hD b).mp hb
      exact (hD _).mpr ⟨hC0.disj a b ha0 hb0, hOr a b ha1 hb1⟩
  exact ((hD x).mp (hx _ hclosed)).2

/-- **Induction on quantifier-free codes**, with the property presented as a
`Prop`-valued predicate together with a witness that it is definable. -/
theorem isQFCodeSem_ind (H : ZFAxioms mem) (P : V → Prop) (phi : Form)
    (e : Nat → V) (hdef : ∀ y, P y ↔ Sat mem (scons y e) phi)
    (hMemAtom : ∀ a b, mem a (omegaV H) → mem b (omegaV H) →
      P (kpair H (natV H 0) (kpair H a b)))
    (hEqAtom : ∀ a b, mem a (omegaV H) → mem b (omegaV H) →
      P (kpair H (natV H 1) (kpair H a b)))
    (hBot : P (kpair H (natV H 2) (vempty H)))
    (hImp : ∀ a b, P a → P b → P (kpair H (natV H 3) (kpair H a b)))
    (hAnd : ∀ a b, P a → P b → P (kpair H (natV H 4) (kpair H a b)))
    (hOr : ∀ a b, P a → P b → P (kpair H (natV H 5) (kpair H a b))) :
    ∀ x, IsQFCodeSem H x → P x := by
  intro x hx
  refine (hdef x).mpr ?_
  refine isQFCodeSem_ind_form H phi e
    (fun a b ha hb => (hdef _).mp (hMemAtom a b ha hb))
    (fun a b ha hb => (hdef _).mp (hEqAtom a b ha hb))
    ((hdef _).mp hBot)
    (fun a b ha hb => (hdef _).mp (hImp a b ((hdef a).mpr ha) ((hdef b).mpr hb)))
    (fun a b ha hb => (hdef _).mp (hAnd a b ((hdef a).mpr ha) ((hdef b).mpr hb)))
    (fun a b ha hb => (hdef _).mp (hOr a b ((hdef a).mpr ha) ((hdef b).mpr hb)))
    x hx

/-! ## Agreement with internal rank zero

The syntactic domain and the rank-zero domain coincide on codes.  Both
inclusions are proved, so nothing here has to choose between the two notions;
the syntactic one is nevertheless the primary definition below, since it is
what the truth predicate recurses on. -/

/-- The parameter block for the rank property: both ranks are the numeral
zero. -/
noncomputable def envQFRanksZero (H : ZFAxioms mem) : Nat → V :=
  scons (natV H 0) (scons (natV H 0) (fun _ => vempty H))

/-- **Both internal ranks of a quantifier-free code are zero.**  The atoms and
falsity have zero ranks outright, and each Boolean clause takes maxima of
zeros. -/
theorem ranks_zero_of_isQFCodeSem (H : ZFAxioms mem) :
    ∀ c, IsQFCodeSem H c → Ranks H c (natV H 0) (natV H 0) := by
  refine isQFCodeSem_ind H (fun c => Ranks H c (natV H 0) (natV H 0))
    (fRanksF 0 1 2) (envQFRanksZero H)
    (fun y => (fRanksF_spec H (scons y (envQFRanksZero H)) 0 1 2).symm)
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro a b ha hb
    exact ranks_memAtom H ha hb
  · intro a b ha hb
    exact ranks_eqAtom H ha hb
  · exact ranks_bot H
  · intro a b ha hb
    have h := ranks_imp H ha hb
    rw [vmaxN_natV] at h
    exact h
  · intro a b ha hb
    have h := ranks_and H ha hb
    rw [vmaxN_natV] at h
    exact h
  · intro a b ha hb
    have h := ranks_or H ha hb
    rw [vmaxN_natV] at h
    exact h

/-- A quantifier-free code has quantifier complexity zero. -/
theorem quantBounded_zero_of_isQFCodeSem (H : ZFAxioms mem) {c : V}
    (h : IsQFCodeSem H c) : QuantBounded H (natV H 0) c := by
  refine ⟨natV H 0, natV H 0, ranks_zero_of_isQFCodeSem H c h, ?_⟩
  rw [vminN_natV]
  exact (leN_natV_iff H (Nat.min 0 0) 0).mpr (by decide)

/-- **No universally quantified code has complexity zero.**  Both of its ranks
dominate the numeral one, hence so does their minimum. -/
theorem not_quantBounded_zero_all (H : ZFAxioms mem) {a : V} :
    ¬ QuantBounded H (natV H 0) (kpair H (natV H 6) a) := by
  rintro ⟨s, p, hr, hle⟩
  obtain ⟨sa, pa, ha, hs, hp⟩ := ranks_all_inv H hr
  obtain ⟨hsa, hpa⟩ := Ranks.mem_omega H ha
  have hm : mem (vmaxN H (natV H 1) pa) (omegaV H) :=
    vmaxN_mem_omega H (natV_mem_omega H 1) hpa
  subst hs
  subst hp
  have h1 : LeN H (natV H 1) (vmaxN H (natV H 1) pa) :=
    leN_vmaxN_left H (natV_mem_omega H 1) hpa
  have h2 : LeN H (natV H 1) (vsucc H (vmaxN H (natV H 1) pa)) :=
    leN_trans H (omega_succ H _ hm) h1 (leN_of_mem H (vsucc_self H _))
  have h4 : LeN H (natV H 1) (natV H 0) :=
    leN_trans H (natV_mem_omega H 0) (leN_vminN H h2 h1) hle
  exact absurd ((leN_natV_iff H 1 0).mp h4) (by omega)

/-- **No existentially quantified code has complexity zero.** -/
theorem not_quantBounded_zero_ex (H : ZFAxioms mem) {a : V} :
    ¬ QuantBounded H (natV H 0) (kpair H (natV H 7) a) := by
  rintro ⟨s, p, hr, hle⟩
  obtain ⟨sa, pa, ha, hs, hp⟩ := ranks_ex_inv H hr
  obtain ⟨hsa, hpa⟩ := Ranks.mem_omega H ha
  have hm : mem (vmaxN H (natV H 1) sa) (omegaV H) :=
    vmaxN_mem_omega H (natV_mem_omega H 1) hsa
  subst hs
  subst hp
  have h1 : LeN H (natV H 1) (vmaxN H (natV H 1) sa) :=
    leN_vmaxN_left H (natV_mem_omega H 1) hsa
  have h2 : LeN H (natV H 1) (vsucc H (vmaxN H (natV H 1) sa)) :=
    leN_trans H (omega_succ H _ hm) h1 (leN_of_mem H (vsucc_self H _))
  have h4 : LeN H (natV H 1) (natV H 0) :=
    leN_trans H (natV_mem_omega H 0) (leN_vminN H h1 h2) hle
  exact absurd ((leN_natV_iff H 1 0).mp h4) (by omega)

/-- The parameter block for the converse: the numeral zero, the bound. -/
noncomputable def envQFBoundZero (H : ZFAxioms mem) : Nat → V :=
  scons (natV H 0) (fun _ => vempty H)

/-- "the code in slot `0` is quantifier-free as soon as it has complexity at
most the bound in slot `1`".

| de Bruijn slot | contents           |
| -------------- | ------------------ |
| `0`            | the code           |
| `1`            | the numeral zero   |
-/
def fQFOfBoundF : Form := fImp (fQuantBoundedF 1 0) (fIsQFCodeF 0)

theorem fQFOfBoundF_spec (H : ZFAxioms mem) (y : V) :
    Sat mem (scons y (envQFBoundZero H)) fQFOfBoundF ↔
      (QuantBounded H (natV H 0) y → IsQFCodeSem H y) := by
  constructor
  · intro h hq
    exact (fIsQFCodeF_spec H (scons y (envQFBoundZero H)) 0).mp
      (h ((fQuantBoundedF_spec H (scons y (envQFBoundZero H)) 1 0).mpr hq))
  · intro h hq
    exact (fIsQFCodeF_spec H (scons y (envQFBoundZero H)) 0).mpr
      (h ((fQuantBoundedF_spec H (scons y (envQFBoundZero H)) 1 0).mp hq))

/-- **A code of complexity zero is quantifier-free.**  The codehood hypothesis
is not removable: `QuantBounded` constrains only sets that carry internal
ranks. -/
theorem isQFCodeSem_of_quantBounded_zero (H : ZFAxioms mem) :
    ∀ c, IsFormCodeSem H c → QuantBounded H (natV H 0) c → IsQFCodeSem H c := by
  refine isFormCodeSem_ind' H
    (fun c => QuantBounded H (natV H 0) c → IsQFCodeSem H c) fQFOfBoundF
    (envQFBoundZero H) (fun y => (fQFOfBoundF_spec H y).symm)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a b ha hb _
    exact isQFCodeSem_memAtom H ha hb
  · intro a b ha hb _
    exact isQFCodeSem_eqAtom H ha hb
  · intro _
    exact isQFCodeSem_bot H
  · intro a b ha hb hq
    exact isQFCodeSem_imp H
      (ha (quantBounded_imp H (natV_mem_omega H 0) hq).1)
      (hb (quantBounded_imp H (natV_mem_omega H 0) hq).2)
  · intro a b ha hb hq
    exact isQFCodeSem_and H
      (ha (quantBounded_and H (natV_mem_omega H 0) hq).1)
      (hb (quantBounded_and H (natV_mem_omega H 0) hq).2)
  · intro a b ha hb hq
    exact isQFCodeSem_or H
      (ha (quantBounded_or H (natV_mem_omega H 0) hq).1)
      (hb (quantBounded_or H (natV_mem_omega H 0) hq).2)
  · intro a _ hq
    exact absurd hq (not_quantBounded_zero_all H)
  · intro a _ hq
    exact absurd hq (not_quantBounded_zero_ex H)

/-- **The syntactic domain is exactly rank zero.** -/
theorem isQFCodeSem_iff_quantBounded_zero (H : ZFAxioms mem) {c : V}
    (hcode : IsFormCodeSem H c) :
    IsQFCodeSem H c ↔ QuantBounded H (natV H 0) c :=
  ⟨quantBounded_zero_of_isQFCodeSem H,
    isQFCodeSem_of_quantBounded_zero H c hcode⟩

/-! ## The local step

`QFJustified H S c e b` is the six-clause relation of the module header.  It is
*local*: it never mentions truth, only membership in the set `S` of
already-established triples.  Its atomic clauses read the **model's own**
membership and equality at the environment's values, falsity is always `0`, and
the three Boolean clauses use the usual truth tables, written as a `vbit` of a
condition on the subbits so that each is an equation rather than a case list.

Evaluation triples are the `satTriple` of `BoundedZFCConsistency.InternalSat`,
so the shape lemmas and the injectivity of the packaging are shared. -/

/-- The triple `⟨c, e, b⟩` is justified by the triples recorded in `S`. -/
def QFJustified (H : ZFAxioms mem) (S c e b : V) : Prop :=
  (∃ i j, mem i (omegaV H) ∧ mem j (omegaV H) ∧
      c = kpair H (natV H 0) (kpair H i j) ∧
      b = vbit H (mem (applyV H e i) (applyV H e j))) ∨
  (∃ i j, mem i (omegaV H) ∧ mem j (omegaV H) ∧
      c = kpair H (natV H 1) (kpair H i j) ∧
      b = vbit H (applyV H e i = applyV H e j)) ∨
  (c = kpair H (natV H 2) (vempty H) ∧ b = natV H 0) ∨
  (∃ c1 c2 b1 b2, c = kpair H (natV H 3) (kpair H c1 c2) ∧
      mem (satTriple H c1 e b1) S ∧ mem (satTriple H c2 e b2) S ∧
      b = vbit H (b1 = natV H 1 → b2 = natV H 1)) ∨
  (∃ c1 c2 b1 b2, c = kpair H (natV H 4) (kpair H c1 c2) ∧
      mem (satTriple H c1 e b1) S ∧ mem (satTriple H c2 e b2) S ∧
      b = vbit H (b1 = natV H 1 ∧ b2 = natV H 1)) ∨
  (∃ c1 c2 b1 b2, c = kpair H (natV H 5) (kpair H c1 c2) ∧
      mem (satTriple H c1 e b1) S ∧ mem (satTriple H c2 e b2) S ∧
      b = vbit H (b1 = natV H 1 ∨ b2 = natV H 1))

/-- **The step relation as a `Form`.**  The clause macros of
`BoundedZFCConsistency.InternalSat` are reused verbatim; only the two atomic
value conditions change, from membership in the structure's relation and
equality of carrier elements to the model's own `fMem` and `fEq` at the two
slots the macro exposes. -/
def fQFJustifiedF (c_i e_i b_i s_i : Nat) : Form :=
  fOr (fJustAtomF c_i e_i b_i 0 (fMem 1 0))
  (fOr (fJustAtomF c_i e_i b_i 1 (fEq 1 0))
  (fOr (fJustBotF c_i b_i)
  (fOr (fJustBinF c_i e_i b_i s_i 3 (fImp (fNumF 1 1) (fNumF 0 1)))
  (fOr (fJustBinF c_i e_i b_i s_i 4 (fAnd (fNumF 1 1) (fNumF 0 1)))
       (fJustBinF c_i e_i b_i s_i 5 (fOr (fNumF 1 1) (fNumF 0 1)))))))

theorem fQFJustifiedF_spec (H : ZFAxioms mem) (ee : Nat → V)
    (c_i e_i b_i s_i : Nat) (hE : IsUnivEnv H (ee e_i)) :
    Sat mem ee (fQFJustifiedF c_i e_i b_i s_i) ↔
      QFJustified H (ee s_i) (ee c_i) (ee e_i) (ee b_i) := by
  have h0 := fJustAtomF_spec H ee c_i e_i b_i 0 (fMem 1 0)
    (fun x y => mem x y) hE (fun _ _ => Iff.rfl)
  have h1 := fJustAtomF_spec H ee c_i e_i b_i 1 (fEq 1 0)
    (fun x y => x = y) hE (fun _ _ => Iff.rfl)
  have h2 := fJustBotF_spec H ee c_i b_i
  have h3 := fJustBinF_spec H ee c_i e_i b_i s_i 3 (fImp (fNumF 1 1) (fNumF 0 1))
    (fun x y => x = natV H 1 → y = natV H 1)
    (fun ee' _ => ⟨fun h hx => (fNumF_spec H 1 0 ee').mp
        (h ((fNumF_spec H 1 1 ee').mpr hx)),
      fun h hx => (fNumF_spec H 1 0 ee').mpr
        (h ((fNumF_spec H 1 1 ee').mp hx))⟩)
  have h4 := fJustBinF_spec H ee c_i e_i b_i s_i 4 (fAnd (fNumF 1 1) (fNumF 0 1))
    (fun x y => x = natV H 1 ∧ y = natV H 1)
    (fun ee' _ => ⟨fun h => ⟨(fNumF_spec H 1 1 ee').mp h.1,
        (fNumF_spec H 1 0 ee').mp h.2⟩,
      fun h => ⟨(fNumF_spec H 1 1 ee').mpr h.1,
        (fNumF_spec H 1 0 ee').mpr h.2⟩⟩)
  have h5 := fJustBinF_spec H ee c_i e_i b_i s_i 5 (fOr (fNumF 1 1) (fNumF 0 1))
    (fun x y => x = natV H 1 ∨ y = natV H 1)
    (fun ee' _ => ⟨fun h => h.imp (fNumF_spec H 1 1 ee').mp
        (fNumF_spec H 1 0 ee').mp,
      fun h => h.imp (fNumF_spec H 1 1 ee').mpr (fNumF_spec H 1 0 ee').mpr⟩)
  unfold QFJustified
  constructor
  · rintro (h | h | h | h | h | h)
    · exact Or.inl (h0.mp h)
    · exact Or.inr (Or.inl (h1.mp h))
    · exact Or.inr (Or.inr (Or.inl (h2.mp h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (h3.mp h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h4.mp h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h5.mp h)))))
  · rintro (h | h | h | h | h | h)
    · exact Or.inl (h0.mpr h)
    · exact Or.inr (Or.inl (h1.mpr h))
    · exact Or.inr (Or.inr (Or.inl (h2.mpr h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (h3.mpr h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h4.mpr h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h5.mpr h)))))

/-! ### Monotonicity and two-valuedness -/

/-- **The step relation is monotone in the certificate.**  Every occurrence of
the certificate in the six clauses is a positive membership assertion. -/
theorem qfJustified_mono (H : ZFAxioms mem) {S S' c e b : V}
    (hsub : ∀ x, mem x S → mem x S') (h : QFJustified H S c e b) :
    QFJustified H S' c e b := by
  unfold QFJustified at h ⊢
  rcases h with h | h | h | ⟨c1, c2, b1, b2, hc, k1, k2, hb⟩ |
    ⟨c1, c2, b1, b2, hc, k1, k2, hb⟩ | ⟨c1, c2, b1, b2, hc, k1, k2, hb⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨c1, c2, b1, b2, hc, hsub _ k1, hsub _ k2, hb⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨c1, c2, b1, b2, hc, hsub _ k1, hsub _ k2, hb⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨c1, c2, b1, b2, hc, hsub _ k1, hsub _ k2, hb⟩))))

/-- **A justified bit is `0` or `1`.**  Every clause fixes the bit either
literally or as a `vbit`. -/
theorem qfJustified_bit (H : ZFAxioms mem) {S c e b : V}
    (h : QFJustified H S c e b) : b = natV H 0 ∨ b = natV H 1 := by
  unfold QFJustified at h
  rcases h with ⟨_, _, _, _, _, hb⟩ | ⟨_, _, _, _, _, hb⟩ | ⟨_, hb⟩ |
    ⟨_, _, _, _, _, _, _, hb⟩ | ⟨_, _, _, _, _, _, _, hb⟩ |
    ⟨_, _, _, _, _, _, _, hb⟩
  · rw [hb]; exact vbit_zero_or_one H _
  · rw [hb]; exact vbit_zero_or_one H _
  · exact Or.inl hb
  · rw [hb]; exact vbit_zero_or_one H _
  · rw [hb]; exact vbit_zero_or_one H _
  · rw [hb]; exact vbit_zero_or_one H _

/-! ### Inverting the step at a known tag

Codes carrying different tags are different sets, so at a code of known shape
exactly one of the six clauses can apply.  Each lemma discards the other five
by `formCode_tag_ne`. -/

theorem qfJustified_memAtom (H : ZFAxioms mem) {S e b i j : V}
    (h : QFJustified H S (kpair H (natV H 0) (kpair H i j)) e b) :
    b = vbit H (mem (applyV H e i) (applyV H e j)) := by
  unfold QFJustified at h
  rcases h with ⟨i', j', _, _, hc, hb⟩ | ⟨_, _, _, _, hc, _⟩ | ⟨hc, _⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩ | ⟨_, _, _, _, hc, _, _, _⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩
  · obtain ⟨-, hp⟩ := kpair_inj H _ _ _ _ hc
    obtain ⟨hi, hj⟩ := kpair_inj H _ _ _ _ hp
    rw [hb, hi, hj]
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)

theorem qfJustified_eqAtom (H : ZFAxioms mem) {S e b i j : V}
    (h : QFJustified H S (kpair H (natV H 1) (kpair H i j)) e b) :
    b = vbit H (applyV H e i = applyV H e j) := by
  unfold QFJustified at h
  rcases h with ⟨_, _, _, _, hc, _⟩ | ⟨i', j', _, _, hc, hb⟩ | ⟨hc, _⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩ | ⟨_, _, _, _, hc, _, _, _⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · obtain ⟨-, hp⟩ := kpair_inj H _ _ _ _ hc
    obtain ⟨hi, hj⟩ := kpair_inj H _ _ _ _ hp
    rw [hb, hi, hj]
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)

theorem qfJustified_bot (H : ZFAxioms mem) {S e b : V}
    (h : QFJustified H S (kpair H (natV H 2) (vempty H)) e b) :
    b = natV H 0 := by
  unfold QFJustified at h
  rcases h with ⟨_, _, _, _, hc, _⟩ | ⟨_, _, _, _, hc, _⟩ | ⟨hc, hb⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩ | ⟨_, _, _, _, hc, _, _, _⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact hb
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)

theorem qfJustified_imp (H : ZFAxioms mem) {S e b c1 c2 : V}
    (h : QFJustified H S (kpair H (natV H 3) (kpair H c1 c2)) e b) :
    ∃ b1 b2, mem (satTriple H c1 e b1) S ∧ mem (satTriple H c2 e b2) S ∧
      b = vbit H (b1 = natV H 1 → b2 = natV H 1) := by
  unfold QFJustified at h
  rcases h with ⟨_, _, _, _, hc, _⟩ | ⟨_, _, _, _, hc, _⟩ | ⟨hc, _⟩ |
    ⟨d1, d2, b1, b2, hc, k1, k2, hb⟩ | ⟨_, _, _, _, hc, _, _, _⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · obtain ⟨-, hp⟩ := kpair_inj H _ _ _ _ hc
    obtain ⟨h1, h2⟩ := kpair_inj H _ _ _ _ hp
    refine ⟨b1, b2, ?_, ?_, hb⟩
    · rw [h1]; exact k1
    · rw [h2]; exact k2
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)

theorem qfJustified_and (H : ZFAxioms mem) {S e b c1 c2 : V}
    (h : QFJustified H S (kpair H (natV H 4) (kpair H c1 c2)) e b) :
    ∃ b1 b2, mem (satTriple H c1 e b1) S ∧ mem (satTriple H c2 e b2) S ∧
      b = vbit H (b1 = natV H 1 ∧ b2 = natV H 1) := by
  unfold QFJustified at h
  rcases h with ⟨_, _, _, _, hc, _⟩ | ⟨_, _, _, _, hc, _⟩ | ⟨hc, _⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩ | ⟨d1, d2, b1, b2, hc, k1, k2, hb⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · obtain ⟨-, hp⟩ := kpair_inj H _ _ _ _ hc
    obtain ⟨h1, h2⟩ := kpair_inj H _ _ _ _ hp
    refine ⟨b1, b2, ?_, ?_, hb⟩
    · rw [h1]; exact k1
    · rw [h2]; exact k2
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)

theorem qfJustified_or (H : ZFAxioms mem) {S e b c1 c2 : V}
    (h : QFJustified H S (kpair H (natV H 5) (kpair H c1 c2)) e b) :
    ∃ b1 b2, mem (satTriple H c1 e b1) S ∧ mem (satTriple H c2 e b2) S ∧
      b = vbit H (b1 = natV H 1 ∨ b2 = natV H 1) := by
  unfold QFJustified at h
  rcases h with ⟨_, _, _, _, hc, _⟩ | ⟨_, _, _, _, hc, _⟩ | ⟨hc, _⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩ | ⟨_, _, _, _, hc, _, _, _⟩ |
    ⟨d1, d2, b1, b2, hc, k1, k2, hb⟩
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · obtain ⟨-, hp⟩ := kpair_inj H _ _ _ _ hc
    obtain ⟨h1, h2⟩ := kpair_inj H _ _ _ _ hp
    refine ⟨b1, b2, ?_, ?_, hb⟩
    · rw [h1]; exact k1
    · rw [h2]; exact k2

/-! ## Certificates

A set is **step-closed** when every triple it records is locally justified by
the set itself, and records only genuine environments.  The environment clause
is not decoration: without it the object-language reading of `applyV` in the
atomic clauses is unavailable, so `fQFSatClosedF` could not have an
unconditional satisfaction spec.

A **certificate** for `⟨c, e, b⟩` is a step-closed set containing that
triple. -/

/-- Every triple of `S` is justified by `S`, over genuine environments. -/
def QFSatClosed (H : ZFAxioms mem) (S : V) : Prop :=
  ∀ c e b, mem (satTriple H c e b) S → (IsUnivEnv H e ∧ QFJustified H S c e b)

/-- "slot `s_i` is step-closed".

| de Bruijn slot | contents              |
| -------------- | --------------------- |
| `0`            | the bit `b`           |
| `1`            | the environment `e`   |
| `2`            | the code `c`          |
| `m+3`          | the caller's slot `m` |
-/
def fQFSatClosedF (s_i : Nat) : Form :=
  fAll (fAll (fAll (fImp (fTripleMemF 2 1 0 (s_i+3))
    (fAnd (fUnivEnvF 1) (fQFJustifiedF 2 1 0 (s_i+3))))))

theorem fQFSatClosedF_spec (H : ZFAxioms mem) (ee : Nat → V) (s_i : Nat) :
    Sat mem ee (fQFSatClosedF s_i) ↔ QFSatClosed H (ee s_i) := by
  unfold QFSatClosed
  constructor
  · intro h c e b hmem
    obtain ⟨h1, h2⟩ := h c e b
      ((fTripleMemF_spec H (scons b (scons e (scons c ee)))
        2 1 0 (s_i+3)).mpr hmem)
    have henv : IsUnivEnv H e :=
      (fUnivEnvF_spec H (scons b (scons e (scons c ee))) 1).mp h1
    exact ⟨henv, (fQFJustifiedF_spec H (scons b (scons e (scons c ee)))
      2 1 0 (s_i+3) henv).mp h2⟩
  · intro h c e b hsat
    obtain ⟨henv, hj⟩ := h c e b
      ((fTripleMemF_spec H (scons b (scons e (scons c ee)))
        2 1 0 (s_i+3)).mp hsat)
    exact ⟨(fUnivEnvF_spec H (scons b (scons e (scons c ee))) 1).mpr henv,
      (fQFJustifiedF_spec H (scons b (scons e (scons c ee)))
        2 1 0 (s_i+3) henv).mpr hj⟩

/-- `S` is a **certificate** assigning the bit `b` to the code `c` under the
environment `e`. -/
structure QFCertifies (H : ZFAxioms mem) (S c e b : V) : Prop where
  /-- Every triple of the certificate is justified by the certificate. -/
  closed : QFSatClosed H S
  /-- The triple in question is recorded. -/
  holds : mem (satTriple H c e b) S

theorem QFCertifies.justified (H : ZFAxioms mem) {S c e b : V}
    (hc : QFCertifies H S c e b) : QFJustified H S c e b :=
  (hc.closed c e b hc.holds).2

theorem QFCertifies.envOn (H : ZFAxioms mem) {S c e b : V}
    (hc : QFCertifies H S c e b) : IsUnivEnv H e :=
  (hc.closed c e b hc.holds).1

/-! ### Building step-closed sets

The empty set is step-closed vacuously, monotonicity makes a union of two
step-closed sets step-closed, and a single justified triple may always be
adjoined.  Those three operations are all the induction below needs: unlike the
set-structure case, no clause quantifies over a carrier, so no certificate has
to be produced uniformly in a parameter. -/

/-- The empty set is a certificate for nothing. -/
theorem qfSatClosed_empty (H : ZFAxioms mem) : QFSatClosed H (vempty H) :=
  fun _ _ _ h => absurd h (vempty_spec H _)

/-- The union of two step-closed sets is step-closed. -/
theorem qfSatClosed_cup (H : ZFAxioms mem) {S1 S2 : V} (h1 : QFSatClosed H S1)
    (h2 : QFSatClosed H S2) : QFSatClosed H (vcup H S1 S2) := by
  have hsub1 : ∀ x, mem x S1 → mem x (vcup H S1 S2) :=
    fun x hx => (vcup_spec H S1 S2 x).mpr (Or.inl hx)
  have hsub2 : ∀ x, mem x S2 → mem x (vcup H S1 S2) :=
    fun x hx => (vcup_spec H S1 S2 x).mpr (Or.inr hx)
  intro c e b hmem
  rcases (vcup_spec H S1 S2 _).mp hmem with h | h
  · exact ⟨(h1 c e b h).1, qfJustified_mono H hsub1 (h1 c e b h).2⟩
  · exact ⟨(h2 c e b h).1, qfJustified_mono H hsub2 (h2 c e b h).2⟩

/-- Adjoining a single justified triple keeps a set step-closed. -/
theorem qfSatClosed_insert (H : ZFAxioms mem) {S c e b : V}
    (hS : QFSatClosed H S) (he : IsUnivEnv H e)
    (hstep : QFJustified H S c e b) :
    QFSatClosed H (vcup H S (vsingle H (satTriple H c e b))) := by
  have hsub : ∀ x, mem x S → mem x (vcup H S (vsingle H (satTriple H c e b))) :=
    fun x hx => (vcup_spec H _ _ x).mpr (Or.inl hx)
  intro c0 e0 b0 hmem
  rcases (vcup_spec H S (vsingle H (satTriple H c e b)) _).mp hmem with h | h
  · exact ⟨(hS c0 e0 b0 h).1, qfJustified_mono H hsub (hS c0 e0 b0 h).2⟩
  · obtain ⟨q1, q2, q3⟩ :=
      satTriple_inj H ((vsingle_spec H (satTriple H c e b) _).mp h)
    rw [q1, q2, q3]
    exact ⟨he, qfJustified_mono H hsub hstep⟩

/-- A justified triple over a step-closed set is certified by adjoining it.
This is the only way certificates are built below. -/
theorem qfCertifies_of_step (H : ZFAxioms mem) {S c e b : V}
    (hS : QFSatClosed H S) (he : IsUnivEnv H e)
    (hstep : QFJustified H S c e b) :
    QFCertifies H (vcup H S (vsingle H (satTriple H c e b))) c e b :=
  ⟨qfSatClosed_insert H hS he hstep,
    (vcup_spec H _ _ _).mpr (Or.inr ((vsingle_spec H _ _).mpr rfl))⟩

/-! ## Single-valuedness

Two certificates never disagree.  The induction is over quantifier-free codes,
so the property is a `Form` together with an environment; the environment slots
carry no parameters, since neither a carrier nor a relation appears. -/

/-- The parameter-free environment used by both induction properties below. -/
noncomputable def envQFBase (H : ZFAxioms mem) : Nat → V := fun _ => vempty H

/-- The bit a certificate assigns to `c` does not depend on the certificate. -/
def QFBitUnique (H : ZFAxioms mem) (c : V) : Prop :=
  ∀ e b b' S S', QFCertifies H S c e b → QFCertifies H S' c e b' → b = b'

/-- `QFBitUnique` as a `Form`, with the code in slot `0` of the caller.

| de Bruijn slot | contents                    |
| -------------- | --------------------------- |
| `0`            | the second certificate `S'` |
| `1`            | the first certificate `S`   |
| `2`            | the second bit `b'`         |
| `3`            | the first bit `b`           |
| `4`            | the environment `e`         |
| `5`            | the code `c`                |
-/
def fQFBitUniqueF : Form :=
  fAll (fAll (fAll (fAll (fAll
    (fImp (fAnd (fQFSatClosedF 1) (fTripleMemF 5 4 3 1))
      (fImp (fAnd (fQFSatClosedF 0) (fTripleMemF 5 4 2 0)) (fEq 3 2)))))))

theorem fQFBitUniqueF_spec (H : ZFAxioms mem) (y : V) :
    Sat mem (scons y (envQFBase H)) fQFBitUniqueF ↔ QFBitUnique H y := by
  unfold QFBitUnique
  constructor
  · intro h e b b' S S' hc hc'
    exact h e b b' S S'
      ⟨(fQFSatClosedF_spec H _ 1).mpr hc.closed,
       (fTripleMemF_spec H _ 5 4 3 1).mpr hc.holds⟩
      ⟨(fQFSatClosedF_spec H _ 0).mpr hc'.closed,
       (fTripleMemF_spec H _ 5 4 2 0).mpr hc'.holds⟩
  · intro h e b b' S S' hc hc'
    obtain ⟨h1, h2⟩ := hc
    obtain ⟨h1', h2'⟩ := hc'
    exact h e b b' S S'
      ⟨(fQFSatClosedF_spec H _ 1).mp h1,
       (fTripleMemF_spec H _ 5 4 3 1).mp h2⟩
      ⟨(fQFSatClosedF_spec H _ 0).mp h1',
       (fTripleMemF_spec H _ 5 4 2 0).mp h2'⟩

/-- **Certificates are single-valued.**  For every quantifier-free code —
including the nonstandard ones, which are not quotations of any external
formula — any two certificates assign the same bit under the same
environment. -/
theorem qfCertificate_bit_unique (H : ZFAxioms mem) :
    ∀ c, IsQFCodeSem H c → QFBitUnique H c := by
  refine isQFCodeSem_ind H (QFBitUnique H) fQFBitUniqueF (envQFBase H)
    (fun y => (fQFBitUniqueF_spec H y).symm) ?_ ?_ ?_ ?_ ?_ ?_
  · intro _ _ _ _ e b b' S S' hc hc'
    rw [qfJustified_memAtom H (QFCertifies.justified H hc),
        qfJustified_memAtom H (QFCertifies.justified H hc')]
  · intro _ _ _ _ e b b' S S' hc hc'
    rw [qfJustified_eqAtom H (QFCertifies.justified H hc),
        qfJustified_eqAtom H (QFCertifies.justified H hc')]
  · intro e b b' S S' hc hc'
    rw [qfJustified_bot H (QFCertifies.justified H hc),
        qfJustified_bot H (QFCertifies.justified H hc')]
  · intro x y hx hy e b b' S S' hc hc'
    obtain ⟨b1, b2, k1, k2, hb⟩ := qfJustified_imp H (QFCertifies.justified H hc)
    obtain ⟨b1', b2', k1', k2', hb'⟩ :=
      qfJustified_imp H (QFCertifies.justified H hc')
    have e1 : b1 = b1' := hx e b1 b1' S S' ⟨hc.closed, k1⟩ ⟨hc'.closed, k1'⟩
    have e2 : b2 = b2' := hy e b2 b2' S S' ⟨hc.closed, k2⟩ ⟨hc'.closed, k2'⟩
    rw [hb, hb', e1, e2]
  · intro x y hx hy e b b' S S' hc hc'
    obtain ⟨b1, b2, k1, k2, hb⟩ := qfJustified_and H (QFCertifies.justified H hc)
    obtain ⟨b1', b2', k1', k2', hb'⟩ :=
      qfJustified_and H (QFCertifies.justified H hc')
    have e1 : b1 = b1' := hx e b1 b1' S S' ⟨hc.closed, k1⟩ ⟨hc'.closed, k1'⟩
    have e2 : b2 = b2' := hy e b2 b2' S S' ⟨hc.closed, k2⟩ ⟨hc'.closed, k2'⟩
    rw [hb, hb', e1, e2]
  · intro x y hx hy e b b' S S' hc hc'
    obtain ⟨b1, b2, k1, k2, hb⟩ := qfJustified_or H (QFCertifies.justified H hc)
    obtain ⟨b1', b2', k1', k2', hb'⟩ :=
      qfJustified_or H (QFCertifies.justified H hc')
    have e1 : b1 = b1' := hx e b1 b1' S S' ⟨hc.closed, k1⟩ ⟨hc'.closed, k1'⟩
    have e2 : b2 = b2' := hy e b2 b2' S S' ⟨hc.closed, k2⟩ ⟨hc'.closed, k2'⟩
    rw [hb, hb', e1, e2]

/-- **Functionality**, in the form later modules consume: a code and an
environment determine the bit, whichever certificates produce it. -/
theorem qfCertificate_functional (H : ZFAxioms mem) {c : V}
    (hcode : IsQFCodeSem H c) {e b b' S S' : V}
    (h : QFCertifies H S c e b) (h' : QFCertifies H S' c e b') : b = b' :=
  qfCertificate_bit_unique H c hcode e b b' S S' h h'

/-! ## Totality

The plain existential form suffices.  For satisfaction in a set structure the
induction hypothesis had to be uniform over a set of environments, because the
quantifier clauses need a certificate for each carrier element and a definable
choice of certificate is unavailable; here every clause mentions the
environment it started with, so a compound certificate is a union of two
certificates plus one new triple. -/

/-- Every environment admits a certified bit for the code. -/
def QFTotal (H : ZFAxioms mem) (c : V) : Prop :=
  ∀ e, IsUnivEnv H e → ∃ S b, QFCertifies H S c e b

/-- `QFTotal` as a `Form`, with the code in slot `0` of the caller.

| de Bruijn slot | contents                               |
| -------------- | -------------------------------------- |
| `0`            | the environment `e`, then `S`, then `b`|
| `1`            | the code, then `e`, then `S`           |
| `2`            | under two binders: `e`                 |
| `3`            | under three binders: the code          |
-/
def fQFTotalF : Form :=
  fAll (fImp (fUnivEnvF 0)
    (fEx (fEx (fAnd (fQFSatClosedF 1) (fTripleMemF 3 2 0 1)))))

theorem fQFTotalF_spec (H : ZFAxioms mem) (y : V) :
    Sat mem (scons y (envQFBase H)) fQFTotalF ↔ QFTotal H y := by
  unfold QFTotal
  constructor
  · intro h e he
    obtain ⟨S, b, hcl, hmem⟩ :=
      h e ((fUnivEnvF_spec H (scons e (scons y (envQFBase H))) 0).mpr he)
    exact ⟨S, b, (fQFSatClosedF_spec H _ 1).mp hcl,
      (fTripleMemF_spec H _ 3 2 0 1).mp hmem⟩
  · intro h e hfn
    obtain ⟨S, b, hcl, hmem⟩ :=
      h e ((fUnivEnvF_spec H (scons e (scons y (envQFBase H))) 0).mp hfn)
    exact ⟨S, b, (fQFSatClosedF_spec H _ 1).mpr hcl,
      (fTripleMemF_spec H _ 3 2 0 1).mpr hmem⟩

/-- **Certificates are total.**  Every quantifier-free code and every
environment carry a certified bit. -/
theorem qfCertificate_total (H : ZFAxioms mem) :
    ∀ c, IsQFCodeSem H c → ∀ e, IsUnivEnv H e → ∃ S b, QFCertifies H S c e b := by
  refine isQFCodeSem_ind H (QFTotal H) fQFTotalF (envQFBase H)
    (fun y => (fQFTotalF_spec H y).symm) ?_ ?_ ?_ ?_ ?_ ?_
  · intro i j hi hj e he
    refine ⟨_, vbit H (mem (applyV H e i) (applyV H e j)),
      qfCertifies_of_step H (qfSatClosed_empty H) he ?_⟩
    unfold QFJustified
    exact Or.inl ⟨i, j, hi, hj, rfl, rfl⟩
  · intro i j hi hj e he
    refine ⟨_, vbit H (applyV H e i = applyV H e j),
      qfCertifies_of_step H (qfSatClosed_empty H) he ?_⟩
    unfold QFJustified
    exact Or.inr (Or.inl ⟨i, j, hi, hj, rfl, rfl⟩)
  · intro e he
    refine ⟨_, natV H 0, qfCertifies_of_step H (qfSatClosed_empty H) he ?_⟩
    unfold QFJustified
    exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · intro a b iha ihb e he
    obtain ⟨S1, b1, hc1⟩ := iha e he
    obtain ⟨S2, b2, hc2⟩ := ihb e he
    refine ⟨_, vbit H (b1 = natV H 1 → b2 = natV H 1),
      qfCertifies_of_step H (qfSatClosed_cup H hc1.closed hc2.closed) he ?_⟩
    unfold QFJustified
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, b1, b2, rfl,
      (vcup_spec H S1 S2 _).mpr (Or.inl hc1.holds),
      (vcup_spec H S1 S2 _).mpr (Or.inr hc2.holds), rfl⟩)))
  · intro a b iha ihb e he
    obtain ⟨S1, b1, hc1⟩ := iha e he
    obtain ⟨S2, b2, hc2⟩ := ihb e he
    refine ⟨_, vbit H (b1 = natV H 1 ∧ b2 = natV H 1),
      qfCertifies_of_step H (qfSatClosed_cup H hc1.closed hc2.closed) he ?_⟩
    unfold QFJustified
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, b1, b2, rfl,
      (vcup_spec H S1 S2 _).mpr (Or.inl hc1.holds),
      (vcup_spec H S1 S2 _).mpr (Or.inr hc2.holds), rfl⟩))))
  · intro a b iha ihb e he
    obtain ⟨S1, b1, hc1⟩ := iha e he
    obtain ⟨S2, b2, hc2⟩ := ihb e he
    refine ⟨_, vbit H (b1 = natV H 1 ∨ b2 = natV H 1),
      qfCertifies_of_step H (qfSatClosed_cup H hc1.closed hc2.closed) he ?_⟩
    unfold QFJustified
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, b, b1, b2, rfl,
      (vcup_spec H S1 S2 _).mpr (Or.inl hc1.holds),
      (vcup_spec H S1 S2 _).mpr (Or.inr hc2.holds), rfl⟩))))

/-! ## Quantifier-free truth over the universe

`QFTrue H c e` says that some certificate assigns the bit one.  Totality and
single-valuedness together make it well behaved: `qfCertifies_bit` states that
the bit assigned by *any* certificate is exactly `vbit` of `QFTrue`, which is
the form in which the Tarski clauses are read off the inversion lemmas. -/

/-- **Quantifier-free truth over the universe.** -/
def QFTrue (H : ZFAxioms mem) (c e : V) : Prop :=
  ∃ S, QFCertifies H S c e (natV H 1)

/-- Truth is read off any certificate. -/
theorem qfTrue_iff_bit_eq_one (H : ZFAxioms mem) {S c e b : V}
    (hcode : IsQFCodeSem H c) (hcert : QFCertifies H S c e b) :
    QFTrue H c e ↔ b = natV H 1 := by
  constructor
  · rintro ⟨S', hc'⟩
    exact qfCertificate_functional H hcode hcert hc'
  · intro hb
    exact ⟨S, hb ▸ hcert⟩

/-- **The bit of any certificate is the truth bit of `QFTrue`.**  This is the
statement that makes `QFTrue` a truth predicate rather than a name for an
existential. -/
theorem qfCertifies_bit (H : ZFAxioms mem) {S c e b : V}
    (hcode : IsQFCodeSem H c) (hcert : QFCertifies H S c e b) :
    b = vbit H (QFTrue H c e) := by
  by_cases htrue : QFTrue H c e
  · rw [vbit_pos H htrue]
    exact (qfTrue_iff_bit_eq_one H hcode hcert).mp htrue
  · rw [vbit_neg H htrue]
    rcases qfJustified_bit H (QFCertifies.justified H hcert) with h | h
    · exact h
    · exact absurd ((qfTrue_iff_bit_eq_one H hcode hcert).mpr h) htrue

/-- A certificate carrying exactly the truth bit exists at every
quantifier-free code and every environment. -/
theorem exists_qfCertifies (H : ZFAxioms mem) {c : V} (hcode : IsQFCodeSem H c)
    {e : V} (he : IsUnivEnv H e) :
    ∃ S, QFCertifies H S c e (vbit H (QFTrue H c e)) := by
  obtain ⟨S, b, hcert⟩ := qfCertificate_total H c hcode e he
  exact ⟨S, qfCertifies_bit H hcode hcert ▸ hcert⟩

/-! ### The Tarski clauses

The atoms are interpreted by the model's own membership and equality, so these
are genuinely clauses about the universe and not about a set structure. -/

/-- Atomic membership: the model's own `mem`, read at the two indices. -/
theorem qfTrue_memAtom (H : ZFAxioms mem) {e i j : V}
    (hi : mem i (omegaV H)) (hj : mem j (omegaV H)) (he : IsUnivEnv H e) :
    QFTrue H (kpair H (natV H 0) (kpair H i j)) e ↔
      mem (applyV H e i) (applyV H e j) := by
  obtain ⟨S, b, hcert⟩ :=
    qfCertificate_total H _ (isQFCodeSem_memAtom H hi hj) e he
  rw [qfTrue_iff_bit_eq_one H (isQFCodeSem_memAtom H hi hj) hcert,
      qfJustified_memAtom H (QFCertifies.justified H hcert)]
  exact vbit_eq_one H _

/-- Atomic equality: the model's own equality, read at the two indices. -/
theorem qfTrue_eqAtom (H : ZFAxioms mem) {e i j : V}
    (hi : mem i (omegaV H)) (hj : mem j (omegaV H)) (he : IsUnivEnv H e) :
    QFTrue H (kpair H (natV H 1) (kpair H i j)) e ↔
      applyV H e i = applyV H e j := by
  obtain ⟨S, b, hcert⟩ :=
    qfCertificate_total H _ (isQFCodeSem_eqAtom H hi hj) e he
  rw [qfTrue_iff_bit_eq_one H (isQFCodeSem_eqAtom H hi hj) hcert,
      qfJustified_eqAtom H (QFCertifies.justified H hcert)]
  exact vbit_eq_one H _

/-- Falsity is never true.  No hypothesis is needed: the falsity clause fixes
the bit outright. -/
theorem qfTrue_bot (H : ZFAxioms mem) {e : V} :
    ¬ QFTrue H (kpair H (natV H 2) (vempty H)) e := by
  rintro ⟨S, hcert⟩
  exact natV_ne H (by decide) (qfJustified_bot H (QFCertifies.justified H hcert))

/-- Implication. -/
theorem qfTrue_imp (H : ZFAxioms mem) {c1 c2 e : V} (h1 : IsQFCodeSem H c1)
    (h2 : IsQFCodeSem H c2) (he : IsUnivEnv H e) :
    QFTrue H (kpair H (natV H 3) (kpair H c1 c2)) e ↔
      (QFTrue H c1 e → QFTrue H c2 e) := by
  obtain ⟨S, b, hcert⟩ :=
    qfCertificate_total H _ (isQFCodeSem_imp H h1 h2) e he
  obtain ⟨b1, b2, k1, k2, hb⟩ := qfJustified_imp H (QFCertifies.justified H hcert)
  have e1 : b1 = vbit H (QFTrue H c1 e) := qfCertifies_bit H h1 ⟨hcert.closed, k1⟩
  have e2 : b2 = vbit H (QFTrue H c2 e) := qfCertifies_bit H h2 ⟨hcert.closed, k2⟩
  have hcong : (vbit H (QFTrue H c1 e) = natV H 1 →
      vbit H (QFTrue H c2 e) = natV H 1) ↔
      (QFTrue H c1 e → QFTrue H c2 e) := by
    rw [vbit_eq_one H (QFTrue H c1 e), vbit_eq_one H (QFTrue H c2 e)]
  rw [qfTrue_iff_bit_eq_one H (isQFCodeSem_imp H h1 h2) hcert, hb, e1, e2,
      vbit_congr H hcong]
  exact vbit_eq_one H _

/-- Conjunction. -/
theorem qfTrue_and (H : ZFAxioms mem) {c1 c2 e : V} (h1 : IsQFCodeSem H c1)
    (h2 : IsQFCodeSem H c2) (he : IsUnivEnv H e) :
    QFTrue H (kpair H (natV H 4) (kpair H c1 c2)) e ↔
      (QFTrue H c1 e ∧ QFTrue H c2 e) := by
  obtain ⟨S, b, hcert⟩ :=
    qfCertificate_total H _ (isQFCodeSem_and H h1 h2) e he
  obtain ⟨b1, b2, k1, k2, hb⟩ := qfJustified_and H (QFCertifies.justified H hcert)
  have e1 : b1 = vbit H (QFTrue H c1 e) := qfCertifies_bit H h1 ⟨hcert.closed, k1⟩
  have e2 : b2 = vbit H (QFTrue H c2 e) := qfCertifies_bit H h2 ⟨hcert.closed, k2⟩
  have hcong : (vbit H (QFTrue H c1 e) = natV H 1 ∧
      vbit H (QFTrue H c2 e) = natV H 1) ↔
      (QFTrue H c1 e ∧ QFTrue H c2 e) := by
    rw [vbit_eq_one H (QFTrue H c1 e), vbit_eq_one H (QFTrue H c2 e)]
  rw [qfTrue_iff_bit_eq_one H (isQFCodeSem_and H h1 h2) hcert, hb, e1, e2,
      vbit_congr H hcong]
  exact vbit_eq_one H _

/-- Disjunction. -/
theorem qfTrue_or (H : ZFAxioms mem) {c1 c2 e : V} (h1 : IsQFCodeSem H c1)
    (h2 : IsQFCodeSem H c2) (he : IsUnivEnv H e) :
    QFTrue H (kpair H (natV H 5) (kpair H c1 c2)) e ↔
      (QFTrue H c1 e ∨ QFTrue H c2 e) := by
  obtain ⟨S, b, hcert⟩ :=
    qfCertificate_total H _ (isQFCodeSem_or H h1 h2) e he
  obtain ⟨b1, b2, k1, k2, hb⟩ := qfJustified_or H (QFCertifies.justified H hcert)
  have e1 : b1 = vbit H (QFTrue H c1 e) := qfCertifies_bit H h1 ⟨hcert.closed, k1⟩
  have e2 : b2 = vbit H (QFTrue H c2 e) := qfCertifies_bit H h2 ⟨hcert.closed, k2⟩
  have hcong : (vbit H (QFTrue H c1 e) = natV H 1 ∨
      vbit H (QFTrue H c2 e) = natV H 1) ↔
      (QFTrue H c1 e ∨ QFTrue H c2 e) := by
    rw [vbit_eq_one H (QFTrue H c1 e), vbit_eq_one H (QFTrue H c2 e)]
  rw [qfTrue_iff_bit_eq_one H (isQFCodeSem_or H h1 h2) hcert, hb, e1, e2,
      vbit_congr H hcong]
  exact vbit_eq_one H _

/-! ## Agreement with the metatheory on quotations

The external counterpart of the code domain, and the theorem that internal
truth of a quotation is external satisfaction at the valuation the environment
induces.  This is what will eventually let the truth of quantifier-free ZFC
axiom instances be established, since those instances are given externally. -/

/-- A metatheoretic formula with no quantifier at any node. -/
def IsQuantFree : Form → Prop
  | fMem _ _ => True
  | fEq _ _ => True
  | fBot => True
  | fImp a b => IsQuantFree a ∧ IsQuantFree b
  | fAnd a b => IsQuantFree a ∧ IsQuantFree b
  | fOr a b => IsQuantFree a ∧ IsQuantFree b
  | fAll _ => False
  | fEx _ => False

/-! The three compound clauses and the two quantifier clauses, named so that
the inductions below never depend on how the recursion is compiled. -/

theorem isQuantFree_imp_iff (a b : Form) :
    IsQuantFree (fImp a b) ↔ (IsQuantFree a ∧ IsQuantFree b) := Iff.rfl

theorem isQuantFree_and_iff (a b : Form) :
    IsQuantFree (fAnd a b) ↔ (IsQuantFree a ∧ IsQuantFree b) := Iff.rfl

theorem isQuantFree_or_iff (a b : Form) :
    IsQuantFree (fOr a b) ↔ (IsQuantFree a ∧ IsQuantFree b) := Iff.rfl

theorem not_isQuantFree_fAll (a : Form) : ¬ IsQuantFree (fAll a) := fun h => h

theorem not_isQuantFree_fEx (a : Form) : ¬ IsQuantFree (fEx a) := fun h => h

/-! The polarity ranks are written with `Nat.min` and `Nat.max`; these two
identities present them in the class form the arithmetic decision procedure
recognizes. -/

theorem natMin_eq_min (x y : Nat) : Nat.min x y = min x y := rfl

theorem natMax_eq_max (x y : Nat) : Nat.max x y = max x y := rfl

/-- The external notion agrees with rank zero as well, so the three
descriptions — no quantifier node, both polarity ranks zero, and
`QuantifierBounded 0` — coincide on metatheoretic formulas. -/
theorem sigmaRank_piRank_zero_of_isQuantFree :
    ∀ phi : Form, IsQuantFree phi → sigmaRank phi = 0 ∧ piRank phi = 0 := by
  intro phi
  induction phi with
  | fMem i j => intro _; exact ⟨rfl, rfl⟩
  | fEq i j => intro _; exact ⟨rfl, rfl⟩
  | fBot => intro _; exact ⟨rfl, rfl⟩
  | fImp a b iha ihb =>
      intro h
      obtain ⟨ha, hb⟩ := (isQuantFree_imp_iff a b).mp h
      obtain ⟨ha1, ha2⟩ := iha ha
      obtain ⟨hb1, hb2⟩ := ihb hb
      simp only [sigmaRank, piRank, ha1, ha2, hb1, hb2]
      decide
  | fAnd a b iha ihb =>
      intro h
      obtain ⟨ha, hb⟩ := (isQuantFree_and_iff a b).mp h
      obtain ⟨ha1, ha2⟩ := iha ha
      obtain ⟨hb1, hb2⟩ := ihb hb
      simp only [sigmaRank, piRank, ha1, ha2, hb1, hb2]
      decide
  | fOr a b iha ihb =>
      intro h
      obtain ⟨ha, hb⟩ := (isQuantFree_or_iff a b).mp h
      obtain ⟨ha1, ha2⟩ := iha ha
      obtain ⟨hb1, hb2⟩ := ihb hb
      simp only [sigmaRank, piRank, ha1, ha2, hb1, hb2]
      decide
  | fAll a _ => intro h; exact absurd h (not_isQuantFree_fAll a)
  | fEx a _ => intro h; exact absurd h (not_isQuantFree_fEx a)

/-- Conversely, complexity zero forces the absence of quantifiers: at a
quantifier node both polarity ranks are at least one, so their minimum is. -/
theorem isQuantFree_of_quantifierBounded_zero :
    ∀ phi : Form, QuantifierBounded 0 phi → IsQuantFree phi := by
  intro phi
  induction phi with
  | fMem i j => intro _; exact trivial
  | fEq i j => intro _; exact trivial
  | fBot => intro _; exact trivial
  | fImp a b iha ihb =>
      intro h
      simp only [QuantifierBounded, quantifierGroups, sigmaRank, piRank,
        natMin_eq_min, natMax_eq_max] at h
      refine (isQuantFree_imp_iff a b).mpr ⟨iha ?_, ihb ?_⟩ <;>
        · simp only [QuantifierBounded, quantifierGroups, natMin_eq_min]
          omega
  | fAnd a b iha ihb =>
      intro h
      simp only [QuantifierBounded, quantifierGroups, sigmaRank, piRank,
        natMin_eq_min, natMax_eq_max] at h
      refine (isQuantFree_and_iff a b).mpr ⟨iha ?_, ihb ?_⟩ <;>
        · simp only [QuantifierBounded, quantifierGroups, natMin_eq_min]
          omega
  | fOr a b iha ihb =>
      intro h
      simp only [QuantifierBounded, quantifierGroups, sigmaRank, piRank,
        natMin_eq_min, natMax_eq_max] at h
      refine (isQuantFree_or_iff a b).mpr ⟨iha ?_, ihb ?_⟩ <;>
        · simp only [QuantifierBounded, quantifierGroups, natMin_eq_min]
          omega
  | fAll a _ =>
      intro h
      exfalso
      simp only [QuantifierBounded, quantifierGroups, sigmaRank, piRank,
        natMin_eq_min, natMax_eq_max] at h
      omega
  | fEx a _ =>
      intro h
      exfalso
      simp only [QuantifierBounded, quantifierGroups, sigmaRank, piRank,
        natMin_eq_min, natMax_eq_max] at h
      omega

/-- The metatheoretic notion is exactly `QuantifierBounded 0`. -/
theorem isQuantFree_iff_quantifierBounded_zero (phi : Form) :
    IsQuantFree phi ↔ QuantifierBounded 0 phi := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := sigmaRank_piRank_zero_of_isQuantFree phi h
    simp only [QuantifierBounded, quantifierGroups, h1, h2]
    decide
  · exact isQuantFree_of_quantifierBounded_zero phi

/-- **Quotation soundness for the quantifier-free fragment**: the code of an
externally quantifier-free formula lies in the internal quantifier-free
domain.  As for the full code predicate the converse is false in nonstandard
models and is not attempted. -/
theorem formCode_isQFCodeSem (H : ZFAxioms mem) :
    ∀ phi : Form, IsQuantFree phi → IsQFCodeSem H (formCode H phi) := by
  intro phi
  induction phi with
  | fMem i j =>
      intro _
      exact isQFCodeSem_memAtom H (natV_mem_omega H i) (natV_mem_omega H j)
  | fEq i j =>
      intro _
      exact isQFCodeSem_eqAtom H (natV_mem_omega H i) (natV_mem_omega H j)
  | fBot => intro _; exact isQFCodeSem_bot H
  | fImp a b iha ihb =>
      intro h
      obtain ⟨ha, hb⟩ := (isQuantFree_imp_iff a b).mp h
      exact isQFCodeSem_imp H (iha ha) (ihb hb)
  | fAnd a b iha ihb =>
      intro h
      obtain ⟨ha, hb⟩ := (isQuantFree_and_iff a b).mp h
      exact isQFCodeSem_and H (iha ha) (ihb hb)
  | fOr a b iha ihb =>
      intro h
      obtain ⟨ha, hb⟩ := (isQuantFree_or_iff a b).mp h
      exact isQFCodeSem_or H (iha ha) (ihb hb)
  | fAll a _ => intro h; exact absurd h (not_isQuantFree_fAll a)
  | fEx a _ => intro h; exact absurd h (not_isQuantFree_fEx a)

/-- **Internal truth of a quotation is external satisfaction.**  The valuation
is the one the internal environment induces on the numerals; that is the
available direction, since an arbitrary metatheoretic valuation need not be the
trace of any set.

The proof is external induction on `phi`, each step being one Tarski clause
together with the corresponding coding equation. -/
theorem qfTrue_formCode_iff (H : ZFAxioms mem) {E : V} (hE : IsUnivEnv H E)
    (v : Nat → V) (hv : ∀ k, v k = applyV H E (natV H k)) :
    ∀ phi : Form, IsQuantFree phi →
      (QFTrue H (formCode H phi) E ↔ Sat mem v phi) := by
  intro phi
  induction phi with
  | fMem i j =>
      intro _
      show QFTrue H (kpair H (natV H 0) (kpair H (natV H i) (natV H j))) E ↔
        mem (v i) (v j)
      rw [qfTrue_memAtom H (natV_mem_omega H i) (natV_mem_omega H j) hE,
          hv i, hv j]
  | fEq i j =>
      intro _
      show QFTrue H (kpair H (natV H 1) (kpair H (natV H i) (natV H j))) E ↔
        v i = v j
      rw [qfTrue_eqAtom H (natV_mem_omega H i) (natV_mem_omega H j) hE,
          hv i, hv j]
  | fBot =>
      intro _
      show QFTrue H (kpair H (natV H 2) (vempty H)) E ↔ False
      exact ⟨fun h => absurd h (qfTrue_bot H), fun h => h.elim⟩
  | fImp a b iha ihb =>
      intro h
      obtain ⟨ha, hb⟩ := (isQuantFree_imp_iff a b).mp h
      show QFTrue H (kpair H (natV H 3)
        (kpair H (formCode H a) (formCode H b))) E ↔
          (Sat mem v a → Sat mem v b)
      rw [qfTrue_imp H (formCode_isQFCodeSem H a ha)
            (formCode_isQFCodeSem H b hb) hE, iha ha, ihb hb]
  | fAnd a b iha ihb =>
      intro h
      obtain ⟨ha, hb⟩ := (isQuantFree_and_iff a b).mp h
      show QFTrue H (kpair H (natV H 4)
        (kpair H (formCode H a) (formCode H b))) E ↔
          (Sat mem v a ∧ Sat mem v b)
      rw [qfTrue_and H (formCode_isQFCodeSem H a ha)
            (formCode_isQFCodeSem H b hb) hE, iha ha, ihb hb]
  | fOr a b iha ihb =>
      intro h
      obtain ⟨ha, hb⟩ := (isQuantFree_or_iff a b).mp h
      show QFTrue H (kpair H (natV H 5)
        (kpair H (formCode H a) (formCode H b))) E ↔
          (Sat mem v a ∨ Sat mem v b)
      rw [qfTrue_or H (formCode_isQFCodeSem H a ha)
            (formCode_isQFCodeSem H b hb) hE, iha ha, ihb hb]
  | fAll a _ => intro h; exact absurd h (not_isQuantFree_fAll a)
  | fEx a _ => intro h; exact absurd h (not_isQuantFree_fEx a)

/-- The agreement theorem in the shape a caller supplies: the valuation is
named by the environment, so no side condition on `v` remains. -/
theorem qfTrue_formCode_iff_apply (H : ZFAxioms mem) {E : V}
    (hE : IsUnivEnv H E) (phi : Form) (hphi : IsQuantFree phi) :
    QFTrue H (formCode H phi) E ↔
      Sat mem (fun k => applyV H E (natV H k)) phi :=
  qfTrue_formCode_iff H hE (fun k => applyV H E (natV H k)) (fun _ => rfl)
    phi hphi

end UniverseTruthZero

end BoundedZFCConsistency
end LeanProofs
