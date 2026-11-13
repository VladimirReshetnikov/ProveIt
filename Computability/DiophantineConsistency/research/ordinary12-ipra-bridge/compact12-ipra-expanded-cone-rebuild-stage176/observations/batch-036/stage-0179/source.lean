import BoundedZFCConsistency.Coding

/-!
# "Codes a formula" as an object-language predicate

`BoundedZFCConsistency.Coding` maps the metatheoretic type `Form` into an
arbitrary model of `ZFAxioms` and proves the map injective.  That is a family
of *external* closed terms: for each metatheoretic `phi` there is a set
`formCode H phi`.  The target sentence `Con_n(ZFC)` cannot mention such a
family, because it is a single `Form` and must quantify over codes internally.
This file supplies the missing internal notion — a set-theoretic predicate
whose extension is the set of formula codes — in both of the forms later
modules need: as a `Prop` about the model, and as a `Form` with a satisfaction
spec.

## The intersection presentation

Stating an inductively generated class inside set theory needs no recursion
theorem, only Separation.  Call a set `C` **formula-closed** when it contains
every atomic code and is closed under the five constructor operations:

| clause     | requirement on `C`                                                    |
| ---------- | --------------------------------------------------------------------- |
| `fMem`     | `⟨0, ⟨a, b⟩⟩ ∈ C` for all `a, b` in the internal omega                |
| `fEq`      | `⟨1, ⟨a, b⟩⟩ ∈ C` for all `a, b` in the internal omega                |
| `fBot`     | `⟨2, ∅⟩ ∈ C`                                                          |
| `fImp`     | `a, b ∈ C → ⟨3, ⟨a, b⟩⟩ ∈ C`                                          |
| `fAnd`     | `a, b ∈ C → ⟨4, ⟨a, b⟩⟩ ∈ C`                                          |
| `fOr`      | `a, b ∈ C → ⟨5, ⟨a, b⟩⟩ ∈ C`                                          |
| `fAll`     | `a ∈ C → ⟨6, a⟩ ∈ C`                                                  |
| `fEx`      | `a ∈ C → ⟨7, a⟩ ∈ C`                                                  |

The tags and shapes are exactly those of `formCode`; the atomic clauses
quantify over *internal* naturals, not over external ones, which is what makes
the notion internal at all.  Then `x` codes a formula when it belongs to every
formula-closed set:

```text
IsFormCodeSem H x  :=  ∀ C, FormulaClosed H C → x ∈ C
```

This is a single unbounded universal quantifier over the model, so it is
directly expressible as a `Form`: `fIsFormCodeF` is `∀ C, fFormulaClosedF C →
x ∈ C`, and `fIsFormCodeF_spec` is a genuine `iff` with the semantic side.

## What is proved

Two facts make the definition correct rather than merely well typed.

* **Quotation soundness** (`formCode_isFormCodeSem`): every externally quoted
  formula satisfies the predicate.  This is the direction that says the
  predicate is not too narrow.
* **The induction principle** (`isFormCodeSem_ind_form`, and its packaged form
  `isFormCodeSem_ind`): a property preserved by the atoms and the five
  constructors holds of every `x` satisfying the predicate.  This is the
  direction that says the predicate is not too wide, and it is what every
  later module will use to push a statement through the syntax.

The induction principle carries two hypotheses that are not removable and are
not artifacts of the presentation.

1. *The property must be definable.*  `ZFAxioms.sep` separates by a `Form`
   with parameters, so the subset carved out by the property is available only
   for definable properties.  `isFormCodeSem_ind_form` takes the property as a
   formula-with-environment, in the style of the definable-induction schema
   `omega_ind` of `ZF.Zf`; `isFormCodeSem_ind` accepts a `Prop`-valued
   predicate together with an explicit witness of its definability.
2. *A formula-closed set must exist.*  If there is none, `IsFormCodeSem` is
   vacuously true of every set and no induction principle can hold.  The
   hypothesis is discharged by producing one closed set, which needs the
   internal finite-recursion layer of `ZF.Zf` (`Approx`, `Theta`,
   `ClosureFO_of_ZF`) applied to the constructor relation over a seed
   containing the atoms.  That construction is a separate module; nothing here
   asserts that a formula-closed set exists.

## What is deliberately absent

No coded derivations, no internal rank bound, no internal satisfaction, and no
`Con_n`.  Also absent, as just noted, is the existence of a formula-closed set
and hence any claim that `IsFormCodeSem` has the codes as its exact extension:
what is proved is that the codes are included in the extension, and that the
extension is included in every closed definable property.
-/

namespace LeanProofs
namespace BoundedZFCConsistency

open SetTheory
open SetTheory.Form

universe u

section CodePredicate

variable {V : Type u} {mem : V → V → Prop}

/-! ## The internal omega as a pure intersection

`omega_spec` characterizes membership in `omegaV` by a conjunction: being an
element of the chosen infinite set *and* belonging to every inductive set.  The
first conjunct is redundant, because `omegaV` is itself inductive, and dropping
it matters here: the resulting characterization is a single unbounded
quantifier and therefore has a direct object-language rendering, whereas the
conjunction would force `InfSet` — a choice-dependent term with no defining
formula — into the syntax. -/

/-- The internal omega is inductive. -/
theorem omega_inductive (H : ZFAxioms mem) : inductiveV H (omegaV H) :=
  ⟨vempty_in_omega H, fun y hy => omega_succ H y hy⟩

/-- Membership in the internal omega is exactly membership in every inductive
set. -/
theorem mem_omega_iff (H : ZFAxioms mem) (n : V) :
    mem n (omegaV H) ↔ ∀ c, inductiveV H c → mem n c :=
  ⟨fun hn => ((omega_spec H n).mp hn).2, fun h => h _ (omega_inductive H)⟩

/-! ## The semantic predicate -/

/-- A set is **formula-closed** when it contains every atomic code and is
closed under the five constructor operations of the coding, following the table
in the module header.  The two atomic clauses range over the internal omega, so
in a nonstandard model a formula-closed set also contains codes with
nonstandard variable indices; that is intended, and is why the predicate is
internal. -/
structure FormulaClosed (H : ZFAxioms mem) (C : V) : Prop where
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
  /-- Closure under the universal quantifier constructor. -/
  all : ∀ a, mem a C → mem (kpair H (natV H 6) a) C
  /-- Closure under the existential quantifier constructor. -/
  ex : ∀ a, mem a C → mem (kpair H (natV H 7) a) C

/-- **"`x` codes a formula", semantically**: `x` belongs to every
formula-closed set.  The quantifier ranges over all sets of the model, so the
predicate is the intersection of a class of sets, taken without asserting that
the intersection is itself a set or that the class is nonempty. -/
def IsFormCodeSem (H : ZFAxioms mem) (x : V) : Prop :=
  ∀ C, FormulaClosed H C → mem x C

/-! ### The predicate is itself closed under the constructors

Each of these is immediate from the definition: the compound code lies in a
given closed set because its components do.  They are the introduction rules a
later module needs in order to build codes internally, and together with
`formCode_isFormCodeSem` they make the external and internal constructions
agree. -/

theorem isFormCodeSem_memAtom (H : ZFAxioms mem) {a b : V}
    (ha : mem a (omegaV H)) (hb : mem b (omegaV H)) :
    IsFormCodeSem H (kpair H (natV H 0) (kpair H a b)) :=
  fun _ hC => hC.memAtom a b ha hb

theorem isFormCodeSem_eqAtom (H : ZFAxioms mem) {a b : V}
    (ha : mem a (omegaV H)) (hb : mem b (omegaV H)) :
    IsFormCodeSem H (kpair H (natV H 1) (kpair H a b)) :=
  fun _ hC => hC.eqAtom a b ha hb

theorem isFormCodeSem_bot (H : ZFAxioms mem) :
    IsFormCodeSem H (kpair H (natV H 2) (vempty H)) :=
  fun _ hC => hC.bot

theorem isFormCodeSem_imp (H : ZFAxioms mem) {a b : V}
    (ha : IsFormCodeSem H a) (hb : IsFormCodeSem H b) :
    IsFormCodeSem H (kpair H (natV H 3) (kpair H a b)) :=
  fun C hC => hC.imp a b (ha C hC) (hb C hC)

theorem isFormCodeSem_and (H : ZFAxioms mem) {a b : V}
    (ha : IsFormCodeSem H a) (hb : IsFormCodeSem H b) :
    IsFormCodeSem H (kpair H (natV H 4) (kpair H a b)) :=
  fun C hC => hC.conj a b (ha C hC) (hb C hC)

theorem isFormCodeSem_or (H : ZFAxioms mem) {a b : V}
    (ha : IsFormCodeSem H a) (hb : IsFormCodeSem H b) :
    IsFormCodeSem H (kpair H (natV H 5) (kpair H a b)) :=
  fun C hC => hC.disj a b (ha C hC) (hb C hC)

theorem isFormCodeSem_all (H : ZFAxioms mem) {a : V} (ha : IsFormCodeSem H a) :
    IsFormCodeSem H (kpair H (natV H 6) a) :=
  fun C hC => hC.all a (ha C hC)

theorem isFormCodeSem_ex (H : ZFAxioms mem) {a : V} (ha : IsFormCodeSem H a) :
    IsFormCodeSem H (kpair H (natV H 7) a) :=
  fun C hC => hC.ex a (ha C hC)

/-! ## Quotation soundness -/

/-- **Every quoted formula satisfies the predicate.**  The induction is on the
external parse tree; the atomic cases use `natV_mem_omega` to see an external
de Bruijn index as an internal natural, which is the only point at which the
external and internal notions of "variable index" have to be reconciled.

The converse — that only codes of external formulas satisfy the predicate — is
false in nonstandard models and is not attempted: the whole point of an
internal predicate is that it also holds of nonstandard codes. -/
theorem formCode_isFormCodeSem (H : ZFAxioms mem) (phi : Form) :
    IsFormCodeSem H (formCode H phi) := by
  intro C hC
  induction phi with
  | fMem i j =>
      exact hC.memAtom _ _ (natV_mem_omega H i) (natV_mem_omega H j)
  | fEq i j =>
      exact hC.eqAtom _ _ (natV_mem_omega H i) (natV_mem_omega H j)
  | fBot => exact hC.bot
  | fImp a b iha ihb => exact hC.imp _ _ iha ihb
  | fAnd a b iha ihb => exact hC.conj _ _ iha ihb
  | fOr a b iha ihb => exact hC.disj _ _ iha ihb
  | fAll a ih => exact hC.all _ ih
  | fEx a ih => exact hC.ex _ ih

/-! ## The induction principle

The instance of the intersection that does the work is the subset of a given
formula-closed set `C0` carved out by the property.  Separation supplies it
whenever the property is definable, and the closure hypotheses say exactly that
the subset is again formula-closed; membership of `x` in it is then immediate
from `IsFormCodeSem`. -/

/-- **Induction on formula codes, as a definable schema.**  The property is
`phi` with parameters `e` in its free slots beyond slot `0`, in the style of
`omega_ind`.

`hC0` is not removable: with no formula-closed set at all, `IsFormCodeSem` is
vacuously universal.  It is discharged by the closure construction of `ZF.Zf`
in a later module. -/
theorem isFormCodeSem_ind_form (H : ZFAxioms mem) (phi : Form) (e : Nat → V)
    {C0 : V} (hC0 : FormulaClosed H C0)
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
      Sat mem (scons (kpair H (natV H 5) (kpair H a b)) e) phi)
    (hAll : ∀ a, Sat mem (scons a e) phi →
      Sat mem (scons (kpair H (natV H 6) a) e) phi)
    (hEx : ∀ a, Sat mem (scons a e) phi →
      Sat mem (scons (kpair H (natV H 7) a) e) phi) :
    ∀ x, IsFormCodeSem H x → Sat mem (scons x e) phi := by
  intro x hx
  have hD : ∀ y, mem y (sepD H phi e C0) ↔
      (mem y C0 ∧ Sat mem (scons y e) phi) :=
    fun y => sepD_spec H phi e C0 y
  have hclosed : FormulaClosed H (sepD H phi e C0) := by
    refine
      ⟨fun a b ha hb => (hD _).mpr ⟨hC0.memAtom a b ha hb, hMemAtom a b ha hb⟩,
       fun a b ha hb => (hD _).mpr ⟨hC0.eqAtom a b ha hb, hEqAtom a b ha hb⟩,
       (hD _).mpr ⟨hC0.bot, hBot⟩, ?_, ?_, ?_, ?_, ?_⟩
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
    · intro a ha
      obtain ⟨ha0, ha1⟩ := (hD a).mp ha
      exact (hD _).mpr ⟨hC0.all a ha0, hAll a ha1⟩
    · intro a ha
      obtain ⟨ha0, ha1⟩ := (hD a).mp ha
      exact (hD _).mpr ⟨hC0.ex a ha0, hEx a ha1⟩
  exact ((hD x).mp (hx _ hclosed)).2

/-- **Induction on formula codes**, with the property presented as a
`Prop`-valued predicate together with a witness `hdef` that it is definable.
Call sites that already have a formula in hand can use
`isFormCodeSem_ind_form` directly; this is the shape most convenient when the
property has been introduced semantically and its formula is a separate
construction. -/
theorem isFormCodeSem_ind (H : ZFAxioms mem) (P : V → Prop)
    (phi : Form) (e : Nat → V)
    (hdef : ∀ y, P y ↔ Sat mem (scons y e) phi)
    {C0 : V} (hC0 : FormulaClosed H C0)
    (hMemAtom : ∀ a b, mem a (omegaV H) → mem b (omegaV H) →
      P (kpair H (natV H 0) (kpair H a b)))
    (hEqAtom : ∀ a b, mem a (omegaV H) → mem b (omegaV H) →
      P (kpair H (natV H 1) (kpair H a b)))
    (hBot : P (kpair H (natV H 2) (vempty H)))
    (hImp : ∀ a b, P a → P b → P (kpair H (natV H 3) (kpair H a b)))
    (hAnd : ∀ a b, P a → P b → P (kpair H (natV H 4) (kpair H a b)))
    (hOr : ∀ a b, P a → P b → P (kpair H (natV H 5) (kpair H a b)))
    (hAll : ∀ a, P a → P (kpair H (natV H 6) a))
    (hEx : ∀ a, P a → P (kpair H (natV H 7) a)) :
    ∀ x, IsFormCodeSem H x → P x := by
  intro x hx
  refine (hdef x).mpr ?_
  refine isFormCodeSem_ind_form H phi e hC0
    (fun a b ha hb => (hdef _).mp (hMemAtom a b ha hb))
    (fun a b ha hb => (hdef _).mp (hEqAtom a b ha hb))
    ((hdef _).mp hBot)
    (fun a b ha hb => (hdef _).mp (hImp a b ((hdef a).mpr ha) ((hdef b).mpr hb)))
    (fun a b ha hb => (hdef _).mp (hAnd a b ((hdef a).mpr ha) ((hdef b).mpr hb)))
    (fun a b ha hb => (hdef _).mp (hOr a b ((hdef a).mpr ha) ((hdef b).mpr hb)))
    (fun a ha => (hdef _).mp (hAll a ((hdef a).mpr ha)))
    (fun a ha => (hdef _).mp (hEx a ((hdef a).mpr ha)))
    x hx

/-! ## The object-language predicate

The macros below follow the house style of `ZF.Zf` and of the coding-shape
macros of `BoundedZFCConsistency.Coding`: each is a genuine `Form` whose
arguments are ABSOLUTE de Bruijn slots at the use site, paired with a spec
lemma stating exactly what its satisfaction means.  Every binder introduced by
a macro shifts the caller's slots by one, and each definition below records the
shift explicitly. -/

/-- "slot `k` is an internal natural number".

| de Bruijn slot   | contents                       |
| ---------------- | ------------------------------ |
| `0`              | the bound inductive set `c`    |
| `k+1`            | the caller's slot `k`          |

The clause is the intersection characterization `mem_omega_iff`, so no
parameter for omega itself is needed. -/
def fNatF (k : Nat) : Form :=
  fAll (fImp (fInd 0) (fMem (k+1) 0))

theorem fNatF_spec (H : ZFAxioms mem) (ee : Nat → V) (k : Nat) :
    Sat mem ee (fNatF k) ↔ mem (ee k) (omegaV H) := by
  rw [mem_omega_iff H (ee k)]
  constructor
  · intro h c hc
    exact h c ((fInd_spec H (scons c ee) 0).mpr hc)
  · intro h c hc
    exact h c ((fInd_spec H (scons c ee) 0).mp hc)

/-- "⟨numeral `t`, ⟨slot `j`, slot `k`⟩⟩ ∈ slot `c`" — membership of a binary
constructor's code, with the tag as an external parameter.

| de Bruijn slot | contents                                    |
| -------------- | ------------------------------------------- |
| `0`            | the code `⟨numeral t, ⟨slot j, slot k⟩⟩`     |
| `1`            | the numeral of `t`                          |
| `m+2`          | the caller's slot `m`                       |
-/
def fTagPairMemF (c t j k : Nat) : Form :=
  fEx (fAnd (fNumF 0 t)
    (fEx (fAnd (fTripleF 0 1 (j+2) (k+2)) (fMem 0 (c+2)))))

theorem fTagPairMemF_spec (H : ZFAxioms mem) (ee : Nat → V) (c t j k : Nat) :
    Sat mem ee (fTagPairMemF c t j k) ↔
      mem (kpair H (natV H t) (kpair H (ee j) (ee k))) (ee c) := by
  constructor
  · rintro ⟨d, hd, p, hp, hmem⟩
    have hd' : d = natV H t := (fNumF_spec H t 0 (scons d ee)).mp hd
    have hp' : p = kpair H d (kpair H (ee j) (ee k)) :=
      (fTripleF_spec H (scons p (scons d ee)) 0 1 (j+2) (k+2)).mp hp
    have hmem' : mem p (ee c) := hmem
    rw [hp', hd'] at hmem'
    exact hmem'
  · intro h
    refine ⟨natV H t, (fNumF_spec H t 0 (scons (natV H t) ee)).mpr rfl,
      kpair H (natV H t) (kpair H (ee j) (ee k)), ?_, h⟩
    exact (fTripleF_spec H
      (scons (kpair H (natV H t) (kpair H (ee j) (ee k))) (scons (natV H t) ee))
      0 1 (j+2) (k+2)).mpr rfl

/-- "⟨numeral `t`, slot `j`⟩ ∈ slot `c`" — membership of a unary constructor's
code.

| de Bruijn slot | contents                          |
| -------------- | --------------------------------- |
| `0`            | the code `⟨numeral t, slot j⟩`     |
| `1`            | the numeral of `t`                |
| `m+2`          | the caller's slot `m`             |
-/
def fTagMemF (c t j : Nat) : Form :=
  fEx (fAnd (fNumF 0 t)
    (fEx (fAnd (fKPairF 0 1 (j+2)) (fMem 0 (c+2)))))

theorem fTagMemF_spec (H : ZFAxioms mem) (ee : Nat → V) (c t j : Nat) :
    Sat mem ee (fTagMemF c t j) ↔ mem (kpair H (natV H t) (ee j)) (ee c) := by
  constructor
  · rintro ⟨d, hd, p, hp, hmem⟩
    have hd' : d = natV H t := (fNumF_spec H t 0 (scons d ee)).mp hd
    have hp' : p = kpair H d (ee j) :=
      (fKPairF_spec H (scons p (scons d ee)) 0 1 (j+2)).mp hp
    have hmem' : mem p (ee c) := hmem
    rw [hp', hd'] at hmem'
    exact hmem'
  · intro h
    refine ⟨natV H t, (fNumF_spec H t 0 (scons (natV H t) ee)).mpr rfl,
      kpair H (natV H t) (ee j), ?_, h⟩
    exact (fKPairF_spec H
      (scons (kpair H (natV H t) (ee j)) (scons (natV H t) ee))
      0 1 (j+2)).mpr rfl

/-- "⟨numeral `t`, ∅⟩ ∈ slot `c`" — membership of a nullary constructor's code.

| de Bruijn slot | contents                    |
| -------------- | --------------------------- |
| `0`            | the code `⟨numeral t, ∅⟩`    |
| `m+1`          | the caller's slot `m`       |
-/
def fTagEmptyMemF (c t : Nat) : Form :=
  fEx (fAnd (fTaggedEmptyF 0 t) (fMem 0 (c+1)))

theorem fTagEmptyMemF_spec (H : ZFAxioms mem) (ee : Nat → V) (c t : Nat) :
    Sat mem ee (fTagEmptyMemF c t) ↔
      mem (kpair H (natV H t) (vempty H)) (ee c) := by
  constructor
  · rintro ⟨d, hd, hmem⟩
    have hd' : d = kpair H (natV H t) (vempty H) :=
      (fTaggedEmptyF_spec H (scons d ee) 0 t).mp hd
    have hmem' : mem d (ee c) := hmem
    rw [hd'] at hmem'
    exact hmem'
  · intro h
    exact ⟨kpair H (natV H t) (vempty H),
      (fTaggedEmptyF_spec H (scons (kpair H (natV H t) (vempty H)) ee) 0 t).mpr
        rfl,
      h⟩

/-- The atomic closure clause for tag `t`: every pair of internal naturals
yields a code in slot `c`.

| de Bruijn slot | contents                    |
| -------------- | --------------------------- |
| `0`            | the second index `b`        |
| `1`            | the first index `a`         |
| `m+2`          | the caller's slot `m`       |
-/
def fClAtomF (c t : Nat) : Form :=
  fAll (fAll (fImp (fAnd (fNatF 1) (fNatF 0)) (fTagPairMemF (c+2) t 1 0)))

theorem fClAtomF_spec (H : ZFAxioms mem) (ee : Nat → V) (c t : Nat) :
    Sat mem ee (fClAtomF c t) ↔
      ∀ a b, mem a (omegaV H) → mem b (omegaV H) →
        mem (kpair H (natV H t) (kpair H a b)) (ee c) := by
  constructor
  · intro h a b ha hb
    have hab := h a b
      ⟨(fNatF_spec H (scons b (scons a ee)) 1).mpr ha,
       (fNatF_spec H (scons b (scons a ee)) 0).mpr hb⟩
    exact (fTagPairMemF_spec H (scons b (scons a ee)) (c+2) t 1 0).mp hab
  · intro h a b hab
    exact (fTagPairMemF_spec H (scons b (scons a ee)) (c+2) t 1 0).mpr
      (h a b ((fNatF_spec H (scons b (scons a ee)) 1).mp hab.1)
             ((fNatF_spec H (scons b (scons a ee)) 0).mp hab.2))

/-- The binary closure clause for tag `t`: two members of slot `c` yield a code
in slot `c`.

| de Bruijn slot | contents                    |
| -------------- | --------------------------- |
| `0`            | the second component `b`    |
| `1`            | the first component `a`     |
| `m+2`          | the caller's slot `m`       |
-/
def fClBinF (c t : Nat) : Form :=
  fAll (fAll (fImp (fAnd (fMem 1 (c+2)) (fMem 0 (c+2)))
    (fTagPairMemF (c+2) t 1 0)))

theorem fClBinF_spec (H : ZFAxioms mem) (ee : Nat → V) (c t : Nat) :
    Sat mem ee (fClBinF c t) ↔
      ∀ a b, mem a (ee c) → mem b (ee c) →
        mem (kpair H (natV H t) (kpair H a b)) (ee c) := by
  constructor
  · intro h a b ha hb
    exact (fTagPairMemF_spec H (scons b (scons a ee)) (c+2) t 1 0).mp
      (h a b ⟨ha, hb⟩)
  · intro h a b hab
    exact (fTagPairMemF_spec H (scons b (scons a ee)) (c+2) t 1 0).mpr
      (h a b hab.1 hab.2)

/-- The unary closure clause for tag `t`: a member of slot `c` yields a code in
slot `c`.

| de Bruijn slot | contents                    |
| -------------- | --------------------------- |
| `0`            | the component `a`           |
| `m+1`          | the caller's slot `m`       |
-/
def fClUnF (c t : Nat) : Form :=
  fAll (fImp (fMem 0 (c+1)) (fTagMemF (c+1) t 0))

theorem fClUnF_spec (H : ZFAxioms mem) (ee : Nat → V) (c t : Nat) :
    Sat mem ee (fClUnF c t) ↔
      ∀ a, mem a (ee c) → mem (kpair H (natV H t) a) (ee c) := by
  constructor
  · intro h a ha
    exact (fTagMemF_spec H (scons a ee) (c+1) t 0).mp (h a ha)
  · intro h a ha
    exact (fTagMemF_spec H (scons a ee) (c+1) t 0).mpr (h a ha)

/-- "slot `c` is formula-closed" — the eight clauses of `FormulaClosed`,
conjoined in the order of the table in the module header. -/
def fFormulaClosedF (c : Nat) : Form :=
  fAnd (fClAtomF c 0)
    (fAnd (fClAtomF c 1)
      (fAnd (fTagEmptyMemF c 2)
        (fAnd (fClBinF c 3)
          (fAnd (fClBinF c 4)
            (fAnd (fClBinF c 5)
              (fAnd (fClUnF c 6) (fClUnF c 7)))))))

theorem fFormulaClosedF_spec (H : ZFAxioms mem) (ee : Nat → V) (c : Nat) :
    Sat mem ee (fFormulaClosedF c) ↔ FormulaClosed H (ee c) := by
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
    exact
      ⟨(fClAtomF_spec H ee c 0).mp h0,
       (fClAtomF_spec H ee c 1).mp h1,
       (fTagEmptyMemF_spec H ee c 2).mp h2,
       (fClBinF_spec H ee c 3).mp h3,
       (fClBinF_spec H ee c 4).mp h4,
       (fClBinF_spec H ee c 5).mp h5,
       (fClUnF_spec H ee c 6).mp h6,
       (fClUnF_spec H ee c 7).mp h7⟩
  · intro h
    exact
      ⟨(fClAtomF_spec H ee c 0).mpr h.memAtom,
       (fClAtomF_spec H ee c 1).mpr h.eqAtom,
       (fTagEmptyMemF_spec H ee c 2).mpr h.bot,
       (fClBinF_spec H ee c 3).mpr h.imp,
       (fClBinF_spec H ee c 4).mpr h.conj,
       (fClBinF_spec H ee c 5).mpr h.disj,
       (fClUnF_spec H ee c 6).mpr h.all,
       (fClUnF_spec H ee c 7).mpr h.ex⟩

/-- **"slot `i` codes a formula", as a `Form`**: slot `i` belongs to every
formula-closed set.

| de Bruijn slot | contents                          |
| -------------- | --------------------------------- |
| `0`            | the bound formula-closed set `C`  |
| `m+1`          | the caller's slot `m`             |
-/
def fIsFormCodeF (i : Nat) : Form :=
  fAll (fImp (fFormulaClosedF 0) (fMem (i+1) 0))

/-- The object-language predicate means exactly the semantic one.  This is the
bridge that lets a later `Form` — ultimately `Con_n(ZFC)` — quantify over
formula codes while the surrounding metatheoretic reasoning stays on the
semantic side. -/
theorem fIsFormCodeF_spec (H : ZFAxioms mem) (ee : Nat → V) (i : Nat) :
    Sat mem ee (fIsFormCodeF i) ↔ IsFormCodeSem H (ee i) := by
  constructor
  · intro h C hC
    exact h C ((fFormulaClosedF_spec H (scons C ee) 0).mpr hC)
  · intro h C hC
    exact h C ((fFormulaClosedF_spec H (scons C ee) 0).mp hC)

/-- Quotation soundness in object-language form: for every external formula
`phi`, any environment placing `formCode H phi` in slot `i` satisfies
`fIsFormCodeF i`. -/
theorem fIsFormCodeF_formCode (H : ZFAxioms mem) (ee : Nat → V) (i : Nat)
    (phi : Form) (hee : ee i = formCode H phi) :
    Sat mem ee (fIsFormCodeF i) := by
  refine (fIsFormCodeF_spec H ee i).mpr ?_
  rw [hee]
  exact formCode_isFormCodeSem H phi

end CodePredicate

end BoundedZFCConsistency
end LeanProofs
