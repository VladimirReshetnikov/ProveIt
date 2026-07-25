import BoundedZFCConsistency.InternalSatTotality

/-!
# Coded renaming, and the substitution lemma for internal satisfaction

`BoundedZFCConsistency.InternalSatTotality` supplies a satisfaction relation
`SatIn` for coded formulas over an internal set structure, together with its
eight Tarski clauses.  Formalized soundness of the seventeen-rule calculus
needs one thing that satisfaction alone does not provide: the calculus moves
formulas across binders.  `P_allI` and `P_exE` rename the whole context along
`Nat.succ`, and `P_allE`, `P_exI` and `P_eqElim` instantiate the outermost
binder at a variable.  Both operations have to exist *inside* the model, as
operations on codes, and their effect on satisfaction has to be known.

This file supplies them.

## Variable maps

A **variable map** is an internal function from the internal omega to itself —
that is, `IsEnvOn H (omegaV H) r`, the very notion `InternalSat` already uses
for environments, at the carrier `omegaV H`.  Reusing it is not a pun: an
environment is a function `omega → A` and a variable map is a function
`omega → omega`, and both need exactly the same internal function interface.
In particular `econs`, its two application equations, and the fact that it
preserves environments are immediately available for variable maps.

The binder case of renaming needs the internal counterpart of `up`:

```text
upV H r  =  econs H ∅ { ⟨n, (r n)+1⟩ : n ∈ omega }
```

so that `upV H r` sends `0` to `0` and `n+1` to `(r n)+1`, matching `up` of
`FirstOrder.Fol` pointwise.

Three variable maps are named, because the calculus asks for exactly them:
`idMap`, the identity; `succMap`, the internal `Nat.succ`; and `instMap H k`,
the internal `inst k`, which is `econs H k (idMap H)` — the coincidence
`inst k = scons_nat k id` read internally.

## The renaming graph

Renaming cannot be defined by external recursion on the code, for the reason
that governs this whole project: a nonstandard model has code-like elements
that are not quotations, so there is no external parse tree to recurse on.  It
also cannot be presented as the intersection of all closed classes, the device
`BoundedZFCConsistency.CodePredicate` uses for "codes a formula".  That device
needs *some* closed set to exist before its induction principle says anything,
and a set closed under the renaming clauses would have to record a triple for
every variable map; the variable maps are subsets of `omega × omega`, and
without Powerset — which the `ZFAxioms` bundle deliberately omits — they are
not available as a set.

What does work is the certificate architecture of `InternalSat`, and for the
same reason: a certificate is a *set* of triples, produced by the induction
itself rather than assumed.  `RenStep H S r c c'` says that `⟨r, c, c'⟩` is
justified by the triples already in `S`:

| tag  | clause   | justification                                              |
| ---- | -------- | ---------------------------------------------------------- |
| `0`  | `fMem`   | `c' = ⟨0, ⟨r i, r j⟩⟩` for `c = ⟨0, ⟨i, j⟩⟩`, `i, j ∈ omega` |
| `1`  | `fEq`    | `c' = ⟨1, ⟨r i, r j⟩⟩` for `c = ⟨1, ⟨i, j⟩⟩`, `i, j ∈ omega` |
| `2`  | `fBot`   | `c = c' = ⟨2, ∅⟩`                                          |
| `3`  | `fImp`   | `⟨r, a, a'⟩, ⟨r, b, b'⟩ ∈ S`                               |
| `4`  | `fAnd`   | `⟨r, a, a'⟩, ⟨r, b, b'⟩ ∈ S`                               |
| `5`  | `fOr`    | `⟨r, a, a'⟩, ⟨r, b, b'⟩ ∈ S`                               |
| `6`  | `fAll`   | `⟨upV r, a, a'⟩ ∈ S`                                       |
| `7`  | `fEx`    | `⟨upV r, a, a'⟩ ∈ S`                                       |

`Renames H r c c'` holds when some closed set records `⟨r, c, c'⟩`.  Unlike
satisfaction, the two quantifier clauses do not range over a carrier, so the
certificate built at a compound code is a union of finitely many certificates
together with one new triple, and neither totality nor single-valuedness needs
the uniform-over-a-set strengthening that `certificate_total` required.  Both
are proved by code induction, so both hold of nonstandard codes as well.

## The substitution lemma

The payoff is

```text
SatIn H A R c' e  ↔  SatIn H A R c (compV H e r)      whenever Renames H r c c'
```

where `compV H e r` is the internal composition `n ↦ e (r n)`.  This is the
internal form of `Sat_rename`, and the two binder cases are exactly where the
work is: they need

```text
compV H (econs H d e) (upV H r) = econs H d (compV H e r)
```

which is proved by internal function extensionality after a case split on
"zero or successor" — the fact `nat_zero_or_succ` that `InternalSat` had to
add to the omega arithmetic.

Specializing at `succMap` and at `instMap H k` gives the two equations the
quantifier rules of the calculus consume:

```text
compV H (econs H d e) (succMap H) = e
compV H e (instMap H k)           = econs H (applyV H e k) e
```

## Agreement with quotation

The internal operation is defined on every code, and on the nonstandard ones
it is not the quotation of anything.  On quotations the two notions do agree:
if a variable map computes an external index function `f` on numerals, then it
renames the code of `phi` to the code of `rename f phi`.  Both named maps
satisfy that hypothesis, so the two equations above have quotation-level
counterparts, which is the form the eventual coded-derivation layer will
consume when it has to relate a coded rule instance to an external one.

## What is deliberately absent

**Coded derivations and internal soundness are not here.**  Nothing below
defines a derivation predicate, and nothing claims that a coded derivation has
a true conclusion.  What is provided is the syntactic-operation layer such a
predicate needs, and the semantic lemma its quantifier rules would consume.

Two further syntactic operations a full derivation layer will want are also
absent, since no rule of the calculus needs them: a coded *substitution* of a
term for a variable — unnecessary here, because the language is purely
relational and the calculus instantiates only at variables — and coded
contexts as internal lists.

Also absent, as everywhere in this project: reflection, `V_alpha`, any rank
bound on codes, and `Con_n` itself.

## De Bruijn bookkeeping

Every formula below carries a table of its de Bruijn slots.  Slot arguments
named `_i` are ABSOLUTE positions in the environment at the use site; each
binder introduced by a macro shifts the caller's slots by one, and the call
sites account for the shift explicitly.  The convention matches `ZF.Zf`,
`BoundedZFCConsistency.Coding` and `BoundedZFCConsistency.InternalSat`.

Neither Powerset nor Regularity is used.
-/

namespace LeanProofs
namespace BoundedZFCConsistency

open SetTheory
open SetTheory.Form

universe u

section InternalSoundness

variable {V : Type u} {mem : V → V → Prop}

/-! ## Internal function extensionality

Two internal functions with the same domain and the same values are the same
set.  The ZF development proves uniqueness of the recursion sequence by an
internal induction instead, so this small fact is not available upstream; it is
what turns each of the composition identities below into a set equality rather
than a pointwise statement. -/

/-- Internal functions on a common domain are equal when their values agree. -/
theorem funOn_ext (H : ZFAxioms mem) {F F' d : V} (hF : IsFunctionOn H F d)
    (hF' : IsFunctionOn H F' d)
    (hval : ∀ n, mem n d → applyV H F n = applyV H F' n) : F = F' := by
  refine H.ext F F' (fun p => ⟨fun hp => ?_, fun hp => ?_⟩)
  · obtain ⟨x, y, hx, rfl⟩ := hF.2.2 p hp
    have hy : applyV H F x = y := applyV_eq H hF.1 hp
    have hmem := applyV_mem H (hF'.2.1 x hx)
    rw [← hval x hx, hy] at hmem
    exact hmem
  · obtain ⟨x, y, hx, rfl⟩ := hF'.2.2 p hp
    have hy : applyV H F' x = y := applyV_eq H hF'.1 hp
    have hmem := applyV_mem H (hF.2.1 x hx)
    rw [hval x hx, hy] at hmem
    exact hmem

/-! ## Internal variable maps

A variable map is an environment over the carrier `omegaV H`.  The
abbreviation is deliberate: everything `InternalSat` proves about environments
— the shift `econs`, its two application equations, and the fact that it is
again an environment — applies verbatim. -/

/-- `r` is an internal map of de Bruijn indices: an internal function from the
internal omega to itself. -/
def IsVarMap (H : ZFAxioms mem) (r : V) : Prop := IsEnvOn H (omegaV H) r

theorem isVarMap_apply (H : ZFAxioms mem) {r : V} (hr : IsVarMap H r) {n : V}
    (hn : mem n (omegaV H)) : mem (applyV H r n) (omegaV H) :=
  isEnvOn_apply H hr hn

theorem isVarMap_functional (H : ZFAxioms mem) {r : V} (hr : IsVarMap H r) :
    ∀ x y y', mem (kpair H x y) r → mem (kpair H x y') r → y = y' := hr.1.1

theorem isVarMap_mem (H : ZFAxioms mem) {r : V} (hr : IsVarMap H r) {n : V}
    (hn : mem n (omegaV H)) : mem (kpair H n (applyV H r n)) r :=
  applyV_mem H (hr.1.2.1 n hn)

/-- "slot `i` is the internal omega".

| de Bruijn slot | contents                |
| -------------- | ----------------------- |
| `0`            | the candidate element   |
| `m+1`          | the caller's slot `m`   |

The element clause is `fNatF`, which uses the pure intersection
characterization of the omega and therefore needs no parameter; extensionality
turns it into an equation. -/
def fIsOmegaF (i : Nat) : Form := fSetByF i (fNatF 0)

theorem fIsOmegaF_spec (H : ZFAxioms mem) (ee : Nat → V) (i : Nat) :
    Sat mem ee (fIsOmegaF i) ↔ ee i = omegaV H :=
  fSetByF_spec H ee i (fNatF 0) (omegaV H)
    (fun x => fNatF_spec H (scons x ee) 0)

/-- "slot `r_i` is a variable map".

| de Bruijn slot | contents                |
| -------------- | ----------------------- |
| `0`            | the internal omega      |
| `m+1`          | the caller's slot `m`   |
-/
def fVarMapF (r_i : Nat) : Form :=
  fEx (fAnd (fIsOmegaF 0) (fEnvOnF (r_i+1) 0))

theorem fVarMapF_spec (H : ZFAxioms mem) (ee : Nat → V) (r_i : Nat) :
    Sat mem ee (fVarMapF r_i) ↔ IsVarMap H (ee r_i) := by
  constructor
  · rintro ⟨w, hw, henv⟩
    have hw' : w = omegaV H := (fIsOmegaF_spec H (scons w ee) 0).mp hw
    have henv' : IsEnvOn H w (ee r_i) :=
      (fEnvOnF_spec H (scons w ee) (r_i+1) 0).mp henv
    rw [hw'] at henv'
    exact henv'
  · intro h
    exact ⟨omegaV H, (fIsOmegaF_spec H (scons (omegaV H) ee) 0).mpr rfl,
      (fEnvOnF_spec H (scons (omegaV H) ee) (r_i+1) 0).mpr h⟩

/-! ### The successor of a variable map, and the binder shift -/

/-- The graph of `n ↦ ⟨n, (r n)+1⟩`, with `r` as the parameter from slot `2`
up.  The uniqueness clause on the value is what makes the relation functional
with no hypothesis on `r`; on a genuine variable map it is redundant.

| de Bruijn slot | contents                              |
| -------------- | ------------------------------------- |
| `0`            | the value `y`, then the successor `s` |
| `1`            | the output pair `p`, then `y`         |
| `2`            | the input index `n`, then `p`         |
| `3`            | the parameter `r`, then `n`           |
-/
def psiSuccValF : Form :=
  fEx (fAnd (fAnd (fPairMemF 2 0 3) (fAll (fImp (fPairMemF 3 0 4) (fEq 0 1))))
    (fEx (fAnd (fSuccF 0 1) (fKPairF 2 3 0))))

theorem psiSuccValF_rel (H : ZFAxioms mem) (r p n : V) :
    relOf mem psiSuccValF (fun _ => r) p n ↔
      ∃ y, (mem (kpair H n y) r ∧ ∀ y', mem (kpair H n y') r → y' = y) ∧
        p = kpair H n (vsucc H y) := by
  unfold relOf psiSuccValF
  constructor
  · rintro ⟨y, ⟨hmem, huniq⟩, s, hs, hp⟩
    refine ⟨y, ⟨(fPairMemF_spec H _ 2 0 3).mp hmem, fun y' hy' => ?_⟩, ?_⟩
    · exact huniq y' ((fPairMemF_spec H _ 3 0 4).mpr hy')
    · have hs' : s = vsucc H y := (fSuccF_spec H _ 0 1).mp hs
      have hp' : p = kpair H n s := (fKPairF_spec H _ 2 3 0).mp hp
      rw [hp', hs']
  · rintro ⟨y, ⟨hmem, huniq⟩, hp⟩
    refine ⟨y, ⟨(fPairMemF_spec H _ 2 0 3).mpr hmem, fun y' hy' => ?_⟩,
      vsucc H y, (fSuccF_spec H _ 0 1).mpr rfl, (fKPairF_spec H _ 2 3 0).mpr hp⟩
    exact huniq y' ((fPairMemF_spec H _ 3 0 4).mp hy')

theorem psiSuccValF_functional (H : ZFAxioms mem) (r : V) :
    Functional (relOf mem psiSuccValF (fun _ => r)) := by
  intro n p p' h1 h2
  obtain ⟨y, ⟨_, huy⟩, hp⟩ := (psiSuccValF_rel H r p n).mp h1
  obtain ⟨y', ⟨hy', _⟩, hp'⟩ := (psiSuccValF_rel H r p' n).mp h2
  rw [hp, hp', huy y' hy']

/-- The image of the internal omega under `n ↦ ⟨n, (r n)+1⟩`. -/
noncomputable def succVals (H : ZFAxioms mem) (r : V) : V :=
  (H.repl psiSuccValF (fun _ => r) (psiSuccValF_functional H r) (omegaV H)).choose

theorem succVals_spec (H : ZFAxioms mem) (r p : V) :
    mem p (succVals H r) ↔
      ∃ n, mem n (omegaV H) ∧ ∃ y,
        (mem (kpair H n y) r ∧ ∀ y', mem (kpair H n y') r → y' = y) ∧
        p = kpair H n (vsucc H y) := by
  unfold succVals
  rw [(H.repl psiSuccValF (fun _ => r) (psiSuccValF_functional H r)
    (omegaV H)).choose_spec p]
  constructor
  · rintro ⟨n, hn, hrel⟩
    exact ⟨n, hn, (psiSuccValF_rel H r p n).mp hrel⟩
  · rintro ⟨n, hn, hy⟩
    exact ⟨n, hn, (psiSuccValF_rel H r p n).mpr hy⟩

/-- On a variable map the uniqueness clause is redundant and the description
collapses to the intended one. -/
theorem succVals_mem (H : ZFAxioms mem) {r : V} (hr : IsVarMap H r) (p : V) :
    mem p (succVals H r) ↔
      ∃ n, mem n (omegaV H) ∧ p = kpair H n (vsucc H (applyV H r n)) := by
  rw [succVals_spec H r p]
  constructor
  · rintro ⟨n, hn, y, ⟨hy, _⟩, hp⟩
    exact ⟨n, hn, by rw [hp, applyV_eq H (isVarMap_functional H hr) hy]⟩
  · rintro ⟨n, hn, hp⟩
    exact ⟨n, hn, applyV H r n,
      ⟨isVarMap_mem H hr hn,
       fun y' hy' => isVarMap_functional H hr n y' _ hy' (isVarMap_mem H hr hn)⟩,
      hp⟩

theorem succVals_isVarMap (H : ZFAxioms mem) {r : V} (hr : IsVarMap H r) :
    IsVarMap H (succVals H r) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro x y y' h1 h2
    obtain ⟨n, _, hk⟩ := (succVals_mem H hr (kpair H x y)).mp h1
    obtain ⟨n', _, hk'⟩ := (succVals_mem H hr (kpair H x y')).mp h2
    obtain ⟨hn, hy⟩ := kpair_inj H _ _ _ _ hk
    obtain ⟨hn', hy'⟩ := kpair_inj H _ _ _ _ hk'
    rw [hy, hy', ← hn, ← hn']
  · intro x hx
    exact ⟨vsucc H (applyV H r x),
      (succVals_mem H hr (kpair H x (vsucc H (applyV H r x)))).mpr ⟨x, hx, rfl⟩⟩
  · intro p hp
    obtain ⟨n, hn, hk⟩ := (succVals_mem H hr p).mp hp
    exact ⟨n, vsucc H (applyV H r n), hn, hk⟩
  · intro n y hk
    obtain ⟨n', hn', hk'⟩ := (succVals_mem H hr (kpair H n y)).mp hk
    obtain ⟨-, hy⟩ := kpair_inj H _ _ _ _ hk'
    rw [hy]
    exact omega_succ H _ (isVarMap_apply H hr hn')

theorem succVals_apply (H : ZFAxioms mem) {r : V} (hr : IsVarMap H r) {n : V}
    (hn : mem n (omegaV H)) :
    applyV H (succVals H r) n = vsucc H (applyV H r n) :=
  applyV_eq H (succVals_isVarMap H hr).1.1
    ((succVals_mem H hr (kpair H n (vsucc H (applyV H r n)))).mpr ⟨n, hn, rfl⟩)

/-- **The binder shift of a variable map.**  `upV H r` sends `0` to `0` and
`n+1` to `(r n)+1`, matching `up` of `FirstOrder.Fol` pointwise. -/
noncomputable def upV (H : ZFAxioms mem) (r : V) : V :=
  econs H (vempty H) (succVals H r)

theorem upV_isVarMap (H : ZFAxioms mem) {r : V} (hr : IsVarMap H r) :
    IsVarMap H (upV H r) :=
  econs_isEnvOn H (succVals_isVarMap H hr) (vempty_in_omega H)

theorem upV_zero (H : ZFAxioms mem) {r : V} (hr : IsVarMap H r) :
    applyV H (upV H r) (vempty H) = vempty H :=
  econs_zero H (succVals_isVarMap H hr).1.1 (vempty H)

theorem upV_succ (H : ZFAxioms mem) {r : V} (hr : IsVarMap H r) {n : V}
    (hn : mem n (omegaV H)) :
    applyV H (upV H r) (vsucc H n) = vsucc H (applyV H r n) := by
  rw [upV, econs_succ H (succVals_isVarMap H hr) (vempty H) hn,
      succVals_apply H hr hn]

/-! ### The three named variable maps -/

/-- The graph of the identity on the internal omega. -/
def psiIdF : Form := fKPairF 0 1 1

theorem psiIdF_rel (H : ZFAxioms mem) (p n : V) :
    relOf mem psiIdF (fun _ => vempty H) p n ↔ p = kpair H n n := by
  unfold relOf psiIdF
  exact fKPairF_spec H (scons p (scons n (fun _ => vempty H))) 0 1 1

theorem psiIdF_functional (H : ZFAxioms mem) :
    Functional (relOf mem psiIdF (fun _ => vempty H)) := by
  intro n p p' h1 h2
  rw [(psiIdF_rel H p n).mp h1, (psiIdF_rel H p' n).mp h2]

/-- The internal identity map on de Bruijn indices. -/
noncomputable def idMap (H : ZFAxioms mem) : V :=
  (H.repl psiIdF (fun _ => vempty H) (psiIdF_functional H) (omegaV H)).choose

theorem idMap_spec (H : ZFAxioms mem) (p : V) :
    mem p (idMap H) ↔ ∃ n, mem n (omegaV H) ∧ p = kpair H n n := by
  unfold idMap
  rw [(H.repl psiIdF (fun _ => vempty H) (psiIdF_functional H)
    (omegaV H)).choose_spec p]
  constructor
  · rintro ⟨n, hn, hrel⟩
    exact ⟨n, hn, (psiIdF_rel H p n).mp hrel⟩
  · rintro ⟨n, hn, hp⟩
    exact ⟨n, hn, (psiIdF_rel H p n).mpr hp⟩

theorem idMap_isVarMap (H : ZFAxioms mem) : IsVarMap H (idMap H) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro x y y' h1 h2
    obtain ⟨n, _, hk⟩ := (idMap_spec H (kpair H x y)).mp h1
    obtain ⟨n', _, hk'⟩ := (idMap_spec H (kpair H x y')).mp h2
    obtain ⟨hn, hy⟩ := kpair_inj H _ _ _ _ hk
    obtain ⟨hn', hy'⟩ := kpair_inj H _ _ _ _ hk'
    rw [hy, hy', ← hn, ← hn']
  · intro x hx
    exact ⟨x, (idMap_spec H (kpair H x x)).mpr ⟨x, hx, rfl⟩⟩
  · intro p hp
    obtain ⟨n, hn, hk⟩ := (idMap_spec H p).mp hp
    exact ⟨n, n, hn, hk⟩
  · intro n y hk
    obtain ⟨n', hn', hk'⟩ := (idMap_spec H (kpair H n y)).mp hk
    obtain ⟨-, hy⟩ := kpair_inj H _ _ _ _ hk'
    rw [hy]
    exact hn'

theorem idMap_apply (H : ZFAxioms mem) {n : V} (hn : mem n (omegaV H)) :
    applyV H (idMap H) n = n :=
  applyV_eq H (idMap_isVarMap H).1.1 ((idMap_spec H (kpair H n n)).mpr ⟨n, hn, rfl⟩)

/-- **The internal successor map**, the coded counterpart of `Nat.succ`.  It is
the successor image of the identity, so it inherits the interface of
`succVals`. -/
noncomputable def succMap (H : ZFAxioms mem) : V := succVals H (idMap H)

theorem succMap_isVarMap (H : ZFAxioms mem) : IsVarMap H (succMap H) :=
  succVals_isVarMap H (idMap_isVarMap H)

theorem succMap_apply (H : ZFAxioms mem) {n : V} (hn : mem n (omegaV H)) :
    applyV H (succMap H) n = vsucc H n := by
  rw [succMap, succVals_apply H (idMap_isVarMap H) hn, idMap_apply H hn]

/-- **The internal instantiation map** at the index `k`, the coded counterpart
of `inst k`: it sends `0` to `k` and `n+1` to `n`.  The identity
`inst k = scons_nat k id` of `FirstOrder.Fol` is what makes it a shift of the
identity map. -/
noncomputable def instMap (H : ZFAxioms mem) (k : V) : V := econs H k (idMap H)

theorem instMap_isVarMap (H : ZFAxioms mem) {k : V} (hk : mem k (omegaV H)) :
    IsVarMap H (instMap H k) :=
  econs_isEnvOn H (idMap_isVarMap H) hk

theorem instMap_zero (H : ZFAxioms mem) (k : V) :
    applyV H (instMap H k) (vempty H) = k :=
  econs_zero H (idMap_isVarMap H).1.1 k

theorem instMap_succ (H : ZFAxioms mem) (k : V) {n : V}
    (hn : mem n (omegaV H)) : applyV H (instMap H k) (vsucc H n) = n := by
  rw [instMap, econs_succ H (idMap_isVarMap H) k hn, idMap_apply H hn]

/-! ## Composing an environment with a variable map

`compV H e r` is the internal function `n ↦ e (r n)`.  It is the environment
side of the substitution lemma: renaming a code along `r` and evaluating at
`e` is evaluating the original code at `compV H e r`. -/

/-- The graph of `n ↦ ⟨n, e (r n)⟩`, with `e` in parameter slot `2` and `r` in
parameter slot `3`.  Both intermediate values carry a uniqueness clause, so
the relation is functional with no hypothesis on `e` or `r`.

| de Bruijn slot | contents                                     |
| -------------- | -------------------------------------------- |
| `0`            | the index `m = r n`, then the value `v`      |
| `1`            | the output pair `p`, then `m`                |
| `2`            | the input index `n`, then `p`                |
| `3`            | the parameter `e`, then `n`                  |
| `4`            | the parameter `r`, then `e`                  |
-/
def psiCompF : Form :=
  fEx (fAnd (fAnd (fPairMemF 2 0 4) (fAll (fImp (fPairMemF 3 0 5) (fEq 0 1))))
    (fEx (fAnd (fAnd (fPairMemF 1 0 4) (fAll (fImp (fPairMemF 2 0 5) (fEq 0 1))))
      (fKPairF 2 3 0))))

/-- The parameter block of `psiCompF`: the environment, then the map. -/
noncomputable def envComp (H : ZFAxioms mem) (e r : V) : Nat → V :=
  scons e (scons r (fun _ => vempty H))

theorem psiCompF_rel (H : ZFAxioms mem) (e r p n : V) :
    relOf mem psiCompF (envComp H e r) p n ↔
      ∃ m, (mem (kpair H n m) r ∧ ∀ m', mem (kpair H n m') r → m' = m) ∧
        ∃ v, (mem (kpair H m v) e ∧ ∀ v', mem (kpair H m v') e → v' = v) ∧
          p = kpair H n v := by
  unfold relOf psiCompF
  constructor
  · rintro ⟨m, ⟨hm, hmu⟩, v, ⟨hv, hvu⟩, hp⟩
    refine ⟨m, ⟨(fPairMemF_spec H _ 2 0 4).mp hm, fun m' hm' => ?_⟩,
      v, ⟨(fPairMemF_spec H _ 1 0 4).mp hv, fun v' hv' => ?_⟩,
      (fKPairF_spec H _ 2 3 0).mp hp⟩
    · exact hmu m' ((fPairMemF_spec H _ 3 0 5).mpr hm')
    · exact hvu v' ((fPairMemF_spec H _ 2 0 5).mpr hv')
  · rintro ⟨m, ⟨hm, hmu⟩, v, ⟨hv, hvu⟩, hp⟩
    refine ⟨m, ⟨(fPairMemF_spec H _ 2 0 4).mpr hm, fun m' hm' => ?_⟩,
      v, ⟨(fPairMemF_spec H _ 1 0 4).mpr hv, fun v' hv' => ?_⟩,
      (fKPairF_spec H _ 2 3 0).mpr hp⟩
    · exact hmu m' ((fPairMemF_spec H _ 3 0 5).mp hm')
    · exact hvu v' ((fPairMemF_spec H _ 2 0 5).mp hv')

theorem psiCompF_functional (H : ZFAxioms mem) (e r : V) :
    Functional (relOf mem psiCompF (envComp H e r)) := by
  intro n p p' h1 h2
  obtain ⟨m, ⟨_, hmu⟩, v, ⟨_, hvu⟩, hp⟩ := (psiCompF_rel H e r p n).mp h1
  obtain ⟨m', ⟨hm', _⟩, v', ⟨hv', _⟩, hp'⟩ := (psiCompF_rel H e r p' n).mp h2
  have hmm : m' = m := hmu m' hm'
  rw [hmm] at hv'
  rw [hp, hp', hvu v' hv']

/-- The internal composition `n ↦ e (r n)`. -/
noncomputable def compV (H : ZFAxioms mem) (e r : V) : V :=
  (H.repl psiCompF (envComp H e r) (psiCompF_functional H e r) (omegaV H)).choose

theorem compV_spec (H : ZFAxioms mem) (e r p : V) :
    mem p (compV H e r) ↔
      ∃ n, mem n (omegaV H) ∧ ∃ m,
        (mem (kpair H n m) r ∧ ∀ m', mem (kpair H n m') r → m' = m) ∧
        ∃ v, (mem (kpair H m v) e ∧ ∀ v', mem (kpair H m v') e → v' = v) ∧
          p = kpair H n v := by
  unfold compV
  rw [(H.repl psiCompF (envComp H e r) (psiCompF_functional H e r)
    (omegaV H)).choose_spec p]
  constructor
  · rintro ⟨n, hn, hrel⟩
    exact ⟨n, hn, (psiCompF_rel H e r p n).mp hrel⟩
  · rintro ⟨n, hn, hbody⟩
    exact ⟨n, hn, (psiCompF_rel H e r p n).mpr hbody⟩

/-- The description of `compV` with the uniqueness clauses discharged, for a
genuine environment and a genuine variable map. -/
theorem compV_mem (H : ZFAxioms mem) {A e r : V} (he : IsEnvOn H A e)
    (hr : IsVarMap H r) (p : V) :
    mem p (compV H e r) ↔
      ∃ n, mem n (omegaV H) ∧ p = kpair H n (applyV H e (applyV H r n)) := by
  rw [compV_spec H e r p]
  constructor
  · rintro ⟨n, hn, m, ⟨hm, _⟩, v, ⟨hv, _⟩, hp⟩
    have hm' : applyV H r n = m := applyV_eq H (isVarMap_functional H hr) hm
    have hv' : applyV H e m = v := applyV_eq H he.1.1 hv
    exact ⟨n, hn, by rw [hp, hm', hv']⟩
  · rintro ⟨n, hn, hp⟩
    refine ⟨n, hn, applyV H r n,
      ⟨isVarMap_mem H hr hn, fun m' hm' =>
        isVarMap_functional H hr n m' _ hm' (isVarMap_mem H hr hn)⟩,
      applyV H e (applyV H r n),
      ⟨applyV_mem H (he.1.2.1 _ (isVarMap_apply H hr hn)), fun v' hv' =>
        he.1.1 _ v' _ hv'
          (applyV_mem H (he.1.2.1 _ (isVarMap_apply H hr hn)))⟩,
      hp⟩

theorem compV_isEnvOn (H : ZFAxioms mem) {A e r : V} (he : IsEnvOn H A e)
    (hr : IsVarMap H r) : IsEnvOn H A (compV H e r) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro x y y' h1 h2
    obtain ⟨n, _, hk⟩ := (compV_mem H he hr (kpair H x y)).mp h1
    obtain ⟨n', _, hk'⟩ := (compV_mem H he hr (kpair H x y')).mp h2
    obtain ⟨hn, hy⟩ := kpair_inj H _ _ _ _ hk
    obtain ⟨hn', hy'⟩ := kpair_inj H _ _ _ _ hk'
    rw [hy, hy', ← hn, ← hn']
  · intro x hx
    exact ⟨applyV H e (applyV H r x),
      (compV_mem H he hr (kpair H x (applyV H e (applyV H r x)))).mpr ⟨x, hx, rfl⟩⟩
  · intro p hp
    obtain ⟨n, hn, hk⟩ := (compV_mem H he hr p).mp hp
    exact ⟨n, applyV H e (applyV H r n), hn, hk⟩
  · intro n y hk
    obtain ⟨n', hn', hk'⟩ := (compV_mem H he hr (kpair H n y)).mp hk
    obtain ⟨_, hy⟩ := kpair_inj H _ _ _ _ hk'
    rw [hy]
    exact isEnvOn_apply H he (isVarMap_apply H hr hn')

theorem compV_apply (H : ZFAxioms mem) {A e r : V} (he : IsEnvOn H A e)
    (hr : IsVarMap H r) {n : V} (hn : mem n (omegaV H)) :
    applyV H (compV H e r) n = applyV H e (applyV H r n) :=
  applyV_eq H (compV_isEnvOn H he hr).1.1
    ((compV_mem H he hr (kpair H n (applyV H e (applyV H r n)))).mpr ⟨n, hn, rfl⟩)

/-! ### The three composition identities

Each is an equation between internal functions on the internal omega, proved
by `funOn_ext` after the case split `nat_zero_or_succ`. -/

/-- **The binder identity.**  Composing a shifted environment with a shifted
variable map is the shift of the composition.  This is the equation the two
quantifier cases of the substitution lemma turn on. -/
theorem compV_econs_upV (H : ZFAxioms mem) {A e r d : V} (he : IsEnvOn H A e)
    (hr : IsVarMap H r) (hd : mem d A) :
    compV H (econs H d e) (upV H r) = econs H d (compV H e r) := by
  refine funOn_ext H (compV_isEnvOn H (econs_isEnvOn H he hd) (upV_isVarMap H hr)).1
    (econs_isEnvOn H (compV_isEnvOn H he hr) hd).1 (fun n hn => ?_)
  rcases nat_zero_or_succ H n hn with rfl | ⟨m, hm, rfl⟩
  · rw [compV_apply H (econs_isEnvOn H he hd) (upV_isVarMap H hr)
        (vempty_in_omega H), upV_zero H hr,
      econs_zero H he.1.1 d, econs_zero H (compV_isEnvOn H he hr).1.1 d]
  · rw [compV_apply H (econs_isEnvOn H he hd) (upV_isVarMap H hr)
        (omega_succ H m hm), upV_succ H hr hm,
      econs_succ H he d (isVarMap_apply H hr hm),
      econs_succ H (compV_isEnvOn H he hr) d hm,
      compV_apply H he hr hm]

/-- **The shift identity.**  Composing a shifted environment with the internal
successor map discards the new slot. -/
theorem compV_succMap (H : ZFAxioms mem) {A e d : V} (he : IsEnvOn H A e)
    (hd : mem d A) : compV H (econs H d e) (succMap H) = e := by
  refine funOn_ext H
    (compV_isEnvOn H (econs_isEnvOn H he hd) (succMap_isVarMap H)).1 he.1
    (fun n hn => ?_)
  rw [compV_apply H (econs_isEnvOn H he hd) (succMap_isVarMap H) hn,
      succMap_apply H hn, econs_succ H he d hn]

/-- **The instantiation identity.**  Composing an environment with the internal
instantiation map at `k` is the shift of that environment by its own value at
`k`. -/
theorem compV_instMap (H : ZFAxioms mem) {A e k : V} (he : IsEnvOn H A e)
    (hk : mem k (omegaV H)) :
    compV H e (instMap H k) = econs H (applyV H e k) e := by
  refine funOn_ext H (compV_isEnvOn H he (instMap_isVarMap H hk)).1
    (econs_isEnvOn H he (isEnvOn_apply H he hk)).1 (fun n hn => ?_)
  rcases nat_zero_or_succ H n hn with rfl | ⟨m, hm, rfl⟩
  · rw [compV_apply H he (instMap_isVarMap H hk) (vempty_in_omega H),
        instMap_zero H k, econs_zero H he.1.1 (applyV H e k)]
  · rw [compV_apply H he (instMap_isVarMap H hk) (omega_succ H m hm),
        instMap_succ H k hm, econs_succ H he (applyV H e k) hm]

/-! ## The renaming graph, by certificates

A renaming triple is `⟨r, ⟨c, c'⟩⟩`: a variable map, a code, and the code it
renames to.  That is literally the shape of `satTriple`, so the triple is
written with `satTriple H r c c'` and the object-language macro `fTripleMemF`
of `BoundedZFCConsistency.InternalSat` reads it unchanged.  The shape is
shared, the meaning is not; nothing below mixes the two uses. -/

/-- The triple `⟨r, c, c'⟩` is justified by the renaming triples recorded in
`S`, by one of the eight clauses of the module header.  Like `Justified`, the
relation is *local*: it never mentions the renaming relation, only membership
in `S`. -/
def RenStep (H : ZFAxioms mem) (S r c c' : V) : Prop :=
  (∃ i j, mem i (omegaV H) ∧ mem j (omegaV H) ∧
      c = kpair H (natV H 0) (kpair H i j) ∧
      c' = kpair H (natV H 0)
        (kpair H (applyV H r i) (applyV H r j))) ∨
  (∃ i j, mem i (omegaV H) ∧ mem j (omegaV H) ∧
      c = kpair H (natV H 1) (kpair H i j) ∧
      c' = kpair H (natV H 1)
        (kpair H (applyV H r i) (applyV H r j))) ∨
  (c = kpair H (natV H 2) (vempty H) ∧ c' = kpair H (natV H 2) (vempty H)) ∨
  (∃ a b a' b', c = kpair H (natV H 3) (kpair H a b) ∧
      c' = kpair H (natV H 3) (kpair H a' b') ∧
      mem (satTriple H r a a') S ∧ mem (satTriple H r b b') S) ∨
  (∃ a b a' b', c = kpair H (natV H 4) (kpair H a b) ∧
      c' = kpair H (natV H 4) (kpair H a' b') ∧
      mem (satTriple H r a a') S ∧ mem (satTriple H r b b') S) ∨
  (∃ a b a' b', c = kpair H (natV H 5) (kpair H a b) ∧
      c' = kpair H (natV H 5) (kpair H a' b') ∧
      mem (satTriple H r a a') S ∧ mem (satTriple H r b b') S) ∨
  (∃ a a', c = kpair H (natV H 6) a ∧ c' = kpair H (natV H 6) a' ∧
      mem (satTriple H (upV H r) a a') S) ∨
  (∃ a a', c = kpair H (natV H 7) a ∧ c' = kpair H (natV H 7) a' ∧
      mem (satTriple H (upV H r) a a') S)

/-- Every clause is positive in the set of established triples, so the step is
monotone.  This is what lets certificates be combined by union. -/
theorem renStep_mono (H : ZFAxioms mem) {S S' r c c' : V} (hsub : Sub mem S S')
    (h : RenStep H S r c c') : RenStep H S' r c c' := by
  unfold RenStep at h ⊢
  rcases h with h | h | h | ⟨a, b, a', b', h1, h2, m1, m2⟩ |
    ⟨a, b, a', b', h1, h2, m1, m2⟩ | ⟨a, b, a', b', h1, h2, m1, m2⟩ |
    ⟨a, a', h1, h2, m⟩ | ⟨a, a', h1, h2, m⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨a, b, a', b', h1, h2, hsub _ m1, hsub _ m2⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨a, b, a', b', h1, h2, hsub _ m1, hsub _ m2⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨a, b, a', b', h1, h2, hsub _ m1, hsub _ m2⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨a, a', h1, h2, hsub _ m⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨a, a', h1, h2, hsub _ m⟩))))))

/-- Every triple of `S` is justified by `S`, over genuine variable maps.  The
variable-map clause plays the role the environment clause plays in
`SatClosed`: without it the object-language reading of `applyV` in the atomic
clauses is unavailable, so `fRenClosedF` could not have an unconditional
satisfaction spec. -/
def RenClosed (H : ZFAxioms mem) (S : V) : Prop :=
  ∀ r c c', mem (satTriple H r c c') S → (IsVarMap H r ∧ RenStep H S r c c')

theorem renClosed_empty (H : ZFAxioms mem) : RenClosed H (vempty H) :=
  fun _ _ _ h => absurd h (vempty_spec H _)

theorem renClosed_cup (H : ZFAxioms mem) {S1 S2 : V} (h1 : RenClosed H S1)
    (h2 : RenClosed H S2) : RenClosed H (vcup H S1 S2) := by
  intro r c c' hmem
  rcases (vcup_spec H S1 S2 _).mp hmem with h | h
  · exact ⟨(h1 r c c' h).1,
      renStep_mono H (fun x hx => (vcup_spec H S1 S2 x).mpr (Or.inl hx))
        (h1 r c c' h).2⟩
  · exact ⟨(h2 r c c' h).1,
      renStep_mono H (fun x hx => (vcup_spec H S1 S2 x).mpr (Or.inr hx))
        (h2 r c c' h).2⟩

/-- Adjoining a single justified triple keeps a set closed.  Unlike the
satisfaction certificates, which had to be extended by a whole Replacement
image of triples indexed by the carrier, one new element always suffices
here: no clause of `RenStep` quantifies over a carrier. -/
theorem renClosed_insert (H : ZFAxioms mem) {S r c c' : V} (hS : RenClosed H S)
    (hr : IsVarMap H r) (hstep : RenStep H S r c c') :
    RenClosed H (vcup H S (vsingle H (satTriple H r c c'))) := by
  have hsub : Sub mem S (vcup H S (vsingle H (satTriple H r c c'))) :=
    fun x hx => (vcup_spec H _ _ x).mpr (Or.inl hx)
  intro s d d' hmem
  rcases (vcup_spec H S (vsingle H (satTriple H r c c')) _).mp hmem with h | h
  · exact ⟨(hS s d d' h).1, renStep_mono H hsub (hS s d d' h).2⟩
  · obtain ⟨e1, e2, e3⟩ :=
      satTriple_inj H ((vsingle_spec H (satTriple H r c c') _).mp h)
    rw [e1, e2, e3]
    exact ⟨hr, renStep_mono H hsub hstep⟩

/-- `S` is a **renaming certificate** for `⟨r, c, c'⟩`. -/
structure RenCertifies (H : ZFAxioms mem) (S r c c' : V) : Prop where
  /-- Every triple of the certificate is justified by the certificate. -/
  closed : RenClosed H S
  /-- The triple in question is recorded. -/
  holds : mem (satTriple H r c c') S

/-- **`c'` is the renaming of `c` along the variable map `r`**: some closed set
records the triple. -/
def Renames (H : ZFAxioms mem) (r c c' : V) : Prop :=
  ∃ S, RenCertifies H S r c c'

theorem Renames.isVarMap (H : ZFAxioms mem) {r c c' : V}
    (h : Renames H r c c') : IsVarMap H r := by
  obtain ⟨S, hS, hmem⟩ := h
  exact (hS r c c' hmem).1

/-- A justified triple over a closed set can always be adjoined, which is the
only way the introduction rules below build certificates. -/
theorem renames_of_step (H : ZFAxioms mem) {S r c c' : V} (hS : RenClosed H S)
    (hr : IsVarMap H r) (hstep : RenStep H S r c c') : Renames H r c c' :=
  ⟨vcup H S (vsingle H (satTriple H r c c')),
    renClosed_insert H hS hr hstep,
    (vcup_spec H _ _ _).mpr (Or.inr ((vsingle_spec H _ _).mpr rfl))⟩

/-! ### The introduction rules -/

theorem renames_memAtom (H : ZFAxioms mem) {r i j : V} (hr : IsVarMap H r)
    (hi : mem i (omegaV H)) (hj : mem j (omegaV H)) :
    Renames H r (kpair H (natV H 0) (kpair H i j))
      (kpair H (natV H 0) (kpair H (applyV H r i) (applyV H r j))) := by
  refine renames_of_step H (renClosed_empty H) hr ?_
  unfold RenStep
  exact Or.inl ⟨i, j, hi, hj, rfl, rfl⟩

theorem renames_eqAtom (H : ZFAxioms mem) {r i j : V} (hr : IsVarMap H r)
    (hi : mem i (omegaV H)) (hj : mem j (omegaV H)) :
    Renames H r (kpair H (natV H 1) (kpair H i j))
      (kpair H (natV H 1) (kpair H (applyV H r i) (applyV H r j))) := by
  refine renames_of_step H (renClosed_empty H) hr ?_
  unfold RenStep
  exact Or.inr (Or.inl ⟨i, j, hi, hj, rfl, rfl⟩)

theorem renames_bot (H : ZFAxioms mem) {r : V} (hr : IsVarMap H r) :
    Renames H r (kpair H (natV H 2) (vempty H))
      (kpair H (natV H 2) (vempty H)) := by
  refine renames_of_step H (renClosed_empty H) hr ?_
  unfold RenStep
  exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))

theorem renames_imp (H : ZFAxioms mem) {r a b a' b' : V} (hr : IsVarMap H r)
    (h1 : Renames H r a a') (h2 : Renames H r b b') :
    Renames H r (kpair H (natV H 3) (kpair H a b))
      (kpair H (natV H 3) (kpair H a' b')) := by
  obtain ⟨S1, hS1, k1⟩ := h1
  obtain ⟨S2, hS2, k2⟩ := h2
  refine renames_of_step H (renClosed_cup H hS1 hS2) hr ?_
  unfold RenStep
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, a', b', rfl, rfl,
    (vcup_spec H S1 S2 _).mpr (Or.inl k1),
    (vcup_spec H S1 S2 _).mpr (Or.inr k2)⟩)))

theorem renames_and (H : ZFAxioms mem) {r a b a' b' : V} (hr : IsVarMap H r)
    (h1 : Renames H r a a') (h2 : Renames H r b b') :
    Renames H r (kpair H (natV H 4) (kpair H a b))
      (kpair H (natV H 4) (kpair H a' b')) := by
  obtain ⟨S1, hS1, k1⟩ := h1
  obtain ⟨S2, hS2, k2⟩ := h2
  refine renames_of_step H (renClosed_cup H hS1 hS2) hr ?_
  unfold RenStep
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, a', b', rfl, rfl,
    (vcup_spec H S1 S2 _).mpr (Or.inl k1),
    (vcup_spec H S1 S2 _).mpr (Or.inr k2)⟩))))

theorem renames_or (H : ZFAxioms mem) {r a b a' b' : V} (hr : IsVarMap H r)
    (h1 : Renames H r a a') (h2 : Renames H r b b') :
    Renames H r (kpair H (natV H 5) (kpair H a b))
      (kpair H (natV H 5) (kpair H a' b')) := by
  obtain ⟨S1, hS1, k1⟩ := h1
  obtain ⟨S2, hS2, k2⟩ := h2
  refine renames_of_step H (renClosed_cup H hS1 hS2) hr ?_
  unfold RenStep
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨a, b, a', b', rfl, rfl,
      (vcup_spec H S1 S2 _).mpr (Or.inl k1),
      (vcup_spec H S1 S2 _).mpr (Or.inr k2)⟩)))))

theorem renames_all (H : ZFAxioms mem) {r a a' : V} (hr : IsVarMap H r)
    (h : Renames H (upV H r) a a') :
    Renames H r (kpair H (natV H 6) a) (kpair H (natV H 6) a') := by
  obtain ⟨S, hS, k⟩ := h
  refine renames_of_step H hS hr ?_
  unfold RenStep
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨a, a', rfl, rfl, k⟩))))))

theorem renames_ex (H : ZFAxioms mem) {r a a' : V} (hr : IsVarMap H r)
    (h : Renames H (upV H r) a a') :
    Renames H r (kpair H (natV H 7) a) (kpair H (natV H 7) a') := by
  obtain ⟨S, hS, k⟩ := h
  refine renames_of_step H hS hr ?_
  unfold RenStep
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨a, a', rfl, rfl, k⟩))))))

/-! ### Inverting the step at a known tag

Codes carrying different tags are different sets, so at a code of known shape
exactly one of the eight clauses can apply.  Each lemma discards the other
seven by `formCode_tag_ne` and reads off the surviving one; this is the
inversion that the intersection presentation could not have supplied. -/

theorem renStep_memAtom (H : ZFAxioms mem) {S r i j c' : V}
    (h : RenStep H S r (kpair H (natV H 0) (kpair H i j)) c') :
    c' = kpair H (natV H 0)
      (kpair H (applyV H r i) (applyV H r j)) := by
  unfold RenStep at h
  rcases h with ⟨_, _, _, _, hc, hd⟩ | ⟨_, _, _, _, hc, _⟩ | ⟨hc, _⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩ | ⟨_, _, _, _, hc, _, _, _⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩ | ⟨_, _, hc, _, _⟩ | ⟨_, _, hc, _, _⟩
  · obtain ⟨-, hp⟩ := kpair_inj H _ _ _ _ hc
    obtain ⟨hi, hj⟩ := kpair_inj H _ _ _ _ hp
    rw [hd, hi, hj]
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)

theorem renStep_eqAtom (H : ZFAxioms mem) {S r i j c' : V}
    (h : RenStep H S r (kpair H (natV H 1) (kpair H i j)) c') :
    c' = kpair H (natV H 1)
      (kpair H (applyV H r i) (applyV H r j)) := by
  unfold RenStep at h
  rcases h with ⟨_, _, _, _, hc, _⟩ | ⟨_, _, _, _, hc, hd⟩ | ⟨hc, _⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩ | ⟨_, _, _, _, hc, _, _, _⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩ | ⟨_, _, hc, _, _⟩ | ⟨_, _, hc, _, _⟩
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · obtain ⟨-, hp⟩ := kpair_inj H _ _ _ _ hc
    obtain ⟨hi, hj⟩ := kpair_inj H _ _ _ _ hp
    rw [hd, hi, hj]
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)

theorem renStep_bot (H : ZFAxioms mem) {S r c' : V}
    (h : RenStep H S r (kpair H (natV H 2) (vempty H)) c') :
    c' = kpair H (natV H 2) (vempty H) := by
  unfold RenStep at h
  rcases h with ⟨_, _, _, _, hc, _⟩ | ⟨_, _, _, _, hc, _⟩ | ⟨hc, hd⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩ | ⟨_, _, _, _, hc, _, _, _⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩ | ⟨_, _, hc, _, _⟩ | ⟨_, _, hc, _, _⟩
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact hd
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)

theorem renStep_imp (H : ZFAxioms mem) {S r a b c' : V}
    (h : RenStep H S r (kpair H (natV H 3) (kpair H a b)) c') :
    ∃ a' b', c' = kpair H (natV H 3) (kpair H a' b') ∧
      mem (satTriple H r a a') S ∧ mem (satTriple H r b b') S := by
  unfold RenStep at h
  rcases h with ⟨_, _, _, _, hc, _⟩ | ⟨_, _, _, _, hc, _⟩ | ⟨hc, _⟩ |
    ⟨x, y, x', y', hc, hd, m1, m2⟩ | ⟨_, _, _, _, hc, _, _, _⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩ | ⟨_, _, hc, _, _⟩ | ⟨_, _, hc, _, _⟩
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · obtain ⟨-, hp⟩ := kpair_inj H _ _ _ _ hc
    obtain ⟨h1, h2⟩ := kpair_inj H _ _ _ _ hp
    refine ⟨x', y', hd, ?_, ?_⟩
    · rw [h1]; exact m1
    · rw [h2]; exact m2
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)

theorem renStep_and (H : ZFAxioms mem) {S r a b c' : V}
    (h : RenStep H S r (kpair H (natV H 4) (kpair H a b)) c') :
    ∃ a' b', c' = kpair H (natV H 4) (kpair H a' b') ∧
      mem (satTriple H r a a') S ∧ mem (satTriple H r b b') S := by
  unfold RenStep at h
  rcases h with ⟨_, _, _, _, hc, _⟩ | ⟨_, _, _, _, hc, _⟩ | ⟨hc, _⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩ | ⟨x, y, x', y', hc, hd, m1, m2⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩ | ⟨_, _, hc, _, _⟩ | ⟨_, _, hc, _, _⟩
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · obtain ⟨-, hp⟩ := kpair_inj H _ _ _ _ hc
    obtain ⟨h1, h2⟩ := kpair_inj H _ _ _ _ hp
    refine ⟨x', y', hd, ?_, ?_⟩
    · rw [h1]; exact m1
    · rw [h2]; exact m2
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)

theorem renStep_or (H : ZFAxioms mem) {S r a b c' : V}
    (h : RenStep H S r (kpair H (natV H 5) (kpair H a b)) c') :
    ∃ a' b', c' = kpair H (natV H 5) (kpair H a' b') ∧
      mem (satTriple H r a a') S ∧ mem (satTriple H r b b') S := by
  unfold RenStep at h
  rcases h with ⟨_, _, _, _, hc, _⟩ | ⟨_, _, _, _, hc, _⟩ | ⟨hc, _⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩ | ⟨_, _, _, _, hc, _, _, _⟩ |
    ⟨x, y, x', y', hc, hd, m1, m2⟩ | ⟨_, _, hc, _, _⟩ | ⟨_, _, hc, _, _⟩
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · obtain ⟨-, hp⟩ := kpair_inj H _ _ _ _ hc
    obtain ⟨h1, h2⟩ := kpair_inj H _ _ _ _ hp
    refine ⟨x', y', hd, ?_, ?_⟩
    · rw [h1]; exact m1
    · rw [h2]; exact m2
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)

theorem renStep_all (H : ZFAxioms mem) {S r a c' : V}
    (h : RenStep H S r (kpair H (natV H 6) a) c') :
    ∃ a', c' = kpair H (natV H 6) a' ∧
      mem (satTriple H (upV H r) a a') S := by
  unfold RenStep at h
  rcases h with ⟨_, _, _, _, hc, _⟩ | ⟨_, _, _, _, hc, _⟩ | ⟨hc, _⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩ | ⟨_, _, _, _, hc, _, _, _⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩ | ⟨x, x', hc, hd, m⟩ | ⟨_, _, hc, _, _⟩
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · obtain ⟨-, h1⟩ := kpair_inj H _ _ _ _ hc
    exact ⟨x', hd, by rw [h1]; exact m⟩
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)

theorem renStep_ex (H : ZFAxioms mem) {S r a c' : V}
    (h : RenStep H S r (kpair H (natV H 7) a) c') :
    ∃ a', c' = kpair H (natV H 7) a' ∧
      mem (satTriple H (upV H r) a a') S := by
  unfold RenStep at h
  rcases h with ⟨_, _, _, _, hc, _⟩ | ⟨_, _, _, _, hc, _⟩ | ⟨hc, _⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩ | ⟨_, _, _, _, hc, _, _, _⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩ | ⟨_, _, hc, _, _⟩ | ⟨x, x', hc, hd, m⟩
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · obtain ⟨-, h1⟩ := kpair_inj H _ _ _ _ hc
    exact ⟨x', hd, by rw [h1]; exact m⟩

/-! ### The inversion rules for `Renames` -/

theorem renames_memAtom_inv (H : ZFAxioms mem) {r i j c' : V}
    (h : Renames H r (kpair H (natV H 0) (kpair H i j)) c') :
    c' = kpair H (natV H 0)
      (kpair H (applyV H r i) (applyV H r j)) := by
  obtain ⟨S, hS, hmem⟩ := h
  exact renStep_memAtom H (hS _ _ _ hmem).2

theorem renames_eqAtom_inv (H : ZFAxioms mem) {r i j c' : V}
    (h : Renames H r (kpair H (natV H 1) (kpair H i j)) c') :
    c' = kpair H (natV H 1)
      (kpair H (applyV H r i) (applyV H r j)) := by
  obtain ⟨S, hS, hmem⟩ := h
  exact renStep_eqAtom H (hS _ _ _ hmem).2

theorem renames_bot_inv (H : ZFAxioms mem) {r c' : V}
    (h : Renames H r (kpair H (natV H 2) (vempty H)) c') :
    c' = kpair H (natV H 2) (vempty H) := by
  obtain ⟨S, hS, hmem⟩ := h
  exact renStep_bot H (hS _ _ _ hmem).2

theorem renames_imp_inv (H : ZFAxioms mem) {r a b c' : V}
    (h : Renames H r (kpair H (natV H 3) (kpair H a b)) c') :
    ∃ a' b', c' = kpair H (natV H 3) (kpair H a' b') ∧
      Renames H r a a' ∧ Renames H r b b' := by
  obtain ⟨S, hS, hmem⟩ := h
  obtain ⟨a', b', hd, m1, m2⟩ := renStep_imp H (hS _ _ _ hmem).2
  exact ⟨a', b', hd, ⟨S, hS, m1⟩, ⟨S, hS, m2⟩⟩

theorem renames_and_inv (H : ZFAxioms mem) {r a b c' : V}
    (h : Renames H r (kpair H (natV H 4) (kpair H a b)) c') :
    ∃ a' b', c' = kpair H (natV H 4) (kpair H a' b') ∧
      Renames H r a a' ∧ Renames H r b b' := by
  obtain ⟨S, hS, hmem⟩ := h
  obtain ⟨a', b', hd, m1, m2⟩ := renStep_and H (hS _ _ _ hmem).2
  exact ⟨a', b', hd, ⟨S, hS, m1⟩, ⟨S, hS, m2⟩⟩

theorem renames_or_inv (H : ZFAxioms mem) {r a b c' : V}
    (h : Renames H r (kpair H (natV H 5) (kpair H a b)) c') :
    ∃ a' b', c' = kpair H (natV H 5) (kpair H a' b') ∧
      Renames H r a a' ∧ Renames H r b b' := by
  obtain ⟨S, hS, hmem⟩ := h
  obtain ⟨a', b', hd, m1, m2⟩ := renStep_or H (hS _ _ _ hmem).2
  exact ⟨a', b', hd, ⟨S, hS, m1⟩, ⟨S, hS, m2⟩⟩

theorem renames_all_inv (H : ZFAxioms mem) {r a c' : V}
    (h : Renames H r (kpair H (natV H 6) a) c') :
    ∃ a', c' = kpair H (natV H 6) a' ∧ Renames H (upV H r) a a' := by
  obtain ⟨S, hS, hmem⟩ := h
  obtain ⟨a', hd, m⟩ := renStep_all H (hS _ _ _ hmem).2
  exact ⟨a', hd, ⟨S, hS, m⟩⟩

theorem renames_ex_inv (H : ZFAxioms mem) {r a c' : V}
    (h : Renames H r (kpair H (natV H 7) a) c') :
    ∃ a', c' = kpair H (natV H 7) a' ∧ Renames H (upV H r) a a' := by
  obtain ⟨S, hS, hmem⟩ := h
  obtain ⟨a', hd, m⟩ := renStep_ex H (hS _ _ _ hmem).2
  exact ⟨a', hd, ⟨S, hS, m⟩⟩

/-! ## The renaming relation as a `Form`

Everything from here on has to be readable inside the object language, because
the induction principle `isFormCodeSem_ind'` takes its property as a formula
with parameters.  The macros follow the house style: absolute slots at the use
site, a table of the binders each macro introduces, and an exact satisfaction
spec.  The only hypotheses any spec carries are single-valuedness facts, which
is what the object-language reading of `applyV` and of `econs` needs. -/

/-- "slot `i` is the successor image of the variable map in slot `r_i`".

| de Bruijn slot | contents                                     |
| -------------- | -------------------------------------------- |
| `0`            | the candidate element `p`                    |
| `1`            | the index `n`, under one further binder      |
| `2`, `3`       | the value `y`, then the successor `s`        |
| `m+1` … `m+4`  | the caller's slot `m` under 1 … 4 binders    |
-/
def fSuccValsF (i r_i : Nat) : Form :=
  fSetByF i
    (fEx (fAnd (fNatF 0)
      (fEx (fAnd (fPairMemF 1 0 (r_i+3))
        (fEx (fAnd (fSuccF 0 1) (fKPairF 3 2 0)))))))

theorem fSuccValsF_spec (H : ZFAxioms mem) (ee : Nat → V) (i r_i : Nat)
    (hr : IsVarMap H (ee r_i)) :
    Sat mem ee (fSuccValsF i r_i) ↔ ee i = succVals H (ee r_i) := by
  refine fSetByF_spec H ee i _ (succVals H (ee r_i)) (fun p => ?_)
  rw [succVals_mem H hr p]
  constructor
  · rintro ⟨n, hn, y, hy, s, hs, hp⟩
    refine ⟨n, (fNatF_spec H (scons n (scons p ee)) 0).mp hn, ?_⟩
    have hy' : mem (kpair H n y) (ee r_i) :=
      (fPairMemF_spec H (scons y (scons n (scons p ee))) 1 0 (r_i+3)).mp hy
    have hs' : s = vsucc H y :=
      (fSuccF_spec H (scons s (scons y (scons n (scons p ee)))) 0 1).mp hs
    have hp' : p = kpair H n s :=
      (fKPairF_spec H (scons s (scons y (scons n (scons p ee)))) 3 2 0).mp hp
    rw [hp', hs', applyV_eq H (isVarMap_functional H hr) hy']
  · rintro ⟨n, hn, hp⟩
    exact ⟨n, (fNatF_spec H (scons n (scons p ee)) 0).mpr hn,
      applyV H (ee r_i) n,
      (fPairMemF_spec H (scons (applyV H (ee r_i) n) (scons n (scons p ee)))
        1 0 (r_i+3)).mpr (isVarMap_mem H hr hn),
      vsucc H (applyV H (ee r_i) n),
      (fSuccF_spec H (scons (vsucc H (applyV H (ee r_i) n))
        (scons (applyV H (ee r_i) n) (scons n (scons p ee)))) 0 1).mpr rfl,
      (fKPairF_spec H (scons (vsucc H (applyV H (ee r_i) n))
        (scons (applyV H (ee r_i) n) (scons n (scons p ee)))) 3 2 0).mpr hp⟩

/-- "slot `i` is the binder shift of the variable map in slot `r_i`".

| de Bruijn slot | contents                          |
| -------------- | --------------------------------- |
| `0`            | the successor image, then `∅`     |
| `1`            | the successor image               |
| `m+2`          | the caller's slot `m`             |
-/
def fUpF (i r_i : Nat) : Form :=
  fEx (fAnd (fSuccValsF 0 (r_i+1))
    (fEx (fAnd (fEmptyF 0) (fEconsF (i+2) 0 1))))

theorem fUpF_spec (H : ZFAxioms mem) (ee : Nat → V) (i r_i : Nat)
    (hr : IsVarMap H (ee r_i)) :
    Sat mem ee (fUpF i r_i) ↔ ee i = upV H (ee r_i) := by
  constructor
  · rintro ⟨sv, hsv, z, hz, hi⟩
    have hsv' : sv = succVals H (ee r_i) :=
      (fSuccValsF_spec H (scons sv ee) 0 (r_i+1) hr).mp hsv
    have hz' : z = vempty H :=
      (fEmptyF_spec H (scons z (scons sv ee)) 0).mp hz
    have hfun : ∀ x y y', mem (kpair H x y) sv → mem (kpair H x y') sv →
        y = y' := by
      rw [hsv']; exact (succVals_isVarMap H hr).1.1
    have hi' : ee i = econs H z sv :=
      (fEconsF_spec H (scons z (scons sv ee)) (i+2) 0 1 hfun).mp hi
    rw [upV, hi', hz', hsv']
  · intro h
    have hfun : ∀ x y y', mem (kpair H x y) (succVals H (ee r_i)) →
        mem (kpair H x y') (succVals H (ee r_i)) → y = y' :=
      (succVals_isVarMap H hr).1.1
    exact ⟨succVals H (ee r_i),
      (fSuccValsF_spec H (scons (succVals H (ee r_i)) ee) 0 (r_i+1) hr).mpr rfl,
      vempty H,
      (fEmptyF_spec H
        (scons (vempty H) (scons (succVals H (ee r_i)) ee)) 0).mpr rfl,
      (fEconsF_spec H (scons (vempty H) (scons (succVals H (ee r_i)) ee))
        (i+2) 0 1 hfun).mpr (by
          show ee i = econs H (vempty H) (succVals H (ee r_i))
          rw [h, upV])⟩

/-- An atomic renaming clause with tag `t`: both indices are internal naturals
and both are transported along the variable map.

| de Bruijn slot | contents                                     |
| -------------- | -------------------------------------------- |
| `0`            | the second index `j`, then the value `v`     |
| `1`            | the first index `i`, then the value `u`      |
| `2`, `3`       | under the inner binders: `j`, then `i`       |
| `m+2`, `m+4`   | the caller's slot `m`                        |
-/
def fRenAtomF (c_i d_i r_i t : Nat) : Form :=
  fEx (fEx (fAnd (fAnd (fNatF 1) (fNatF 0))
    (fAnd (fTagPairF (c_i+2) t 1 0)
      (fEx (fEx (fAnd (fAnd (fPairMemF 3 1 (r_i+4)) (fPairMemF 2 0 (r_i+4)))
        (fTagPairF (d_i+4) t 1 0)))))))

theorem fRenAtomF_spec (H : ZFAxioms mem) (ee : Nat → V) (c_i d_i r_i t : Nat)
    (hr : IsVarMap H (ee r_i)) :
    Sat mem ee (fRenAtomF c_i d_i r_i t) ↔
      ∃ i j, mem i (omegaV H) ∧ mem j (omegaV H) ∧
        ee c_i = kpair H (natV H t) (kpair H i j) ∧
        ee d_i = kpair H (natV H t)
          (kpair H (applyV H (ee r_i) i) (applyV H (ee r_i) j)) := by
  constructor
  · rintro ⟨i, j, ⟨hi, hj⟩, hc, u, v, ⟨hu, hv⟩, hd⟩
    refine ⟨i, j, (fNatF_spec H (scons j (scons i ee)) 1).mp hi,
      (fNatF_spec H (scons j (scons i ee)) 0).mp hj,
      (fTagPairF_spec H (scons j (scons i ee)) (c_i+2) t 1 0).mp hc, ?_⟩
    have hu' : applyV H (ee r_i) i = u :=
      applyV_eq H (isVarMap_functional H hr)
        ((fPairMemF_spec H (scons v (scons u (scons j (scons i ee))))
          3 1 (r_i+4)).mp hu)
    have hv' : applyV H (ee r_i) j = v :=
      applyV_eq H (isVarMap_functional H hr)
        ((fPairMemF_spec H (scons v (scons u (scons j (scons i ee))))
          2 0 (r_i+4)).mp hv)
    rw [hu', hv']
    exact (fTagPairF_spec H (scons v (scons u (scons j (scons i ee))))
      (d_i+4) t 1 0).mp hd
  · rintro ⟨i, j, hi, hj, hc, hd⟩
    exact ⟨i, j, ⟨(fNatF_spec H (scons j (scons i ee)) 1).mpr hi,
      (fNatF_spec H (scons j (scons i ee)) 0).mpr hj⟩,
      (fTagPairF_spec H (scons j (scons i ee)) (c_i+2) t 1 0).mpr hc,
      applyV H (ee r_i) i, applyV H (ee r_i) j,
      ⟨(fPairMemF_spec H (scons (applyV H (ee r_i) j)
          (scons (applyV H (ee r_i) i) (scons j (scons i ee))))
          3 1 (r_i+4)).mpr (isVarMap_mem H hr hi),
       (fPairMemF_spec H (scons (applyV H (ee r_i) j)
          (scons (applyV H (ee r_i) i) (scons j (scons i ee))))
          2 0 (r_i+4)).mpr (isVarMap_mem H hr hj)⟩,
      (fTagPairF_spec H (scons (applyV H (ee r_i) j)
        (scons (applyV H (ee r_i) i) (scons j (scons i ee))))
        (d_i+4) t 1 0).mpr hd⟩

/-- A binary renaming clause with tag `t`: both subcodes are renamed along the
same map, and both sub-triples are already recorded.

| de Bruijn slot | contents                      |
| -------------- | ----------------------------- |
| `0`            | the second renamed part `b'`  |
| `1`            | the first renamed part `a'`   |
| `2`            | the second part `b`           |
| `3`            | the first part `a`            |
| `m+4`          | the caller's slot `m`         |
-/
def fRenBinF (c_i d_i r_i s_i t : Nat) : Form :=
  fEx (fEx (fEx (fEx (fAnd (fTagPairF (c_i+4) t 3 2)
    (fAnd (fTagPairF (d_i+4) t 1 0)
      (fAnd (fTripleMemF (r_i+4) 3 1 (s_i+4))
            (fTripleMemF (r_i+4) 2 0 (s_i+4))))))))

theorem fRenBinF_spec (H : ZFAxioms mem) (ee : Nat → V)
    (c_i d_i r_i s_i t : Nat) :
    Sat mem ee (fRenBinF c_i d_i r_i s_i t) ↔
      ∃ a b a' b', ee c_i = kpair H (natV H t) (kpair H a b) ∧
        ee d_i = kpair H (natV H t) (kpair H a' b') ∧
        mem (satTriple H (ee r_i) a a') (ee s_i) ∧
        mem (satTriple H (ee r_i) b b') (ee s_i) := by
  constructor
  · rintro ⟨a, b, a', b', hc, hd, m1, m2⟩
    exact ⟨a, b, a', b',
      (fTagPairF_spec H _ (c_i+4) t 3 2).mp hc,
      (fTagPairF_spec H _ (d_i+4) t 1 0).mp hd,
      (fTripleMemF_spec H _ (r_i+4) 3 1 (s_i+4)).mp m1,
      (fTripleMemF_spec H _ (r_i+4) 2 0 (s_i+4)).mp m2⟩
  · rintro ⟨a, b, a', b', hc, hd, m1, m2⟩
    exact ⟨a, b, a', b',
      (fTagPairF_spec H _ (c_i+4) t 3 2).mpr hc,
      (fTagPairF_spec H _ (d_i+4) t 1 0).mpr hd,
      (fTripleMemF_spec H _ (r_i+4) 3 1 (s_i+4)).mpr m1,
      (fTripleMemF_spec H _ (r_i+4) 2 0 (s_i+4)).mpr m2⟩

/-- A quantifier renaming clause with tag `t`: the body is renamed along the
binder shift of the map.

| de Bruijn slot | contents                      |
| -------------- | ----------------------------- |
| `0`            | the renamed body `a'`, then the shifted map |
| `1`            | the body `a`, then `a'`       |
| `2`            | under the innermost binder: `a` |
| `m+2`, `m+3`   | the caller's slot `m`         |
-/
def fRenQuantF (c_i d_i r_i s_i t : Nat) : Form :=
  fEx (fEx (fAnd (fTagUnF (c_i+2) t 1)
    (fAnd (fTagUnF (d_i+2) t 0)
      (fEx (fAnd (fUpF 0 (r_i+3)) (fTripleMemF 0 2 1 (s_i+3)))))))

theorem fRenQuantF_spec (H : ZFAxioms mem) (ee : Nat → V)
    (c_i d_i r_i s_i t : Nat) (hr : IsVarMap H (ee r_i)) :
    Sat mem ee (fRenQuantF c_i d_i r_i s_i t) ↔
      ∃ a a', ee c_i = kpair H (natV H t) a ∧
        ee d_i = kpair H (natV H t) a' ∧
        mem (satTriple H (upV H (ee r_i)) a a') (ee s_i) := by
  constructor
  · rintro ⟨a, a', hc, hd, w, hw, hm⟩
    have hw' : w = upV H (ee r_i) :=
      (fUpF_spec H (scons w (scons a' (scons a ee))) 0 (r_i+3) hr).mp hw
    have hm' := (fTripleMemF_spec H (scons w (scons a' (scons a ee)))
      0 2 1 (s_i+3)).mp hm
    rw [hw'] at hm'
    exact ⟨a, a', (fTagUnF_spec H (scons a' (scons a ee)) (c_i+2) t 1).mp hc,
      (fTagUnF_spec H (scons a' (scons a ee)) (d_i+2) t 0).mp hd, hm'⟩
  · rintro ⟨a, a', hc, hd, hm⟩
    exact ⟨a, a', (fTagUnF_spec H (scons a' (scons a ee)) (c_i+2) t 1).mpr hc,
      (fTagUnF_spec H (scons a' (scons a ee)) (d_i+2) t 0).mpr hd,
      upV H (ee r_i),
      (fUpF_spec H (scons (upV H (ee r_i)) (scons a' (scons a ee)))
        0 (r_i+3) hr).mpr rfl,
      (fTripleMemF_spec H (scons (upV H (ee r_i)) (scons a' (scons a ee)))
        0 2 1 (s_i+3)).mpr hm⟩

/-- "the triple ⟨slot `r_i`, slot `c_i`, slot `d_i`⟩ is justified by slot
`s_i`" — the eight clauses of `RenStep`, in the order of the module header. -/
def fRenStepF (c_i d_i r_i s_i : Nat) : Form :=
  fOr (fRenAtomF c_i d_i r_i 0)
   (fOr (fRenAtomF c_i d_i r_i 1)
    (fOr (fAnd (fTaggedEmptyF c_i 2) (fTaggedEmptyF d_i 2))
     (fOr (fRenBinF c_i d_i r_i s_i 3)
      (fOr (fRenBinF c_i d_i r_i s_i 4)
       (fOr (fRenBinF c_i d_i r_i s_i 5)
        (fOr (fRenQuantF c_i d_i r_i s_i 6)
             (fRenQuantF c_i d_i r_i s_i 7)))))))

theorem fRenStepF_spec (H : ZFAxioms mem) (ee : Nat → V) (c_i d_i r_i s_i : Nat)
    (hr : IsVarMap H (ee r_i)) :
    Sat mem ee (fRenStepF c_i d_i r_i s_i) ↔
      RenStep H (ee s_i) (ee r_i) (ee c_i) (ee d_i) := by
  unfold RenStep
  exact or_congr (fRenAtomF_spec H ee c_i d_i r_i 0 hr)
    (or_congr (fRenAtomF_spec H ee c_i d_i r_i 1 hr)
      (or_congr (and_congr (fTaggedEmptyF_spec H ee c_i 2)
          (fTaggedEmptyF_spec H ee d_i 2))
        (or_congr (fRenBinF_spec H ee c_i d_i r_i s_i 3)
          (or_congr (fRenBinF_spec H ee c_i d_i r_i s_i 4)
            (or_congr (fRenBinF_spec H ee c_i d_i r_i s_i 5)
              (or_congr (fRenQuantF_spec H ee c_i d_i r_i s_i 6 hr)
                        (fRenQuantF_spec H ee c_i d_i r_i s_i 7 hr)))))))

/-- "slot `s_i` is closed under the renaming step".

| de Bruijn slot | contents                |
| -------------- | ----------------------- |
| `0`            | the renamed code `c'`   |
| `1`            | the code `c`            |
| `2`            | the variable map `r`    |
| `m+3`          | the caller's slot `m`   |
-/
def fRenClosedF (s_i : Nat) : Form :=
  fAll (fAll (fAll (fImp (fTripleMemF 2 1 0 (s_i+3))
    (fAnd (fVarMapF 2) (fRenStepF 1 0 2 (s_i+3))))))

theorem fRenClosedF_spec (H : ZFAxioms mem) (ee : Nat → V) (s_i : Nat) :
    Sat mem ee (fRenClosedF s_i) ↔ RenClosed H (ee s_i) := by
  unfold RenClosed
  constructor
  · intro h r c c' hmem
    obtain ⟨h1, h2⟩ := h r c c'
      ((fTripleMemF_spec H (scons c' (scons c (scons r ee)))
        2 1 0 (s_i+3)).mpr hmem)
    have hr : IsVarMap H r :=
      (fVarMapF_spec H (scons c' (scons c (scons r ee))) 2).mp h1
    exact ⟨hr, (fRenStepF_spec H (scons c' (scons c (scons r ee)))
      1 0 2 (s_i+3) hr).mp h2⟩
  · intro h r c c' hsat
    obtain ⟨hr, hstep⟩ := h r c c'
      ((fTripleMemF_spec H (scons c' (scons c (scons r ee)))
        2 1 0 (s_i+3)).mp hsat)
    exact ⟨(fVarMapF_spec H (scons c' (scons c (scons r ee))) 2).mpr hr,
      (fRenStepF_spec H (scons c' (scons c (scons r ee)))
        1 0 2 (s_i+3) hr).mpr hstep⟩

/-- "slot `d_i` is the renaming of slot `c_i` along slot `r_i`".

| de Bruijn slot | contents                |
| -------------- | ----------------------- |
| `0`            | the certificate `S`     |
| `m+1`          | the caller's slot `m`   |
-/
def fRenamesF (r_i c_i d_i : Nat) : Form :=
  fEx (fAnd (fRenClosedF 0) (fTripleMemF (r_i+1) (c_i+1) (d_i+1) 0))

theorem fRenamesF_spec (H : ZFAxioms mem) (ee : Nat → V) (r_i c_i d_i : Nat) :
    Sat mem ee (fRenamesF r_i c_i d_i) ↔
      Renames H (ee r_i) (ee c_i) (ee d_i) := by
  constructor
  · rintro ⟨S, hS, hmem⟩
    exact ⟨S, (fRenClosedF_spec H (scons S ee) 0).mp hS,
      (fTripleMemF_spec H (scons S ee) (r_i+1) (c_i+1) (d_i+1) 0).mp hmem⟩
  · rintro ⟨S, hS, hmem⟩
    exact ⟨S, (fRenClosedF_spec H (scons S ee) 0).mpr hS,
      (fTripleMemF_spec H (scons S ee) (r_i+1) (c_i+1) (d_i+1) 0).mpr hmem⟩

/-! ## Totality

The property carried through the code induction is universally quantified over
variable maps, because the quantifier cases apply the induction hypothesis at
the *shifted* map, not at the one the property started with.  No uniformity
over a set of maps is needed — and none would be available, since the maps do
not form a set — because a quantifier clause consults the induction hypothesis
exactly once. -/

/-- Every variable map renames the code to something. -/
def RenTotal (H : ZFAxioms mem) (c : V) : Prop :=
  ∀ r, IsVarMap H r → ∃ c', Renames H r c c'

/-- `RenTotal` as a `Form`, with the code in slot `0` of the caller.

| de Bruijn slot | contents                            |
| -------------- | ----------------------------------- |
| `0`            | the map `r`, then the renaming `c'` |
| `1`            | the code `c`, then `r`              |
| `2`            | under the inner binder: `c`         |
-/
def fRenTotalF : Form :=
  fAll (fImp (fVarMapF 0) (fEx (fRenamesF 1 2 0)))

theorem fRenTotalF_spec (H : ZFAxioms mem) (y : V) :
    Sat mem (scons y (fun _ => vempty H)) fRenTotalF ↔ RenTotal H y := by
  unfold RenTotal
  constructor
  · intro h r hr
    obtain ⟨c', hc'⟩ := h r ((fVarMapF_spec H _ 0).mpr hr)
    exact ⟨c', (fRenamesF_spec H _ 1 2 0).mp hc'⟩
  · intro h r hr
    obtain ⟨c', hc'⟩ := h r ((fVarMapF_spec H _ 0).mp hr)
    exact ⟨c', (fRenamesF_spec H _ 1 2 0).mpr hc'⟩

/-- **Renaming is total.**  Every code — including the nonstandard ones — has a
renaming along every variable map.  The atomic and falsity cases start from the
empty certificate, the three Boolean cases union the two certificates supplied
by the induction hypothesis at the same map, and the two quantifier cases apply
it once, at the binder shift. -/
theorem renTotal_of_isFormCodeSem (H : ZFAxioms mem) :
    ∀ c, IsFormCodeSem H c → RenTotal H c := by
  refine isFormCodeSem_ind' H (RenTotal H) fRenTotalF (fun _ => vempty H)
    (fun y => (fRenTotalF_spec H y).symm) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun i j hi hj r hr => ⟨_, renames_memAtom H hr hi hj⟩
  · exact fun i j hi hj r hr => ⟨_, renames_eqAtom H hr hi hj⟩
  · exact fun r hr => ⟨_, renames_bot H hr⟩
  · intro a b ha hb r hr
    obtain ⟨a', ha'⟩ := ha r hr
    obtain ⟨b', hb'⟩ := hb r hr
    exact ⟨_, renames_imp H hr ha' hb'⟩
  · intro a b ha hb r hr
    obtain ⟨a', ha'⟩ := ha r hr
    obtain ⟨b', hb'⟩ := hb r hr
    exact ⟨_, renames_and H hr ha' hb'⟩
  · intro a b ha hb r hr
    obtain ⟨a', ha'⟩ := ha r hr
    obtain ⟨b', hb'⟩ := hb r hr
    exact ⟨_, renames_or H hr ha' hb'⟩
  · intro a ha r hr
    obtain ⟨a', ha'⟩ := ha (upV H r) (upV_isVarMap H hr)
    exact ⟨_, renames_all H hr ha'⟩
  · intro a ha r hr
    obtain ⟨a', ha'⟩ := ha (upV H r) (upV_isVarMap H hr)
    exact ⟨_, renames_ex H hr ha'⟩

/-! ## Single-valuedness -/

/-- A code and a variable map determine the renaming. -/
def RenUnique (H : ZFAxioms mem) (c : V) : Prop :=
  ∀ r c1 c2, Renames H r c c1 → Renames H r c c2 → c1 = c2

/-- `RenUnique` as a `Form`, with the code in slot `0` of the caller.

| de Bruijn slot | contents                     |
| -------------- | ---------------------------- |
| `0`            | the second renaming `c2`     |
| `1`            | the first renaming `c1`      |
| `2`            | the variable map `r`         |
| `3`            | the code `c`                 |
-/
def fRenUniqueF : Form :=
  fAll (fAll (fAll (fImp (fRenamesF 2 3 1) (fImp (fRenamesF 2 3 0) (fEq 1 0)))))

theorem fRenUniqueF_spec (H : ZFAxioms mem) (y : V) :
    Sat mem (scons y (fun _ => vempty H)) fRenUniqueF ↔ RenUnique H y := by
  unfold RenUnique
  constructor
  · intro h r c1 c2 h1 h2
    exact h r c1 c2 ((fRenamesF_spec H _ 2 3 1).mpr h1)
      ((fRenamesF_spec H _ 2 3 0).mpr h2)
  · intro h r c1 c2 h1 h2
    exact h r c1 c2 ((fRenamesF_spec H _ 2 3 1).mp h1)
      ((fRenamesF_spec H _ 2 3 0).mp h2)

/-- **Renaming is single-valued.**  Each case inverts both hypotheses at the
known tag and either reads off the same closed term or applies the induction
hypothesis to the subcodes. -/
theorem renUnique_of_isFormCodeSem (H : ZFAxioms mem) :
    ∀ c, IsFormCodeSem H c → RenUnique H c := by
  refine isFormCodeSem_ind' H (RenUnique H) fRenUniqueF (fun _ => vempty H)
    (fun y => (fRenUniqueF_spec H y).symm) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro _ _ _ _ r c1 c2 h1 h2
    rw [renames_memAtom_inv H h1, renames_memAtom_inv H h2]
  · intro _ _ _ _ r c1 c2 h1 h2
    rw [renames_eqAtom_inv H h1, renames_eqAtom_inv H h2]
  · intro r c1 c2 h1 h2
    rw [renames_bot_inv H h1, renames_bot_inv H h2]
  · intro a b ha hb r c1 c2 h1 h2
    obtain ⟨a1, b1, hc1, k1, l1⟩ := renames_imp_inv H h1
    obtain ⟨a2, b2, hc2, k2, l2⟩ := renames_imp_inv H h2
    rw [hc1, hc2, ha r a1 a2 k1 k2, hb r b1 b2 l1 l2]
  · intro a b ha hb r c1 c2 h1 h2
    obtain ⟨a1, b1, hc1, k1, l1⟩ := renames_and_inv H h1
    obtain ⟨a2, b2, hc2, k2, l2⟩ := renames_and_inv H h2
    rw [hc1, hc2, ha r a1 a2 k1 k2, hb r b1 b2 l1 l2]
  · intro a b ha hb r c1 c2 h1 h2
    obtain ⟨a1, b1, hc1, k1, l1⟩ := renames_or_inv H h1
    obtain ⟨a2, b2, hc2, k2, l2⟩ := renames_or_inv H h2
    rw [hc1, hc2, ha r a1 a2 k1 k2, hb r b1 b2 l1 l2]
  · intro a ha r c1 c2 h1 h2
    obtain ⟨a1, hc1, k1⟩ := renames_all_inv H h1
    obtain ⟨a2, hc2, k2⟩ := renames_all_inv H h2
    rw [hc1, hc2, ha (upV H r) a1 a2 k1 k2]
  · intro a ha r c1 c2 h1 h2
    obtain ⟨a1, hc1, k1⟩ := renames_ex_inv H h1
    obtain ⟨a2, hc2, k2⟩ := renames_ex_inv H h2
    rw [hc1, hc2, ha (upV H r) a1 a2 k1 k2]

/-! ## Renaming as an operation

Totality and single-valuedness together turn the graph into a function.  As
with `applyV`, the operator is made total by a conditional choice, and every
specification lemma below states its hypotheses explicitly; outside the
formula codes the value is unconstrained and no lemma mentions it. -/

theorem renameV_exists (H : ZFAxioms mem) (r c : V) :
    ∃ d, (∃ d', Renames H r c d') → Renames H r c d := by
  rcases Classical.em (∃ d', Renames H r c d') with h | h
  · exact ⟨h.choose, fun _ => h.choose_spec⟩
  · exact ⟨vempty H, fun h' => absurd h' h⟩

/-- The renaming of the code `c` along the variable map `r`. -/
noncomputable def renameV (H : ZFAxioms mem) (r c : V) : V :=
  (renameV_exists H r c).choose

theorem renames_renameV (H : ZFAxioms mem) {r c : V} (hc : IsFormCodeSem H c)
    (hr : IsVarMap H r) : Renames H r c (renameV H r c) :=
  (renameV_exists H r c).choose_spec (renTotal_of_isFormCodeSem H c hc r hr)

/-- The operator inverts the graph: the graph determines the value. -/
theorem renameV_eq (H : ZFAxioms mem) {r c d : V} (hc : IsFormCodeSem H c)
    (h : Renames H r c d) : renameV H r c = d :=
  renUnique_of_isFormCodeSem H c hc r _ _
    ((renameV_exists H r c).choose_spec ⟨d, h⟩) h

/-! ### The recursion equations

They are equations, not a definition: the operator was already defined, and
each equation is read off the corresponding introduction rule together with
single-valuedness. -/

theorem renameV_memAtom (H : ZFAxioms mem) {r i j : V} (hr : IsVarMap H r)
    (hi : mem i (omegaV H)) (hj : mem j (omegaV H)) :
    renameV H r (kpair H (natV H 0) (kpair H i j))
      = kpair H (natV H 0) (kpair H (applyV H r i) (applyV H r j)) :=
  renameV_eq H (isFormCodeSem_memAtom H hi hj) (renames_memAtom H hr hi hj)

theorem renameV_eqAtom (H : ZFAxioms mem) {r i j : V} (hr : IsVarMap H r)
    (hi : mem i (omegaV H)) (hj : mem j (omegaV H)) :
    renameV H r (kpair H (natV H 1) (kpair H i j))
      = kpair H (natV H 1) (kpair H (applyV H r i) (applyV H r j)) :=
  renameV_eq H (isFormCodeSem_eqAtom H hi hj) (renames_eqAtom H hr hi hj)

theorem renameV_bot (H : ZFAxioms mem) {r : V} (hr : IsVarMap H r) :
    renameV H r (kpair H (natV H 2) (vempty H))
      = kpair H (natV H 2) (vempty H) :=
  renameV_eq H (isFormCodeSem_bot H) (renames_bot H hr)

theorem renameV_imp (H : ZFAxioms mem) {r a b : V} (hr : IsVarMap H r)
    (ha : IsFormCodeSem H a) (hb : IsFormCodeSem H b) :
    renameV H r (kpair H (natV H 3) (kpair H a b))
      = kpair H (natV H 3) (kpair H (renameV H r a) (renameV H r b)) :=
  renameV_eq H (isFormCodeSem_imp H ha hb)
    (renames_imp H hr (renames_renameV H ha hr) (renames_renameV H hb hr))

theorem renameV_and (H : ZFAxioms mem) {r a b : V} (hr : IsVarMap H r)
    (ha : IsFormCodeSem H a) (hb : IsFormCodeSem H b) :
    renameV H r (kpair H (natV H 4) (kpair H a b))
      = kpair H (natV H 4) (kpair H (renameV H r a) (renameV H r b)) :=
  renameV_eq H (isFormCodeSem_and H ha hb)
    (renames_and H hr (renames_renameV H ha hr) (renames_renameV H hb hr))

theorem renameV_or (H : ZFAxioms mem) {r a b : V} (hr : IsVarMap H r)
    (ha : IsFormCodeSem H a) (hb : IsFormCodeSem H b) :
    renameV H r (kpair H (natV H 5) (kpair H a b))
      = kpair H (natV H 5) (kpair H (renameV H r a) (renameV H r b)) :=
  renameV_eq H (isFormCodeSem_or H ha hb)
    (renames_or H hr (renames_renameV H ha hr) (renames_renameV H hb hr))

theorem renameV_all (H : ZFAxioms mem) {r a : V} (hr : IsVarMap H r)
    (ha : IsFormCodeSem H a) :
    renameV H r (kpair H (natV H 6) a)
      = kpair H (natV H 6) (renameV H (upV H r) a) :=
  renameV_eq H (isFormCodeSem_all H ha)
    (renames_all H hr (renames_renameV H ha (upV_isVarMap H hr)))

theorem renameV_ex (H : ZFAxioms mem) {r a : V} (hr : IsVarMap H r)
    (ha : IsFormCodeSem H a) :
    renameV H r (kpair H (natV H 7) a)
      = kpair H (natV H 7) (renameV H (upV H r) a) :=
  renameV_eq H (isFormCodeSem_ex H ha)
    (renames_ex H hr (renames_renameV H ha (upV_isVarMap H hr)))

/-! ## Renaming preserves codehood

The atomic cases are where this is not automatic: a renamed index is a value of
the variable map, so it is an internal natural exactly because the map lands in
the internal omega. -/

/-- Every renaming of the code is again a code. -/
def RenCode (H : ZFAxioms mem) (c : V) : Prop :=
  ∀ r c', IsVarMap H r → Renames H r c c' → IsFormCodeSem H c'

/-- `RenCode` as a `Form`, with the code in slot `0` of the caller.

| de Bruijn slot | contents                |
| -------------- | ----------------------- |
| `0`            | the renaming `c'`       |
| `1`            | the variable map `r`    |
| `2`            | the code `c`            |
-/
def fRenCodeF : Form :=
  fAll (fAll (fImp (fVarMapF 1) (fImp (fRenamesF 1 2 0) (fIsFormCodeF 0))))

theorem fRenCodeF_spec (H : ZFAxioms mem) (y : V) :
    Sat mem (scons y (fun _ => vempty H)) fRenCodeF ↔ RenCode H y := by
  unfold RenCode
  constructor
  · intro h r c' hr hren
    exact (fIsFormCodeF_spec H _ 0).mp
      (h r c' ((fVarMapF_spec H _ 1).mpr hr)
        ((fRenamesF_spec H _ 1 2 0).mpr hren))
  · intro h r c' hr hren
    exact (fIsFormCodeF_spec H _ 0).mpr
      (h r c' ((fVarMapF_spec H _ 1).mp hr)
        ((fRenamesF_spec H _ 1 2 0).mp hren))

theorem renCode_of_isFormCodeSem (H : ZFAxioms mem) :
    ∀ c, IsFormCodeSem H c → RenCode H c := by
  refine isFormCodeSem_ind' H (RenCode H) fRenCodeF (fun _ => vempty H)
    (fun y => (fRenCodeF_spec H y).symm) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i j hi hj r c' hr hren
    rw [renames_memAtom_inv H hren]
    exact isFormCodeSem_memAtom H (isVarMap_apply H hr hi)
      (isVarMap_apply H hr hj)
  · intro i j hi hj r c' hr hren
    rw [renames_eqAtom_inv H hren]
    exact isFormCodeSem_eqAtom H (isVarMap_apply H hr hi)
      (isVarMap_apply H hr hj)
  · intro r c' _ hren
    rw [renames_bot_inv H hren]
    exact isFormCodeSem_bot H
  · intro a b ha hb r c' hr hren
    obtain ⟨a', b', hc', k1, k2⟩ := renames_imp_inv H hren
    rw [hc']
    exact isFormCodeSem_imp H (ha r a' hr k1) (hb r b' hr k2)
  · intro a b ha hb r c' hr hren
    obtain ⟨a', b', hc', k1, k2⟩ := renames_and_inv H hren
    rw [hc']
    exact isFormCodeSem_and H (ha r a' hr k1) (hb r b' hr k2)
  · intro a b ha hb r c' hr hren
    obtain ⟨a', b', hc', k1, k2⟩ := renames_or_inv H hren
    rw [hc']
    exact isFormCodeSem_or H (ha r a' hr k1) (hb r b' hr k2)
  · intro a ha r c' hr hren
    obtain ⟨a', hc', k⟩ := renames_all_inv H hren
    rw [hc']
    exact isFormCodeSem_all H (ha (upV H r) a' (upV_isVarMap H hr) k)
  · intro a ha r c' hr hren
    obtain ⟨a', hc', k⟩ := renames_ex_inv H hren
    rw [hc']
    exact isFormCodeSem_ex H (ha (upV H r) a' (upV_isVarMap H hr) k)

/-- **A renaming of a code is a code**, in the graph form. -/
theorem renames_isFormCodeSem (H : ZFAxioms mem) {r c c' : V}
    (hc : IsFormCodeSem H c) (hr : IsVarMap H r) (h : Renames H r c c') :
    IsFormCodeSem H c' :=
  renCode_of_isFormCodeSem H c hc r c' hr h

/-- **A renaming of a code is a code**, in the operator form. -/
theorem renameV_isFormCodeSem (H : ZFAxioms mem) {r c : V}
    (hc : IsFormCodeSem H c) (hr : IsVarMap H r) :
    IsFormCodeSem H (renameV H r c) :=
  renames_isFormCodeSem H hc hr (renames_renameV H hc hr)

/-! ## The substitution lemma

The property pushed through the code induction has to be a `Form`, so both
`SatIn` and `compV` need object-language renderings.  Neither is hard: `SatIn`
is an existential over step-closed sets, and `fSatClosedF` already exists; and
`compV` is described elementwise, so `fSetByF` renders it.

The property also has to carry codehood of the code itself, because the two
atomic clauses of `SatIn` and both quantifier clauses are stated for codes.
The induction hypotheses of `isFormCodeSem_ind'` supply only the property, so
the property says "is a code, *and* renaming commutes with satisfaction". -/

/-- "slot `c_i` is satisfied at slot `e_i` in the structure ⟨slot `a_i`,
slot `r_i`⟩".

| de Bruijn slot | contents                |
| -------------- | ----------------------- |
| `0`            | the certificate `S`     |
| `1`            | that certificate, then the numeral one |
| `m+1`, `m+2`   | the caller's slot `m`   |
-/
def fSatInF (c_i e_i a_i r_i : Nat) : Form :=
  fEx (fAnd (fSatClosedF 0 (a_i+1) (r_i+1))
    (fEx (fAnd (fNumF 0 1) (fTripleMemF (c_i+2) (e_i+2) 0 1))))

theorem fSatInF_spec (H : ZFAxioms mem) (ee : Nat → V) (c_i e_i a_i r_i : Nat) :
    Sat mem ee (fSatInF c_i e_i a_i r_i) ↔
      SatIn H (ee a_i) (ee r_i) (ee c_i) (ee e_i) := by
  unfold SatIn
  constructor
  · rintro ⟨S, hS, one, hone, hmem⟩
    refine ⟨S, (fSatClosedF_spec H (scons S ee) 0 (a_i+1) (r_i+1)).mp hS, ?_⟩
    have hone' : one = natV H 1 :=
      (fNumF_spec H 1 0 (scons one (scons S ee))).mp hone
    have hmem' := (fTripleMemF_spec H (scons one (scons S ee))
      (c_i+2) (e_i+2) 0 1).mp hmem
    rw [hone'] at hmem'
    exact hmem'
  · rintro ⟨S, hS, hmem⟩
    exact ⟨S, (fSatClosedF_spec H (scons S ee) 0 (a_i+1) (r_i+1)).mpr hS,
      natV H 1, (fNumF_spec H 1 0 (scons (natV H 1) (scons S ee))).mpr rfl,
      (fTripleMemF_spec H (scons (natV H 1) (scons S ee))
        (c_i+2) (e_i+2) 0 1).mpr hmem⟩

/-- "slot `i` is the composition of the environment in slot `e_i` with the
variable map in slot `r_i`".

| de Bruijn slot | contents                                   |
| -------------- | ------------------------------------------ |
| `0`            | the candidate pair `p`                     |
| `1`            | the index `n`, then the renamed index `m`  |
| `2`, `3`       | the value `v`, then the pair again         |
| `m+1` … `m+4`  | the caller's slot `m` under 1 … 4 binders  |
-/
def fCompF (i e_i r_i : Nat) : Form :=
  fSetByF i
    (fEx (fAnd (fNatF 0)
      (fEx (fAnd (fPairMemF 1 0 (r_i+3))
        (fEx (fAnd (fPairMemF 1 0 (e_i+4)) (fKPairF 3 2 0)))))))

theorem fCompF_spec (H : ZFAxioms mem) (ee : Nat → V) (i e_i r_i : Nat)
    {A : V} (he : IsEnvOn H A (ee e_i)) (hr : IsVarMap H (ee r_i)) :
    Sat mem ee (fCompF i e_i r_i) ↔ ee i = compV H (ee e_i) (ee r_i) := by
  refine fSetByF_spec H ee i _ (compV H (ee e_i) (ee r_i)) (fun p => ?_)
  rw [compV_mem H he hr p]
  constructor
  · rintro ⟨n, hn, m, hm, v, hv, hp⟩
    have hn' : mem n (omegaV H) := (fNatF_spec H (scons n (scons p ee)) 0).mp hn
    have hm' : mem (kpair H n m) (ee r_i) :=
      (fPairMemF_spec H (scons m (scons n (scons p ee))) 1 0 (r_i+3)).mp hm
    have hv' : mem (kpair H m v) (ee e_i) :=
      (fPairMemF_spec H (scons v (scons m (scons n (scons p ee))))
        1 0 (e_i+4)).mp hv
    have hp' : p = kpair H n v :=
      (fKPairF_spec H (scons v (scons m (scons n (scons p ee)))) 3 2 0).mp hp
    refine ⟨n, hn', ?_⟩
    rw [hp', applyV_eq H (isVarMap_functional H hr) hm', applyV_eq H he.1.1 hv']
  · rintro ⟨n, hn, hp⟩
    exact ⟨n, (fNatF_spec H (scons n (scons p ee)) 0).mpr hn,
      applyV H (ee r_i) n,
      (fPairMemF_spec H
        (scons (applyV H (ee r_i) n) (scons n (scons p ee)))
        1 0 (r_i+3)).mpr (isVarMap_mem H hr hn),
      applyV H (ee e_i) (applyV H (ee r_i) n),
      (fPairMemF_spec H
        (scons (applyV H (ee e_i) (applyV H (ee r_i) n))
          (scons (applyV H (ee r_i) n) (scons n (scons p ee))))
        1 0 (e_i+4)).mpr
        (applyV_mem H (he.1.2.1 _ (isVarMap_apply H hr hn))),
      (fKPairF_spec H
        (scons (applyV H (ee e_i) (applyV H (ee r_i) n))
          (scons (applyV H (ee r_i) n) (scons n (scons p ee))))
        3 2 0).mpr hp⟩

/-- **Renaming commutes with satisfaction**, as the property a code induction
can carry: the code is a code, and every renaming of it is satisfied at an
environment exactly when the code itself is satisfied at the composed
environment. -/
def SubstOK (H : ZFAxioms mem) (A R c : V) : Prop :=
  IsFormCodeSem H c ∧
  ∀ r c' e, IsVarMap H r → IsEnvOn H A e → Renames H r c c' →
    (SatIn H A R c' e ↔ SatIn H A R c (compV H e r))

/-- The parameter block of `fSubstOKF`: the carrier, then the relation. -/
noncomputable def envSubst (H : ZFAxioms mem) (A R : V) : Nat → V :=
  scons A (scons R (fun _ => vempty H))

/-- `SubstOK` as a `Form`, with the code in slot `0` of the caller.

| de Bruijn slot | contents                |
| -------------- | ----------------------- |
| `0`            | the environment `e`     |
| `1`            | the renaming `c'`       |
| `2`            | the variable map `r`    |
| `3`            | the code `c`            |
| `4`            | the carrier `A`         |
| `5`            | the relation `R`        |

The right-hand side of the biconditional introduces one further binder for the
composed environment, so under it every slot above is shifted by one. -/
def fSubstOKF : Form :=
  fAnd (fIsFormCodeF 0)
    (fAll (fAll (fAll (fImp (fVarMapF 2)
      (fImp (fEnvOnF 0 4)
        (fImp (fRenamesF 2 3 1)
          (fIff (fSatInF 1 0 4 5)
            (fEx (fAnd (fCompF 0 1 3) (fSatInF 4 0 5 6))))))))))

/-- The right-hand side of the biconditional, read semantically. -/
theorem fSubstRhs_spec (H : ZFAxioms mem) {A : V} (R y r c' e : V)
    (hr : IsVarMap H r) (he : IsEnvOn H A e) :
    Sat mem (scons e (scons c' (scons r (scons y (envSubst H A R)))))
        (fEx (fAnd (fCompF 0 1 3) (fSatInF 4 0 5 6))) ↔
      SatIn H A R y (compV H e r) := by
  constructor
  · rintro ⟨w, hw, hsat⟩
    have hw' : w = compV H e r :=
      (fCompF_spec H
        (scons w (scons e (scons c' (scons r (scons y (envSubst H A R))))))
        0 1 3 he hr).mp hw
    have hs := (fSatInF_spec H
      (scons w (scons e (scons c' (scons r (scons y (envSubst H A R))))))
      4 0 5 6).mp hsat
    rw [hw'] at hs
    exact hs
  · intro hsat
    exact ⟨compV H e r,
      (fCompF_spec H
        (scons (compV H e r)
          (scons e (scons c' (scons r (scons y (envSubst H A R))))))
        0 1 3 he hr).mpr rfl,
      (fSatInF_spec H
        (scons (compV H e r)
          (scons e (scons c' (scons r (scons y (envSubst H A R))))))
        4 0 5 6).mpr hsat⟩

theorem fSubstOKF_spec (H : ZFAxioms mem) (A R y : V) :
    Sat mem (scons y (envSubst H A R)) fSubstOKF ↔ SubstOK H A R y := by
  unfold SubstOK
  constructor
  · rintro ⟨hcode, h⟩
    refine ⟨(fIsFormCodeF_spec H (scons y (envSubst H A R)) 0).mp hcode,
      fun r c' e hr he hren => ?_⟩
    have hiff := Sat_fIff.mp (h r c' e
      ((fVarMapF_spec H
        (scons e (scons c' (scons r (scons y (envSubst H A R))))) 2).mpr hr)
      ((fEnvOnF_spec H
        (scons e (scons c' (scons r (scons y (envSubst H A R))))) 0 4).mpr he)
      ((fRenamesF_spec H
        (scons e (scons c' (scons r (scons y (envSubst H A R)))))
        2 3 1).mpr hren))
    exact (((fSatInF_spec H
      (scons e (scons c' (scons r (scons y (envSubst H A R)))))
      1 0 4 5).symm.trans hiff).trans (fSubstRhs_spec H R y r c' e hr he))
  · rintro ⟨hcode, h⟩
    refine ⟨(fIsFormCodeF_spec H (scons y (envSubst H A R)) 0).mpr hcode,
      fun r c' e hr he hren => ?_⟩
    have hr' : IsVarMap H r :=
      (fVarMapF_spec H
        (scons e (scons c' (scons r (scons y (envSubst H A R))))) 2).mp hr
    have he' : IsEnvOn H A e :=
      (fEnvOnF_spec H
        (scons e (scons c' (scons r (scons y (envSubst H A R))))) 0 4).mp he
    have hren' : Renames H r y c' :=
      (fRenamesF_spec H
        (scons e (scons c' (scons r (scons y (envSubst H A R)))))
        2 3 1).mp hren
    exact Sat_fIff.mpr (((fSatInF_spec H
      (scons e (scons c' (scons r (scons y (envSubst H A R)))))
      1 0 4 5).trans (h r c' e hr' he' hren')).trans
      (fSubstRhs_spec H R y r c' e hr' he').symm)

/-- **The substitution lemma**, in the form the code induction proves.

The two atomic cases reduce both sides to the same fact about the structure,
using `compV_apply`; falsity is refuted on both sides; the three Boolean cases
apply the induction hypothesis to the subcodes at the same map and
environment; and the two quantifier cases apply it at the shifted map and the
shifted environment, where `compV_econs_upV` identifies the two ways of
shifting. -/
theorem substOK_of_isFormCodeSem (H : ZFAxioms mem) {A R : V}
    (hS : IsSetStructure H A R) :
    ∀ c, IsFormCodeSem H c → SubstOK H A R c := by
  refine isFormCodeSem_ind' H (SubstOK H A R) fSubstOKF (envSubst H A R)
    (fun y => (fSubstOKF_spec H A R y).symm) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i j hi hj
    refine ⟨isFormCodeSem_memAtom H hi hj, fun r c' e hr he hren => ?_⟩
    rw [renames_memAtom_inv H hren,
        satIn_memAtom H hS (isVarMap_apply H hr hi) (isVarMap_apply H hr hj) he,
        satIn_memAtom H hS hi hj (compV_isEnvOn H he hr),
        compV_apply H he hr hi, compV_apply H he hr hj]
  · intro i j hi hj
    refine ⟨isFormCodeSem_eqAtom H hi hj, fun r c' e hr he hren => ?_⟩
    rw [renames_eqAtom_inv H hren,
        satIn_eqAtom H hS (isVarMap_apply H hr hi) (isVarMap_apply H hr hj) he,
        satIn_eqAtom H hS hi hj (compV_isEnvOn H he hr),
        compV_apply H he hr hi, compV_apply H he hr hj]
  · refine ⟨isFormCodeSem_bot H, fun r c' e hr he hren => ?_⟩
    rw [renames_bot_inv H hren]
    exact ⟨fun h => absurd h (satIn_bot H), fun h => absurd h (satIn_bot H)⟩
  · intro a b ha hb
    refine ⟨isFormCodeSem_imp H ha.1 hb.1, fun r c' e hr he hren => ?_⟩
    obtain ⟨a', b', hc', k1, k2⟩ := renames_imp_inv H hren
    rw [hc', satIn_imp H hS (renames_isFormCodeSem H ha.1 hr k1)
          (renames_isFormCodeSem H hb.1 hr k2) he,
        satIn_imp H hS ha.1 hb.1 (compV_isEnvOn H he hr),
        ha.2 r a' e hr he k1, hb.2 r b' e hr he k2]
  · intro a b ha hb
    refine ⟨isFormCodeSem_and H ha.1 hb.1, fun r c' e hr he hren => ?_⟩
    obtain ⟨a', b', hc', k1, k2⟩ := renames_and_inv H hren
    rw [hc', satIn_and H hS (renames_isFormCodeSem H ha.1 hr k1)
          (renames_isFormCodeSem H hb.1 hr k2) he,
        satIn_and H hS ha.1 hb.1 (compV_isEnvOn H he hr),
        ha.2 r a' e hr he k1, hb.2 r b' e hr he k2]
  · intro a b ha hb
    refine ⟨isFormCodeSem_or H ha.1 hb.1, fun r c' e hr he hren => ?_⟩
    obtain ⟨a', b', hc', k1, k2⟩ := renames_or_inv H hren
    rw [hc', satIn_or H hS (renames_isFormCodeSem H ha.1 hr k1)
          (renames_isFormCodeSem H hb.1 hr k2) he,
        satIn_or H hS ha.1 hb.1 (compV_isEnvOn H he hr),
        ha.2 r a' e hr he k1, hb.2 r b' e hr he k2]
  · intro a ha
    refine ⟨isFormCodeSem_all H ha.1, fun r c' e hr he hren => ?_⟩
    obtain ⟨a', hc', k⟩ := renames_all_inv H hren
    rw [hc', satIn_all H hS
          (renames_isFormCodeSem H ha.1 (upV_isVarMap H hr) k) he,
        satIn_all H hS ha.1 (compV_isEnvOn H he hr)]
    constructor
    · intro h d hd
      have hstep := (ha.2 (upV H r) a' (econs H d e) (upV_isVarMap H hr)
        (econs_isEnvOn H he hd) k).mp (h d hd)
      rwa [compV_econs_upV H he hr hd] at hstep
    · intro h d hd
      refine (ha.2 (upV H r) a' (econs H d e) (upV_isVarMap H hr)
        (econs_isEnvOn H he hd) k).mpr ?_
      rw [compV_econs_upV H he hr hd]
      exact h d hd
  · intro a ha
    refine ⟨isFormCodeSem_ex H ha.1, fun r c' e hr he hren => ?_⟩
    obtain ⟨a', hc', k⟩ := renames_ex_inv H hren
    rw [hc', satIn_ex H hS
          (renames_isFormCodeSem H ha.1 (upV_isVarMap H hr) k) he,
        satIn_ex H hS ha.1 (compV_isEnvOn H he hr)]
    constructor
    · rintro ⟨d, hd, hsat⟩
      refine ⟨d, hd, ?_⟩
      have hstep := (ha.2 (upV H r) a' (econs H d e) (upV_isVarMap H hr)
        (econs_isEnvOn H he hd) k).mp hsat
      rwa [compV_econs_upV H he hr hd] at hstep
    · rintro ⟨d, hd, hsat⟩
      refine ⟨d, hd, (ha.2 (upV H r) a' (econs H d e) (upV_isVarMap H hr)
        (econs_isEnvOn H he hd) k).mpr ?_⟩
      rw [compV_econs_upV H he hr hd]
      exact hsat

/-- **The substitution lemma.**  Satisfaction of a renamed code under an
environment is satisfaction of the original code under the composed
environment. -/
theorem satIn_renames (H : ZFAxioms mem) {A R : V} (hS : IsSetStructure H A R)
    {c c' r e : V} (hc : IsFormCodeSem H c) (hr : IsVarMap H r)
    (he : IsEnvOn H A e) (hren : Renames H r c c') :
    SatIn H A R c' e ↔ SatIn H A R c (compV H e r) :=
  (substOK_of_isFormCodeSem H hS c hc).2 r c' e hr he hren

/-- The substitution lemma in operator form. -/
theorem satIn_renameV (H : ZFAxioms mem) {A R : V} (hS : IsSetStructure H A R)
    {c r e : V} (hc : IsFormCodeSem H c) (hr : IsVarMap H r)
    (he : IsEnvOn H A e) :
    SatIn H A R (renameV H r c) e ↔ SatIn H A R c (compV H e r) :=
  satIn_renames H hS hc hr he (renames_renameV H hc hr)

/-! ### The two instances the calculus consumes

`P_allI` and `P_exE` shift a whole context along the successor map, and
`P_allE`, `P_exI` and `P_eqElim` instantiate the outermost binder at a
variable.  Each becomes a single equation about `SatIn`. -/

/-- **The successor shift.**  Renaming along the internal successor map makes a
code indifferent to the newly bound slot.  This is what an eigenvariable
argument needs. -/
theorem satIn_renameV_succMap (H : ZFAxioms mem) {A R : V}
    (hS : IsSetStructure H A R) {c e d : V} (hc : IsFormCodeSem H c)
    (he : IsEnvOn H A e) (hd : mem d A) :
    SatIn H A R (renameV H (succMap H) c) (econs H d e) ↔ SatIn H A R c e := by
  rw [satIn_renameV H hS hc (succMap_isVarMap H) (econs_isEnvOn H he hd),
      compV_succMap H he hd]

/-- **Instantiation at a variable.**  Renaming along the internal instantiation
map at the index `k` is evaluation with the binder filled by the value of the
environment at `k`.  This is what the two quantifier elimination rules and the
Leibniz rule need. -/
theorem satIn_renameV_instMap (H : ZFAxioms mem) {A R : V}
    (hS : IsSetStructure H A R) {c e k : V} (hc : IsFormCodeSem H c)
    (he : IsEnvOn H A e) (hk : mem k (omegaV H)) :
    SatIn H A R (renameV H (instMap H k) c) e ↔
      SatIn H A R c (econs H (applyV H e k) e) := by
  rw [satIn_renameV H hS hc (instMap_isVarMap H hk) he, compV_instMap H he hk]

/-! ## Agreement with external renamings

The internal operation is defined on all codes, standard or not, and nothing
above relates it to the metatheoretic `rename`.  On *quotations* the two do
agree, and that is the direction quotation soundness always goes: an external
formula's code renames to the code of the external formula's renaming.

The hypothesis is pointwise agreement on numerals, which is what the two named
maps satisfy, and which the binder shift preserves — the internal `upV` and the
external `up` are pointwise the same operation on numerals. -/

/-- The variable map `r` computes the external index function `f` on numerals. -/
def AgreesWith (H : ZFAxioms mem) (r : V) (f : Nat → Nat) : Prop :=
  ∀ k : Nat, applyV H r (natV H k) = natV H (f k)

theorem upV_agreesWith (H : ZFAxioms mem) {r : V} {f : Nat → Nat}
    (hr : IsVarMap H r) (h : AgreesWith H r f) :
    AgreesWith H (upV H r) (up f) := by
  intro k
  cases k with
  | zero => exact upV_zero H hr
  | succ k =>
      show applyV H (upV H r) (vsucc H (natV H k)) = vsucc H (natV H (f k))
      rw [upV_succ H hr (natV_mem_omega H k), h k]

theorem succMap_agreesWith (H : ZFAxioms mem) :
    AgreesWith H (succMap H) Nat.succ :=
  fun k => succMap_apply H (natV_mem_omega H k)

theorem instMap_agreesWith (H : ZFAxioms mem) (k : Nat) :
    AgreesWith H (instMap H (natV H k)) (inst k) := by
  intro m
  cases m with
  | zero => exact instMap_zero H (natV H k)
  | succ m => exact instMap_succ H (natV H k) (natV_mem_omega H m)

/-- **Quotation soundness for renaming.**  The code of an external formula
renames, along any variable map computing `f`, to the code of the external
renaming along `f`.  The induction is on the external parse tree; the two
quantifier cases are where `upV_agreesWith` is used. -/
theorem renames_formCode (H : ZFAxioms mem) :
    ∀ (phi : Form) (r : V) (f : Nat → Nat), IsVarMap H r → AgreesWith H r f →
      Renames H r (formCode H phi) (formCode H (rename f phi)) := by
  intro phi
  induction phi with
  | fMem i j =>
      intro r f hr h
      have hren := renames_memAtom H hr (natV_mem_omega H i) (natV_mem_omega H j)
      rw [h i, h j] at hren
      exact hren
  | fEq i j =>
      intro r f hr h
      have hren := renames_eqAtom H hr (natV_mem_omega H i) (natV_mem_omega H j)
      rw [h i, h j] at hren
      exact hren
  | fBot => intro r f hr _; exact renames_bot H hr
  | fImp a b iha ihb =>
      intro r f hr h
      exact renames_imp H hr (iha r f hr h) (ihb r f hr h)
  | fAnd a b iha ihb =>
      intro r f hr h
      exact renames_and H hr (iha r f hr h) (ihb r f hr h)
  | fOr a b iha ihb =>
      intro r f hr h
      exact renames_or H hr (iha r f hr h) (ihb r f hr h)
  | fAll a ih =>
      intro r f hr h
      exact renames_all H hr
        (ih (upV H r) (up f) (upV_isVarMap H hr) (upV_agreesWith H hr h))
  | fEx a ih =>
      intro r f hr h
      exact renames_ex H hr
        (ih (upV H r) (up f) (upV_isVarMap H hr) (upV_agreesWith H hr h))

theorem renameV_formCode (H : ZFAxioms mem) {r : V} (f : Nat → Nat)
    (hr : IsVarMap H r) (h : AgreesWith H r f) (phi : Form) :
    renameV H r (formCode H phi) = formCode H (rename f phi) :=
  renameV_eq H (formCode_isFormCodeSem H phi) (renames_formCode H phi r f hr h)

/-- The context shift of `P_allI` and `P_exE`, at the level of quotations. -/
theorem renameV_formCode_succMap (H : ZFAxioms mem) (phi : Form) :
    renameV H (succMap H) (formCode H phi)
      = formCode H (rename Nat.succ phi) :=
  renameV_formCode H Nat.succ (succMap_isVarMap H) (succMap_agreesWith H) phi

/-- The instantiation of `P_allE`, `P_exI` and `P_eqElim`, at the level of
quotations. -/
theorem renameV_formCode_instMap (H : ZFAxioms mem) (k : Nat) (phi : Form) :
    renameV H (instMap H (natV H k)) (formCode H phi)
      = formCode H (rename (inst k) phi) :=
  renameV_formCode H (inst k) (instMap_isVarMap H (natV_mem_omega H k))
    (instMap_agreesWith H k) phi

end InternalSoundness

end BoundedZFCConsistency
end LeanProofs
