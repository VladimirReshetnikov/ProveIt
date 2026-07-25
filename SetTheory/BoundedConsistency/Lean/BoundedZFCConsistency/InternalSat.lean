import BoundedZFCConsistency.FormulaClosedSet
import BoundedZFCConsistency.OmegaRecursion

/-!
# Internal satisfaction for set-sized structures, by certificates

Satisfaction has to be available *inside* the object theory, as a relation
between a formula code, an internal environment, and a truth value.  Two
routes are unavailable and neither is attempted here.

Recursion on the **depth** of a code is circular: depth is itself defined by
recursion on codes, and a nonstandard model has code-like elements with no
external depth at all.

The **intersection presentation** that `BoundedZFCConsistency.CodePredicate`
uses for "codes a formula" does not transfer either.  That presentation works
because the eight closure clauses are monotone in the set being defined, so
the intersection of all closed sets is again closed.  The Tarski clauses are
not monotone: implication and falsity put the recursive occurrence in negative
position, and a least fixed point of a non-monotone operator need not exist.

What does work is **certificates**.  A satisfaction fact is witnessed by an
internal set recording the evaluation of a code together with the evaluations
of its subcodes, each entry locally justified by other entries.  The predicate
"some certificate assigns bit `b` to code `c` under environment `e`" is then a
single existential over sets, and its two defining properties — being
single-valued and being total — are proved separately by induction on codes.
This is the same architecture the repository's arithmetic project uses against
the same obstruction.

## The ambient structure

Everything is relative to an internal **set structure**: a nonempty set `A`,
the carrier, together with a set `R` of Kuratowski pairs from `A`, the
interpretation of the membership symbol.  Equality is interpreted by the
model's own equality on elements of `A`, so the structure carries no third
component.

## Internal environments

An environment is an internal function from the internal omega into `A`, in
the sense of `IsFunctionOn`/`applyV` of `BoundedZFCConsistency.OmegaRecursion`.
`constEnv` shows that one exists as soon as `A` is nonempty.  `econs H d E` is
the `scons`-analogue: it sends `0` to `d` and `k+1` to `E k`, and it is again
an environment.  Building it needs a fact about the internal omega that the ZF
development does not carry — every internal natural is either zero or the
successor of an internal natural — which is proved here as `nat_zero_or_succ`.

## The local step and certificates

`Justified H A R S c e b` says that the triple `⟨c, e, b⟩` is justified by the
already-established triples in `S`, by one of eight clauses:

| tag | clause    | bit                                                        |
| --- | --------- | ---------------------------------------------------------- |
| `0` | `fMem`    | `1` exactly when `⟨e i, e j⟩ ∈ R`                          |
| `1` | `fEq`     | `1` exactly when `e i = e j`                               |
| `2` | `fBot`    | always `0`                                                 |
| `3` | `fImp`    | `1` exactly when the first subbit is `0` or the second `1` |
| `4` | `fAnd`    | `1` exactly when both subbits are `1`                      |
| `5` | `fOr`     | `1` exactly when some subbit is `1`                        |
| `6` | `fAll`    | `1` witnessed by `1` at every `d ∈ A`, `0` by a `0` at one |
| `7` | `fEx`     | `1` witnessed by a `1` at one `d ∈ A`, `0` by `0` at all   |

A **certificate** for `⟨c, e, b⟩` is a set `S` every one of whose triples is
justified by `S` — and whose environments are genuine environments — together
with the requirement that `⟨c, e, b⟩` itself lies in `S`.

The quantifier clauses are stated with an explicit witness on each side rather
than with a totality clause over `d ∈ A`.  That is exactly the Tarski
condition, and it is what makes the clause deterministic *given* that the
subcode is already known to be single-valued, which is what the induction
supplies.

## What is proved

* every model of `ZFAxioms` with a nonempty `A` has an environment, and the
  shift of an environment is an environment, with its two application
  equations;
* the step relation is rendered as a `Form` with a full `iff` satisfaction
  spec, relative to the single hypothesis that the environment slot holds an
  internal function on the omega — without it the object-language reading of
  `applyV` is not available and no unconditional `iff` is possible;
* **functionality**: two certificates never assign different bits to the same
  code and environment (`certificate_functional`).

## What is deliberately absent

**Totality** is not proved.  The statement left open is exactly

```text
∀ c, IsFormCodeSem H c → ∀ e, IsEnvOn H A e → ∃ S b, Certifies H A R S c e b
```

and the obstruction is the quantifier clauses: a certificate is needed
uniformly in `d ∈ A`, so the per-`d` certificates have to be collected by
Replacement along a definable choice of certificate and then unioned, and the
union has to be shown step-closed.  Nothing here asserts totality, and
`Certifies` should not be read as a satisfaction relation until it is proved.

Also absent: the arithmetical-hierarchy stratification, relativization to a
`V_alpha`, formalized soundness, reflection, and `Con_n` itself.

## De Bruijn bookkeeping

Every formula below carries a table of its de Bruijn slots.  Slot arguments
named `_i` are ABSOLUTE positions in the environment at the use site; each
binder introduced by a macro shifts the caller's slots by one, and the call
sites account for the shift explicitly.  The convention matches `ZF.Zf`.

Neither Powerset nor Regularity is used, matching the six axioms bundled in
`ZFAxioms`.
-/

namespace LeanProofs
namespace BoundedZFCConsistency

open SetTheory
open SetTheory.Form

universe u

section InternalSat

variable {V : Type u} {mem : V → V → Prop}

/-! ## Internal set structures

The carrier is required to be nonempty, since an environment is a total
function into it.  The clause on `R` records that the membership relation is a
set of Kuratowski pairs from the carrier; it is part of what "structure" means
and is stated for the benefit of later modules, but none of the results below
depend on it. -/

/-- An internal first-order structure for the language of set theory: a
nonempty carrier `A` and a relation `R` on it. -/
structure IsSetStructure (H : ZFAxioms mem) (A R : V) : Prop where
  /-- The carrier is nonempty. -/
  nonempty : ∃ d, mem d A
  /-- The interpretation of membership consists of pairs from the carrier. -/
  pairs : ∀ p, mem p R → ∃ x y, mem x A ∧ mem y A ∧ p = kpair H x y

/-! ## Case analysis on internal natural numbers

The internal arithmetic of `ZF.Zf`, extended by
`BoundedZFCConsistency.OmegaRecursion`, has transitivity, irreflexivity,
injectivity of the successor, and linearity, but not the fact that the
successor is onto the nonzero naturals.  That fact is what makes the shifted
environment *total*, so it is proved here, by the definable-induction
schema. -/

/-- "slot `0` is zero or a successor of an internal natural".

| de Bruijn slot | contents                   |
| -------------- | -------------------------- |
| `0`            | the predecessor `m`        |
| `1`            | the induction variable `n` |
| `k+1`          | the caller's slot `k`      |
-/
def fZeroOrSuccF : Form :=
  fOr (fEmptyF 0) (fEx (fAnd (fNatF 0) (fSuccF 1 0)))

theorem fZeroOrSuccF_spec (H : ZFAxioms mem) (n : V) (e : Nat → V) :
    Sat mem (scons n e) fZeroOrSuccF ↔
      (n = vempty H ∨ ∃ m, mem m (omegaV H) ∧ n = vsucc H m) := by
  constructor
  · rintro (h | ⟨m, hm, hs⟩)
    · exact Or.inl ((fEmptyF_spec H (scons n e) 0).mp h)
    · exact Or.inr ⟨m, (fNatF_spec H (scons m (scons n e)) 0).mp hm,
        (fSuccF_spec H (scons m (scons n e)) 1 0).mp hs⟩
  · rintro (h | ⟨m, hm, hs⟩)
    · exact Or.inl ((fEmptyF_spec H (scons n e) 0).mpr h)
    · exact Or.inr ⟨m, (fNatF_spec H (scons m (scons n e)) 0).mpr hm,
        (fSuccF_spec H (scons m (scons n e)) 1 0).mpr hs⟩

/-- **Every internal natural is zero or a successor.**  The induction is
immediate; what it buys is a case analysis that external recursion cannot
supply, because a nonstandard natural is not reachable from zero by finitely
many external steps. -/
theorem nat_zero_or_succ (H : ZFAxioms mem) :
    ∀ n, mem n (omegaV H) →
      (n = vempty H ∨ ∃ m, mem m (omegaV H) ∧ n = vsucc H m) := by
  intro n hn
  refine (fZeroOrSuccF_spec H n (fun _ => vempty H)).mp ?_
  refine omega_ind H fZeroOrSuccF (fun _ => vempty H) ?_ ?_ n hn
  · exact (fZeroOrSuccF_spec H (vempty H) (fun _ => vempty H)).mpr (Or.inl rfl)
  · intro k hk _
    exact (fZeroOrSuccF_spec H (vsucc H k) (fun _ => vempty H)).mpr
      (Or.inr ⟨k, hk, rfl⟩)

/-! ## Internal environments -/

/-- `E` is an environment over the carrier `A`: an internal function on the
internal omega, all of whose values lie in `A`. -/
def IsEnvOn (H : ZFAxioms mem) (A E : V) : Prop :=
  IsFunctionOn H E (omegaV H) ∧ ∀ n y, mem (kpair H n y) E → mem y A

theorem isEnvOn_apply (H : ZFAxioms mem) {A E : V} (hE : IsEnvOn H A E)
    {n : V} (hn : mem n (omegaV H)) : mem (applyV H E n) A :=
  hE.2 n _ (applyV_mem H (hE.1.2.1 n hn))

/-! ### The constant environment

Existence of at least one environment is what makes the carrier's
nonemptiness the right hypothesis: it is exactly what the quantifier clauses
need in order to be about something. -/

/-- The graph of `fun n => ⟨n, d⟩`, with `d` as the parameter in slot `2`. -/
def psiConstEnvF : Form := fKPairF 0 1 2

theorem psiConstEnvF_rel (H : ZFAxioms mem) (d p n : V) :
    relOf mem psiConstEnvF (fun _ => d) p n ↔ p = kpair H n d := by
  unfold relOf psiConstEnvF
  exact fKPairF_spec H (scons p (scons n (fun _ => d))) 0 1 2

theorem psiConstEnvF_functional (H : ZFAxioms mem) (d : V) :
    Functional (relOf mem psiConstEnvF (fun _ => d)) := by
  intro n p p' h1 h2
  rw [(psiConstEnvF_rel H d p n).mp h1, (psiConstEnvF_rel H d p' n).mp h2]

/-- The environment taking the constant value `d`. -/
noncomputable def constEnv (H : ZFAxioms mem) (d : V) : V :=
  (H.repl psiConstEnvF (fun _ => d) (psiConstEnvF_functional H d)
    (omegaV H)).choose

theorem constEnv_spec (H : ZFAxioms mem) (d p : V) :
    mem p (constEnv H d) ↔ ∃ n, mem n (omegaV H) ∧ p = kpair H n d := by
  unfold constEnv
  rw [(H.repl psiConstEnvF (fun _ => d) (psiConstEnvF_functional H d)
    (omegaV H)).choose_spec p]
  constructor
  · rintro ⟨n, hn, hrel⟩
    exact ⟨n, hn, (psiConstEnvF_rel H d p n).mp hrel⟩
  · rintro ⟨n, hn, hp⟩
    exact ⟨n, hn, (psiConstEnvF_rel H d p n).mpr hp⟩

theorem constEnv_isEnvOn (H : ZFAxioms mem) {A d : V} (hd : mem d A) :
    IsEnvOn H A (constEnv H d) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro x y y' h1 h2
    obtain ⟨n, _, hk⟩ := (constEnv_spec H d (kpair H x y)).mp h1
    obtain ⟨n', _, hk'⟩ := (constEnv_spec H d (kpair H x y')).mp h2
    rw [(kpair_inj H x y n d hk).2, (kpair_inj H x y' n' d hk').2]
  · intro x hx
    exact ⟨d, (constEnv_spec H d (kpair H x d)).mpr ⟨x, hx, rfl⟩⟩
  · intro p hp
    obtain ⟨n, hn, hk⟩ := (constEnv_spec H d p).mp hp
    exact ⟨n, d, hn, hk⟩
  · intro n y hk
    obtain ⟨n', _, hk'⟩ := (constEnv_spec H d (kpair H n y)).mp hk
    rw [(kpair_inj H n y n' d hk').2]
    exact hd

/-- **Environments exist.**  This is the only use of the nonemptiness clause
of `IsSetStructure`. -/
theorem exists_isEnvOn (H : ZFAxioms mem) {A : V} (hA : ∃ d, mem d A) :
    ∃ E, IsEnvOn H A E := by
  obtain ⟨d, hd⟩ := hA
  exact ⟨constEnv H d, constEnv_isEnvOn H hd⟩

/-! ### The shift

`econs H d E` is the internal counterpart of `scons`.  Its successor part is
the image of the internal omega under `n ↦ ⟨n+1, E n⟩`.  That map is rendered
with an explicit uniqueness clause on the value, so that the relation is
functional in every model with no hypothesis on `E`; on a genuine environment
the clause is redundant, and `econs_spec` drops it. -/

/-- The graph of `n ↦ ⟨n+1, E n⟩`, with `E` as the parameter in slot `2`.

| de Bruijn slot | contents                                    |
| -------------- | ------------------------------------------- |
| `0`            | the value `y`, then the successor `s`       |
| `1`            | the output pair `p`, then `y`               |
| `2`            | the input index `n`, then `p`               |
| `3`            | the parameter `E`, then `n`                 |
-/
def psiShiftF : Form :=
  fEx (fAnd (fAnd (fPairMemF 2 0 3) (fAll (fImp (fPairMemF 3 0 4) (fEq 0 1))))
    (fEx (fAnd (fSuccF 0 3) (fKPairF 2 0 1))))

theorem psiShiftF_rel (H : ZFAxioms mem) (E p n : V) :
    relOf mem psiShiftF (fun _ => E) p n ↔
      ∃ y, (mem (kpair H n y) E ∧ ∀ y', mem (kpair H n y') E → y' = y) ∧
        p = kpair H (vsucc H n) y := by
  unfold relOf psiShiftF
  constructor
  · rintro ⟨y, ⟨hmem, huniq⟩, s, hs, hp⟩
    refine ⟨y, ⟨(fPairMemF_spec H _ 2 0 3).mp hmem, fun y' hy' => ?_⟩, ?_⟩
    · exact huniq y' ((fPairMemF_spec H _ 3 0 4).mpr hy')
    · have hs' : s = vsucc H n := (fSuccF_spec H _ 0 3).mp hs
      have hp' : p = kpair H s y := (fKPairF_spec H _ 2 0 1).mp hp
      rw [hp', hs']
  · rintro ⟨y, ⟨hmem, huniq⟩, hp⟩
    refine ⟨y, ⟨(fPairMemF_spec H _ 2 0 3).mpr hmem, fun y' hy' => ?_⟩,
      vsucc H n, (fSuccF_spec H _ 0 3).mpr rfl, (fKPairF_spec H _ 2 0 1).mpr hp⟩
    exact huniq y' ((fPairMemF_spec H _ 3 0 4).mp hy')

theorem psiShiftF_functional (H : ZFAxioms mem) (E : V) :
    Functional (relOf mem psiShiftF (fun _ => E)) := by
  intro n p p' h1 h2
  obtain ⟨y, ⟨_, huy⟩, hp⟩ := (psiShiftF_rel H E p n).mp h1
  obtain ⟨y', ⟨hy', _⟩, hp'⟩ := (psiShiftF_rel H E p' n).mp h2
  rw [hp, hp', huy y' hy']

/-- The image of the internal omega under `n ↦ ⟨n+1, E n⟩`. -/
noncomputable def shiftImg (H : ZFAxioms mem) (E : V) : V :=
  (H.repl psiShiftF (fun _ => E) (psiShiftF_functional H E) (omegaV H)).choose

theorem shiftImg_spec (H : ZFAxioms mem) (E p : V) :
    mem p (shiftImg H E) ↔
      ∃ n, mem n (omegaV H) ∧ ∃ y,
        (mem (kpair H n y) E ∧ ∀ y', mem (kpair H n y') E → y' = y) ∧
        p = kpair H (vsucc H n) y := by
  unfold shiftImg
  rw [(H.repl psiShiftF (fun _ => E) (psiShiftF_functional H E)
    (omegaV H)).choose_spec p]
  constructor
  · rintro ⟨n, hn, hrel⟩
    exact ⟨n, hn, (psiShiftF_rel H E p n).mp hrel⟩
  · rintro ⟨n, hn, hy⟩
    exact ⟨n, hn, (psiShiftF_rel H E p n).mpr hy⟩

/-- **The shifted environment.**  `econs H d E` sends `0` to `d` and `k+1` to
the value of `E` at `k`. -/
noncomputable def econs (H : ZFAxioms mem) (d E : V) : V :=
  vcup H (vsingle H (kpair H (vempty H) d)) (shiftImg H E)

theorem econs_spec (H : ZFAxioms mem) {E : V}
    (hfun : ∀ x y y', mem (kpair H x y) E → mem (kpair H x y') E → y = y')
    (d p : V) :
    mem p (econs H d E) ↔
      (p = kpair H (vempty H) d ∨
        ∃ n, mem n (omegaV H) ∧ ∃ y, mem (kpair H n y) E ∧
          p = kpair H (vsucc H n) y) := by
  unfold econs
  rw [vcup_spec H (vsingle H (kpair H (vempty H) d)) (shiftImg H E) p,
      vsingle_spec H (kpair H (vempty H) d) p, shiftImg_spec H E p]
  constructor
  · rintro (h | ⟨n, hn, y, ⟨hy, _⟩, hp⟩)
    · exact Or.inl h
    · exact Or.inr ⟨n, hn, y, hy, hp⟩
  · rintro (h | ⟨n, hn, y, hy, hp⟩)
    · exact Or.inl h
    · exact Or.inr ⟨n, hn, y, ⟨hy, fun y' hy' => hfun n y' y hy' hy⟩, hp⟩

theorem econs_functional (H : ZFAxioms mem) {E : V}
    (hfun : ∀ x y y', mem (kpair H x y) E → mem (kpair H x y') E → y = y')
    (d : V) :
    ∀ x y y', mem (kpair H x y) (econs H d E) →
      mem (kpair H x y') (econs H d E) → y = y' := by
  intro x y y' h1 h2
  rcases (econs_spec H hfun d (kpair H x y)).mp h1 with h1' | ⟨n, _, u, hu, h1'⟩
  · rcases (econs_spec H hfun d (kpair H x y')).mp h2 with h2' | ⟨n', hn', u', _, h2'⟩
    · rw [(kpair_inj H x y (vempty H) d h1').2,
          (kpair_inj H x y' (vempty H) d h2').2]
    · exfalso
      have hx : x = vempty H := (kpair_inj H x y (vempty H) d h1').1
      have hx' : x = vsucc H n' := (kpair_inj H x y' (vsucc H n') u' h2').1
      rw [hx] at hx'
      exact vempty_spec H n' (by rw [hx']; exact vsucc_self H n')
  · rcases (econs_spec H hfun d (kpair H x y')).mp h2 with h2' | ⟨n', hn', u', hu', h2'⟩
    · exfalso
      have hx : x = vsucc H n := (kpair_inj H x y (vsucc H n) u h1').1
      have hx' : x = vempty H := (kpair_inj H x y' (vempty H) d h2').1
      rw [hx] at hx'
      exact vempty_spec H n (by rw [← hx']; exact vsucc_self H n)
    · have hx : x = vsucc H n := (kpair_inj H x y (vsucc H n) u h1').1
      have hx' : x = vsucc H n' := (kpair_inj H x y' (vsucc H n') u' h2').1
      have hnn : vsucc H n = vsucc H n' := by rw [← hx, hx']
      have hn0 : n = n' := vsucc_inj_omega H n' hn' n hnn
      rw [(kpair_inj H x y (vsucc H n) u h1').2,
          (kpair_inj H x y' (vsucc H n') u' h2').2]
      rw [hn0] at hu
      exact hfun n' u u' hu hu'

/-- **The shift is again an environment.** -/
theorem econs_isEnvOn (H : ZFAxioms mem) {A E d : V} (hE : IsEnvOn H A E)
    (hd : mem d A) : IsEnvOn H A (econs H d E) := by
  have hfun := hE.1.1
  refine ⟨⟨econs_functional H hfun d, ?_, ?_⟩, ?_⟩
  · intro x hx
    rcases nat_zero_or_succ H x hx with hx0 | ⟨m, hm, hx0⟩
    · exact ⟨d, (econs_spec H hfun d (kpair H x d)).mpr (Or.inl (by rw [hx0]))⟩
    · obtain ⟨y, hy⟩ := hE.1.2.1 m hm
      exact ⟨y, (econs_spec H hfun d (kpair H x y)).mpr
        (Or.inr ⟨m, hm, y, hy, by rw [hx0]⟩)⟩
  · intro p hp
    rcases (econs_spec H hfun d p).mp hp with h | ⟨n, hn, y, _, h⟩
    · exact ⟨vempty H, d, vempty_in_omega H, h⟩
    · exact ⟨vsucc H n, y, omega_succ H n hn, h⟩
  · intro n y hk
    rcases (econs_spec H hfun d (kpair H n y)).mp hk with h | ⟨m, _, u, hu, h⟩
    · rw [(kpair_inj H n y (vempty H) d h).2]
      exact hd
    · rw [(kpair_inj H n y (vsucc H m) u h).2]
      exact hE.2 m u hu

/-- The first application equation of the shift. -/
theorem econs_zero (H : ZFAxioms mem) {E : V}
    (hfun : ∀ x y y', mem (kpair H x y) E → mem (kpair H x y') E → y = y')
    (d : V) : applyV H (econs H d E) (vempty H) = d :=
  applyV_eq H (econs_functional H hfun d)
    ((econs_spec H hfun d (kpair H (vempty H) d)).mpr (Or.inl rfl))

/-- The second application equation of the shift. -/
theorem econs_succ (H : ZFAxioms mem) {A E : V} (hE : IsEnvOn H A E) (d : V)
    {n : V} (hn : mem n (omegaV H)) :
    applyV H (econs H d E) (vsucc H n) = applyV H E n :=
  applyV_eq H (econs_functional H hE.1.1 d)
    ((econs_spec H hE.1.1 d (kpair H (vsucc H n) (applyV H E n))).mpr
      (Or.inr ⟨n, hn, applyV H E n, applyV_mem H (hE.1.2.1 n hn), rfl⟩))

/-- "slot `i` is the shift of slot `e_i` by slot `d_i`".

| de Bruijn slot | contents                                          |
| -------------- | ------------------------------------------------- |
| `0`            | the candidate member `p` of the shifted function  |
| `1`            | under the left disjunct: the empty set            |
| `1`,`2`,`3`    | under the right disjunct: `n`, then `y`, then `s` |
| `m+1`          | the caller's slot `m`                             |

The spec is an equality of sets and therefore needs Extensionality; it also
needs the environment slot to be single-valued, because the clean description
of the successor part suppresses the uniqueness clause of `psiShiftF`. -/
def fEconsF (i d_i e_i : Nat) : Form :=
  fSetByF i
    (fOr (fEx (fAnd (fEmptyF 0) (fKPairF 1 0 (d_i+2))))
         (fEx (fAnd (fNatF 0)
            (fEx (fAnd (fPairMemF 1 0 (e_i+3))
               (fEx (fAnd (fSuccF 0 2) (fKPairF 3 0 1))))))))

theorem fEconsF_spec (H : ZFAxioms mem) (ee : Nat → V) (i d_i e_i : Nat)
    (hfun : ∀ x y y', mem (kpair H x y) (ee e_i) →
      mem (kpair H x y') (ee e_i) → y = y') :
    Sat mem ee (fEconsF i d_i e_i) ↔ ee i = econs H (ee d_i) (ee e_i) := by
  refine fSetByF_spec H ee i _ (econs H (ee d_i) (ee e_i)) (fun p => ?_)
  rw [econs_spec H hfun (ee d_i) p]
  constructor
  · rintro (⟨z, hz, hp⟩ | ⟨n, hn, y, hy, s, hs, hp⟩)
    · refine Or.inl ?_
      have hz' : z = vempty H := (fEmptyF_spec H (scons z (scons p ee)) 0).mp hz
      have hp' : p = kpair H z (ee d_i) :=
        (fKPairF_spec H (scons z (scons p ee)) 1 0 (d_i+2)).mp hp
      rw [hp', hz']
    · refine Or.inr ⟨n, (fNatF_spec H (scons n (scons p ee)) 0).mp hn, y,
        (fPairMemF_spec H (scons y (scons n (scons p ee))) 1 0 (e_i+3)).mp hy, ?_⟩
      have hs' : s = vsucc H n :=
        (fSuccF_spec H (scons s (scons y (scons n (scons p ee)))) 0 2).mp hs
      have hp' : p = kpair H s y :=
        (fKPairF_spec H (scons s (scons y (scons n (scons p ee)))) 3 0 1).mp hp
      rw [hp', hs']
  · rintro (hp | ⟨n, hn, y, hy, hp⟩)
    · exact Or.inl ⟨vempty H,
        (fEmptyF_spec H (scons (vempty H) (scons p ee)) 0).mpr rfl,
        (fKPairF_spec H (scons (vempty H) (scons p ee)) 1 0 (d_i+2)).mpr hp⟩
    · exact Or.inr ⟨n, (fNatF_spec H (scons n (scons p ee)) 0).mpr hn, y,
        (fPairMemF_spec H (scons y (scons n (scons p ee))) 1 0 (e_i+3)).mpr hy,
        vsucc H n,
        (fSuccF_spec H
          (scons (vsucc H n) (scons y (scons n (scons p ee)))) 0 2).mpr rfl,
        (fKPairF_spec H
          (scons (vsucc H n) (scons y (scons n (scons p ee)))) 3 0 1).mpr hp⟩

/-- "slot `f_i` is an internal function on the internal omega".

The domain is not passed as a slot: membership in the omega is written with
`fNatF`, which uses the pure intersection characterization and therefore needs
no parameter.

| de Bruijn slot | contents                                     |
| -------------- | -------------------------------------------- |
| `0`            | the innermost bound variable of each clause  |
| `1`, `2`       | the outer bound variables of the same clause |
| `m+n`          | the caller's slot `m` under `n` binders      |
-/
def fFunOnOmegaF (f_i : Nat) : Form :=
  fAnd (fAppC1 f_i)
    (fAnd (fAll (fImp (fNatF 0) (fEx (fPairMemF 1 0 (f_i+2)))))
          (fAll (fImp (fMem 0 (f_i+1))
                  (fEx (fEx (fAnd (fNatF 1) (fKPairF 2 1 0)))))))

theorem fFunOnOmegaF_spec (H : ZFAxioms mem) (ee : Nat → V) (f_i : Nat) :
    Sat mem ee (fFunOnOmegaF f_i) ↔ IsFunctionOn H (ee f_i) (omegaV H) := by
  unfold IsFunctionOn
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(fAppC1_spec H ee f_i).mp h1, ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy⟩ := h2 x ((fNatF_spec H (scons x ee) 0).mpr hx)
      exact ⟨y, (fPairMemF_spec H (scons y (scons x ee)) 1 0 (f_i+2)).mp hy⟩
    · intro p hp
      obtain ⟨x, y, hx, hk⟩ := h3 p hp
      exact ⟨x, y, (fNatF_spec H (scons y (scons x (scons p ee))) 1).mp hx,
        (fKPairF_spec H (scons y (scons x (scons p ee))) 2 1 0).mp hk⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(fAppC1_spec H ee f_i).mpr h1, ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy⟩ := h2 x ((fNatF_spec H (scons x ee) 0).mp hx)
      exact ⟨y, (fPairMemF_spec H (scons y (scons x ee)) 1 0 (f_i+2)).mpr hy⟩
    · intro p hp
      obtain ⟨x, y, hx, hk⟩ := h3 p hp
      exact ⟨x, y, (fNatF_spec H (scons y (scons x (scons p ee))) 1).mpr hx,
        (fKPairF_spec H (scons y (scons x (scons p ee))) 2 1 0).mpr hk⟩

/-- "slot `e_i` is an environment over the carrier in slot `a_i`".

| de Bruijn slot | contents                |
| -------------- | ----------------------- |
| `0`            | the value `y`           |
| `1`            | the index `n`           |
| `m+2`          | the caller's slot `m`   |
-/
def fEnvOnF (e_i a_i : Nat) : Form :=
  fAnd (fFunOnOmegaF e_i)
    (fAll (fAll (fImp (fPairMemF 1 0 (e_i+2)) (fMem 0 (a_i+2)))))

theorem fEnvOnF_spec (H : ZFAxioms mem) (ee : Nat → V) (e_i a_i : Nat) :
    Sat mem ee (fEnvOnF e_i a_i) ↔ IsEnvOn H (ee a_i) (ee e_i) := by
  unfold IsEnvOn
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(fFunOnOmegaF_spec H ee e_i).mp h1, fun n y hk => ?_⟩
    exact h2 n y ((fPairMemF_spec H (scons y (scons n ee)) 1 0 (e_i+2)).mpr hk)
  · rintro ⟨h1, h2⟩
    refine ⟨(fFunOnOmegaF_spec H ee e_i).mpr h1, fun n y hk => ?_⟩
    exact h2 n y ((fPairMemF_spec H (scons y (scons n ee)) 1 0 (e_i+2)).mp hk)

/-! ## Truth bits and evaluation triples

The two truth values are the internal numerals `0` and `1`, so `natV_ne`
separates them.  `vbit` names the bit of a metatheoretic proposition; it is
the only place where the ambient classical logic enters the coding, and it is
harmless, because every proposition it is applied to is rendered by a `Form`
whose satisfaction is the same proposition. -/

/-- The truth bit of a proposition: the internal numeral `1` if it holds and
the internal numeral `0` otherwise. -/
noncomputable def vbit (H : ZFAxioms mem) (p : Prop) : V :=
  @ite V p (Classical.propDecidable p) (natV H 1) (natV H 0)

theorem vbit_pos (H : ZFAxioms mem) {p : Prop} (hp : p) :
    vbit H p = natV H 1 := by
  unfold vbit
  exact if_pos hp

theorem vbit_neg (H : ZFAxioms mem) {p : Prop} (hp : ¬ p) :
    vbit H p = natV H 0 := by
  unfold vbit
  exact if_neg hp

theorem vbit_congr (H : ZFAxioms mem) {p q : Prop} (h : p ↔ q) :
    vbit H p = vbit H q := by
  by_cases hp : p
  · rw [vbit_pos H hp, vbit_pos H (h.mp hp)]
  · rw [vbit_neg H hp, vbit_neg H (fun hq => hp (h.mpr hq))]

theorem vbit_eq_one (H : ZFAxioms mem) (p : Prop) :
    vbit H p = natV H 1 ↔ p := by
  constructor
  · intro h
    by_cases hp : p
    · exact hp
    · rw [vbit_neg H hp] at h
      exact absurd h (natV_ne H (by decide))
  · exact vbit_pos H

theorem vbit_eq_zero (H : ZFAxioms mem) (p : Prop) :
    vbit H p = natV H 0 ↔ ¬ p := by
  constructor
  · intro h hp
    rw [vbit_pos H hp] at h
    exact natV_ne H (by decide) h
  · exact vbit_neg H

/-- The evaluation triple `⟨c, ⟨e, b⟩⟩`: a code, an environment, and a bit,
packaged in the same "head paired with payload" shape as `formCode`. -/
noncomputable def satTriple (H : ZFAxioms mem) (c e b : V) : V :=
  kpair H c (kpair H e b)

theorem satTriple_inj (H : ZFAxioms mem) {c e b c' e' b' : V}
    (h : satTriple H c e b = satTriple H c' e' b') :
    c = c' ∧ e = e' ∧ b = b' := by
  unfold satTriple at h
  obtain ⟨hc, hp⟩ := kpair_inj H _ _ _ _ h
  obtain ⟨he, hb⟩ := kpair_inj H _ _ _ _ hp
  exact ⟨hc, he, hb⟩

/-! ## Object-language macros for the step

Each macro is a genuine `Form` whose arguments are ABSOLUTE de Bruijn slots at
the use site, paired with a spec lemma stating exactly what its satisfaction
means, in the house style of `ZF.Zf` and of `BoundedZFCConsistency.Coding`. -/

/-- "⟨slot `c_i`, slot `e_i`, slot `b_i`⟩ ∈ slot `s_i`".

| de Bruijn slot | contents                |
| -------------- | ----------------------- |
| `0`            | the triple itself       |
| `m+1`          | the caller's slot `m`   |
-/
def fTripleMemF (c_i e_i b_i s_i : Nat) : Form :=
  fEx (fAnd (fTripleF 0 (c_i+1) (e_i+1) (b_i+1)) (fMem 0 (s_i+1)))

theorem fTripleMemF_spec (H : ZFAxioms mem) (ee : Nat → V)
    (c_i e_i b_i s_i : Nat) :
    Sat mem ee (fTripleMemF c_i e_i b_i s_i) ↔
      mem (satTriple H (ee c_i) (ee e_i) (ee b_i)) (ee s_i) := by
  constructor
  · rintro ⟨t, ht, hmem⟩
    have ht' : t = kpair H (ee c_i) (kpair H (ee e_i) (ee b_i)) :=
      (fTripleF_spec H (scons t ee) 0 (c_i+1) (e_i+1) (b_i+1)).mp ht
    have hmem' : mem t (ee s_i) := hmem
    rw [ht'] at hmem'
    exact hmem'
  · intro h
    exact ⟨satTriple H (ee c_i) (ee e_i) (ee b_i),
      (fTripleF_spec H (scons (satTriple H (ee c_i) (ee e_i) (ee b_i)) ee)
        0 (c_i+1) (e_i+1) (b_i+1)).mpr rfl,
      h⟩

/-- "slot `i` = ⟨numeral `t`, ⟨slot `j`, slot `k`⟩⟩" — the code shape of a
binary constructor, with the tag as an external parameter.

| de Bruijn slot | contents                |
| -------------- | ----------------------- |
| `0`            | the numeral of `t`      |
| `m+1`          | the caller's slot `m`   |
-/
def fTagPairF (i t j k : Nat) : Form :=
  fEx (fAnd (fNumF 0 t) (fTripleF (i+1) 0 (j+1) (k+1)))

theorem fTagPairF_spec (H : ZFAxioms mem) (ee : Nat → V) (i t j k : Nat) :
    Sat mem ee (fTagPairF i t j k) ↔
      ee i = kpair H (natV H t) (kpair H (ee j) (ee k)) := by
  constructor
  · rintro ⟨d, hd, hi⟩
    have hd' : d = natV H t := (fNumF_spec H t 0 (scons d ee)).mp hd
    have hi' : ee i = kpair H d (kpair H (ee j) (ee k)) :=
      (fTripleF_spec H (scons d ee) (i+1) 0 (j+1) (k+1)).mp hi
    rw [hi', hd']
  · intro h
    exact ⟨natV H t, (fNumF_spec H t 0 (scons (natV H t) ee)).mpr rfl,
      (fTripleF_spec H (scons (natV H t) ee) (i+1) 0 (j+1) (k+1)).mpr h⟩

/-- "slot `i` = ⟨numeral `t`, slot `j`⟩" — the code shape of a unary
constructor.

| de Bruijn slot | contents                |
| -------------- | ----------------------- |
| `0`            | the numeral of `t`      |
| `m+1`          | the caller's slot `m`   |
-/
def fTagUnF (i t j : Nat) : Form :=
  fEx (fAnd (fNumF 0 t) (fKPairF (i+1) 0 (j+1)))

theorem fTagUnF_spec (H : ZFAxioms mem) (ee : Nat → V) (i t j : Nat) :
    Sat mem ee (fTagUnF i t j) ↔ ee i = kpair H (natV H t) (ee j) := by
  constructor
  · rintro ⟨d, hd, hi⟩
    have hd' : d = natV H t := (fNumF_spec H t 0 (scons d ee)).mp hd
    have hi' : ee i = kpair H d (ee j) :=
      (fKPairF_spec H (scons d ee) (i+1) 0 (j+1)).mp hi
    rw [hi', hd']
  · intro h
    exact ⟨natV H t, (fNumF_spec H t 0 (scons (natV H t) ee)).mpr rfl,
      (fKPairF_spec H (scons (natV H t) ee) (i+1) 0 (j+1)).mpr h⟩

/-- "⟨slot `c_i`, the shift of slot `e_i` by slot `d_i`, numeral `t`⟩ ∈ slot
`s_i`" — the shape the quantifier clauses record.

| de Bruijn slot | contents                     |
| -------------- | ---------------------------- |
| `0`            | the shifted environment      |
| `1`            | that environment, then the bit |
| `m+2`          | the caller's slot `m`        |
-/
def fShiftTripleMemF (c_i d_i e_i s_i t : Nat) : Form :=
  fEx (fAnd (fEconsF 0 (d_i+1) (e_i+1))
    (fEx (fAnd (fNumF 0 t) (fTripleMemF (c_i+2) 1 0 (s_i+2)))))

theorem fShiftTripleMemF_spec (H : ZFAxioms mem) (ee : Nat → V)
    (c_i d_i e_i s_i t : Nat)
    (hfun : ∀ x y y', mem (kpair H x y) (ee e_i) →
      mem (kpair H x y') (ee e_i) → y = y') :
    Sat mem ee (fShiftTripleMemF c_i d_i e_i s_i t) ↔
      mem (satTriple H (ee c_i) (econs H (ee d_i) (ee e_i)) (natV H t))
        (ee s_i) := by
  constructor
  · rintro ⟨E, hE, beta, hbeta, hmem⟩
    have hE' : E = econs H (ee d_i) (ee e_i) :=
      (fEconsF_spec H (scons E ee) 0 (d_i+1) (e_i+1) hfun).mp hE
    have hbeta' : beta = natV H t :=
      (fNumF_spec H t 0 (scons beta (scons E ee))).mp hbeta
    have hmem' :=
      (fTripleMemF_spec H (scons beta (scons E ee)) (c_i+2) 1 0 (s_i+2)).mp hmem
    rw [hE', hbeta'] at hmem'
    exact hmem'
  · intro h
    refine ⟨econs H (ee d_i) (ee e_i),
      (fEconsF_spec H (scons (econs H (ee d_i) (ee e_i)) ee)
        0 (d_i+1) (e_i+1) hfun).mpr rfl,
      natV H t,
      (fNumF_spec H t 0
        (scons (natV H t) (scons (econs H (ee d_i) (ee e_i)) ee))).mpr rfl, ?_⟩
    exact (fTripleMemF_spec H
      (scons (natV H t) (scons (econs H (ee d_i) (ee e_i)) ee))
      (c_i+2) 1 0 (s_i+2)).mpr h

/-- "slot `b_i` is the truth bit of `phi`".  The two disjuncts are the two
rows of the definition of `vbit`; no slot is introduced, so `phi` is read in
the caller's own environment. -/
def fBitOfF (b_i : Nat) (phi : Form) : Form :=
  fOr (fAnd phi (fNumF b_i 1)) (fAnd (fImp phi fBot) (fNumF b_i 0))

theorem fBitOfF_spec (H : ZFAxioms mem) (ee : Nat → V) (b_i : Nat)
    (phi : Form) :
    Sat mem ee (fBitOfF b_i phi) ↔ ee b_i = vbit H (Sat mem ee phi) := by
  by_cases hP : Sat mem ee phi
  · rw [vbit_pos H hP]
    constructor
    · rintro (⟨_, h⟩ | ⟨hn, _⟩)
      · exact (fNumF_spec H 1 b_i ee).mp h
      · exact absurd hP hn
    · intro h
      exact Or.inl ⟨hP, (fNumF_spec H 1 b_i ee).mpr h⟩
  · rw [vbit_neg H hP]
    constructor
    · rintro (⟨h, _⟩ | ⟨_, h⟩)
      · exact absurd h hP
      · exact (fNumF_spec H 0 b_i ee).mp h
    · intro h
      exact Or.inr ⟨fun hq => hP hq, (fNumF_spec H 0 b_i ee).mpr h⟩

/-! ## The local Tarski step

`Justified H A R S c e b` is the eight-clause relation of the module header.
It is *local*: it never mentions satisfaction, only membership in the set `S`
of already-established triples.  Its atomic clauses read the structure off `R`
and off the model's own equality; falsity is always `0`; the three binary
Boolean clauses use the usual truth tables; and the two quantifier clauses
range over `d ∈ A` with the shifted environment.

The bit of a compound clause is written as `vbit` of the corresponding
metatheoretic condition on the subbits.  That makes each truth table an
equation rather than a case list, and it is what makes the functionality proof
a rewrite once the subbits are known to agree. -/

/-- The triple `⟨c, e, b⟩` is justified by the triples recorded in `S`. -/
def Justified (H : ZFAxioms mem) (A R S c e b : V) : Prop :=
  (∃ i j, mem i (omegaV H) ∧ mem j (omegaV H) ∧
      c = kpair H (natV H 0) (kpair H i j) ∧
      b = vbit H (mem (kpair H (applyV H e i) (applyV H e j)) R)) ∨
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
      b = vbit H (b1 = natV H 1 ∨ b2 = natV H 1)) ∨
  (∃ c1, c = kpair H (natV H 6) c1 ∧
      ((b = natV H 1 ∧ ∀ d, mem d A →
          mem (satTriple H c1 (econs H d e) (natV H 1)) S) ∨
       (b = natV H 0 ∧ ∃ d, mem d A ∧
          mem (satTriple H c1 (econs H d e) (natV H 0)) S))) ∨
  (∃ c1, c = kpair H (natV H 7) c1 ∧
      ((b = natV H 0 ∧ ∀ d, mem d A →
          mem (satTriple H c1 (econs H d e) (natV H 0)) S) ∨
       (b = natV H 1 ∧ ∃ d, mem d A ∧
          mem (satTriple H c1 (econs H d e) (natV H 1)) S)))

/-! ### The clauses as formulas

The two atomic clauses and the three binary clauses differ only in a tag and
in a condition on two slots, so each family is rendered once, with the
condition supplied as a formula `rho` read at slots `1` and `0` under four
binders.  The hypothesis `hrho` is stated with the usual offset condition, so
that `rho` may also mention the caller's slots. -/

/-- An atomic clause with tag `t` and value condition `rho`.

| de Bruijn slot | contents                                  |
| -------------- | ----------------------------------------- |
| `0`            | the second index `j`, then the value `v`  |
| `1`            | the first index `i`, then the value `u`   |
| `2`            | under the inner binders: `j`              |
| `3`            | under the inner binders: `i`              |
| `m+2`, `m+4`   | the caller's slot `m`                     |
-/
def fJustAtomF (c_i e_i b_i t : Nat) (rho : Form) : Form :=
  fEx (fEx (fAnd (fAnd (fNatF 1) (fNatF 0))
    (fAnd (fTagPairF (c_i+2) t 1 0)
      (fEx (fEx (fAnd (fAnd (fPairMemF 3 1 (e_i+4)) (fPairMemF 2 0 (e_i+4)))
                      (fBitOfF (b_i+4) rho)))))))

theorem fJustAtomF_spec (H : ZFAxioms mem) (ee : Nat → V)
    (c_i e_i b_i t : Nat) (rho : Form) (Q : V → V → Prop)
    (hE : IsFunctionOn H (ee e_i) (omegaV H))
    (hrho : ∀ ee' : Nat → V, (∀ k, ee' (k + 4) = ee k) →
      (Sat mem ee' rho ↔ Q (ee' 1) (ee' 0))) :
    Sat mem ee (fJustAtomF c_i e_i b_i t rho) ↔
      ∃ i j, mem i (omegaV H) ∧ mem j (omegaV H) ∧
        ee c_i = kpair H (natV H t) (kpair H i j) ∧
        ee b_i = vbit H (Q (applyV H (ee e_i) i) (applyV H (ee e_i) j)) := by
  constructor
  · rintro ⟨i, j, ⟨hi, hj⟩, hc, u, v, ⟨hu, hv⟩, hb⟩
    have hi' : mem i (omegaV H) := (fNatF_spec H (scons j (scons i ee)) 1).mp hi
    have hj' : mem j (omegaV H) := (fNatF_spec H (scons j (scons i ee)) 0).mp hj
    have hc' : ee c_i = kpair H (natV H t) (kpair H i j) :=
      (fTagPairF_spec H (scons j (scons i ee)) (c_i+2) t 1 0).mp hc
    have hu' : mem (kpair H i u) (ee e_i) :=
      (fPairMemF_spec H (scons v (scons u (scons j (scons i ee))))
        3 1 (e_i+4)).mp hu
    have hv' : mem (kpair H j v) (ee e_i) :=
      (fPairMemF_spec H (scons v (scons u (scons j (scons i ee))))
        2 0 (e_i+4)).mp hv
    have hb' : ee b_i =
        vbit H (Sat mem (scons v (scons u (scons j (scons i ee)))) rho) :=
      (fBitOfF_spec H (scons v (scons u (scons j (scons i ee)))) (b_i+4) rho).mp hb
    refine ⟨i, j, hi', hj', hc', ?_⟩
    rw [applyV_eq H hE.1 hu', applyV_eq H hE.1 hv', hb']
    exact vbit_congr H
      (hrho (scons v (scons u (scons j (scons i ee)))) (fun _ => rfl))
  · rintro ⟨i, j, hi, hj, hc, hb⟩
    refine ⟨i, j,
      ⟨(fNatF_spec H (scons j (scons i ee)) 1).mpr hi,
       (fNatF_spec H (scons j (scons i ee)) 0).mpr hj⟩,
      (fTagPairF_spec H (scons j (scons i ee)) (c_i+2) t 1 0).mpr hc,
      applyV H (ee e_i) i, applyV H (ee e_i) j, ⟨?_, ?_⟩, ?_⟩
    · exact (fPairMemF_spec H
        (scons (applyV H (ee e_i) j)
          (scons (applyV H (ee e_i) i) (scons j (scons i ee))))
        3 1 (e_i+4)).mpr (applyV_mem H (hE.2.1 i hi))
    · exact (fPairMemF_spec H
        (scons (applyV H (ee e_i) j)
          (scons (applyV H (ee e_i) i) (scons j (scons i ee))))
        2 0 (e_i+4)).mpr (applyV_mem H (hE.2.1 j hj))
    · refine (fBitOfF_spec H
        (scons (applyV H (ee e_i) j)
          (scons (applyV H (ee e_i) i) (scons j (scons i ee))))
        (b_i+4) rho).mpr ?_
      show ee b_i = vbit H (Sat mem
        (scons (applyV H (ee e_i) j)
          (scons (applyV H (ee e_i) i) (scons j (scons i ee)))) rho)
      rw [hb]
      exact (vbit_congr H (hrho
        (scons (applyV H (ee e_i) j)
          (scons (applyV H (ee e_i) i) (scons j (scons i ee))))
        (fun _ => rfl))).symm

/-- The falsity clause: the code of `fBot` always takes the bit `0`. -/
def fJustBotF (c_i b_i : Nat) : Form :=
  fAnd (fTaggedEmptyF c_i 2) (fNumF b_i 0)

theorem fJustBotF_spec (H : ZFAxioms mem) (ee : Nat → V) (c_i b_i : Nat) :
    Sat mem ee (fJustBotF c_i b_i) ↔
      (ee c_i = kpair H (natV H 2) (vempty H) ∧ ee b_i = natV H 0) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(fTaggedEmptyF_spec H ee c_i 2).mp h1, (fNumF_spec H 0 b_i ee).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(fTaggedEmptyF_spec H ee c_i 2).mpr h1,
      (fNumF_spec H 0 b_i ee).mpr h2⟩

/-- A binary Boolean clause with tag `t` and truth table `rho`.

| de Bruijn slot | contents                |
| -------------- | ----------------------- |
| `0`            | the second subbit `b2`  |
| `1`            | the first subbit `b1`   |
| `2`            | the second subcode `c2` |
| `3`            | the first subcode `c1`  |
| `m+4`          | the caller's slot `m`   |
-/
def fJustBinF (c_i e_i b_i s_i t : Nat) (rho : Form) : Form :=
  fEx (fEx (fEx (fEx
    (fAnd (fTagPairF (c_i+4) t 3 2)
      (fAnd (fAnd (fTripleMemF 3 (e_i+4) 1 (s_i+4))
                  (fTripleMemF 2 (e_i+4) 0 (s_i+4)))
            (fBitOfF (b_i+4) rho))))))

theorem fJustBinF_spec (H : ZFAxioms mem) (ee : Nat → V)
    (c_i e_i b_i s_i t : Nat) (rho : Form) (Q : V → V → Prop)
    (hrho : ∀ ee' : Nat → V, (∀ k, ee' (k + 4) = ee k) →
      (Sat mem ee' rho ↔ Q (ee' 1) (ee' 0))) :
    Sat mem ee (fJustBinF c_i e_i b_i s_i t rho) ↔
      ∃ c1 c2 b1 b2, ee c_i = kpair H (natV H t) (kpair H c1 c2) ∧
        mem (satTriple H c1 (ee e_i) b1) (ee s_i) ∧
        mem (satTriple H c2 (ee e_i) b2) (ee s_i) ∧
        ee b_i = vbit H (Q b1 b2) := by
  constructor
  · rintro ⟨c1, c2, b1, b2, hc, ⟨h1, h2⟩, hb⟩
    refine ⟨c1, c2, b1, b2,
      (fTagPairF_spec H (scons b2 (scons b1 (scons c2 (scons c1 ee))))
        (c_i+4) t 3 2).mp hc,
      (fTripleMemF_spec H (scons b2 (scons b1 (scons c2 (scons c1 ee))))
        3 (e_i+4) 1 (s_i+4)).mp h1,
      (fTripleMemF_spec H (scons b2 (scons b1 (scons c2 (scons c1 ee))))
        2 (e_i+4) 0 (s_i+4)).mp h2, ?_⟩
    have hb' : ee b_i =
        vbit H (Sat mem (scons b2 (scons b1 (scons c2 (scons c1 ee)))) rho) :=
      (fBitOfF_spec H (scons b2 (scons b1 (scons c2 (scons c1 ee))))
        (b_i+4) rho).mp hb
    rw [hb']
    exact vbit_congr H
      (hrho (scons b2 (scons b1 (scons c2 (scons c1 ee)))) (fun _ => rfl))
  · rintro ⟨c1, c2, b1, b2, hc, h1, h2, hb⟩
    refine ⟨c1, c2, b1, b2,
      (fTagPairF_spec H (scons b2 (scons b1 (scons c2 (scons c1 ee))))
        (c_i+4) t 3 2).mpr hc,
      ⟨(fTripleMemF_spec H (scons b2 (scons b1 (scons c2 (scons c1 ee))))
          3 (e_i+4) 1 (s_i+4)).mpr h1,
       (fTripleMemF_spec H (scons b2 (scons b1 (scons c2 (scons c1 ee))))
          2 (e_i+4) 0 (s_i+4)).mpr h2⟩, ?_⟩
    refine (fBitOfF_spec H (scons b2 (scons b1 (scons c2 (scons c1 ee))))
      (b_i+4) rho).mpr ?_
    show ee b_i =
      vbit H (Sat mem (scons b2 (scons b1 (scons c2 (scons c1 ee)))) rho)
    rw [hb]
    exact (vbit_congr H
      (hrho (scons b2 (scons b1 (scons c2 (scons c1 ee)))) (fun _ => rfl))).symm

/-- A quantifier clause with tag `t`: the bit `u` is witnessed by the value `u`
at every `d` in the carrier, and the bit `v` by the value `v` at one such `d`.
Taking `u = 1, v = 0` gives the universal quantifier and `u = 0, v = 1` the
existential one.

| de Bruijn slot | contents                |
| -------------- | ----------------------- |
| `0`            | the carrier element `d` |
| `1`            | the subcode `c1`        |
| `m+2`          | the caller's slot `m`   |
-/
def fJustQuantF (c_i e_i b_i s_i a_i t u v : Nat) : Form :=
  fEx (fAnd (fTagUnF (c_i+1) t 0)
    (fOr (fAnd (fNumF (b_i+1) u)
               (fAll (fImp (fMem 0 (a_i+2))
                 (fShiftTripleMemF 1 0 (e_i+2) (s_i+2) u))))
         (fAnd (fNumF (b_i+1) v)
               (fEx (fAnd (fMem 0 (a_i+2))
                 (fShiftTripleMemF 1 0 (e_i+2) (s_i+2) v))))))

theorem fJustQuantF_spec (H : ZFAxioms mem) (ee : Nat → V)
    (c_i e_i b_i s_i a_i t u v : Nat)
    (hfun : ∀ x y y', mem (kpair H x y) (ee e_i) →
      mem (kpair H x y') (ee e_i) → y = y') :
    Sat mem ee (fJustQuantF c_i e_i b_i s_i a_i t u v) ↔
      ∃ c1, ee c_i = kpair H (natV H t) c1 ∧
        ((ee b_i = natV H u ∧ ∀ d, mem d (ee a_i) →
            mem (satTriple H c1 (econs H d (ee e_i)) (natV H u)) (ee s_i)) ∨
         (ee b_i = natV H v ∧ ∃ d, mem d (ee a_i) ∧
            mem (satTriple H c1 (econs H d (ee e_i)) (natV H v)) (ee s_i))) := by
  constructor
  · rintro ⟨c1, hc, hcase⟩
    refine ⟨c1, (fTagUnF_spec H (scons c1 ee) (c_i+1) t 0).mp hc, ?_⟩
    rcases hcase with ⟨hb, hall⟩ | ⟨hb, d, hd, hdv⟩
    · refine Or.inl ⟨(fNumF_spec H u (b_i+1) (scons c1 ee)).mp hb,
        fun d hd => ?_⟩
      exact (fShiftTripleMemF_spec H (scons d (scons c1 ee))
        1 0 (e_i+2) (s_i+2) u hfun).mp (hall d hd)
    · exact Or.inr ⟨(fNumF_spec H v (b_i+1) (scons c1 ee)).mp hb, d, hd,
        (fShiftTripleMemF_spec H (scons d (scons c1 ee))
          1 0 (e_i+2) (s_i+2) v hfun).mp hdv⟩
  · rintro ⟨c1, hc, hcase⟩
    refine ⟨c1, (fTagUnF_spec H (scons c1 ee) (c_i+1) t 0).mpr hc, ?_⟩
    rcases hcase with ⟨hb, hall⟩ | ⟨hb, d, hd, hdv⟩
    · refine Or.inl ⟨(fNumF_spec H u (b_i+1) (scons c1 ee)).mpr hb,
        fun d hd => ?_⟩
      exact (fShiftTripleMemF_spec H (scons d (scons c1 ee))
        1 0 (e_i+2) (s_i+2) u hfun).mpr (hall d hd)
    · exact Or.inr ⟨(fNumF_spec H v (b_i+1) (scons c1 ee)).mpr hb, d, hd,
        (fShiftTripleMemF_spec H (scons d (scons c1 ee))
          1 0 (e_i+2) (s_i+2) v hfun).mpr hdv⟩

/-- **The step relation as a `Form`**, in the order of the table in the module
header. -/
def fJustifiedF (c_i e_i b_i s_i a_i r_i : Nat) : Form :=
  fOr (fJustAtomF c_i e_i b_i 0 (fPairMemF 1 0 (r_i+4)))
  (fOr (fJustAtomF c_i e_i b_i 1 (fEq 1 0))
  (fOr (fJustBotF c_i b_i)
  (fOr (fJustBinF c_i e_i b_i s_i 3 (fImp (fNumF 1 1) (fNumF 0 1)))
  (fOr (fJustBinF c_i e_i b_i s_i 4 (fAnd (fNumF 1 1) (fNumF 0 1)))
  (fOr (fJustBinF c_i e_i b_i s_i 5 (fOr (fNumF 1 1) (fNumF 0 1)))
  (fOr (fJustQuantF c_i e_i b_i s_i a_i 6 1 0)
       (fJustQuantF c_i e_i b_i s_i a_i 7 0 1)))))))

theorem fJustifiedF_spec (H : ZFAxioms mem) (ee : Nat → V)
    (c_i e_i b_i s_i a_i r_i : Nat)
    (hE : IsFunctionOn H (ee e_i) (omegaV H)) :
    Sat mem ee (fJustifiedF c_i e_i b_i s_i a_i r_i) ↔
      Justified H (ee a_i) (ee r_i) (ee s_i) (ee c_i) (ee e_i) (ee b_i) := by
  have h0 := fJustAtomF_spec H ee c_i e_i b_i 0 (fPairMemF 1 0 (r_i+4))
    (fun x y => mem (kpair H x y) (ee r_i)) hE
    (fun ee' hoff => by rw [fPairMemF_spec H ee' 1 0 (r_i+4), hoff r_i])
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
  have h6 := fJustQuantF_spec H ee c_i e_i b_i s_i a_i 6 1 0 hE.1
  have h7 := fJustQuantF_spec H ee c_i e_i b_i s_i a_i 7 0 1 hE.1
  unfold Justified
  constructor
  · rintro (h | h | h | h | h | h | h | h)
    · exact Or.inl (h0.mp h)
    · exact Or.inr (Or.inl (h1.mp h))
    · exact Or.inr (Or.inr (Or.inl (h2.mp h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (h3.mp h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h4.mp h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h5.mp h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (h6.mp h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (h7.mp h)))))))
  · rintro (h | h | h | h | h | h | h | h)
    · exact Or.inl (h0.mpr h)
    · exact Or.inr (Or.inl (h1.mpr h))
    · exact Or.inr (Or.inr (Or.inl (h2.mpr h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (h3.mpr h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h4.mpr h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h5.mpr h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (h6.mpr h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (h7.mpr h)))))))

/-! ## Certificates

A set is **step-closed** when every triple it records is locally justified by
the set itself, and records only genuine environments.  The environment clause
is not decoration: without it the object-language reading of `applyV` in the
atomic clauses is unavailable, so `fSatClosedF` could not have an
unconditional satisfaction spec.

A **certificate** for `⟨c, e, b⟩` is a step-closed set containing that
triple. -/

/-- Every triple of `S` is justified by `S`, over genuine environments. -/
def SatClosed (H : ZFAxioms mem) (A R S : V) : Prop :=
  ∀ c e b, mem (satTriple H c e b) S →
    (IsEnvOn H A e ∧ Justified H A R S c e b)

/-- "slot `s_i` is step-closed over the carrier `a_i` and the relation `r_i`".

| de Bruijn slot | contents                |
| -------------- | ----------------------- |
| `0`            | the bit `b`             |
| `1`            | the environment `e`     |
| `2`            | the code `c`            |
| `m+3`          | the caller's slot `m`   |
-/
def fSatClosedF (s_i a_i r_i : Nat) : Form :=
  fAll (fAll (fAll (fImp (fTripleMemF 2 1 0 (s_i+3))
    (fAnd (fEnvOnF 1 (a_i+3))
          (fJustifiedF 2 1 0 (s_i+3) (a_i+3) (r_i+3))))))

theorem fSatClosedF_spec (H : ZFAxioms mem) (ee : Nat → V)
    (s_i a_i r_i : Nat) :
    Sat mem ee (fSatClosedF s_i a_i r_i) ↔
      SatClosed H (ee a_i) (ee r_i) (ee s_i) := by
  unfold SatClosed
  constructor
  · intro h c e b hmem
    obtain ⟨h1, h2⟩ := h c e b
      ((fTripleMemF_spec H (scons b (scons e (scons c ee)))
        2 1 0 (s_i+3)).mpr hmem)
    have henv : IsEnvOn H (ee a_i) e :=
      (fEnvOnF_spec H (scons b (scons e (scons c ee))) 1 (a_i+3)).mp h1
    exact ⟨henv, (fJustifiedF_spec H (scons b (scons e (scons c ee)))
      2 1 0 (s_i+3) (a_i+3) (r_i+3) henv.1).mp h2⟩
  · intro h c e b hsat
    obtain ⟨henv, hj⟩ := h c e b
      ((fTripleMemF_spec H (scons b (scons e (scons c ee)))
        2 1 0 (s_i+3)).mp hsat)
    exact ⟨(fEnvOnF_spec H (scons b (scons e (scons c ee))) 1 (a_i+3)).mpr henv,
      (fJustifiedF_spec H (scons b (scons e (scons c ee)))
        2 1 0 (s_i+3) (a_i+3) (r_i+3) henv.1).mpr hj⟩

/-- `S` is a **certificate** assigning the bit `b` to the code `c` under the
environment `e`. -/
structure Certifies (H : ZFAxioms mem) (A R S c e b : V) : Prop where
  /-- Every triple of the certificate is justified by the certificate. -/
  closed : SatClosed H A R S
  /-- The triple in question is recorded. -/
  holds : mem (satTriple H c e b) S

theorem Certifies.justified (H : ZFAxioms mem) {A R S c e b : V}
    (hc : Certifies H A R S c e b) : Justified H A R S c e b :=
  (hc.closed c e b hc.holds).2

theorem Certifies.envOn (H : ZFAxioms mem) {A R S c e b : V}
    (hc : Certifies H A R S c e b) : IsEnvOn H A e :=
  (hc.closed c e b hc.holds).1

/-! ### Inverting the step at a known tag

Codes carrying different tags are different sets, so at a code of known shape
exactly one of the eight clauses can apply.  Each lemma below discards the
other seven by `formCode_tag_ne` and reads off the surviving one. -/

theorem justified_memAtom (H : ZFAxioms mem) {A R S e b i j : V}
    (h : Justified H A R S (kpair H (natV H 0) (kpair H i j)) e b) :
    b = vbit H (mem (kpair H (applyV H e i) (applyV H e j)) R) := by
  unfold Justified at h
  rcases h with ⟨i', j', _, _, hc, hb⟩ | ⟨i', j', _, _, hc, _⟩ | ⟨hc, _⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩ | ⟨_, _, _, _, hc, _, _, _⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩ | ⟨_, hc, _⟩ | ⟨_, hc, _⟩
  · obtain ⟨-, hp⟩ := kpair_inj H _ _ _ _ hc
    obtain ⟨hi, hj⟩ := kpair_inj H _ _ _ _ hp
    rw [hb, hi, hj]
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)

theorem justified_eqAtom (H : ZFAxioms mem) {A R S e b i j : V}
    (h : Justified H A R S (kpair H (natV H 1) (kpair H i j)) e b) :
    b = vbit H (applyV H e i = applyV H e j) := by
  unfold Justified at h
  rcases h with ⟨i', j', _, _, hc, _⟩ | ⟨i', j', _, _, hc, hb⟩ | ⟨hc, _⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩ | ⟨_, _, _, _, hc, _, _, _⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩ | ⟨_, hc, _⟩ | ⟨_, hc, _⟩
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · obtain ⟨-, hp⟩ := kpair_inj H _ _ _ _ hc
    obtain ⟨hi, hj⟩ := kpair_inj H _ _ _ _ hp
    rw [hb, hi, hj]
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)

theorem justified_bot (H : ZFAxioms mem) {A R S e b : V}
    (h : Justified H A R S (kpair H (natV H 2) (vempty H)) e b) :
    b = natV H 0 := by
  unfold Justified at h
  rcases h with ⟨_, _, _, _, hc, _⟩ | ⟨_, _, _, _, hc, _⟩ | ⟨hc, hb⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩ | ⟨_, _, _, _, hc, _, _, _⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩ | ⟨_, hc, _⟩ | ⟨_, hc, _⟩
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact hb
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)

theorem justified_imp (H : ZFAxioms mem) {A R S e b c1 c2 : V}
    (h : Justified H A R S (kpair H (natV H 3) (kpair H c1 c2)) e b) :
    ∃ b1 b2, mem (satTriple H c1 e b1) S ∧ mem (satTriple H c2 e b2) S ∧
      b = vbit H (b1 = natV H 1 → b2 = natV H 1) := by
  unfold Justified at h
  rcases h with ⟨_, _, _, _, hc, _⟩ | ⟨_, _, _, _, hc, _⟩ | ⟨hc, _⟩ |
    ⟨d1, d2, b1, b2, hc, k1, k2, hb⟩ | ⟨_, _, _, _, hc, _, _, _⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩ | ⟨_, hc, _⟩ | ⟨_, hc, _⟩
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
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)

theorem justified_and (H : ZFAxioms mem) {A R S e b c1 c2 : V}
    (h : Justified H A R S (kpair H (natV H 4) (kpair H c1 c2)) e b) :
    ∃ b1 b2, mem (satTriple H c1 e b1) S ∧ mem (satTriple H c2 e b2) S ∧
      b = vbit H (b1 = natV H 1 ∧ b2 = natV H 1) := by
  unfold Justified at h
  rcases h with ⟨_, _, _, _, hc, _⟩ | ⟨_, _, _, _, hc, _⟩ | ⟨hc, _⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩ | ⟨d1, d2, b1, b2, hc, k1, k2, hb⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩ | ⟨_, hc, _⟩ | ⟨_, hc, _⟩
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
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)

theorem justified_or (H : ZFAxioms mem) {A R S e b c1 c2 : V}
    (h : Justified H A R S (kpair H (natV H 5) (kpair H c1 c2)) e b) :
    ∃ b1 b2, mem (satTriple H c1 e b1) S ∧ mem (satTriple H c2 e b2) S ∧
      b = vbit H (b1 = natV H 1 ∨ b2 = natV H 1) := by
  unfold Justified at h
  rcases h with ⟨_, _, _, _, hc, _⟩ | ⟨_, _, _, _, hc, _⟩ | ⟨hc, _⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩ | ⟨_, _, _, _, hc, _, _, _⟩ |
    ⟨d1, d2, b1, b2, hc, k1, k2, hb⟩ | ⟨_, hc, _⟩ | ⟨_, hc, _⟩
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
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)

theorem justified_all (H : ZFAxioms mem) {A R S e b c1 : V}
    (h : Justified H A R S (kpair H (natV H 6) c1) e b) :
    (b = natV H 1 ∧ ∀ d, mem d A →
        mem (satTriple H c1 (econs H d e) (natV H 1)) S) ∨
    (b = natV H 0 ∧ ∃ d, mem d A ∧
        mem (satTriple H c1 (econs H d e) (natV H 0)) S) := by
  unfold Justified at h
  rcases h with ⟨_, _, _, _, hc, _⟩ | ⟨_, _, _, _, hc, _⟩ | ⟨hc, _⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩ | ⟨_, _, _, _, hc, _, _, _⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩ | ⟨d1, hc, hcase⟩ | ⟨_, hc, _⟩
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · obtain ⟨-, h1⟩ := kpair_inj H _ _ _ _ hc
    rw [h1]
    exact hcase
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)

theorem justified_ex (H : ZFAxioms mem) {A R S e b c1 : V}
    (h : Justified H A R S (kpair H (natV H 7) c1) e b) :
    (b = natV H 0 ∧ ∀ d, mem d A →
        mem (satTriple H c1 (econs H d e) (natV H 0)) S) ∨
    (b = natV H 1 ∧ ∃ d, mem d A ∧
        mem (satTriple H c1 (econs H d e) (natV H 1)) S) := by
  unfold Justified at h
  rcases h with ⟨_, _, _, _, hc, _⟩ | ⟨_, _, _, _, hc, _⟩ | ⟨hc, _⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩ | ⟨_, _, _, _, hc, _, _, _⟩ |
    ⟨_, _, _, _, hc, _, _, _⟩ | ⟨_, hc, _⟩ | ⟨d1, hc, hcase⟩
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · exact absurd hc (formCode_tag_ne H (by decide) _ _)
  · obtain ⟨-, h1⟩ := kpair_inj H _ _ _ _ hc
    rw [h1]
    exact hcase

/-! ## Functionality

Two certificates never disagree.  The proof is induction on the code, by
`isFormCodeSem_ind'`, so the property has to be a `Form` together with an
environment: the parameters are the carrier and the relation, and the five
binders are the environment, the two bits, and the two certificates.  The
environment is universally quantified inside the property because the
quantifier clauses apply the induction hypothesis at a *shifted* environment,
not at the one the property started with. -/

/-- The bit a certificate assigns to `c` does not depend on the certificate. -/
def BitUnique (H : ZFAxioms mem) (A R c : V) : Prop :=
  ∀ e b b' S S', Certifies H A R S c e b → Certifies H A R S' c e b' → b = b'

/-- `BitUnique` as a `Form`, with the code in slot `0` of the caller.

| de Bruijn slot | contents                    |
| -------------- | --------------------------- |
| `0`            | the second certificate `S'` |
| `1`            | the first certificate `S`   |
| `2`            | the second bit `b'`         |
| `3`            | the first bit `b`           |
| `4`            | the environment `e`         |
| `5`            | the code `c`                |
| `6`            | the carrier `A`             |
| `7`            | the relation `R`            |
-/
def fBitUniqueF : Form :=
  fAll (fAll (fAll (fAll (fAll
    (fImp (fAnd (fSatClosedF 1 6 7) (fTripleMemF 5 4 3 1))
      (fImp (fAnd (fSatClosedF 0 6 7) (fTripleMemF 5 4 2 0)) (fEq 3 2)))))))

/-- The parameter block of `fBitUniqueF`: the carrier, then the relation. -/
noncomputable def envBitUnique (H : ZFAxioms mem) (A R : V) : Nat → V :=
  scons A (scons R (fun _ => vempty H))

theorem fBitUniqueF_spec (H : ZFAxioms mem) (A R y : V) :
    Sat mem (scons y (envBitUnique H A R)) fBitUniqueF ↔ BitUnique H A R y := by
  unfold BitUnique
  constructor
  · intro h e b b' S S' hc hc'
    exact h e b b' S S'
      ⟨(fSatClosedF_spec H _ 1 6 7).mpr hc.closed,
       (fTripleMemF_spec H _ 5 4 3 1).mpr hc.holds⟩
      ⟨(fSatClosedF_spec H _ 0 6 7).mpr hc'.closed,
       (fTripleMemF_spec H _ 5 4 2 0).mpr hc'.holds⟩
  · intro h e b b' S S' hc hc'
    obtain ⟨h1, h2⟩ := hc
    obtain ⟨h1', h2'⟩ := hc'
    exact h e b b' S S'
      ⟨(fSatClosedF_spec H _ 1 6 7).mp h1, (fTripleMemF_spec H _ 5 4 3 1).mp h2⟩
      ⟨(fSatClosedF_spec H _ 0 6 7).mp h1',
       (fTripleMemF_spec H _ 5 4 2 0).mp h2'⟩

/-- **Certificates are single-valued.**  For every code — including the
nonstandard ones, which are not quotations of any external formula — any two
certificates assign the same bit under the same environment.

The atomic and falsity cases are equations between the same `vbit`; the three
Boolean cases apply the induction hypothesis to the two subcodes under the
same environment; and the two quantifier cases apply it at a shifted
environment, where a disagreement would put both bits at one and the same
triple. -/
theorem certificate_bit_unique (H : ZFAxioms mem) (A R : V) :
    ∀ c, IsFormCodeSem H c → BitUnique H A R c := by
  refine isFormCodeSem_ind' H (BitUnique H A R) fBitUniqueF (envBitUnique H A R)
    (fun y => (fBitUniqueF_spec H A R y).symm) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro _ _ _ _ e b b' S S' hc hc'
    rw [justified_memAtom H (Certifies.justified H hc),
        justified_memAtom H (Certifies.justified H hc')]
  · intro _ _ _ _ e b b' S S' hc hc'
    rw [justified_eqAtom H (Certifies.justified H hc),
        justified_eqAtom H (Certifies.justified H hc')]
  · intro e b b' S S' hc hc'
    rw [justified_bot H (Certifies.justified H hc),
        justified_bot H (Certifies.justified H hc')]
  · intro x y hx hy e b b' S S' hc hc'
    obtain ⟨b1, b2, k1, k2, hb⟩ := justified_imp H (Certifies.justified H hc)
    obtain ⟨b1', b2', k1', k2', hb'⟩ :=
      justified_imp H (Certifies.justified H hc')
    have e1 : b1 = b1' := hx e b1 b1' S S' ⟨hc.closed, k1⟩ ⟨hc'.closed, k1'⟩
    have e2 : b2 = b2' := hy e b2 b2' S S' ⟨hc.closed, k2⟩ ⟨hc'.closed, k2'⟩
    rw [hb, hb', e1, e2]
  · intro x y hx hy e b b' S S' hc hc'
    obtain ⟨b1, b2, k1, k2, hb⟩ := justified_and H (Certifies.justified H hc)
    obtain ⟨b1', b2', k1', k2', hb'⟩ :=
      justified_and H (Certifies.justified H hc')
    have e1 : b1 = b1' := hx e b1 b1' S S' ⟨hc.closed, k1⟩ ⟨hc'.closed, k1'⟩
    have e2 : b2 = b2' := hy e b2 b2' S S' ⟨hc.closed, k2⟩ ⟨hc'.closed, k2'⟩
    rw [hb, hb', e1, e2]
  · intro x y hx hy e b b' S S' hc hc'
    obtain ⟨b1, b2, k1, k2, hb⟩ := justified_or H (Certifies.justified H hc)
    obtain ⟨b1', b2', k1', k2', hb'⟩ :=
      justified_or H (Certifies.justified H hc')
    have e1 : b1 = b1' := hx e b1 b1' S S' ⟨hc.closed, k1⟩ ⟨hc'.closed, k1'⟩
    have e2 : b2 = b2' := hy e b2 b2' S S' ⟨hc.closed, k2⟩ ⟨hc'.closed, k2'⟩
    rw [hb, hb', e1, e2]
  · intro x hx e b b' S S' hc hc'
    rcases justified_all H (Certifies.justified H hc) with
      ⟨hb, hall⟩ | ⟨hb, d, hd, hdz⟩
    · rcases justified_all H (Certifies.justified H hc') with
        ⟨hb', _⟩ | ⟨hb', d', hd', hdz'⟩
      · rw [hb, hb']
      · exact absurd (hx (econs H d' e) (natV H 1) (natV H 0) S S'
          ⟨hc.closed, hall d' hd'⟩ ⟨hc'.closed, hdz'⟩) (natV_ne H (by decide))
    · rcases justified_all H (Certifies.justified H hc') with
        ⟨hb', hall'⟩ | ⟨hb', _⟩
      · exact absurd (hx (econs H d e) (natV H 0) (natV H 1) S S'
          ⟨hc.closed, hdz⟩ ⟨hc'.closed, hall' d hd⟩) (natV_ne H (by decide))
      · rw [hb, hb']
  · intro x hx e b b' S S' hc hc'
    rcases justified_ex H (Certifies.justified H hc) with
      ⟨hb, hall⟩ | ⟨hb, d, hd, hdo⟩
    · rcases justified_ex H (Certifies.justified H hc') with
        ⟨hb', _⟩ | ⟨hb', d', hd', hdo'⟩
      · rw [hb, hb']
      · exact absurd (hx (econs H d' e) (natV H 0) (natV H 1) S S'
          ⟨hc.closed, hall d' hd'⟩ ⟨hc'.closed, hdo'⟩) (natV_ne H (by decide))
    · rcases justified_ex H (Certifies.justified H hc') with
        ⟨hb', hall'⟩ | ⟨hb', _⟩
      · exact absurd (hx (econs H d e) (natV H 1) (natV H 0) S S'
          ⟨hc.closed, hdo⟩ ⟨hc'.closed, hall' d hd⟩) (natV_ne H (by decide))
      · rw [hb, hb']

/-- **Functionality**, in the form later modules consume: a code and an
environment determine the bit, whichever certificates produce it. -/
theorem certificate_functional (H : ZFAxioms mem) (A R : V) {c : V}
    (hcode : IsFormCodeSem H c) {e b b' S S' : V}
    (h : Certifies H A R S c e b) (h' : Certifies H A R S' c e b') : b = b' :=
  certificate_bit_unique H A R c hcode e b b' S S' h h'

/-! ## Totality, and what it would take

Nothing above asserts that a certificate exists.  The statement left open is

```text
∀ c, IsFormCodeSem H c → ∀ e, IsEnvOn H A e → ∃ S b, Certifies H A R S c e b
```

for a structure `IsSetStructure H A R`, again by `isFormCodeSem_ind'`.  The
atomic and falsity cases are one-point certificates and the Boolean cases are
unions of two, but the quantifier cases need a certificate for the subcode
uniformly in `d ∈ A`.  The per-`d` certificates therefore have to be collected
by Replacement along a definable choice of certificate — a definable choice,
because Replacement carves out images along a `Form`, not along an arbitrary
Lean function — and their union has to be shown step-closed, which is where
`SatClosed` being a conjunction over the elements of the union does the work.

Until that is proved, `Certifies` is a single-valued *partial* assignment and
must not be read as a satisfaction relation. -/

end InternalSat

end BoundedZFCConsistency
end LeanProofs
