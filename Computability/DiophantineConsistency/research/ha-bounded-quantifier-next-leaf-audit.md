# Bounded quantifiers after genuine HA order decidability

Read-only proposal by `circuit_reduction`, 2026-10-26. The interval prerequisite
has been authorized as a separate implementation. The bounded-quantifier
construction below remains a proposal, not a proved endpoint or an accepted
normalization of the actual proof checker.

## Exact target syntax

Use the existing PAHF `Term`/`Formula` and the actual `HA.Proves` relation.
Writing `dec a := a ∨ ¬a`, the proposed literal definitions are:

```lean
ball (t : Term) (a : Formula) :=
  Formula.all (.imp (ltFormula (.var 0) (Term.rename Nat.succ t)) a)
bex (t : Term) (a : Formula) :=
  Formula.ex (.and (ltFormula (.var 0) (Term.rename Nat.succ t)) a)
```

The free slot zero of `a` is the quantified witness. Its slots one and above
are the ambient parameters. The bound `t` is an outer-context term, so it is
shifted under this binder and cannot depend on that witness. This convention
retains arbitrary sparse parameters and nested binders.

The desired genuine HA theorems are, for arbitrary `t` and `a`:

```text
HA.Proves ((∀x. dec a) → dec (ball t a))
HA.Proves ((∀x. dec a) → dec (bex t a)).
```

These are object-language implications. The uniform decision hypothesis is
itself an HA formula, rather than a Lean `Decidable` instance, a model
`ProperOn` assumption, or an assertion that every standard instance happens
to be provable. A convenience theorem accepting an actual proof of that
universal formula, and a relative-context theorem accepting its actual
derivation under `G`, would follow by weakening and modus ponens.

## Small prerequisite and proof route

The first separated leaf `HAStrictIntervals` should prove:

* `HA.Proves (¬ltFormula s 0)`;
* `HA.Proves (ltFormula s (S s))`;
* both HA implications in `ltFormula s (S t) ↔ (ltFormula s t ∨ s=t)`.

In the existing interpretation, `s<t` is literally an existential witness
for `s+S d=t`. For the successor split, eliminate the actual `d` and use the
already proved HA natural-case formula `d=0 ∨ ∃e.d=S e`. The zero case gives
`S s=S t`, then `s=t`. The successor case applies successor injectivity to
`s+S(S e)=S t`, retaining `e` as the actual witness for `s<t`. Reverse
implications use witness zero or a successor witness (or the already proved
transitivity and `t<S t`). The empty interval uses `add_succ` and
`succ_ne_zero`. No order DNE or arithmetic semantic oracle is required.

The next, currently unimplemented, leaf would prove the empty-bound cases and
the actual HA successor equivalences:

```text
ball (S t) a ↔ (ball t a ∧ a[t])
bex  (S t) a ↔ (bex  t a ∨ a[t]),
```

where `a[t]` is `Formula.subst (Formula.instTerm t) a`. Equality transport of
the matrix uses the existing actual Leibniz eliminator with the complete
matrix and shifted contexts. It cannot replace arbitrary free-variable
occurrences by an informal substitution.

Finite intuitionistic case analysis proves conjunction/disjunction decisions
from decisions of their two operands. Apply genuine HA formula induction to
the bound, under the finite context containing `∀x.dec a`. One convenient
induction body pairs the universal and existential decisions. Insert the new
bound slot into the matrix using
`aPlus := Formula.rename (SetTheory.up Nat.succ) a`: witness slot zero remains
zero, while every ambient parameter shifts past the induction variable.
At each successor step, instantiate the shifted universal premise at the
current bound. The base cases need no decision premise. Finally instantiate
the proved universal induction conclusion at arbitrary outer term `t`.

The required binder identities reduce to the already available
`Formula.subst_comp`, `Formula.subst_instTerm_rename_up`,
`Formula.subst_instTerm_var_zero_rename_up_succ`, and `Formula.subst_ext`.
Two explicit identities about substituting under the bound-witness binder
while renaming with `up succ` should be proved and tested. In particular,
substituting a bound does not capture an ambient parameter using slot zero.
Checks should include bound zero/one, a matrix with nested quantifiers,
variables zero and seven, and successor-renamed finite contexts.

This proof does not infer `∃x.¬a` from `¬∀x.a` in general. It builds decisions
by finite successor decompositions. It also does not eliminate double
negations of arbitrary existential arithmetic statements.

## Available proofs and exact cache boundary

The accepted `FoundationHAOrderDecidable` main proves actual HA order
decidability/stability and capture-safe right transport. It imports the proved
plain trichotomy and irreflexivity. `HAEqualityDecidable` proves actual
equality decisions, not only GG images. `HABasicArithmetic.Arithmetic.induction`
opens the conventional formula-induction axiom and retains finite contexts.
`Relative.all_intro`/`ex_elim` require sentence axioms and shift every open
assumption; those side conditions must be kept in the new construction.

An import of `FoundationHAOrderDecidable` selects **99 cached current-source
modules**, **76 Foundation modules**, **327 cached artifacts**, and **34
external boundary names**. This is the existing 98-module closure plus the
accepted decidability main. All 98 source/object records plus that new main
were rehashed during this audit. The interval implementation uses root's
independently freshly checked main object:

```text
/tmp/foundation-ha-order-decidable-root-peer-uoenjcjc/lib/
  DiophantineConsistency/FoundationHAOrderDecidable.olean
SHA d808204fd0e3efc97ef90e9cbfd16189ca2d8aca72984a96fadfafacc01efa9c
```

Its root result record SHA is
`7248b43fe1b36937cb4e65bddd20dcd9acf2b71a592a769dc45dddacf2bed9cb`.
An eventual bounded-quantifier leaf importing the frozen interval main would
have 100 cached custom modules with the same Foundation/package boundary,
assuming no additional imports. Neither stage needs a Foundation rebuild.

Relevant source pins:

| Source | SHA-256 |
|---|---|
| `HABasicArithmetic.lean` | `7922744c26ffd0b307b019696197aaa3cdb5acd49ed173e158d6e3a29011e3a2` |
| `HANaturalCases.lean` | `7c1552f2f650238b04b7fc2fb142c2ab3aaf7885278f6e49aaaf66b8c5e1b1a3` |
| `HAEqualityDecidable.lean` | `3decb32e7c5bd2bdf2d45b9ce73f1ff85752d5d0927cbb45c1a0940c672985cd` |
| `FoundationPAHFSyntax.lean` | `6ef6d070feed7382fe5e90fbb1edf9dba41aae33e3ca65b049c16a1b015ede35` |
| `FoundationHAOrderDecidable.lean` | `353549b5ac2dcc51e84b7a8ac7f9714cd66e7eaa28e1df90007ed7598b3ba006` |

## Actual Foundation checker remains a separate bridge

The read source is the pinned Foundation checkout at
`/home/codex/src/Proofs/lib/FormalizedFormalLogic-Foundation`.

`Foundation/FirstOrder/Arithmetic/Basic/Hierarchy.lean:10` defines the actual
hierarchy syntax. At level zero its constructors include atoms/negative atoms,
conjunction/disjunction and bounded quantifiers. The bounded constructor's
`t.Positive` excludes bound variable zero from the bound term:
`Foundation/Syntax/Predicate/Term.lean:129` defines it as positivity of every
bound-variable index, not numerical positivity of the term's value.

`Foundation/FirstOrder/Basic/Operator.lean:428` defines `ballLT` using the
shifted bound. In the classical source syntax,
`Foundation/FirstOrder/Basic/Syntax/Formula.lean:133` gives
`ball = ∀(bound → matrix)`, where source implication is `¬bound ∨ matrix`.
The eventual comparison to the PAHF bounded formula must account for this
literal source GG encoding; it is not definitional identification with a
primitive intuitionistic implication. The existing checked logical adapter
can be reused rather than copying the GG recursion.

Crucially, `Foundation/FirstOrder/Bootstrapping/Syntax/Proof/Basic.lean:478`
defines `proof T` as a **Δ1 pair**, whose sigma member is an existential
formula using `insertDef` and `derivationOf.sigma`. The latter contains the
Δ1 derivation fixed point. Line 482 defines `provable T` by a further
existential proof code; `provabilityPred` substitutes the quoted sentence.
`Foundation/FirstOrder/Incompleteness/Consistency.lean:36` wraps its negation
as the actual consistency sentence.

Thus a bounded-matrix decision theorem, even after proved, is not by itself
a literal decision or normalization theorem for `proof T`. An exact
source-bound HA normal-form/GG comparison is still needed for this checker
syntax, with any auxiliary unbounded existential witnesses handled honestly.
Classical IΣ1 `ProperOn`, a model-defined Δ1 relation, or the assertion that
the target is Π1 does not provide that HA proof. No Markov principle,
positive Σ1 DNE, or blanket Π1 stability is being asserted.

The hierarchy source SHA is
`c9ac3be94e6691675ae3d37ed2d9e6a03abc0cd22a970db321ee447ea3eb14bf`;
the proof-encoding source SHA is
`72e3cf386967e3fed4366ee5aa59678a0333cd2f40c8dbb09bebbf8dd4fa80e3`.
No source/cache changes or compiler runs were part of this read-only audit.
