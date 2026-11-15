# A guarded compiler from arithmetic derivations to the relational source theory

The direction `¬Halt(M₁₉₄) → Con(PA)` needs, in every candidate-PRA model whose arithmetic
reduct satisfies `𝗜𝚺₁`, a refutation in the relational source theory from a refutation in
`ordinaryPAeq` (`OrdinaryCompiler` of
[`pa194-model-logic`](../pa194-model-logic/ORDINARY-SOURCE-COMPILER.md)). The route there is
`conditional_compile`: an induction over an internal derivation that keeps a source
derivation of the translated sequent, with four rule suppliers left as hypotheses
(`RemainingRules`).

This directory replaces the invariant of that induction, proves the rules that are syntactic
for the new invariant, and reduces the compiler to an interface with no packet and no size
condition (`Interpretation`).

## Why the invariant has to change

`conditional_refutation` instantiates the packet as `rootParameters d`, whose free environment
is `d+1` copies of the source free variable `&0`, and the invariant is "the source theory
derives the translated sequent".

- A free variable of the arithmetic language is translated to a source variable, and the
  translation of an atom contains the domain formula of every variable it reads
  (`variableValue z x = Dom(z) ∧ z = x`). `ordinaryPAeq` derives the sequent `{&0 = &0}`, but
  the source theory does not derive its translation: in a model of the source theory with an
  element outside the ordinal domain, the translation is false at that element. So the
  invariant fails for a derivable sequent, and `RemainingRules U T (rootParameters d)` is
  false in the standard model for a large enough `d` (walk a derivation of `{&0 = &0}`: the
  rules already proved preserve the invariant, so one of the four fields fails).
- All free variables are sent to the same source variable. The premise of a universal
  introduction is derivable for a fresh variable; after the collapse the fresh variable is
  identified with the variables of the context, and the translated premise no longer
  entails the translated conclusion.

This is an argument on paper. No theorem here states that `RemainingRules` is refutable; that
would need a model of the source theory in Lean.

## The guarded calculus

`GDerivable T Δ`: the source theory derives `Δ` together with the guards `¬Dom(&i)` below
some bound. Because the bound is existential, guarded derivations combine by weakening. The
quantifier rules are relativized to the domain: a universal introduction turns the guard of
its eigenvariable into the domain hypothesis of the quantifier (`all_rel`), and an
existential introduction with a free variable as witness takes the domain formula of the
witness from the guards (`ex_rel`). At the root of a refutation the sequent is `{⊥}` and the
guards are removed one at a time (`discharge_guards`): the guard of `&0` is generalized, cut
against `∃x Dom(x)`, and the other guards move down by one index.

The packet is an *identity packet*: its free environment sends the free variable `i` to the
source free variable `i`, so distinct variables stay distinct. The translation under such a
packet does not depend on its length (`formula_ext`), which gives the translation `tr` of a
formula of arity zero and `trBody` of a formula under one binder, with no size condition.

## Modules

| Module | Content |
| --- | --- |
| `PA194GuardedCompile` | `guard`, `guards` with their definability, shift and membership lemmas, and `discharge_guards`: from `Provable T (∃x Dom(x))` and a derivation of `guards n ∪ {⊥}`, a proof of `⊥`. |
| `PA194TranslateShift` | `formula_shift`: for packets related by `EnvShiftRel` (every environment term shifted, the free environment re-indexed by one), the translation of `shift p` is the shift of the translation of `p`. Proved for every internally valid formula code by `𝚷₁` structural induction over terms (`term_shift`) and formulas, from shift lemmas for the fixed templates and the value constructors. `IdentityPacket`, `translateFormula_shift`. |
| `PA194TranslateSubst` | `formula_subst`: for a substitution of the arithmetic language whose entries are variables and packets related by `EnvSubstRel`, the translation of the substituted formula is a source substitution applied to the translation. `translateFormula_substs1_fvar`: instantiating the bound variable of a formula of arity one by a free variable. `translateFormula_free`: the translation of `free p` is `free` of the translation of `p` under one binder. |
| `PA194TranslateExt` | `formula_ext`: two packets that agree on the bound environment and on the free entries below both lengths translate a formula below both lengths to the same code. `idParam` (identity packets from Foundation's `fvarVec`), `tr`, `trBody`, and the lemmas `tr_and`, `tr_or`, `tr_all`, `tr_exs`, `tr_neg`, `tr_shift`, `tr_substs1_fvar`, `tr_free`. |
| `PA194GuardedCalculus` | `GDerivable` with weakening, the logical axiom, verum, conjunction, disjunction, cut, shift, `all_rel`, `ex_rel`, and `root` (a guarded refutation is a refutation when the domain is inhabited). |
| `PA194TrCompile` | `Interpretation U T`: for every internal axiom `φ` of `U` a guarded proof of `tr φ`; for every formula `p` of arity one and term `t` that is not a free variable, a guarded derivation of `{¬tr(p[t]), tr(∃p)}`; and `Provable T (∃x Dom(x))`. `tr_compile`: the induction over an internal derivation, all ten rules. `refutation_of_interpretation`: a refutation in `U` gives `Provable T ⊥`. |
| `PA194Leibniz` | `TermFacts T`: three facts about terms (below). `leibniz`: for every internal formula `p` of arity one, term `t` and free variable `c`, a guarded derivation of `{¬tr(&c = t), ¬tr(p[t]), tr(p[&c])}`. Opening a quantifier of `p` shifts the free variables of `t`, so the induction is over the coded triples `(p, t, c)` with the formula complexity as measure (`measured_bounded_sigma1_order_induction`); the quantifier cases use `free_subst_qVec` (opening the quantified variable of `q[#0, t]` gives `(free1 q)[shift t]`). `witness_of_termFacts`: the `witness` field of `Interpretation`, by eliminating `c` against `tr(∃x. x = t)`. `interpretation_of_termFacts` assembles `Interpretation` from `TermFacts`, the axioms and the inhabitation of the domain. |
| `PA194TermNames` | Three formulas of the arithmetic language in which the naming variable is quantified: `nameAll s s'` (every `x` with `x = s` has `x = s'`), `uniq s` (two names of `s` are equal), `exName s` (some `x` has `x = s`). `NameFacts T`: seventeen guarded facts, each about one function layer with arbitrary internal terms as arguments (below). `uniq_all`, `exName_all`: by induction over the term. `nameSubst`: names transfer along a substitution `a[u] ↦ a[w]` once they transfer from `u` to `w`, by induction over `a`. `termFacts_of_nameFacts`: `TermFacts T`. Because the naming variable is bound inside the formulas, no step of these inductions opens a quantifier: each is a cut. |

All statements are for an arbitrary model `V` of `𝗜𝚺₁`, arbitrary `Δ₁` theories `U` and `T`
of the two languages, and internally valid codes that may be nonstandard.

## What is open

`OrdinaryCompiler` follows from `Interpretation ordinaryPAeq adjunctiveFullSepTheory` in every
model. None of its three fields is proved for these theories.

- `witness`, the existential introduction at a function term, is reduced to `TermFacts T`
  (`witness_of_termFacts`) and that to `NameFacts T` (`termFacts_of_nameFacts`). The
  seventeen fields of `NameFacts` are not proved. Each is a guarded derivation of the
  translation of a formula that `ordinaryPAeq` proves, with `s, s', …` arbitrary internal
  terms of arity zero:
  - `nRefl`: `nameAll s s`;
  - `atomTransfer`: `nameAll s₁ s₁' → nameAll s₂ s₂' → s₁ = s₂ → s₁' = s₂'`;
  - `nameOfUniq`: `uniq t → &c = t → nameAll t &c`, and `nameOfEq`: `&c = t → nameAll &c t`;
  - `nSucc`, `nAdd`, `nMul`: `nameAll` passes through one function symbol;
  - `uVar`, `uZero`, `uSucc`, `uAdd`, `uMul`: `uniq` for a variable and for zero, and through
    one function symbol;
  - `eVar`, `eZero`, `eSucc`, `eAdd`, `eMul`: the same for `exName`.

  In each the translation of the arguments occurs only as a subformula that is not looked
  into (the value formula of `s`), so the proofs are first-order arguments in the source
  theory with those subformulas as parameters, from fixed facts about the ordinal domain:
  order isomorphism is an equivalence there, zero exists and is unique up to isomorphism,
  and successor, addition and multiplication are total and respect isomorphism. None of
  these seventeen is written.
- `axioms`: a guarded proof of the translation of each fixed axiom of `ordinaryPAeq` and of
  each closed induction instance. `pa194-model-logic` works on these under `rootParameters`.
  For a sentence that translation should equal `tr`, by `formula_ext` restricted to formulas
  without free variables; that lemma is not written.
- `inhabited` for the actual source theory. The standard development has a derivation of it
  from the empty-set formula (`emptyFoundationDerivation` of
  [`pa194-foundation-ordinal`](../pa194-foundation-ordinal/README.md)); it is not yet
  transported to models here.

Nothing here yields a consistency implication.

## Checking

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-guarded-compiler/check.sh
```

runs [`check_bridge.py`](../pa194-model-fairness/check_bridge.py) with each module as the top
module, passing its arguments on (for example `--out DIR` to reuse compiled objects). On
2026-11-15 the eight modules were compiled directly with `lean`, in dependency order, against
objects of the standalone modules they import (the import closure of
`PA194ConditionalRefutation` and `PA194OrderIsoRew`, compiled from the repository sources at
`34c4c35edc`). The thirty-four axiom reports are `[propext, Classical.choice, Quot.sound]`.
The script itself has not been run.

Two incremental replays against the repository sources were made for an earlier state of this
directory, before `PA194GuardedCalculus` and `PA194TrCompile` existed and while the compiler
had a fixed guard bound (modules `PA194GuardedCompile`, `PA194TranslateShift`,
`PA194TranslateSubst`, `PA194GuardedEndpoint`, and then `PA194TranslateExt`).

- The first, after the shared PairGraph syntax change, rebuilt `PA194ConditionalRefutation`
  and those four modules, reported the twenty axiom audits they had then, and found no
  `sorryAx`. The dispatcher, sequent, Foundation and other listed overlays were prebuilt, so
  it was not a clean transitive build.
- The second rebuilt `PA194TranslateExt` against the result of the first; its seven axiom
  reports passed with no `sorryAx`, with transitive dependencies prebuilt.

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-guarded-compiler/check-incremental.sh "$PWD" NEW_EMPTY_OUTPUT
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-guarded-compiler/check-translate-ext.sh "$PWD" NEW_EMPTY_OUTPUT
```

`check-incremental.sh` now lists the current eight modules with their report counts, because
`PA194GuardedEndpoint` no longer exists. In that form it has not been run. It writes
`PA194TranslateExt` into its output directory, so `check-translate-ext.sh` is only needed to
replay that module alone.
