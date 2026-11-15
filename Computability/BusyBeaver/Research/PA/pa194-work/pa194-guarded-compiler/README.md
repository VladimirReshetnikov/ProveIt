# A guarded compiler from arithmetic derivations to the relational source theory

The direction `¬Halt(M₁₉₄) → Con(PA)` needs, in every candidate-PRA model whose arithmetic
reduct satisfies `𝗜𝚺₁`, a refutation in the relational source theory from a refutation in
`ordinaryPAeq` (`OrdinaryCompiler` of
[`pa194-model-logic`](../pa194-model-logic/ORDINARY-SOURCE-COMPILER.md)). The route there is
`conditional_compile`: an induction over an internal derivation that keeps a source
derivation of the translated sequent, with four rule suppliers left as hypotheses
(`RemainingRules`).

This directory replaces the invariant of that induction and proves three of the suppliers
for the new one.

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

## The guarded invariant

`Guarded T param n s`: the source theory derives `guards n ∪ translatedSequent param s`,
where `guards n` is the coded set of the formulas `¬Dom(&i)` for `i < n`, and `n` is the code
of the derivation. The packet is an *identity packet* (`IdentityPacket`): its free
environment sends the free variable `i` to the source free variable `i`, so distinct
variables stay distinct. `identityPacket_exists` gives one of every length.

At the root of a refutation the sequent is `{⊥}` and the guards are removed one at a time
(`discharge_guards`): the guard of `&0` is generalized, cut against `∃x Dom(x)`, and the
other guards move down by one index.

## Modules

| Module | Content |
| --- | --- |
| `PA194GuardedCompile` | `guard`, `guards` with their definability, shift and membership lemmas. `GuardedRules`: the universal, existential, shift and theory-axiom rules for the invariant `Guarded`. `guarded_compile`: the induction over an internal derivation, with the logical axiom, verum, conjunction, disjunction, weakening and cut cases proved from Foundation's `Derivable` rules. `discharge_guards` and `guarded_refutation`: a refutation in `U` gives `Provable T ⊥`, from `GuardedRules` and `Provable T (∃x Dom(x))`. |
| `PA194TranslateShift` | `formula_shift`: for packets related by `EnvShiftRel` (every environment term shifted, the free environment re-indexed by one), the translation of `shift p` is the shift of the translation of `p`. Proved for every internally valid formula code by `𝚷₁` structural induction over terms (`term_shift`) and formulas, from shift lemmas for the fixed templates and the value constructors. `translateFormula_shift` is the instance for an identity packet, and `shiftRule_guarded` is the shift rule. |
| `PA194TranslateSubst` | `formula_subst`: for a substitution of the arithmetic language whose entries are variables and packets related by `EnvSubstRel`, the translation of the substituted formula is a source substitution applied to the translation. `translateFormula_substs1_fvar`: instantiating the bound variable of a formula of arity one by a free variable. `translateFormula_free`: the translation of `free p` is `free` of the translation of `p` under one binder. `allRule_guarded`: the universal rule. |
| `PA194GuardedEndpoint` | `exsRule_guarded_fvar`: the existential rule when the witness is a free variable. `OpenGuardedRules`: the existential rule for other witnesses and the theory axioms, the two rules still assumed. `theoryAxiom_guarded`: an axiom whose translation has a proof of its own gives the guarded leaf. `refutation_of_open_rules`: a refutation in `U` gives `Provable T ⊥` from `OpenGuardedRules` for every identity packet and `Provable T (∃x Dom(x))`. |

All statements are for an arbitrary model `V` of `𝗜𝚺₁`, arbitrary `Δ₁` theories `U` and `T`
of the two languages, and internally valid codes that may be nonstandard.

## What is open

- The existential rule for a witness that is a function term. The translation of
  `φ[t]` is not a substitution instance of the translation of `φ`: the value formula of `t`
  replaces a variable lookup. The rule needs, as theorems of the source theory for
  nonstandard `φ` and `t`: a value of `t` exists when its free variables are in the domain,
  values are unique up to order isomorphism, and translated formulas respect order
  isomorphism. These in turn need the corresponding facts for zero, successor, addition and
  multiplication as fixed theorems of the source theory.
  One difficulty is already visible. A substitution lemma "`(φ[t])*` is equivalent to the
  translation of `φ` at a value of `t`" has the witness `t` as a parameter of the model, and
  an induction over `φ` that opens a quantifier by a fresh free variable (the pattern of
  `PA194PAeqUniversalFormulaCongruence.replace_aux`) shifts the free variables of `t`. The
  induction hypothesis is then needed at `shift t`, so a fixed `𝚺₁` predicate in `φ` does not
  suffice. Two ways out are not tried yet: carry the finite family `t, shift t, …` under a
  bounded quantifier, or prove the lemma only for the one-step terms `0`, `S #0`, `#1 + #0`,
  `#1 · #0`, which have no free variable, and reach a general witness by an induction over
  `t` with the formula ranging over substitution instances below a bound.
- The theory axioms: a proof in the source theory of the translation of each fixed axiom of
  `ordinaryPAeq` and of each closed induction instance, under an identity packet.
  `pa194-model-logic` works on these under `rootParameters`; for a sentence the two
  translations should agree, but that is not proved here (it needs a lemma that the
  translation reads the free environment only at free variables of the formula).
- `Provable T (∃x Dom(x))` for the actual source theory. The standard development has a
  derivation of it from the empty-set formula
  (`emptyFoundationDerivation` of [`pa194-foundation-ordinal`](../pa194-foundation-ordinal/README.md));
  it is not yet transported to models here.
- `OrdinaryCompiler` itself is therefore not proved, and nothing here yields a consistency
  implication.

## Checking

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-guarded-compiler/check.sh
```

runs [`check_bridge.py`](../pa194-model-fairness/check_bridge.py) with each module as the top
module, passing its arguments on (for example `--out DIR` to reuse compiled objects). On
2026-11-15 the four modules were compiled directly with `lean`, in dependency order, against
objects of the standalone modules they import (the import closure of
`PA194ConditionalRefutation` and `PA194OrderIsoRew`, compiled from the repository sources at
`34c4c35edc`). The twenty axiom reports are `[propext, Classical.choice, Quot.sound]`. The
script itself has not been run.
