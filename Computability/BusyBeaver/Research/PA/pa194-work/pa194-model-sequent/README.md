# Sequents of nonstandard length, in models of IΣ₁

The direction `¬Halt(M₁₉₄) → Con(PA)` has to turn an internal first-order derivation, an
element of a model that may be nonstandard, into a derivation of the contradiction code in
the numerical calculus. The sequents of such a derivation are hereditarily finite sets of
formula codes with a possibly nonstandard number of members, so the context proofs of
[`pa194-model-logic`](../pa194-model-logic/README.md) (`Ctx Γ a`, with `Γ` a list of standard
length) do not reach them.

This directory supplies the sequent layer for internal lists and internal finite sets, for an
abstract calculus. It is independent of the translation of source formulas: the translation
enters as a parameter.

**Status.** The two generic modules are checked. Their instance for the numerical calculus
(`impValue`, `allValue`, `TargetProvable`) is not in the repository yet. No internal
derivation is compiled here and nothing here yields a consistency implication.

## Modules

| Module | Content |
| --- | --- |
| `ConPASequent` | In any model `V` of `𝗜𝚺₁`. A calculus `Calc V` is a `𝚺₁` implication constructor and a `𝚺₁` provability predicate `Pr` with modus ponens and the combinators K, S, B, C. `seq Γ a` is the implication chain of the Foundation vector `Γ` ending in `a`, and `Pr (seq Γ a)` is read as `Γ ⊢ a`. Proved by `𝚺₁` induction inside `V`: `seq_weaken`, `seq_proj` (every entry is derivable), `seq_mp`, `seq_adjoin_iff` (deduction theorem), `seq_cut` (if `Δ` derives every entry of `Γ` then `(Γ ⊢ a) → (Δ ⊢ a)` is a theorem), `seq_mono` (weakening, exchange, contraction), and for a calculus `Quant V` with a quantifier constructor `seq_gen` (generalization under hypotheses closed under the quantifier). |
| `ConPASetSequent` | For a `𝚺₁` translation `tr e p` with a parameter `e`, `setList e s` lists the translated members of the finite set `s`, and `sseq e s a = seq (setList e s) a`. `sseq_mem`, `sseq_cut` (between two sets and two parameters), `sseq_mono`, `sseq_insert_iff` (`insert p s ⊢ a` exactly when `s ⊢ tr e p → a`). |

## What is and is not proved

Lists and sets are elements of the model. Each rule is a statement about the `𝚺₁` predicate
`Pr`, so the inductions are `𝚺₁` inductions inside the model. A hypothesis that is not `𝚺₁`
as a function of the induction variable (for example "`Δ` derives every entry of `Γ`") stays
outside the induction, which then runs on the length of a suffix of `Γ`.

`setList e s` is defined by primitive recursion on a bound, so it is a single `𝚺₁` function
of `e` and `s` and no enumeration of `s` has to be chosen.

Still open for the compiler: the instance for the numerical calculus, the choice of `tr`
(the negated translation of a source formula under a variable assignment, see
[`pa194-model-logic`](../pa194-model-logic/README.md)), the simulation of each rule of
Foundation's internal calculus, and the induction over an internal derivation with a bounded
quantifier over assignments.

## Checking

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-sequent/check.sh
```

compiles the two modules against the root Lake workspace (Foundation must be built there)
and requires eleven axiom reports without `sorryAx`. On 2026-11-14 both modules were compiled
directly with `lean` against rebuilt Foundation objects; every printed report was
`[propext, Classical.choice, Quot.sound]`. The script itself has not been run.
