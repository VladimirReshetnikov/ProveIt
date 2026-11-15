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

**Status.** The three generic modules are checked. `ConPADerivation` reduces the compilation
of an internal derivation to one requirement on the translation per inference rule; no
translation is shown to meet them. `PA194ModelSequent` instantiates the sequent layer with the
numerical calculus (`impValue`, `allValue`, `TargetProvable`) and is checked. Nothing here
yields a consistency implication.

## Modules

| Module | Content |
| --- | --- |
| `ConPASequent` | In any model `V` of `𝗜𝚺₁`. A calculus `Calc V` is a `𝚺₁` implication constructor and a `𝚺₁` provability predicate `Pr` with modus ponens and the combinators K, S, B, C. `seq Γ a` is the implication chain of the Foundation vector `Γ` ending in `a`, and `Pr (seq Γ a)` is read as `Γ ⊢ a`. Proved by `𝚺₁` induction inside `V`: `seq_weaken`, `seq_proj` (every entry is derivable), `seq_mp`, `seq_adjoin_iff` (deduction theorem), `seq_cut` (if `Δ` derives every entry of `Γ` then `(Γ ⊢ a) → (Δ ⊢ a)` is a theorem), `seq_mono` (weakening, exchange, contraction), and for a calculus `Quant V` with a quantifier constructor `seq_gen` (generalization under hypotheses closed under the quantifier). |
| `ConPASetSequent` | For a `𝚺₁` translation `tr e p` with a parameter `e`, `setList e s` lists the translated members of the finite set `s`, and `sseq e s a = seq (setList e s) a`. `sseq_mem`, `sseq_cut` (between two sets and two parameters), `sseq_mono`, `sseq_insert_iff` (`insert p s ⊢ a` exactly when `s ⊢ tr e p → a`), `sseq_gen`. |
| `ConPADerivation` | For Foundation's internal derivations of a theory `T` (`Bootstrapping.Derivation T d`, with `d` an element of the model). `Sim Q N T` lists what a translation `N` into the calculus `Q` has to satisfy; `Sim.compile` proves by `𝚺₁` induction on `d` that `Pr (sseq e (fstIdx d) bot)` for every admissible environment `e` below a fixed bound, and `Sim.proof` gives `Pr (imp (N e φ) bot)` from an internal proof of `φ`. |
| `PA194ModelSequent` | The instance for a candidate-PRA model `M` with an IΣ₁ reduct: `quantM` packages `impValue`, `allValue` and `TargetProvable` (with `imp_k`, `imp_s`, `imp_comp`, `imp_exchange`, `tp_gen`, `r2` of `pa194-model-logic`). `Derives Γ a` is `TargetProvable (seqValue Γ a)` for an internal list `Γ`: `Derives.closed`, `.assumption`, `.mp`, `.cut`, `.mono`, `.generalize`, `derives_adjoin_iff`. `Ctx.derives` moves every proof tree of standard size of `PA194ModelContext` under an internal list that derives its hypotheses; `Derives.cases` is an example. |

## The requirements of `Sim`

`N.tr e p` is meant as the negated translation of the formula `p` under the environment `e`
(labels of the free variables and whatever the translation needs to allocate labels), so
that a derivation of the sequent `s`, read as a disjunction, becomes a derivation of `bot`
from the translated members of `s`.

| Field | Requirement |
| --- | --- |
| `Adm e d`, `bound` | Admissibility of `e` for the derivation `d`, a `𝚷₁` relation, and a bound on the environments. The induction predicate is `∀ e ≤ bound, Adm e d → Pr (…)`, which is `𝚺₁`. |
| `admAnd`, `admOr`, `admExs`, `admWk`, `admCut` | Admissibility passes to the premises. |
| `admAll`, `admShift` | For the `∀` rule and the shift rule it passes to `push e` and `pop e`, which stay below the bound. |
| `ruleAxL` | `N e p → (N e (¬p) → bot)`. |
| `ruleVerum` | `N e ⊤ → bot`. |
| `ruleAnd` | `(N e p → bot) → ((N e q → bot) → (N e (p ∧ q) → bot))`. |
| `ruleOr` | `(N e q → (N e p → bot)) → (N e (p ∨ q) → bot)`. |
| `ruleAllShift` | `N e q → N (push e) (shift q)` for the formulas `q` of the sequent. |
| `ruleAllFresh` | `N e q → ∀x N e q` for the generalized label `x = eig e` and the formulas `q` of the sequent. |
| `ruleAll` | `∀x (N (push e) (free p) → bot) → (N e (∀p) → bot)`. |
| `ruleExs` | `(N e (p[t]) → bot) → (N e (∃p) → bot)` for an internal term `t`. |
| `ruleShift` | `N e (shift q) → N (pop e) q` for the formulas `q` of the premise. |
| `ruleCut` | `(N e p → bot) → ((N e (¬p) → bot) → bot)`. |
| `ruleAxm` | `N e p → bot` for the axioms `p` of `T`. |

Each requirement receives the admissibility of `e` for the rule node, `e ≤ bound`, and the
facts of the rule (membership in the sequent, validity of the sequent). The weakening rule
needs none.

## What is and is not proved

Lists and sets are elements of the model. Each rule is a statement about the `𝚺₁` predicate
`Pr`, so the inductions are `𝚺₁` inductions inside the model. A hypothesis that is not `𝚺₁`
as a function of the induction variable (for example "`Δ` derives every entry of `Γ`") stays
outside the induction, which then runs on the length of a suffix of `Γ`.

`setList e s` is defined by primitive recursion on a bound, so it is a single `𝚺₁` function
of `e` and `s` and no enumeration of `s` has to be chosen.

Still open for the compiler: a `Sim` for the source translation of [`pa194-model-logic`](../pa194-model-logic/README.md): the
environments with `push`, `pop` and `eig`, their bound, and the requirements above.

## Checking

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-sequent/check.sh
```

compiles the three generic modules against the root Lake workspace (Foundation must be built
there) and requires fourteen axiom reports without `sorryAx`; it then runs
[`check_bridge.py`](../pa194-model-fairness/check_bridge.py) with `PA194ModelSequent` as the
top module (eight reports), passing its arguments on (for example `--out DIR` to reuse
compiled objects). On 2026-11-14 the four modules were compiled directly with `lean`: the
generic ones against rebuilt Foundation objects, `PA194ModelSequent` against rebuilt
workspace objects and retained objects of the standalone modules it imports, whose sources
are unchanged since those objects were built. Every printed report was
`[propext, Classical.choice, Quot.sound]`. The script itself has not been run.
