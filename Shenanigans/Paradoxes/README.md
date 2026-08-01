# Paradoxes: `False` from an ingredient the theory withholds

Nothing here is an implementation defect, and nothing here is a `False` you can
use. Every theorem in this directory takes an explicit hypothesis — a rule the
system deliberately does not have — and derives `False` from it. Read a
`… → False` here as a proof that the hypothesised rule *cannot be added*.

Category (see [`../README.md`](../README.md)): the cost is visible in the
**type**, not in the audit. Every headline theorem reports *no axioms at all*.

## Contents

### Lean — the `TypeTheoryParadoxes` library

Registered in the root [`lakefile.toml`](../../lakefile.toml) and imported by
[`ProveIt.lean`](../../ProveIt.lean), because unlike the rest of this directory
it is safe to build alongside ordinary mathematics: it asserts nothing.

| Module | Hypothesis granted | Classical name |
| --- | --- | --- |
| [`Girard.lean`](Lean/TypeTheoryParadoxes/Girard.lean) | `Type u` contains a code for every product of a `Type u`-indexed family (`pi`/`lam`/`app`/`beta`); and, separately, a Tarski-style decoding `El : V → Type u` with a section | Girard 1972, Hurkens 1995 |
| [`CoquandPaulin.lean`](Lean/TypeTheoryParadoxes/CoquandPaulin.lean) | a retraction of `Phi α = (α → Prop) → Prop` into `α`; and the operator-free form, a retraction of the powerset of `A` onto `A` | Coquand–Paulin 1990; Cantor |
| [`LargeElimination.lean`](Lean/TypeTheoryParadoxes/LargeElimination.lean) | any data-carrying eliminator for a `Prop` with two distinguishable constructors | the subsingleton-elimination barrier |
| [`Blockers.lean`](Lean/TypeTheoryParadoxes/Blockers.lean) | **nothing** — records the exact judgment Lean refuses in each of the above, with every error message captured by `#guard_msgs` | — |

### Rocq

| File | Contents |
| --- | --- |
| [`Coq/Hurkens.v`](Coq/Hurkens.v) | Girard/Hurkens via the stdlib `Hurkens` module: `Type` is not one of its own elements, `Prop ≠ Type`, and a retract of `Type` into `Prop` collapses the logic. Plus §3, the historical loophole that once reached the hypothesis *for real* — and the universe constraint that closed it. |

## Reproducing

```bash
pwsh Shenanigans/Paradoxes/verify.ps1
```

Expected final line: `All 6 paradox exhibits behaved as documented.`
Verified on Lean `4.32.0` and The Rocq Prover `9.2`.

## Which ingredient each classical paradox is denied

| Paradox | What Lean denies it | Where |
| --- | --- | --- |
| **Girard** (System U) | a *second* impredicative sort. `∀ α : Type u, F α` computes to `Type (u+1)` — the universe bumps. There is exactly one impredicative sort and it is `Prop`. | `Blockers.lean` §4 |
| **Hurkens** | `Prop` closed under powerset. Denied arithmetically: for `X : Prop`, `X → Prop : Sort (imax 0 1) = Type 0`. Impredicativity lives only in the codomain, because `imax u 0 = 0`. | `Blockers.lean` §1–3 |
| **Coquand–Paulin** | non-strict positivity, and only that. The refusal comes from the *kernel*, not the elaborator, and there is no Lean counterpart of Rocq's `Unset Positivity Checking`. | `Blockers.lean` §5 |
| **Curry** (negative occurrence) | the same positivity check. In Rocq the flag exists and the derivation is three lines — [`../EscapeHatches/Coq/TypingFlags.v`](../EscapeHatches/Coq/TypingFlags.v) §2. | `Blockers.lean` §5 |
| **Cantor** | nothing — it is a theorem, not a paradox. `no_powerset_retract` is the internal statement of why the hierarchy is necessary. | `CoquandPaulin.lean` |
| **Reynolds** | set-theoretic semantics for polymorphism; irrelevant to a predicative hierarchy with a set-theoretic model. It is nonetheless the reason `Prop` *must* be interpreted proof-irrelevantly. | — |
| **Berardi** | harmless: it derives proof irrelevance, which Lean already has definitionally. | — |
| **Chicli–Pottier–Simpson** | proof-relevant quotients in an impredicative sort. Lean's `Quot` at `u = 0` is a definitional isomorph of a subsingleton; the Rocq route needs `-impredicative-set`, which Lean has no analogue of. | [`../EscapeHatches/Coq/ImpredicativeSet.v`](../EscapeHatches/Coq/ImpredicativeSet.v) |

The unifying statement, and the reason `LargeElimination.lean` is the sharpest
file here: **impredicativity is safe exactly when paired with proof irrelevance,
and fatal when paired with proof relevance.** Every paradox in this family needs
an impredicative sort *plus* a data-carrying elimination out of it. Lean pairs
impredicativity with proof irrelevance and never with proof relevance;
`elim_only_at_universe_zero` is exactly that barrier. The two constructions that
look like exemptions — `Acc` and `Quot` — turn out to *satisfy* the subsingleton
criterion rather than bypass it.

Rocq's `-impredicative-set` is the same statement seen from the failure side: the
flag grants an impredicative sort that also has large elimination, and
`{A} + {~A}` is exactly the proof-relevant pairing that makes it fatal.

## A correction worth stating

It is commonly said that Lean's core theory has a consistency proof relative to
ZFC plus countably many inaccessibles (Carneiro, *The Type Theory of Lean*).
**That overstates the record.** Conjectures 2.7 and 2.9 were downgraded from
theorems to conjectures, because the stratification of the typing judgment used
to break the mutual induction between typing and definitional equality does not
and cannot respect substitution.

The set-theoretic model construction stands. The metatheoretic bridge between it
and the typing judgment has an acknowledged gap, and the gap sits exactly at the
interaction between typing and definitional equality — which is precisely where
the extra kernel rules live. The mechanization in
[Lean4Lean](https://github.com/digama0/lean4lean) has since proved unique typing,
but its treatment of inductive types is still incomplete: `VInductDecl.WF` and
`VEnv.addInduct` remain `sorry` in `Lean4Lean/Theory/Inductive.lean`.

Full account in [`../Audits/Lean/Metatheory/Findings.md`](../Audits/Lean/Metatheory/Findings.md).
