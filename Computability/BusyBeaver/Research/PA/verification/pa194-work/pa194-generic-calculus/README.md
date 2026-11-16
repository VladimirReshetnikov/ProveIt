# The numerical calculus for an arbitrary closed set of codes

The candidates differ in the axioms that their AX command emits. To compare two such
calculi inside a model, one needs the laws of the calculus for sets of codes other than
`TargetProvable`: for the formulas that the command words of some scheduler compute, and for
the codes whose translations arithmetic proves. This directory has two independent modules
for that. Both work in an arbitrary candidate-PRA model `M` whose arithmetic reduct satisfies
`𝗜𝚺₁`, so the codes may be nonstandard.

## `ConPAGenericCalculus`

`Closed P` says that the predicate `P : M → Prop` is closed under modus ponens and
generalization and contains the restricted row `ρ₈` under its side condition, the first head
`(∃x_D ∀x_D H) → H`, the second head (commutation of two universal quantifiers) and the sixth
head (distribution of a universal quantifier over an implication). From `Closed P` the module
derives, as statements about `P`:

- the implication basis `k`, `s`, `peirce`, `comp`, `exchange`, by instantiating the generic
  derivation `M6.Logic.RestrictedImplication` of the upstream snapshot with `P` as the proof
  predicate;
- proofs from hypotheses (`Ctx`) and the deduction theorem (`Ctx.deduction`);
- `explosion`, `doubleNegationElimination`, `contraposition`, and the three laws for a
  negated implication, `negImpLeft`, `negImpRight`, `negImpIntro`;
- `negationVacuity`, `implicationVacuity`, `universalVacuity`: if `a → U(x, a)` is in `P`,
  so are the corresponding statements for `¬a`, for `a → b` (given the one for `b`) and for
  `U(y, a)`.

These are the derivations of `pa194-model-logic` (`PA194ModelPropositional`,
`PA194ModelContext`), which are stated there for `TargetProvable` only; the proofs are the
same with the rules taken from `Closed P`.

The main statement uses `AtomVac P`: `P` contains `M(a,b) → U(c, M(a,b))` and
`E(a,b) → U(c, E(a,b))` whenever `c ≠ a` and `c ≠ b`.

```lean
theorem vacuity (C : Closed P) (hP : 𝚺₁-Predicate P) (A : AtomVac P) (c B : M) (h : B ≤ c) :
    P (impValue B (allValue c B))
theorem diagonal (C : Closed P) (hP : 𝚺₁-Predicate P) (A : AtomVac P) (B : M) :
    P (diagonalValue B)
```

`vacuity` is proved by `Σ₁` order induction on the code `B`. A code is `4·p(a,b)` (an
implication), `4·p(a,b) + 1` or `4·p(a,b) + 3` (an atom), or `4·p(a,b) + 2` (a universal
formula), by `PA194SourceOutputWF.source_cases`. The components of an implication other than
`0` and the body of a universal formula are smaller codes, and the labels of an atom are
below the atom, hence different from `c`. `diagonal` is the case `c = B`: the diagonal
`Γ(B) = B → U(B, B)` of the primary calculus is a theorem of every calculus with atom
vacuity. This is the step that relates a calculus whose gate bundles atom vacuity (PA196)
to the calculus of the primary table, whose AX emits the diagonal.

## `PA194SourceEqVacuity`

`PA194SourceLineSoundness.good x` says that arithmetic proves the translation of the code
`x`. The module proves, for all `a b c : M` with `c ≠ a` and `c ≠ b`,

```lean
lemma eq_vacuity (a b c : M) (ha : c ≠ a) (hb : c ≠ b) :
    Provable 𝗣𝗔 (translated (impSource (eqSource a b) (allSource c (eqSource a b))))
```

the equality vacuity in the gate of PA196. The proof is the one of
`PA194SourceDiagonalPreservation.diagonal` with the freshness of `c` taken from the two
inequalities instead of from a bound.

## Use

Neither module mentions a scheduler or a machine.
[`pa194-controller-schedulers`](../pa194-controller-schedulers/README.md) uses both for the
schedulers whose AX has the gate of PA196: `diagonal` for the formulas that the scheduler
computes (completeness), and `eq_vacuity` together with the laws for `good` (soundness).
It also uses `Closed` for its soundness direction in general.

## Checking

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-generic-calculus/check.sh [--out DIR]
```

compiles each module with the standalone modules it imports, one `lean` process at a time,
and checks the number of axiom reports: five in `ConPAGenericCalculus` and two in
`PA194SourceEqVacuity`, all `propext`, `Classical.choice`, `Quot.sound`.
