# A Diophantine equation for syntactic consistency of ZFC

Research started 23 October 2026, from repository commit `22e75dd6b8`.
This directory contains active research, its Lean proofs, and the delivered
manuscripts in [con-zfc-diophantine-forms](con-zfc-diophantine-forms/README.md).
The manuscript collection was moved here from the Cardinals reports tree
on 23 October 2026 at the repository owner's request.

The target is one integer-coefficient polynomial, with an exactly stated
witness domain, whose absence of zeros is equivalent to the absence of a
finite derivation of falsity from the repository's ZFC axiom predicate.
Neither consistency nor inconsistency is assumed.

## Approach and comparison

There is no single established meaning of "simplest": number of variables,
total degree, arithmetic operations, and coefficient size give different
answers. We first seek the fewest natural witnesses available from the
repository's proved reductions, while retaining a quartic alternative.
Global optimality is not asserted.

After reviewing the eight wave-7 proposals, the next small-nine target is
package 52's interior-regular equation: nine positive variables, 548 binary
operations, degree 15,502,748 (551 operations over naturals). Package 53's
738-operation, degree-7,344,328 form remains the lower-degree target.
The selection, alternatives, finite replays and remaining proof obligations
are recorded in [PROPOSAL_REVIEW.md](PROPOSAL_REVIEW.md). These proposals
supersede wave 6 as numerical targets; the current closed Lean equations
remain the certified baseline until a replacement is fully checked.

The wave-5 and wave-6 report packages explicitly distinguish their new final
equations from an end-to-end Lean certificate. The inherited P67 is a particularly short
candidate: 15 strictly positive witnesses, degree 155, and 67 binary
arithmetic operations. Its fixed coefficient tuple and native-window/Pell
compiler still need a formal semantic bridge. Nine-natural-variable forms
use the already formalized Jones reduction but introduce very large powers.
The ten-unrestricted-integer Sun construction is not formalized here.

The wave-6 packages arrived on `origin/main` during this research and were
merged at `2d7766807b`. Their direct quadratic/Sidon encodings improve the
reported low-variable degree and operation counts substantially; for example,
[package 45](con-zfc-diophantine-forms/45-multioutput/README.md) reports nine
positive unknowns at degree 129,875,980 in 788 operations. These were useful
comparison targets. The executable generic Jones route below
prioritizes a complete checked construction and does not claim to improve
those degree or operation counts.

The first formal route is now checked:

1. A concrete semidecision procedure halts exactly when ZFC has a finite
   refutation. Reuse the checked K215/program endpoint rather than assume
   that its halting predicate is computable.
2. Apply the proved MRDP theorem and Jones quartic compression.
3. Apply the proved nine-variable reduction and fix the ordinary input to
   1, obtaining one polynomial in nine natural variables.
4. Negate the solvability equivalence.

An existential representation chosen with `Classical.choose` is a useful
checked milestone, but is not a materialized explicit coefficient recipe.
These two levels will be reported separately. Likewise, a Lean theorem
about syntactic ZFC consistency is distinct from a derivation *inside* the
repository's object-level ZFC proof calculus. Portability of an arithmetic
argument to ZFC is not itself a checked object-level derivation.
The concrete remaining internalization obligations and the first actual
object-language arithmetic proofs are documented in [OBJECT_ZFC.md](OBJECT_ZFC.md).

See [STATUS.md](STATUS.md) for the current evidence and remaining work.

The main checked result is now
`ExplicitZFC.noNaturalZero_iff_conZFC` in
[ExplicitZFC.lean](Lean/DiophantineConsistency/ExplicitZFC.lean). It uses a
closed, executable nine-variable coefficient recipe and has no consistency,
compiler, program, or representation hypothesis. See
[EXPLICIT_EQUATION.md](EXPLICIT_EQUATION.md) for the equation and proof chain.
The earlier existence-based theorem in [ZFC.lean](Lean/DiophantineConsistency/ZFC.lean)
and its 58-witness quartic alternative remain available as separate milestones.
The checked shift in `PositiveZFC` gives the same variable count over strictly
positive integers. A second closed route in
[DIRECT_GRAPH.md](DIRECT_GRAPH.md) represents source arithmetic directly;
its final degree and operation comparison remains to be measured.

For a concrete small arithmetic circuit, see
[SHORT_EQUATION.md](SHORT_EQUATION.md): a 69-operation, degree-111 polynomial
with 15 positive unknowns, bound to the historical package-36 coefficient
tuple. Lean checks its complete positive zero set against the literal P67
baseline. The native-window compiler connecting those explicit circuits to
ZFC refutations remains to be formalized.

The lower-degree alternative in [SHORT_SYSTEM.md](SHORT_SYSTEM.md) uses
75 operations at degree 68, with the same 15 positive unknowns and fixed
coefficient tuple. Lean proves its degree bound and complete positive-zero
equivalence to P67. Grouping the main norm with the two coupled unit factors
saves two operations over the intermediate 77-operation sum of squares.

The checked tradeoff in [SHORT_FRONTIER.md](SHORT_FRONTIER.md) uses
73 operations at degree 80. It groups the six unit factors into three
residuals and has the same complete positive zero set. The present frontier
includes 69 operations/degree 111, 73/80, and 75/68.
The further reduction in [SHORT_REDUCED_STRONG.md](SHORT_REDUCED_STRONG.md)
uses 76 operations at degree 64. It adds a multiple of another vanishing
residual to cancel leading terms; Lean checks complete integer zero
equivalence to P75. Each of these alternatives uses 15 positive unknowns.

## Executable construction and further reductions

The current computability/MRDP interfaces hide the program and polynomial
inside propositions. Extracting executable polynomial data from those
propositions would require an unjustified elimination from `Prop` into
`Type`. The explicit route builds data-valued arithmetic syntax and
representation constructors, with separate correctness proofs. A
syntax-directed primitive-recursion compiler can then retain its polynomial
data throughout. The proved Jones nine-variable reduction accepts any
normalized quartic, so a direct gate-to-quartic conversion can avoid the
58-witness universal representation during this phase.
The detailed contracts and remaining links are tracked in
[COMPILER.md](COMPILER.md).

The supplied-data route now includes arithmetic graphs, Pell sequences,
power, binomial, factorial, and bounded universal quantification.
[`EquationFromRep.construct`](COMPILER_JONES.md) constructs a normalized
quartic and a nine-variable equation directly from supplied representation
syntax, with a checked equivalence for both presentations.
`ExecutableJones.fromRep` also gives a complete executable syntax path,
including its coefficient readers and index. The concrete refutation program
is now supplied by `DirectEnumerator.program`; `ExplicitZFC` closes the
executable equation construction with the actual syntactic endpoint.

## Reproducing the checked milestones

From the repository root, with Lean and Mathlib 4.32.0:

```sh
lake build DiophantineConsistency.ZFC DiophantineConsistency.ShortFrontier
lake env lean Computability/DiophantineConsistency/Lean/checks/ZFCAxioms.lean
lake env lean Computability/DiophantineConsistency/Lean/checks/ShortEquationAxioms.lean
lake build DiophantineConsistency
lake env lean Computability/DiophantineConsistency/Lean/checks/CompilerAxioms.lean
python3 Computability/DiophantineConsistency/tools/audit_short_circuit.py
python3 Computability/DiophantineConsistency/tools/audit_sos_circuit.py
python3 Computability/DiophantineConsistency/tools/audit_frontier_circuit.py
python3 Computability/DiophantineConsistency/tools/audit_reduced_strong.py
```

The axiom audits list only `propext`, `Classical.choice`, and `Quot.sound`.
The finite circuit audit verifies operation count, liveness, source binding,
and exact degree independently of the semantic compiler obligations.

## Source interfaces

* `BusyBeaver.ZFC.KEndpoint215.blank_halts_iff_zfc_refutation`: the literal
  215-state machine halts on blank tape iff `BProv ZFCax_s [] Form.fBot`.
* `Diophantine.Common.MRDPCore`: `MRDP.mrdp`, proved without a DPRM axiom.
* `Diophantine.Paper1982.RecursivelyEnumerableQuartic`:
  `Jones1982.rePred_quartic58`.
* `Diophantine.Paper1982.NineMain`: `Jones1982.nine_unknowns`.

All new mathematical statements must have complete proofs: no `sorry`,
`admit`, or additional axioms. Transitive axiom audits and reproducible
build commands will accompany completed milestones.
