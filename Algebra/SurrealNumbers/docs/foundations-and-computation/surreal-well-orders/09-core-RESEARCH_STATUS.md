# Research and verification status

## Logical settings

**ZFC:** Fixed-set enumeration spaces, cardinality, binary coding, the exact
ordinal spectrum, finite-tail adjacency, and birthday-bounded versions.

**GB with ordinary set choice:** A global ordinal enumeration of the entire
surreal class exists if and only if global choice holds. The reverse direction
uses set-sized well-founded extensional codes and their Mostowski collapses;
it does not use a truth predicate or class-valued recursion.

**GBC (GB plus global choice):** Class universality, class back-and-forth,
eventual-agreement support cores, interpolation of uniform set-indexed families,
bounded reflection, the explicit proper-class cut, and the uniform no-coding
argument. All recursions used for construction have set-valued stages and
set-sized histories, with fixed class parameters.

**ZFC plus a strongly inaccessible cardinal κ:** A separate conditional
set-sized illustration. The κ-sized support core is order-isomorphic to
No_{<κ}; the full set of κ-length enumerations has size 2^κ. This assumption is
not needed for the earlier ZFC or GBC theorems.

## Proof-status ledger

| Result | Status |
|---|---|
| Set-cut property and birthday bounds for surreal sign sequences | Classical input; matching repository declarations inspected. |
| Class universality and set-homogeneity | Classical mechanism; complete written arguments included. |
| Cardinality and exact ordinal spectrum for a fixed set | Self-contained written proof; related real-line repository work acknowledged. |
| Limit-prefix cofinality for variable-length words | Written proof showing why equimorphism need not be isomorphism. |
| Global baseline equivalent to global choice | Complete standard coding argument included. |
| Extension into a bounded-support permutation | Written proof; finite prefix mechanism tested. |
| Uniform set-family interpolation and C_b ≅ No | Main construction and written proofs. |
| Reflection into one bounded permutation stage | Written proof; finite first-disagreement mechanism tested. |
| Missing proper-class branch | Explicit construction and written proof. |
| Uniform no-coding theorem | Written diagonal proof, valid even with extra nonfunctional rows; finite functional-row mechanism tested. |
| Inaccessible-cardinal model | Conditional written theorem. |
| Lean formalization | Dependency plan only; no new Lean module or kernel-check claim. |

## Important boundaries

The manuscript does not form a class whose members are proper classes. A
uniform family is one class relation with sections indexed by sets. The symbol
for all global enumerations abbreviates a property of class variables, not a
same-level carrier containing those variables as elements.

The global enumeration representation covers set-like class well-orders.
Non-set-like class well-orders are discussed separately, including an alternative
comparison of relation codes relative to an auxiliary global coordinate order.
No complete classification of that alternative comparison is claimed.

The core realizes uniform set-sized cuts. It does not realize all proper-class
cuts; an explicit counterexample is supplied. The full global comparison object
also fails to fill that counterexample.

For fixed alphabets, absence of κ⁺ and its reverse is not claimed to be a
sufficient embeddability criterion for arbitrary linear orders. The article does
not classify all automorphisms or all higher-level cuts. Its nine research
directions are proposed continuations, not a claim that each is a catalogued
open problem.

## Sources and repository audit

Pinned ProveIt commit: `63bb8b1d99359e7188abf0a33fb152e121858150`.

Inspected repository material:

1. `SetTheory/Cardinals/docs/reports/ordinals-and-order-types/lexicographic-well-orderings-of-reals/README.md`
2. `Algebra/SurrealNumbers/Surreal/Foundations/SignSequence.lean`
3. `Algebra/SurrealNumbers/Surreal/Foundations/SignSequenceCutOperation.lean`

The article records the actual relevant declaration names and their universe
levels. Reading the source is not independent kernel verification; the project
and its transitive dependencies were not rebuilt.

Primary literature checked: Kanovei–Shelah's original index definition,
Rangel–Mariano's set/class framework, and the class-recursion discussion in
Gitman–Hamkins–Holy–Schlicht–Williams. The Kanovei–Shelah index page was visually
inspected. Publisher and arXiv metadata were checked for the latter paper.
Gonshor's book is cited as a standard reference, not as an exhaustively audited
source. The article contains full bibliographic references.

## Reproducibility

The finite test script uses Python's standard library and deterministic seed
20261002. It reports 164,560 passing assertions across five suites. These are
finite consistency checks of the mechanisms, not proofs of infinitary claims.
The source compiles in three pdfLaTeX passes; final compilation has no undefined
references, duplicate-label warnings, or overfull boxes. Rendered pages were
inspected for layout and mathematical glyphs.

No claim of peer review, historical priority, or independent formal verification
is made. The manuscript is AI-assisted and unrefereed.
