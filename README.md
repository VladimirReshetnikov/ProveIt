# Proofs

**Machine-checked mathematics in Lean 4 and Rocq/Coq, organized by subject.**

`Proofs` contains formal mathematics, executable proof certificates, and the
research artifacts needed to reproduce difficult certificates. Lean 4 with
mathlib is the primary environment; Rocq/Coq developments provide independent
or complementary checks. Generated data and exploratory computations are not
part of the trusted theorem boundary unless a proved checker connects them to
the formal semantics.

**Toolchains:** Lean `4.32.0` · mathlib `v4.32.0` · Rocq `>= 9.2`
(developed against `9.0.1`) · MathComp boot `2.5.0` · [MIT-0](LICENSE)

## Repository map

The top-level source directories are mathematical topics. Within each coherent
project, `Lean/` and `Coq/` are siblings; `Research/`, `Support/`, and
`Article/` stay beside the mathematics they document.

| Topic | Contents |
| --- | --- |
| [`Algebra/`](Algebra/) | Jacobian-conjecture counterexamples: the dimension-three witness and a lower-degree stable representative checked independently in Lean and Coq, plus an exact cubic reduction. |
| [`Analysis/`](Analysis/) | Exact trigonometric, arctangent, and exponential identities. |
| [`Combinatorics/`](Combinatorics/) | Enumeration of power towers and radical expressions, including OEIS certificates and research corpora; squaring the square (Duijvestijn's order-21 perfect squared square and small-order impossibility). |
| [`Computability/`](Computability/) | Set Turing degrees (order, joins, cardinalities, jump/c.e. theory, and Post's problem); lambda/SK/SKI/Iota universality; Busy Beaver semantics, domination, exact small-state scores and times, and certificate bridges. |
| [`Logic/`](Logic/) | First-order logic and completeness, propositional/equational axiom systems, PA infinitude, and PA/HF interpretability. |
| [`NumberTheory/`](NumberTheory/) | FLT for exponent four, floor-square-root sums, rational enumeration, and an arithmetic RH sentence. |
| [`SetTheory/`](SetTheory/) | First-order ZF and the Closure axiomatization's equivalence with ZF. |
| [`lib/`](lib/) | Vendored third-party code only. |

Repository-wide configuration remains at the root. [`Proofs.lean`](Proofs.lean)
is the broad Lean import surface.

## Highlights

- A Lean/Coq proof that the Jacobian conjecture is false in dimension three:
  an explicit polynomial map has formal Jacobian determinant `-2` but
  identifies distinct integral and rational points.  A stabilization
  theorem extends the refutation to every dimension at least three.  A
  second kernel-checked representative lowers maximum degree from seven to
  six, and exact stable reductions reach the globally optimal degree three
  in ten variables.  Both developments also prove the witness's discrete
  mirror symmetry and the weighted torus action behind it, exhibiting the
  rational collision family as the orbit of a single integral collision.
- Fermat's Last Theorem for `n = 4`, an exact floor-square-root sum, and a
  bijective Calkin-Wilf rational orbit.
- Exact trigonometric, arctangent, and tiny-exponent-tower identities.
- Formal semantics and finite certificates for OEIS A000081, A002845,
  A158415, A198683, and A199812.
- A Lean/Coq [squaring-the-square development](Combinatorics/SquaredSquare/README.md):
  Duijvestijn's order-21 perfect squared square of side 112 — a square cut
  into 21 pairwise non-congruent squares, kernel-checked from integer
  certificates and extended by dilation to every square in Lean — plus the
  elementary lower bound that every perfect squared square has at least 7
  pieces, bracketing the minimum order in `[7, 21]`.  The sharp bound 21
  (Duijvestijn's exhaustive search of orders 7–20) is documented as not
  formalized.
- Nicod's NAND axiom, Wolfram's single Boolean equation, Meredith's basis,
  and checked equational certificates.
- A [first-order completeness and compactness development](Logic/FirstOrder/README.md):
  from-scratch independent Lean/Coq Henkin proofs for the repository's fixed
  countable relation language, plus arbitrary-language semantic compactness
  in Lean.
- Full deductive equivalence between the Closure axiomatization and ZF,
  checked independently in Lean and Coq.
- A deductive bi-interpretation between PA and finite-generation hereditary
  finite set theory.
- A [constructive Lean/Coq proof](Logic/PeanoArithmetic/NoFiniteModel/README.md)
  that Peano arithmetic has no finite model, using only injectivity of
  successor and zero's absence from its image.
- Independent Lean/Coq [natural-number codings of finite lists](Logic/PeanoArithmetic/ListCoding/README.md),
  with genuine PA formulae defining validity, access, concatenation,
  flattening, multiplicity, permutations, substrings, subsequences,
  duplicate-freedom, numeric and lexicographic sorting, sum, product, extrema,
  twice-median and unique-mode statistics, one-based nth primes, powers, prime
  factorizations, canonical base digits and divisor lists, and the canonical
  lexicographic enumeration of every distinct permutation.  The same project
  proves in both Lean and Rocq that the full three-argument natural
  hyperoperator—simultaneously covering exponentiation, tetration,
  pentation, and every higher rank—is Diophantine via formalized
  Matiyasevich constructions and finite evaluator traces.  It also gives a
  shared natural coding of hereditary Cantor normal forms below
  epsilon zero, PA formulae for validity, order, addition, multiplication, and
  exponentiation, and checked natural laws for those operations.
- An [executable Cooper quantifier eliminator](Logic/PresburgerArithmetic/README.md)
  deciding every Presburger sentence in Lean, with an independent constructive
  Coq proof and decision procedure for the normalized one-variable step.
- Lean/Coq proofs that [first-order Peano-arithmetic theoremhood is
  undecidable](Logic/PeanoArithmetic/Undecidable/README.md), by reductions from
  the halting problem and Hilbert's tenth problem respectively.
- Lean/Coq proofs that first-order Peano arithmetic has two non-isomorphic
  models, separating the numeral-generated standard model from a compactness
  model with an element above every standard numeral.
- Independent Lean and Rocq/Coq proofs that pure SK, SKI, and Iota simulate
  closed weak untyped lambda calculus by compositional positive-step compilers,
  and that Iota embeds faithfully back into closed lambda terms.
- Busy Beaver domination plus exact results `Sigma(2)=4`, `Sigma(3)=6`,
  `Sigma(4)=13` and `BB(2)=6`, `BB(3)=21`, `BB(4)=107` for the documented
  score/time conventions.
- A [Lean/Rocq Turing-degree development](Computability/TuringDegrees/README.md)
  covering the quotient/setoid order, degree zero, exact even/odd joins,
  cardinalities of degree classes and cones, jump strictness, Kleene--Post
  incomparability, c.e.-completeness, Shoenfield's limit lemma, Post's theorem,
  and a conditional constructive solution of Post's problem.

## Lean workspace

The root workspace is pinned by [`lean-toolchain`](lean-toolchain) and
[`lake-manifest.json`](lake-manifest.json):

```powershell
lake exe cache get
lake build
```

The broad build is intentionally expensive. Focused examples are:

```powershell
lake build JacobianConjecture
lake build +DiophantineEquations.FermatFour
lake build +ShefferStroke.Sheffer
lake build +FirstOrder.Fol
lake build +ClosureAxiomatization.Forward
lake build +NoFiniteModel
lake build +PAListCoding +PAListCoding.Audit
lake build +PAFiniteBasisReduction
lake build +PAUndecidable +PAUndecidable.Audit
lake build +PowerTowers.Core
lake build +SquaredSquare
lake build +CombinatoryLogic
lake build +BusyBeaver.BB2
lake build +BusyBeaver.BB3
lake build +BusyBeaver.Mathlib
lake build +TuringDegrees +TuringDegrees.Audit
```

These projects also have project-local Lake files for focused builds:

```powershell
lake --dir Algebra/JacobianConjecture/Lean build
lake --dir Logic/Propositional/NaturalDeduction/Lean build
lake --dir Logic/Propositional/FiniteMatrixNoncharacterizability/Lean build
lake --dir Logic/Propositional/MonotonicityOfEntailment/Lean build
lake --dir Logic/Propositional/PrincipleOfExplosion/Lean build
lake --dir Logic/QuantifierCommutation/Lean build
lake --dir Logic/FirstOrder/Lean build
lake --dir Logic/FirstOrder/Compactness/Lean build
lake --dir Logic/Interpretability/PAHF/Lean build
lake --dir Logic/PeanoArithmetic/NoFiniteModel/Lean build
lake --dir Logic/PeanoArithmetic/ListCoding/Lean build
lake --dir Logic/PeanoArithmetic/NotFinitelyAxiomatizable/Lean build
lake --dir Logic/PeanoArithmetic/Undecidable/Lean build
lake --dir Logic/PresburgerArithmetic/Lean build
lake --dir SetTheory/ZF/Lean build
lake --dir SetTheory/ClosureAxiomatization/Lean build
lake --dir NumberTheory/RiemannHypothesis/PAStatement/Lean build
lake --dir Computability/BusyBeaver/Lean build
lake --dir Computability/TuringDegrees/Lean build
```

The Busy Beaver facade excludes the expensive BB2/BB3 classifications and the
mathlib compiler bridge; request those modules explicitly.

## Rocq/Coq workspace

The root [`_CoqProject`](_CoqProject) contains all logical `-Q` mappings and a
registered source list whose dependency graph is resolved by `rocq makefile`,
including the vendored certificates under
`lib/Coq-BB5`:

```powershell
git submodule update --init lib/Coq-Synthetic-Computability
pwsh -NoProfile -File Computability/TuringDegrees/Coq/BuildSyntheticComputability.ps1
rocq makefile -f _CoqProject -o Makefile.coq
make -f Makefile.coq
```

Topic READMEs document focused `rocq c` commands and Lean/Rocq parity boundaries.
The combinatory-logic development checks the same weak-lambda-to-SK-to-SKI-to-
Iota simulation and the converse faithful Iota-to-lambda embedding independently
in both systems. In particular, some other Coq ports check the finite
certificate surface while the analytic or semantic bridge remains Lean-only;
no blanket parity is claimed.

The Turing-degree project uses a pinned `coq-synthetic-computability`
submodule. Its focused README documents the compatibility-patched dependency
build and wrapper build; constructive principles and effective-enumeration
hypotheses remain visible in theorem signatures.

## Trust and status

- Lean statements are checked by Lean's kernel. Sites using `native_decide`
  deliberately include Lean's native compiler/runtime in their trust boundary
  and remain visible in source. The exhaustive Lean BB2/BB3 shards use ordinary
  kernel `decide`.
- Rocq proofs use kernel checking and documented `vm_compute` or VM conversion.
  The vendored Coq-BB5 snapshots retain their assumptions and local hardening
  notes.
- Generated traces, interval tables, and candidate partitions are accepted
  only through proved checkers or explicit theorem hypotheses.
- Conditional theorems remain explicitly conditional. The A198683 research
  ledger distinguishes semantic proofs, finite data checks, conditional
  results, and heuristic evidence.

## Vendored components

Only [`lib/`](lib/) contains vendored code. `lib/Coq-BB5/BB2`, `BB3`, and
`BB4` come from `ccz181078/Coq-BB5` commit `9142e219...`; their nested READMEs
record provenance and repository-local kernel hardening, and their nested MIT
licenses are retained. The focused
[`lib/Coq-Library-Undecidability`](lib/Coq-Library-Undecidability/) snapshot
comes from `uds-psl/coq-library-undecidability` commit `806690d0...`; its
nested README records the exact 186-file dependency closure and its MPL-2.0
license is retained.
[`lib/Coq-Synthetic-Computability`](lib/Coq-Synthetic-Computability/) is pinned
to `uds-psl/coq-synthetic-computability` commit `8fc0014f...`; its MIT license
is retained, and the Turing-degree project owns a small, reproducible Rocq
9.2/stdpp 1.13 compatibility patch rather than modifying the pin.

## License

Unless a nested license says otherwise, this repository is available under
the [MIT No Attribution License (MIT-0)](LICENSE).
