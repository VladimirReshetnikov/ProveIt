# ProveIt

**Machine-checked mathematics in Lean 4 and Rocq/Coq, organized by subject.**

`ProveIt` contains formal mathematics, executable proof certificates, and the
research artifacts needed to reproduce difficult certificates. Lean 4 with
mathlib is the primary environment; Rocq/Coq developments provide independent
or complementary checks. Generated data and exploratory computations are not
part of the trusted theorem boundary unless a proved checker connects them to
the formal semantics.

> **Most active ongoing work:** [Lean formalization and audit of Lazard's
> solvable-quintic algorithm](Algebra/PolynomialFormulas/LazardQuinticFormalization.pdf),
> including a detailed checkpoint of completed proofs, open obligations, and
> the ordered plan for resuming the development.

**Toolchains:** Lean `4.32.0` · mathlib `v4.32.0` · Rocq `>= 9.2`
(developed against `9.0.1`) · MathComp boot `2.5.0` · [MIT-0](LICENSE)

> ### Building: one Lean process at a time
>
> **Do not start a dozen Lean processes in parallel.** Each `lean.exe` worker on
> a Mathlib-importing file holds 1&ndash;1.5&nbsp;GB; a default parallel `lake build`
> exhausts memory and then fails with *misleading* errors such as
> `failed to read file '...Basic.olean'`, which are swap-thrash symptoms rather
> than real failures. `lake build -j1` does **not** help: Lake 5.0.0 removed
> the `-j` flag and rejects `--jobs` too, so the limits go in the environment.
> Build **one module per `lake build` invocation, in topological order**, with
> `LAKE_JOBS=1` set and `LEAN_NUM_THREADS` left alone &mdash; see
> [the caution in the Lean workspace section](#lean-workspace) for what the
> variable bounds and the measurements behind it (including why
> `LEAN_NUM_THREADS=0` costs a ~30&times; slowdown), and
> [`Analysis/FabiusFunction/AGENTS.md`](Analysis/FabiusFunction/AGENTS.md)
> for the driver, the retry rule, and the Windows traps.

## Repository map

The top-level source directories are mathematical topics. Within each coherent
project, `Lean/` and `Coq/` are siblings; `Research/`, `Support/`, and
`Article/` stay beside the mathematics they document.

| Topic | Contents |
| --- | --- |
| [`Algebra/`](Algebra/) | Linear-through-quartic root formulas; rational and generic Abel--Ruffini obstructions above degree four; a Lean-verified primitive-recursive radical-solvability criterion for individual integer quintics; and Jacobian-conjecture counterexamples including the dimension-three witness, a lower-degree stable representative, and an exact cubic reduction. |
| [`Analysis/`](Analysis/) | Exact trigonometric, arctangent, and exponential identities; Fabius-function definitions, exact dyadic arithmetic, and paper statements. |
| [`Combinatorics/`](Combinatorics/) | Enumeration of power towers and radical expressions, including OEIS certificates and research corpora; an exact `4.5235` upper-bound certificate for Klarner's polyomino growth constant; squaring the square (Duijvestijn's order-21 perfect squared square and small-order impossibility). |
| [`Computability/`](Computability/) | Set Turing degrees (order, joins, cardinalities, jump/c.e. theory, and Post's problem); lambda/SK/SKI/Iota universality; Busy Beaver semantics, domination, exact small-state scores and times, and certificate bridges. |
| [`Logic/`](Logic/) | First-order completeness, propositional/equational axiom systems, modal Kripke semantics and correspondence theory, PA infinitude, PA/HF interpretability, and bounded-complexity self-consistency for PA and for ZFC-inside-PA. |
| [`NumberTheory/`](NumberTheory/) | FLT for exponent four, floor-square-root sums, rational enumeration, and an arithmetic RH sentence. |
| [`SetTheory/`](SetTheory/) | First-order ZF, the Closure axiomatization's equivalence with ZF, and bounded-complexity consistency `ZFC ⊢ Conₙ(ZFC)`. |
| [`Tools/`](Tools/) | Development tooling: Rocq 9.2 compatibility shims. **Leant**, the GHCi-style interactive REPL for Lean 4 that grew up here, now lives in its own repository at [VladimirReshetnikov/Leant](https://github.com/VladimirReshetnikov/Leant). |
| [`lib/`](lib/) | Vendored third-party code only. |

Repository-wide configuration remains at the root. [`ProveIt.lean`](ProveIt.lean)
is the broad Lean import surface, and the
[`Analysis/FabiusFunction` agent guide](Analysis/FabiusFunction/AGENTS.md)
records the working agreements for that active development — above all the
requirement to build Lean one module at a time.

## Highlights

- Field-generic Lean and independent real-field Coq checks of the classical
  formulas through degree four: unique linear and exhaustive quadratic roots,
  Cardano's cubic translation and branch-compatible radicals, and Ferrari's
  cubic resolvent and quartic factorization. Executable root-collection
  functions have entrywise correctness and exhaustiveness theorems, with a
  complex Coq cubic development covering nonreal roots and exact examples.
- Lean and Rocq/Coq rational Abel--Ruffini obstructions: every root of the
  explicit quintic `X^5 - 4X + 2` lacks a radical expression, and padding it
  with zero roots refutes a universal complete radical formula in every degree
  at least five.  Lean additionally proves that `X^n - X - 1` has exact degree
  `n`, exactly `n` complex roots, and no root solvable by radicals over `Q` for
  every `n > 4`.  An independent symmetric rational-function construction
  supplies a second all-roots theorem.  The distinct scopes and assumptions
  are documented and kernel-audited.
- A Lean formalization that radical solvability of an individual integer
  quintic is primitive recursive. It verifies the complete bounded factor
  search, scalar Frobenius--Dummit resolvent and Chapman's correction, the
  irreducible Galois criterion, the bounded rational-root test, correctness of
  the assembled Boolean, `ComputablePred`, and existence of a
  `PartrecToTM2` program. A certified 302-term sparse coefficient table makes
  the final Lean Boolean directly evaluable; its four largest finite
  identities use the repository's documented `native_decide` trust boundary.
  A Rocq reflector independently checks the exact all-roots radical-expression
  semantics on natural-number encodings, but remains a semantic rather than
  extracted coefficient implementation.
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
- A [Rocq/Coq modal-logic development](Logic/Modal/README.md) porting a central
  semantic slice of Foundation: generic Geach and named frame
  correspondences, the exact Kripke characterization of Loeb's axiom,
  bisimulation and bounded-morphism preservation, modal undefinability of
  irreflexivity, coarsest/finest/transitive-closure filtrations with an
  explicit exponential finite-model bound, and a deep first-order standard
  translation.
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
- A Lean/Rocq [bounded-consistency development for PA](Logic/PeanoArithmetic/BoundedConsistency/README.md).
  Lean proves the single arithmetic sentence asserting that *for every* `n`
  — nonstandard elements included — PA proves its own bounded-complexity
  consistency statement `Conₙ(PA)`.  Its construction is a model-indexed
  dynamic truth-certificate family rather than an external recursion, which
  is what makes it one sentence with one derivation instead of a schema.
  Rocq/Coq proves every externally indexed instance and currently exposes an
  exact conditional compiler boundary for the stronger single sentence; it
  does not yet prove that uniform endpoint unconditionally.  Tarski's theorem
  is respected structurally: truth levels recurse externally, so each level
  is a separate, strictly larger formula.
- The set-theoretic counterpart, in two parts.  [`SetTheory/BoundedConsistency`](SetTheory/BoundedConsistency/README.md)
  proves in Lean that `ZFC ⊢ Conₙ(ZFC)` for every metatheoretic `n`, via a
  partial satisfaction predicate over the universe with ranked internal
  certificates for derivations.  [`Logic/Interpretability/ZFCinPA`](Logic/Interpretability/ZFCinPA/README.md)
  is the in-progress syntactic version, `PA ⊢ ∀ n, Prov_ZFC(⌜Conₙ(ZFC)⌝)`; its
  reduction to eight internal implications is proved and is an equivalence, and
  those implications are discharged at standard indices, so the endpoint is at
  present **conditional** — see that project's status table.
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

> [!CAUTION]
> **Never start Lean or Lake builds in parallel, and never start a second
> build while one is already running.** Run exactly one `lake build` at a
> time, with one target. Do not launch background build loops, pass a batch
> of targets, or use parallel runners such as `xargs -P`.
>
> One invocation is not by itself one process: Lake sizes its worker pool to
> hardware concurrency and starts one `lean.exe` **per core** whenever the
> target has a stale dependency set. On this machine several agent sessions
> share 13 GB, so that fan-out starves all of them. Bound the number of
> processes on every build:
>
> ```bash
> LAKE_JOBS=1 lake build <one target>
> ```
>
> **Corrected 2026-09-02: `LAKE_JOBS` does not bound anything here.** Lake
> `5.0.0-src+8c9756b` accepts neither `-j` (`unknown short option '-j'`) nor
> `--jobs`, and it does not read the environment variable either. Measured with
> `LAKE_JOBS=1` exported and every `lean.exe` attributed by `ParentProcessId`
> to the invoking `lake`: a build with 136 modules pending went `0 → 1 → 12`
> workers across two 30-second samples, all twelve children of that lake. The
> jump is a burst rather than a ramp, and `lake` spends about a minute in trace
> checking before spawning anything, so an early sample proves nothing.
> Keeping the variable costs nothing, but the only real control is the rule
> below: **one module per invocation, and only when its dependencies are
> already compiled.** The 2026-08-27 figures are left here as history and need
> recheck; a later test that peaked at two workers proved nothing, because the
> chosen target's dependency chain was near-linear and never had more than two
> modules ready at once.
>
> **Do not set `LEAN_NUM_THREADS=0`.** It does not mean "auto" &mdash; it
> serializes elaboration *inside* the one process, and it is not what limits
> memory. Measured the same day, under the same competing load:
> `FabiusFunction.AlgebraicBranch` took **~35 minutes** with
> `LEAN_NUM_THREADS=0`, against **~60 seconds** without it; three further
> modules built in 172 s, 214 s and 145 s with the variable unset. If a
> single process is itself too large, set a small *positive* value (2&ndash;4),
> never `0`.
>
> Starvation does not look like starvation. It surfaces as errors that read
> like corruption:
>
> ```
> failed to read file '...\Mathlib\...\Basic.olean'
> libc++abi: terminating due to uncaught exception of type std::bad_alloc
> ```
>
> These are out-of-memory symptoms, **not** broken proofs -- the same module
> built by itself succeeds. Never "fix" them by editing Lean sources.
>
> Before starting, check that nothing else -- including another agent session
> in a sibling worktree -- is already building; after interrupting a build,
> check for survivors, because stopping a task does not reliably kill the
> processes it spawned:
>
> ```powershell
> Get-Process lean,lake -ErrorAction SilentlyContinue
> ```
>
> If a build is running, wait for it rather than racing it.

The root workspace is pinned by [`lean-toolchain`](lean-toolchain) and
[`lake-manifest.json`](lake-manifest.json):

```powershell
lake exe cache get
$env:LAKE_JOBS=1
lake build +FabiusFunction.Basic
```

The broad build is intentionally expensive, and on a memory-constrained
machine it must be **serialized**: build one module per `lake build`
invocation, in topological order. Parallel Lean workers exhaust RAM and report
`failed to read file '...olean'`, which looks like corruption but is not; the
same module compiles on a serial retry. `lake build -j1` is not a workaround
(Lake 5.0.0 removed `-j` and rejects `--jobs`), and neither is `LAKE_JOBS=1`,
which this toolchain ignores &mdash; see the corrected caution above. Serializing
the invocations is the whole of the remedy (and `LEAN_NUM_THREADS` is left
alone &mdash; `0` serializes elaboration for a ~30&times; slowdown). The
[`Analysis/FabiusFunction` agent guide](Analysis/FabiusFunction/AGENTS.md)
has the driver and the retry rule.

Focused examples are:

```powershell
$env:LAKE_JOBS=1
# Run exactly one target at a time:
lake build JacobianConjecture
lake build +PolynomialFormulas
lake build FabiusFunction
lake build +DiophantineEquations.FermatFour
lake build +ShefferStroke.Sheffer
lake build +FirstOrder.Fol
lake build +ClosureAxiomatization.Forward
lake build +NoFiniteModel
lake build +PAListCoding
lake build +PAListCoding.Audit
lake build +PAFiniteBasisReduction
lake build +PAUndecidable
lake build +PAUndecidable.Audit
lake build +PowerTowers.Core
lake build +SquaredSquare
lake build +CombinatoryLogic
lake build +BusyBeaver.BB2
lake build +BusyBeaver.BB3
lake build +BusyBeaver.Mathlib
lake build +TuringDegrees
lake build +TuringDegrees.Audit
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
git submodule update --init lib/Coq-Synthetic-Computability lib/MathComp-Abel
opam install --yes --deps-only ./lib/MathComp-Abel/coq-mathcomp-abel.opam
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

The modal project has no build-time dependency on Foundation: its Lean source
is retained as a read-only reference, while the Coq statements and proofs are
checked independently.  The focused modal README documents its constructive
and classical boundaries and provides a `coqchk` command.

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
- Everything tracked here is ordinary mathematics held to those standards. The
  deliberate paradox and kernel-defect work that used to sit outside them has
  moved to its own repository; see the section below.

## Shenanigans: moved to its own repository

`Shenanigans/` — the one directory here whose contents were **not ordinary
mathematics** — now lives at
[VladimirReshetnikov/Shenanigans](https://github.com/VladimirReshetnikov/Shenanigans),
with its full history. It is a catalog of the ways one can get
`theorem Paradox : False` accepted in Lean 4 and in Rocq/Coq, grouped by what
each route costs — which is exactly what the assumption audit reports: paradoxes
of type theory that hypothesize an ingredient the system withholds, sanctioned
escape hatches that the audit names, implementation defects that the audit
reports nothing at all about, and audits that looked and found nothing.

It was split out precisely so that the two are not confused. A `False` derived
there is a statement about a formal system or a program — never a mathematical
fact, and never grounds for doubting anything proved here. Nothing in this
repository depends on it, and nothing there depends on this one; the single
deliberate exception, the axiom-free `TypeTheoryParadoxes` library that was
registered in [`lakefile.toml`](lakefile.toml) and imported by
[`ProveIt.lean`](ProveIt.lean), went with it.

[`Shenanigans/README.md`](Shenanigans/README.md) is a temporary redirect stub
holding the old-path-to-new-path map for anyone arriving from a stale link. It
carries no content of its own and will be removed in due course.

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
[`lib/FormalizedFormalLogic-Foundation`](lib/FormalizedFormalLogic-Foundation/)
is a read-only submodule of `FormalizedFormalLogic/Foundation`, pinned at
commit `32e1a095...`; its Apache-2.0 license is retained.  The corresponding
Coq port lives outside `lib/` under [`Logic/Modal/`](Logic/Modal/).
[`lib/MathComp-Abel`](lib/MathComp-Abel/) is the axiom-free MathComp
Abel--Galois and Abel--Ruffini development, pinned at commit `bce31b97...`;
its CeCILL-B license is retained.  The polynomial-formulas project wraps its
explicit radical-term semantics and quintic obstruction, while the root Rocq
build compiles the pinned sources under the `Abel` logical path.

## License

Unless a nested license says otherwise, this repository is available under
the [MIT No Attribution License (MIT-0)](LICENSE).
