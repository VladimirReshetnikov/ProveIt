# Finite contracts for mathematics in intuitionistic primitive recursive arithmetic

Research report prepared for Vladimir Reshetnikov, 16 November 2026.

**Start with `paper/ipra_framework.pdf`.** Its complete LaTeX source is
`paper/ipra_framework.tex`, with the argument split into the files in
`paper/sections/`. The article contains the full mathematical arguments;
the code and Lean files support reproduction and subsequent formalization.

Source repository: <https://github.com/VladimirReshetnikov/ProveIt>

Pinned source commit: `42c64ff3a9f56f2a9edc1525e75ece3b720c7f77`.

## Results

The framework gives a direct bounded-formula Booleanization argument, a
guarded quantifier-free induction rule for bounded loops, proof-producing
composition, and contracts exposing the finite observations a construction
needs. Fixed primitive recursive evaluators, finite input tables, and
clocked traces are separate interfaces. A universal unclocked primitive
recursive evaluator is explicitly ruled out.

The common analytic tools include rational separation, a finite arithmetic
precision budget, ordinary operations on names, finite-grid integration,
extension from rational to represented points, and finite positivity and
cover certificates.

The principal applications are:

1. **Stable finite windows.** Explicit primitive recursive selectors for
   bounded monotone rational and represented-real sequences. The represented
   selector minimizes rational endpoint differences and retains a strict
   numerical margin. A separate cardinality theorem constructs an empty
   window. Explicit computability examples explain why these results do not
   supply a final convergence modulus or cutoff.
2. **Coherent approximate witnesses.** A finite rational residual minimizer,
   together with a supplied primitive recursive isolation modulus, yields a
   single fast name. Qualitative uniqueness alone is not substituted for
   that modulus.
3. **Local analytic branches.** A finite contraction certificate gives
   coefficient names, a radius, explicit tails and residual estimates for
   an implicit branch with arbitrary fixed primitive recursive Cauchy
   coefficients. A further theorem computes the certificate from a supplied
   simple-root name and derivative gap, using predetermined precisions.
   Singular chart discovery remains outside this theorem.
4. **Integral power-gap certificates.** If `D^m f = A^m + R`, `m >= 2`,
   `r = deg A >= 1`, `R != 0`, and `deg R < (m-1)r`, all integral solutions
   of `y^m = f(x)` satisfy `|x| <= H`, `|y| <= K`, where
   `H = (m-1) sum_(i<r) |a_i| + sum_i |r_i|` and
   `K = sum_i |f_i| H^i`. The report proves a certificate constructor by
   rational polynomial power completion, complete bounded enumeration, and
   transport with a supplied denominator bound. It classifies all integer
   points of `y^m = x^(mr) + x + 1`, uniformly for `m >= 3`, `r >= 1`.

These are extensions and a common organization of established mathematical
methods, with explicit attribution to the existing packet results. No
mathematical priority claim is made.

## Exact proof status

The article supplies written mathematical proofs and the arithmetic
induction audit. **The major application theorems have not been converted
into complete Lean `Prf PRAAx` terms.**

There are three distinct Lean categories:

| Category | Files and scope |
|---|---|
| Embedded iPRA infrastructure and examples, compiled | `ObjectKernel`, `ObjectBridge`, `ObjectExamples`. The example includes the actual object-theory proof of `forall x, x + 0 = x` using quantifier-free induction. |
| General semantic lemmas, compiled | `FiniteContracts`, `Metastability`, `PowerGap`. These are ordinary Lean proofs about finite algorithms and integers, including the all-sign integer power gap. |
| Compiled definitions and **unproved propositions** | `AnalyticTargets`, `SelectionTargets`, `SeriesTargets`, `ChartProducerTargets`, `PowerGapTargets`. The few definitional lemmas and closed examples in these files are separately identified; compiling a target does not prove it. |

`RepositoryBridge.lean` is an additional source adapter to the inspected
native bi-interpretation API. It was **not compiled against the complete
upstream dependency closure**. The other twelve `.lean` files, including
`AxiomAudit.lean`, are included in the standalone build.

The audited proof declarations use no `sorryAx` or `Classical.choice`.
Some use Lean's standard `propext` and `Quot.sound`; these concern the
metatheory and do not add rules to the embedded intuitionistic theory.
There is no general claim that a semantic Lean theorem automatically yields
an iPRA derivation. The article and `lean/README.md` give the missing
definitions, proof constructors, main targets, and dependency order.

General effective Siegel, Faltings, Roth, uniform Mordell–Weil generation,
Chebotarev, Siegel–Walfisz, and Bombieri–Vinogradov are not proved here.
Nor is their independence from iPRA claimed.

## Contents

| Path | Contents |
|---|---|
| `paper/` | Full LaTeX sources, PDF, references, and PDF build script. |
| `lean/` | Standalone Lean modules, integration adapter, exact status, upstream source hashes and license. |
| `code/` | Four exact-arithmetic reference programs using Python's standard library. |
| `validation/`, `verification/` | Actual build records, axiom audits, exact finite check results, and review status. |
| `provenance/packet_catalog.csv` | All 46 index entries; a catalog, not a verification of 46 packets. |
| `provenance/source_manifest.json` | Exact paths, pinned URLs, and hashes for 31 selected consulted files. |
| `provenance/SOURCE_AUDIT.md` | What was read, inherited results, additions, and remaining dependency boundaries. |
| `proof_status.json` | Machine-readable result/status inventory. |
| `SHA256SUMS` | Integrity checksums for the delivered archive members other than this manifest itself. |

The full source repository, Lean distribution, generated `.olean` files,
TeX auxiliary files, and private rendering intermediates are not bundled.
No source repository changes were committed or published.

## Rebuild

The standalone Lean build requires **Lean 4.32.0** and `Std`; Mathlib is
not required. The compiler used was commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`.

```sh
LEAN_BIN=/absolute/path/to/lean-4.32.0/bin/lean ./build.sh lean
```

The reference computations require Python 3.10 or newer and only its
standard library. They use exact integer and rational arithmetic.

```sh
./build.sh checks
```

The PDF uses pdfLaTeX with ordinary TeX Live packages, including Latin
Modern, AMS mathematics, geometry, microtype, booktabs, longtable, xurl,
enumitem, fancyhdr, and hyperref. No shell escape is required.

```sh
./build.sh paper
```

`paper/build.sh` performs three passes and fails on missing references.
It includes a private fallback for Linux installations whose TeX source
files exist but whose format/database was not initialized; normal TeX
installations use their existing configuration. The optional fallback is
kept under `paper/.tex-runtime/` and does not modify system configuration.

```sh
LEAN_BIN=/absolute/path/to/lean-4.32.0/bin/lean ./build.sh all
```

Finite test results are implementation evidence, not universal proofs and
not an iPRA proof checker. The checks include invalid inputs, sign and
parity cases, clipped rational approximations, complex chart inputs,
empty windows, polynomial completion, and denominator transport.

To regenerate the provenance files from a checkout at the pinned commit:

```sh
python3 provenance/rebuild_provenance.py /absolute/path/to/ProveIt
```

The source identity of the copied foundational blocks is documented in
`lean/UPSTREAM_SOURCES.json`. Their upstream MIT No Attribution license is
included in `lean/LICENSE-ProveIt.txt`. The standalone kernel and original
repository kernel define the same names; use one kernel source at a time.
