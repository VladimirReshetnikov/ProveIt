# Quantitative integration and transport in iPRA

Research package prepared for Vladimir Reshetnikov, 20 November 2026.

Start with **paper/ipra_measure_transport.pdf**. Its LaTeX source and every
included section are beside it. The package extends the inspected ProveIt
continuous frameworks with quantitative measure constructions, corrected
substitution rules, and stable analytic/topological observations.

## Main mathematical outcomes

- A corrected clipping estimate constructs an L1 limit from a bounded-metric
  Cauchy rate and a uniform excess-tail cutoff. A supplied limit is unnecessary.
- Coherent dyadic masses construct a unique density from an energy-tail rate.
  A local sibling-oscillation bound produces that rate explicitly.
- A mere energy cap yields a bounded-search stability window. A halting
  reduction proves that a uniform full convergence-rate extractor is impossible.
- Fubini, conditional averages, bounded operators, concrete tensor products,
  and integral-quantifier semantics share finite norm estimates.
- Diagonal substitution and supremum are shown to be invalid L1 operations.
  Bounded compression and an explicit Lipschitz upgrade repair useful cases.
- Rips interleavings use interval distance certificates and labelled vertices,
  retaining stable topology without deciding exact threshold equality.
- Contractive integral equations and holomorphic transforms of L1 data have
  explicit primitive recursive producers and error schedules.
- A reverse pass through a dependency graph combines sensitivities and reuses
  input approximations; no polynomial-time claim is made for arbitrary data.

## Verification status

`lean/` is a standalone **successfully compiled Lean 4.32.0 project** containing
35 named proved theorems and eight checked examples. It verifies finite rational
clipping, stable truncation, excess-tail bounds, energy identities, and a bounded
energy-window search. No new axiom declaration or admitted proof occurs.

These are **host Lean proofs, not new `Prf PRAAx` derivations**. Their axiom audit
reports `propext`, `Classical.choice`, and `Quot.sound`. The report, blueprints,
and `lean/OBJECT_LANGUAGE_PLAN.md` state the separate path to intuitionistic
object-theory derivations. The new analytic endpoints are not fully reified.

The Python programs perform exact-rational finite checks; their results do not
replace the human proofs or prove the universal theorems. All counts and scopes
are in `validation/`. The mathematical review files record independent checks
and the resolution of their corrections.

## Layout

| Directory | Contents |
|---|---|
| `paper/` | Complete report, compiled PDF, main TEX, section TEX files and references |
| `lean/` | Checked finite rational kernel, pinned toolchain, build files, axiom receipt and object-language plan |
| `blueprints/` | Definitions, theorem targets, and implementation order for measure, category/model/topology, and analytic modules |
| `code/` | Exact-rational measure, topology, operator, and analytic demonstrations |
| `metadata/` | Source audits, pinned revision, source hashes, theorem ledger |
| `validation/` | Check results, Lean build receipt, independent mathematical reviews and PDF review |

## Reproduce

Run `python3 reproduce.py` for the three standard-library-only Python checks.
Run `python3 reproduce.py --lean` to additionally build the Lean project; Elan
can select the toolchain from `lean/lean-toolchain`. A standalone Lean install
can be used by setting `LEAN_LAKE_BIN` to its absolute `bin/lake` path.

Run `python3 reproduce.py --pdf` to additionally compile the LaTeX with a working
TeX installation. Set `PDFLATEX_BIN` to an absolute pdfLaTeX executable when it
is not selected by the normal PATH. The document needs standard LaTeX packages including amsmath,
amsthm, lmodern, microtype, booktabs, longtable, enumitem, xurl, hyperref and
fancyhdr. The delivered PDF is compiled from the included TEX, not reconstructed
from a text summary. No compiler binary or downloaded TeX distribution is bundled.

## Source baseline and attribution

ProveIt commit: `b2341af5370cd8a43f72ebb2341c0d7d7395b634`.
The source audit distinguishes already checked object-iPRA results from earlier
unverified delivered packets. In particular, the repaired separate-tail shortcut
in the expected-value packet is different from the library's valid common-envelope
truncation theorem. Standard classical and constructive results are credited in
the bibliography; no novelty claim is made for the classical theorems.

`SHA256SUMS` records the packaged files, excluding itself. The ZIP checksum is provided with the delivery.
