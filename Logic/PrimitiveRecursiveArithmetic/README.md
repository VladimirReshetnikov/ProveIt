# Primitive recursive arithmetic

This directory holds ProveIt's work on intuitionistic primitive recursive arithmetic
(iPRA): first-order intuitionistic logic with equality, a function symbol for every
primitive recursive definition with its defining equations, successor axioms, and induction
for quantifier-free formulas.

It has two parts. They differ in what has been checked.

| Part | What it is | Status |
|---|---|---|
| [`ConciseIPRA/`](ConciseIPRA/README.md) | Very small complete presentations of a theory bi-interpretable with iPRA, and a Lean formalization of the smallest | Lean library, checked by the kernel |
| [`docs/proofs/`](docs/proofs/README.md) | Delivered research packets giving finitary proofs of classical theorems, meant to be expressed in iPRA | Filed as delivered; nothing rerun, checked or compiled |

## ConciseIPRA

[`ConciseIPRA/`](ConciseIPRA/README.md) asks how small a complete proof checker for a theory
bi-interpretable with iPRA can be. The smallest checkers all implement the *native scalar
core*. It has one numerical sort with a single iterator, two binders, and six rules besides
the two computation equations of the iterator.

- [`ConciseIPRA/docs/Article/`](ConciseIPRA/docs/Article/) is the unified article that merges
  the delivered packages.
- [`ConciseIPRA/Artifacts/`](ConciseIPRA/Artifacts/) keeps the executable part of each
  package: its proof checkers, certificates and evidence.
- [`ConciseIPRA/Lean/ConciseIPRA/`](ConciseIPRA/Lean/ConciseIPRA/) is the Lake library
  `ConciseIPRA` of the root workspace (namespace `LeanProofs.ConciseIPRA`). It formalizes three
  systems and proves them mutually bi-interpretable:
  - the native scalar core;
  - `T_eq`, intuitionistic natural deduction with equality over the iterator terms;
  - iPRA in the usual form, `PR` terms with the axioms `PRAAx` and derivations `Prf`.

  The transfer theorem `pra_iff_native` is the bridge that the proof packets aim at.

The [ConciseIPRA README](ConciseIPRA/README.md) states the results with their Lean names. It
also records the intake of those packages.

## Proof packets

[`docs/proofs/`](docs/proofs/README.md) files 56 research packets, delivered on 14 and
15 November 2026. Each gives a human-readable proof of a classical theorem in a finitary,
quantitative form intended for iPRA. Most add exact-arithmetic reference code and a Lean plan
or scaffold aimed at `ConciseIPRA`.

The packets are grouped by area:

| Area | Packets | Examples |
|---|---:|---|
| [`algebra/`](docs/proofs/algebra/) | 6 | fundamental theorem of algebra, Puiseux expansions, Abel–Ruffini, Cayley–Hamilton |
| [`analysis/`](docs/proofs/analysis/) | 8 | fundamental theorem of calculus, Stirling's formula, the Gamma function, residues |
| [`analytic-number-theory/`](docs/proofs/analytic-number-theory/) | 10 | prime number theorem, Dirichlet's theorem, the zeta functional equation |
| [`combinatorics/`](docs/proofs/combinatorics/) | 1 | Bell numbers |
| [`diophantine-number-theory/`](docs/proofs/diophantine-number-theory/) | 12 | Pell equations, transcendence of e and π, Fermat for exponents divisible by 3, 4, 5 or 7, Siegel and Faltings analyses |
| [`foundations/`](docs/proofs/foundations/) | 5 | cross-domain frameworks of certificates, moduli and finite contracts |
| [`geometry/`](docs/proofs/geometry/) | 11 | isoperimetric inequality, Platonic solids, spherical trigonometry |
| [`probability/`](docs/proofs/probability/) | 1 | central limit theorems |
| [`topology/`](docs/proofs/topology/) | 2 | Jordan curve theorem, invariance of dimension |

**None of these packets has been verified.** The summaries in the
[proofs README](docs/proofs/README.md) repeat what each packet says about itself. Many
packets say that their Lean files are uncompiled outlines, or that they prove only part of
what was asked; for example, the Faltings and Siegel packets do not prove the general
theorems. No packet supplies a completed derivation in `ConciseIPRA`'s `Prf PRAAx`. The
proofs README also lists the members that were not placed, in
[`OMITTED.tsv`](docs/proofs/OMITTED.tsv).

## Delivering new material

New packets arrive as `.zip` archives in [`docs/incoming/`](docs/incoming/). Each is placed
under `docs/proofs/<area>/<archive name>/`, recorded in the proofs README, and then removed
from `docs/incoming/`. The ledger in
[`docs/incoming/README.md`](../../docs/incoming/README.md#ipra-proof-packets-from-docsdrafts)
records each intake. `ConciseIPRA` has its own drop directory,
[`ConciseIPRA/docs/incoming/`](ConciseIPRA/docs/incoming/).
