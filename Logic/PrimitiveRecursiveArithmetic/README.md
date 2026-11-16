# Primitive recursive arithmetic

This directory holds ProveIt's work on intuitionistic primitive recursive arithmetic
(iPRA): first-order intuitionistic logic with equality, a function symbol for every
primitive recursive definition with its defining equations, successor axioms, and induction
for quantifier-free formulas.

The parts have different verification statuses.

| Part | What it is | Status |
|---|---|---|
| [`ConciseIPRA/`](ConciseIPRA/README.md) | Very small complete presentations of a theory bi-interpretable with iPRA, and a Lean formalization of the smallest | Lean library, checked by the kernel |
| [`Derivations/`](Derivations/README.md) | Derivations in `ConciseIPRA`'s `Prf PRAAx` of theorems from the packets, with a reusable arithmetic library | Lean library, checked by the kernel |
| [`Bridge/`](Bridge/README.md) | Transport between the Foundation iPRA used by Busy Beaver and ConciseIPRA’s ordinary `Prf PRAAx` | Lean library, checked by the kernel |
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

## Derivations

[`Derivations/`](Derivations/README.md) is the Lake library `IPRADerivations`. Each of its
theorems has the type `[] ⊢[PRAAx] φ` for an explicit iPRA sentence `φ`, and Lean's kernel
checks it. The derivations use only the axioms `PRAAx`: defining equations, successor
axioms and quantifier-free induction. Mathlib is used only in the metatheory, to find and
check them. The library is built bottom-up:

- semiring laws, order, truncated subtraction, division with remainder, gcd and Bézout, parity,
  bounded sums, bounded search, pairing and simultaneous recursion;
- a ring tool that turns polynomial identities over the integers into iPRA derivations;
- a generic infinite-descent theorem.

On top of these it derives theorems from about thirty packets. Examples include the
Cayley–Hamilton theorem in sizes 2 and 3, the universal Desargues identity, Heron's
formula, Brahmagupta's identity and Pell powers, the five Platonic solids, the
irrationality behind the impossibility of doubling the cube and trisecting `60°`,
Euclid's theorem, Bézout's identity, `C(2n, n) ≤ 2^{2n}` and the Catalan identity. The
[Derivations README](Derivations/README.md) lists every module with its packet.

## Proof packets

[`docs/proofs/`](docs/proofs/README.md) files 98 research packets, delivered from 14 to
16 November 2026. Each gives a human-readable proof of a classical theorem in a finitary,
quantitative form intended for iPRA. Most add exact-arithmetic reference code and a Lean plan
or scaffold aimed at `ConciseIPRA`.

The packets are grouped by area:

| Area | Packets | Examples |
|---|---:|---|
| [`algebra/`](docs/proofs/algebra/) | 8 | fundamental theorem of algebra, Puiseux expansions, Abel–Ruffini, Cayley–Hamilton |
| [`analysis/`](docs/proofs/analysis/) | 9 | fundamental theorem of calculus, Stirling's formula, the Gamma and Barnes G functions, residues |
| [`analytic-number-theory/`](docs/proofs/analytic-number-theory/) | 10 | prime number theorem, Dirichlet's theorem, the zeta functional equation |
| [`combinatorics/`](docs/proofs/combinatorics/) | 3 | Bell numbers, Catalan numbers, Fibonacci and Lucas numbers |
| [`diophantine-number-theory/`](docs/proofs/diophantine-number-theory/) | 12 | Pell equations, transcendence of e and π, Fermat for exponents divisible by 3, 4, 5 or 7, Siegel and Faltings analyses |
| [`foundations/`](docs/proofs/foundations/) | 34 | cross-domain frameworks of certificates, moduli and finite contracts |
| [`geometry/`](docs/proofs/geometry/) | 15 | isoperimetric inequality, Platonic solids, spherical trigonometry, Zariski descent, the hat monotile, the Conway criterion |
| [`probability/`](docs/proofs/probability/) | 4 | central limit theorems, expected value, medians, the normal distribution |
| [`topology/`](docs/proofs/topology/) | 3 | Jordan curve theorem, invariance of dimension, observation towers |

**None of these packets has been verified.** The summaries in the
[proofs README](docs/proofs/README.md) repeat what each packet says about itself. Many
packets say that their Lean files are uncompiled outlines, or that they prove only part of
what was asked; for example, the Faltings and Siegel packets do not prove the general
theorems. Sixteen packets state that they construct derivations in `ConciseIPRA`'s `Prf PRAAx`,
all for framework rules and small examples:
- `cifer_ipra_framework_2026-11-15`, in uncompiled source, for residual proof-graph
  compilation and boundary discharge by simultaneous cut;
- `ipra_categorical_methods`, in uncompiled source expressions, for inverse uniqueness,
  Yoneda components and contract cut;
- `ipra_cbip_framework_2026-11-16`, in an uncompiled candidate, for a normalised
  trace-reflection kernel;
- `ipra_coherent_methods_2026-11-15`, for contract composition, specialization, a
  quantifier-free induction interface and identity iteration;
- `ipra_finite_query_normal_form_2026-11-16`, in uncompiled source, for structural
  combinators under its certificate extractor;
- `ipra_frnf_framework_bundle`, in uncompiled source, for logical combinators that
  compose local derivations by simultaneous cut;
- `ipra_kernel_finite_use_framework_2026-11-15`, in untypechecked source, for composing a
  proof schedule by simultaneous cut and for a quantifier-free induction loop;
- `ipra_kifc_framework_2026-11-15`, in an uncompiled outline, for compiling a proof
  schedule and a quantifier-free induction loop certificate;
- `ipra_kifc_framework_2026-11-16`, its second edition, in uncompiled adapters, for the same
  compilers on top of the checked bounded-search backend;
- `ipra_kifcr_framework_2026-11-16`, in uncompiled outlines, for residual compilation
  closed by simultaneous cut;
- `ipra_local_global`, for a variable-length recursion rule and an example;
- `ipra_native_clause_framework_2026-11-15`, through the native clause calculus `KPrf` in
  uncompiled source, for list cut and export by `native_iff_pra`;
- `ipra_presentations_to_witnesses`, for fusion, relational simulation, squaring transport
  and a successor instance;
- `ipra_resources_and_elimination_2026-11-15`, for a term-to-symbol compiler and the
  equations of a backward demand pass;
- `ipra_staged_contract_kernel_2026-11-15`, in uncompiled source, for staged specialisation
  by `Prf.subst`, `Prf.weaken` and `Prf.trans`;
- `algebra/ipra_stable_observables`, for five observation combinators.

The first fifteen are in `foundations/`.

No packet claims such a derivation for one of its main theorems; checked derivations of a
number of them are in [`Derivations/`](Derivations/README.md). The proofs README also lists the
members that were not placed, in
[`OMITTED.tsv`](docs/proofs/OMITTED.tsv).

## Delivering new material

New packets arrive as `.zip` archives in [`docs/incoming/`](docs/incoming/). Each is placed
under `docs/proofs/<area>/<archive name>/`, recorded in the proofs README, and then removed
from `docs/incoming/`. The ledger in
[`docs/incoming/README.md`](../../docs/incoming/README.md#ipra-proof-packets-from-docsdrafts)
records each intake. `ConciseIPRA` has its own drop directory,
[`ConciseIPRA/docs/incoming/`](ConciseIPRA/docs/incoming/).
