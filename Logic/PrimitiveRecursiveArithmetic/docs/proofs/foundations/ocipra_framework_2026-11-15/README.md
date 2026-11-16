# OCiPRA: Observation-Contract Internalization for iPRA

Research package prepared for Vladimir Reshetnikov, 15 November 2026
(America/Los_Angeles).

## Start here

Read **`paper/ocipra_framework.pdf`**, a 49-page report. Its complete editable
source is **`paper/ocipra_framework.tex`** with the section files under
**`paper/sections/`**.

The package is based on ProveIt commit
`9df5cbdf39e6220be823f611987bd584d37711fd`, with a targeted audit of
`Logic/PrimitiveRecursiveArithmetic`.

## Main contribution

The existing repository already contains strong finite-observation, demand,
relational-certificate, local-to-global, and stable-observable ideas. OCiPRA
organizes them into one proof-producing statement calculus with four theorem
classes:

1. deterministic contracts;
2. bounded relational contracts;
3. branch-independent or diameter-stable observables;
4. conditional theorems whose nonuniform producer data is explicit.

The framework keeps four boundaries separate: finite observation versus ideal
object, producer versus verifier, host semantic theorem versus object-language
derivation, and relation versus exact selector.

The report gives detailed human proofs of:

- finite coding closure and bounded-formula Booleanization;
- least bounded search and complete bounded enumeration;
- deterministic contract-DAG composition;
- clocked finite-trace reflection;
- monotone finite demand closure for cyclic precision requirements;
- backward-demand/forward-replay compilation for changing-parameter recursion;
- finite backward viability and least successful paths;
- exact branch elimination under observable invariance;
- approximate branch elimination under a diameter certificate;
- producer-verifier-derivation factorization;
- height-to-list conversion and the obstruction to deriving a cutoff from
  cardinality alone;
- reusable treatments of represented reals, formal series, finite laws, finite
  nets, root clusters, spectral data, and conditional Diophantine/analytic
  certificates.

## Exact status

- **Human mathematical arguments:** complete for the framework theorems in
  `metadata/THEOREM_LEDGER.md`.
- **Python:** eleven exact-arithmetic regression tests pass; the demo produces
  replayable JSON evidence for bounded search, demand closure, deterministic
  DAG evaluation, relational viability, and statement classification.
- **PDF:** compiled successfully, preflighted, rendered at 160 DPI, and visually
  inspected page by page. The delivered report has 49 pages.
- **Lean:** an integration-oriented outline uses the current repository names
  `PR`, `PTm`, `PRAAx`, `Prf`, `NPrf`, `PRA.qfInd`, and
  `native_iff_pra`. It includes proof-carrying contract structures and a small
  actual object-language identity contract. No Lean executable was present in
  the artifact runtime, so no new kernel build is claimed.

The Lean sources contain no declared `axiom` and no `sorry`. Unfinished results
are represented as proof-field interfaces or commented theorem signatures, not
as admitted theorems or trivial proposition placeholders.

This package does **not** claim a newly checked generic `Prf PRAAx` compiler,
general effective Faltings or Siegel, uniform Mordell-Weil representatives,
ineffective prime-distribution constants, an exact branch selector through
arbitrary collisions, or verification of all repository packets.

## Contents

| Path | Purpose |
|---|---|
| `paper/` | Complete LaTeX source and compiled PDF |
| `lean/OCiPRA/` | Object-language interfaces, target packages, compiler blueprint, and example |
| `lean/FORMALIZATION_PLAN.md` | Dependency-ordered route to complete Lean formalization |
| `code/ocipra.py` | Exact reference algorithms |
| `code/test_ocipra.py` | Eleven regression tests |
| `code/demo.py` | Reproducible finite examples |
| `schema/contract.schema.json` | Machine-readable theorem-contract schema |
| `metadata/` | Theorem ledger, claim inventory, and difficulty matrix |
| `provenance/` | Pinned source audit and manifest |
| `validation/` | Test results, TeX logs, PDF metadata, preflight, and visual-QA record |
| `verify.py` | Standard-library verification runner |
| `build.sh` | Rebuild tests, PDF, and checksums |
| `MANIFEST.sha256` | Integrity hashes for archive members other than the manifest |

## Reproduce

Python 3.10 or newer and a standard `pdflatex` installation are sufficient for
the included checks and report:

```sh
./build.sh
```

Or run the finite checks alone:

```sh
python3 verify.py
```

The build does not download Lean. To test the Lean outline, place the `OCiPRA`
modules in the pinned ProveIt root workspace using Lean 4.32.0 and follow
`lean/FORMALIZATION_PLAN.md`.

Finite tests are implementation evidence, not universal proofs or an iPRA proof
checker. A host theorem is not counted as an iPRA theorem unless its conclusion
is an actual `NPrf` or `Prf PRAAx` judgment.
