# A constructive complexity-theory atlas in iPRA

Prepared for Vladimir Reshetnikov, 22 November 2026.

Start with **ipra_complexity_atlas.pdf**. Its complete editable source is
`report.tex` with the included `sections/` files.

## Mathematical scope

The report develops **86 labelled theorem and lemma groups**, with explicit
algorithms, witness transformations, resource bounds, and finite induction
invariants. The selected coverage ledger records **59 immediate outgoing
topic links** from the requested computational-complexity article.

Highlights include Cook–Levin and concrete graph/arithmetic/counting
completeness reductions; 2SAT and Horn algorithms; Savitch and constructive
space complementation; QBF and polynomial-horizon games; explicit time and
space separation witnesses; AP = PSPACE; fixed polynomial-hierarchy levels;
uniform circuit simulations; exact randomized amplification; PP, advice,
and second-level hierarchy containment; finite zero-error computation;
matching-order worst-case circuit bounds; sorting, query and communication
lower bounds; and exact integer quantum-path simulations for a stated gate
model.

This reconstructs established complexity results in the stated arithmetic
setting; it does not claim that the classical results are new or settle open
complexity-class equalities. Restricted models, conditional statements,
constructible space-budget hypotheses, nonuniform advice, and omitted
advanced theorems are identified explicitly.

## Formal verification status

- The principal proofs are **human-readable constructive arguments**.
- The new `lean/` files are **uncompiled outlines** containing concrete finite
  definitions and precise proof obligations.
- **No new complete kernel-checked object-language iPRA derivations of the
  main complexity theorems are claimed.**
- Python checks are finite implementation checks, not general proofs or
  asymptotic machine-cost certificates.
- Existing ProveIt endpoints were inspected at commit
  `3eb195cab4cc3d552a9eca78880c6d428f3e44f9`, not rebuilt here.

The exact eventual target is an actual derivation of the encoded sentence:

```lean
([] : List (Fm PTm 0)) ⊢[PRAAx] phi
```

The roadmap separates numerical PR syntax, bounded-formula reflection,
quantifier-free induction, compiler correctness, and operational time/space
bounds. A host theorem or a structure with an assumed correctness field must
not be relabelled an object-language proof.

## Archive contents

| Path | Contents |
|---|---|
| `ipra_complexity_atlas.pdf` | Complete research report |
| `report.tex`, `sections/` | Complete LaTeX source and bibliography |
| `lean/` | Uncompiled semantic outlines and object-proof targets |
| `code/` | Exact finite implementations and independent check programs |
| `CLAIMS.json` | 86-entry result and verification-status inventory |
| `sources/coverage_map.json` | 59 selected immediate-link topics and exclusions |
| `sources/` | Primary references and pinned ProveIt source audit |
| `validation/` | Finite checks, PDF preflight, and verification boundary |
| `SHA256SUMS` | Integrity hashes for all other delivered files |

## Reproduce the finite checks

Python 3.10 or later, standard library only:

```sh
python3 code/verify_all.py
```

The five scripts check machine codecs and packed/sparse semantics; SAT,
circuits and integer/graph reductions; reachability, nonreachability and QBF;
exact probability/counting/lower-bound identities; and quantum path sums
against an independent rational-pair amplitude evaluator.

## Rebuild the PDF

Use a TeX Live installation with pdfLaTeX and the packages listed in
`report.tex`:

```sh
bash build_report.sh
```

The script runs three passes. Temporary `build/` files are excluded from the
archive; the final PDF is placed at the package root.

## Continue the Lean formalization

The included `lean-toolchain` matches the inspected ProveIt toolchain,
Lean 4.32.0. The semantic modules use Std only. With the toolchain installed:

```sh
cd lean
lake build
```

This is a **prospective validation command**, not a build that succeeded in
this delivery. Resolve any elaboration/API issues before treating the semantic
definitions as compiled. `integration/ObjectTargets.lean` belongs in the
ProveIt workspace and is excluded from the standalone build. It imports
actual ConciseIPRA and IPRADerivations interfaces and defines proof targets;
it does not admit them as axioms.

## Suggested ProveIt placement

File the packet under
`Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/` with its source
audit. Eventual checked proofs should live in
`Derivations/Lean/IPRADerivations/`. No repository changes were made for this
archive delivery.
