# Smaller proofs for K215 and a nine-head axiom emitter

Research contribution for Vladimir Reshetnikov's ProveIt, 21 October 2026.

Start with **report.pdf** (17 pages); **report.tex** is the complete editable source.
This package contains checked proof refactoring, checked auxiliary semantic
lemmas, reproducible source edits, and bounded state-reduction experiments.
**It does not contain a verified machine with 214 or fewer states.**

## Concrete results

| Component | Result | Verification boundary |
|---|---|---|
| `seed_semantics/` | A single bundle/seed semantic equivalence and relation-congruence lemma remove 120 lines and 3,788 bytes from two Lean files while retaining their original public signatures. | Fresh Lean 4.32.0 build of all 26 local dependencies plus typed audit. Four axiom reports contain only `propext`, `Classical.choice`, `Quot.sound`. The full 184-module K215 endpoint was not rebuilt. |
| `drain_normalization/` | Universal exact drain theorem; literal checking of all 1,059 drain loops in the inherited 1,426-vertex graph; rank bound six and 367 retained vertices. | Coq 8.18.0 compilation, 11 closed assumption reports, recursive `coqchk`. The result relates configurations of the same graph. Source-to-graph adequacy and a separately encoded compact-machine equivalence are outside this component. |
| `ax9/` | Exact AX10 = DROP;AX9 factorization; restricted biased factorization; protected-tail soundness from prefix credit; finite ghost-zero corollary eliminating credit assumptions for clean-zero-stack soundness. | Coq 8.18.0 compilation, 12 closed assumption reports, recursive `coqchk`. Pairing and theorem-preservation interfaces are explicit parameters. The complete modified witness compiler is a written argument, not a compiled native or binary endpoint. |
| `state_search/` | Exact shorter source artifacts; identity-controlled protected allocations; two context-fold searches and source-reassociation searches. | Bounded experimental evidence only. The 218/217/216-state allocation tables are expressly unverified as consistency machines. No verified 214-state result and no global lower bound. |

The clear AX9 emitter removes the interpreter's preservation of the incoming
top; the existing DROP command restores that action in compiled witnesses.
The biased emitter needs a separate generalization construction. Its factorization
must not be used without the incoming-cache-zero condition.

For the existing 215-state alternatives, M124/M160 give particularly small
local marker invariants; CM215 has the more advanced exact Core/dense adapter.
The report distinguishes this practical integration advantage from an
independently smaller transitive proof. ZC215 provides the useful prefix-credit
interface for arbitrary raw tails. Its count inequality is for prefixes of the
concatenated exhaustive schedule, not of each separately enumerated candidate.

## Integration order

1. Verify the archive's manifest and the two Lean baseline hashes.
2. Review and apply `seed_semantics/seed-semantics.patch` at the repository root.
   Rebuild the affected downstream closure and both endpoint clients with the
   repository's pinned toolchain; repeat their axiom reports.
3. Keep the drain theorem as a reusable arithmetic interface. Do not infer a
   Turing-state reduction from the smaller auxiliary proof graph.
4. Bind the protected-tail/ghost-zero command theorem to the concrete native
   command contracts before using it in an exact-machine endpoint.
5. If pursuing AX9 as a state optimization, formalize its witness compiler and
   optimize the changed source jointly with decoder allocation and consumers.
   The supplied tables do not establish a smaller consistency machine.

No upstream commit or remote repository write was performed by this packet.
The exact inherited K215 theorem, external mathematical consistency calibration,
and a separately internalized PA/ZFC-syntax endpoint remain distinct claims.

## Reproduction

Integrity first (standard-library Python 3):

```sh
python3 verify_manifest.py
```

Fresh local Lean closure, with installed Lean 4.32.0:

```sh
python3 seed_semantics/replay.py --lean /absolute/path/to/lean
```

Generic and literal Coq drain proofs, with Coq 8.18.0:

```sh
python3 drain_normalization/replay.py \
  --coqc /absolute/path/to/coqc --coqchk /absolute/path/to/coqchk \
  --out /tmp/k215-drain-fresh --recursive
```

The command/resource proof and exact source reconstruction are documented in
`ax9/README.md`. From that directory:

```sh
coqc AX9Factor.v
coqchk -silent AX9Factor
python3 verify_ax9_source.py
```

`state_search/README.md` lists complete commands and bounds. Source and fold
checks use Python's standard library; allocation also needs NumPy and SciPy.
Do not disable Python assertions. Search counts are properties of the supplied
deterministic bounded procedures, not exhaustive minimization claims.

Rebuild the report with `sh build_report.sh`. It uses `pdflatex` and standard
LaTeX packages. The delivered PDF was compiled twice and all 17 pages were
rendered and visually inspected. Integrity hashes describe the delivered bytes;
a rebuild may change PDFs, proof objects, or generated logs.

## Contents and trust

Each component keeps its own README, sources, original evidence receipts,
provenance and inherited notices. Compiler binaries, cached proof objects,
virtual environments and unrelated repository material are omitted. Tool
versions and source/object/log hashes in historical receipts describe the
recorded builds; paths in those receipts need not exist on another machine.
Use the portable replay drivers and shipped source snapshots.

`provenance.json` records the two exact upstream commits and core input hashes.
The new semantic results are deliberately separated from inherited graph counts,
marker transports, allocator machinery and the accepted K215 correctness theorem.
A passing SHA-256 manifest is an integrity check only.

New material follows ProveIt's MIT No Attribution terms in `LICENSE.ProveIt`.
Retain the original terms and notices for inherited components in their existing
subdirectories. See `NOTICE.md` for the attribution boundary.
