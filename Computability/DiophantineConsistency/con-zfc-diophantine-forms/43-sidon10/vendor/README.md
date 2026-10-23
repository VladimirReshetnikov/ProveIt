# Inherited sources, coefficient reconstruction, and proof dependencies

This directory preserves the sources used by the new simultaneous quadratic
coefficient construction. The main inspected ProveIt snapshot is

`VladimirReshetnikov/ProveIt@22e75dd6b87b1b199bb08c778d7cf075ae5aae08`.

The exact source root is
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms`.
The complete manifest is [SOURCES.json](SOURCES.json). Every copied source is
byte-for-byte unchanged: its original Git blob SHA-1 was recomputed during
retrieval, and the manifest also gives its SHA-256, size, repository path, and
retrieval commit. The manifest covers 70 preserved files, totaling 630,099
bytes. This guide, the reconstruction wrapper, and the new receipts are new
package support files, rather than upstream copies.

## Reproduce the active coefficients and algebraic parent

From the archive root, run:

```sh
python3 vendor/rebuild_coefficients.py
```

The script uses only the Python standard library. It locates the archive
relative to its own file, so it also works from another current directory.
An optional positional argument specifies a different archive root. No
network access is required. The script executes the two preserved builders
in temporary copies and removes those copies afterwards. It does not
rewrite any preserved upstream source or active data file.

The reconstruction checks all preserved file hashes, all eight input pins
in the inherited coefficient generator, and literal equality of the 430
compiler transition rows with [machine/k215.tm](machine/k215.tm). It then
reconstructs all 943 ordered Wang tiles, runs the original finite geometry
and rank-control checks, and materializes the four fixed integer ports.
The generated raw bytes must agree exactly with all four active files under
`../data/`. The program also regenerates the 31-variable quadratic parent
from its preserved 32-variable ancestor and compares it byte for byte with
`../data/parent_quartic31.json`.

The fresh receipts are:

- [REBUILD_RECEIPT.json](REBUILD_RECEIPT.json): source authentication, machine
  table equality, 69,230 native basis checks, coefficient geometry,
  rank-control checks, and four raw coefficient comparisons.
- [PARENT_REBUILD_RECEIPT.json](PARENT_REBUILD_RECEIPT.json): inherited exact
  algebraic audits and the regenerated parent SHA-256
  `1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287`.

Both reconstructions passed when this packet was prepared. All four gzip
files also reproduced byte for byte under Python 3.12.14. Raw integer bytes
are the mathematical identity criterion; the wrapper records gzip equality
separately because compressor output can vary between Python versions.

### The complete active tuple

The native compiler has `rho = 2^121`, `L = 8801`, and
`B_native = 2^1064921`. Its actual four ports are:

| Active port | Payload name | Definition | Bit length |
|---|---|---|---:|
| `beta` | `beta.bin.gz` | `B_native - 1` | 1,064,921 |
| `K0` | `K.bin.gz` | `DC + B_native * DR` | 1,070,004 |
| `MC` | `MC.bin.gz` | Native computation mask | 1,064,921 |
| `MF` | `MF_source.bin.gz` | `MF_native + B_native - 1` | 1,064,922 |

The raw unsigned little-endian payloads total 533,099 bytes. Their SHA-256
values are recorded in both receipts and in the active binding. The fourth
port is **already shifted**; no further shift is applied. All four ports
are replaced together. These native constants are distinct from the new
source-compression base constant `beta_Q = 2^2134940` and its variable radix.

The active adapter proof is
[package31/coefficients/COEFFICIENT_PROOF.md](package31/coefficients/COEFFICIENT_PROOF.md).
Its original literal builder, input tables, source pins, binding, proof
antecedents, and compressed payloads retain their original relative layout
under `package31/coefficients/`. The package-level `../INSTANCE.json` gives
the authoritative active interpretation. Historical default bindings in
the algebraic parent and package 18 describe older tuples and do not select
the tuple used by the new equation.

## What each preserved group supplies

| Local location | Role in the proof |
|---|---|
| `machine/k215.tm` | Exact 215-state, two-symbol blank-input machine; 430 working transitions. |
| `machine/KEndpoint215.lean` | Exact endpoint statement `BlankHalts machine215` iff `BProv ZFCax_s [] Form.fBot`, with its explicit Lean imports. |
| `machine/proof.md`, `README.md`, `provenance.json`, `canonicalization.json` | Ordinary machine/calculus calibration, conventions, provenance, and dense-state correspondence. |
| `compiler/WANG943_COEFFICIENTS.md` | Directed-signal 943-tile language, marked periodic tableau semantics, and its native arithmetic interface. |
| `compiler/WANG943_COMPACT_LAYOUT.md` | Earlier compact-layout adapter, preserved as ancestry. Its coefficient tuple is historical. |
| `package31/coefficients/COEFFICIENT_PROOF.md` | Complete active 121-by-8801 coefficient adapter and port conventions. |
| `package31/coefficients/upstream/` | Original transition/tile inputs and the package 24, 25, and 27 coefficient proofs used by that adapter. |
| `package31/sources/BLANK_HELICAL_PROOF.md` | Blank-tableau completeness and helical seams; the newer Wang language has its own preserved interface proof above. |
| `package31/sources/FIXED_BLANK_67_PROOF.md`, `ORDINARY_BLANK_PROOF.md`, `PELL_LEMMA_AUDIT.md` | Native-window/Pell semantics, sign and positivity obligations, actual-rank control, and completeness. |
| `compiler/pell/` | Ten detailed antecedent Pell and auxiliary-projection proofs referenced by the inherited audit. |
| `package18/report.tex` | Earlier quartic/compiler exposition at the exact package-18 source pin. Its nine-variable specialization and default coefficients are historical. |
| `quartic31-source/` | Exact packing-register elimination proof and executable algebraic builder, together with all three literal inputs needed by that builder. |
| `package31/sources/QUARTIC31_SOURCE_PROOF.md` | Current package-31 copy of the 31-positive-variable, 22-quadratic-equation source theorem. |
| `package31/signed10/SIGNED10_PROOF.md` | Inherited Sun bridge and signed finalizer, with the predecessor's geometric source positions. The new report replaces only the source-coding construction and rechecks the bridge interface. |
| `package31/signed10/build_signed10.py`, `circuit.py` | Exact predecessor finalizer code for comparison. These files are archival reference; its old data/generated tree is not reproduced here. |
| `package31/signed10/SOURCES.json` | Primary Sun paper references and the precise imported theorem locations. |

The extra signed-17 and digit-circuit proof copies in `package31/sources/`
retain useful ancestry and attribution. They do not change the selected
10-integer construction or its current coefficient binding.

The mathematical dependency is: finite ZFC refutation, calibrated blank
K215 halt, marked 943-tile computation, the coherent four-port Pell/compiler
instance, the 31-positive-variable quadratic system, the new simultaneous
quadratic digit construction, and the inherited signed finalizer. The new
report proves the new coefficient-extraction and bridge obligations.

## Pins and historical references

Most files are retrieved from the main inspected pin
`22e75dd6b87b1b199bb08c778d7cf075ae5aae08`. Its package 31 itself preserves
the earlier source pin `8c6eec9d19ef80538c8e61ff6e0180040583446a`. This
historical value remains unchanged inside the original generator, notices,
and source-pin files; it is not a conflicting claim about the current
retrieval snapshot.

Two additional preserved groups use their exact historical snapshots:

- `quartic31-source/` is retrieved from
  `8c6eec9d19ef80538c8e61ff6e0180040583446a`, where the complete original
  package-30 builder and its literal inputs remain together.
- `package18/` is retrieved from
  `ae3007ca4467011e0e051c84acb4a1dd13971b0e`, the precise package-18 ancestor
  cited by that builder and its source ledger.

Each file has its own `retrieval_commit` in the new manifest. Historical
documents retain their original relative references, numerical records,
and claims; none was edited to impersonate the new construction. Use this
directory map for bundled counterparts and the manifest's repository path
and commit for an unbundled historical reference. For example, the complete
upstream file URL has the form
`https://github.com/VladimirReshetnikov/ProveIt/blob/<retrieval_commit>/<repository_path>`.

## Proof boundary and externally cited results

Everything needed to regenerate the active four coefficients and the
literal quadratic parent is present. These finite executions establish
exact identities and stated finite checks. They do not establish the
unbounded compiler theorem, prove the consistency of ZFC, or produce a new
proof-assistant certificate for the complete final equation.

The archive includes the exact K215 endpoint theorem source for a precise
calibration target. Its complete transitive Lean imports, Mathlib/toolchain,
and historical machine compiler implementation are not bundled. Rebuilding
that formal endpoint requires the pinned ProveIt project. The endpoint
statement is imported with the scope identified in the article.

The two published/preprint mathematical sources are cited, rather than
reproduced, here:

- Zhi-Wei Sun, *Further results on Hilbert's Tenth Problem*, Science China
  Mathematics 64 (2021), 281–306; [arXiv:1704.03504v7](https://arxiv.org/html/1704.03504v7).
- Zhi-Wei Sun, *Ten unknowns for Hilbert's tenth problem over the integers*,
  2026 preprint; [arXiv:2609.01594v2](https://arxiv.org/html/2609.01594v2).

The inherited ten-variable theorem and Pell/interpolation bridge are Sun's
results. The new work is the explicit simultaneous quadratic encoding and
its verified specialization, not a new general ten-variable theorem.

## Attribution and licenses

The original ProveIt MIT No Attribution terms are preserved in
[package31/LICENSE](package31/LICENSE) and
[package31/coefficients/licenses/LICENSE](package31/coefficients/licenses/LICENSE).
The coefficient subtree also preserves `LICENSE.Wade` and `NOTICE-K215.md`.
The machine subtree preserves its `NOTICE.md`, `LICENSE.ProveIt`,
`LICENSE.Wade`, original/normalized-source notices, and source pins.
The historical package-18 notice and license are retained beside its report.

These inherited notices credit their respective authors and contributors,
including Vladimir Reshetnikov's ProveIt project, the Codex research
collaboration, Mira, Elliot Glazer, Jeff's busy-beaver/Rocq work, Andrew James
Wade's compiler ancestry, BusyCoq, and the Coq Library of Undecidability.
Each notice keeps its own stated scope. New support files follow the
package's MIT No Attribution terms; inherited third-party terms are not
replaced or broadened by this guide.
