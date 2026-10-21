# Intake note: proof-simplification proposal for the K215 endpoints

`proof_refactor/` of `Proof_Simplification_and_GC-ZC215_2026-10-21.zip` (arrival commit
`05d063acef`, pinned at `c9dc793234`), placed in batch 204 as delivered and byte-identical; the
rest of the archive is `candidate-k215/alternatives/gc-zc215/`. Nothing here is compiled; the
delivery says so itself (`REPORT.md`, `METRICS.json`).

Status of its proposals against `main` at placement:

* **Offset-bisimulation symmetry in Lean** (`OffsetBisimSymmetry.lean`, `proposed/`): already
  realized on `main` by `RMOffsetBisim.OBisim.symm`; `KSource215` checks only the forward
  certificate and the sixteen backward-check modules are gone. The proposal is superseded.
* **The same symmetry in Rocq**: `Source215.v` still checks `Cert215` and `omirror Cert215`
  separately; a generic `ocheck_mirror` lemma removes the second check. Open.
* **Compact Rocq certificate** (`Cert215Compact.v`, 190,411 bytes against 1,499,170 for
  `Cert215Offsets.v`, the same 2,240 rows by the delivery's Python round trip): open; adopt only
  with a kernel-checked decoding.
* **Ordinary bisimulation for zero offsets**, and **shared decoder proofs for `KSites215`**:
  open research directions; the report itself warns that identical source subtrees are not a valid
  memoization key.

`upstream/` copies pinned repository files and build records; they keep the build machine's
absolute paths.
