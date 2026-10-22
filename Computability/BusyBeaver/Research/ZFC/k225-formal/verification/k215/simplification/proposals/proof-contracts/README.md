# K215: semantic proof contracts and a shared implication derivation

Research contribution for Vladimir Reshetnikov's **ProveIt**, 21 October 2026.

Reviewed revision: `6f0d42d368506bc29c70ace1c992ed88b2651346`.

Start with **report.pdf**. Its complete editable source is **report.tex**.
The packet includes two independently checked component proposals, their minimal
source dependencies, exact source patches, serial build drivers, raw logs,
source identities, finite audits, and further research questions.

## Recommendation

Make the generic binary/source simulation consume **semantic site contracts**.
The existing full symbolic checker, a shared decoder prefix followed by an
occurrence-specific suffix check, and eventual parameterized primitive proofs
can then produce the same evidence. Preserve exact paths, registers, overflow,
spare data, halt ports, and positive physical progress.

Separately, use the **same existing 58-step truth-free implication derivation**
for Lean and Rocq, with a small numerical adapter in each assistant. The new
Rocq core and adapter have 31.0% fewer source bytes than the maintained replay.

The broader semantic-contract proposal and the 58-step derivation already exist
in the repository. This packet contributes checked implementations and attachment
work; it does not claim to have invented those underlying ideas.

## What was checked

| Component | Actual result | Scope |
| --- | --- | --- |
| Lean semantic simulator | Fresh 29-module build with seven typed compatibility clients | Old executable definitions and public simulator contracts retained |
| Exact decoder/suffix composition | Generic prefix/suffix bridge, literal-source bridge, and actual word `000` decrement example | The example closes both decrement outcomes, 2 of 6,176 branches |
| Rocq implication core | Abstract core, numerical adapter, unchanged `ThmDom` client, recursive `coqchk` | Coq 8.18.0 component check, with included `Stdlib` namespace shims |
| Shared generator | Current Lean core and earlier Nat renderings remain byte-identical | New `--core-rocq` output comes from the same neutral derivation |
| Source audit | Exact machine/source hashes, complete prefix-free source tree, occurrence counts | Finite Python audit; not a kernel theorem |

The full K215 machine-to-ZFC endpoint has **not** been rebuilt with these
patches. The complete-source suffix theorem deliberately retains both the
finite source-shape premise and `CheckedLeafSuffixes`. Neither global premise
is proved in this packet. The old complete coverage proof remains available.

The exact machine is unchanged: 215 working states, 430 actions, dense table
SHA-256 `fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090`.
The preserved endpoint is halting iff ZFC has a finite refutation, followed by
its negation for the consistency equivalence. This is not an unconditional
nonhalting proof or a new internally encoded ZFC/PA derivation.

## Measured source change

| Proof source | Baseline | Proposal | Change |
| --- | ---: | ---: | ---: |
| Rocq dominated implication, counting core and adapter | 22,673 bytes / 1,169 lines | 15,638 bytes / 329 lines | −31.0% bytes / −71.9% lines |
| Lean `KSim` | 16,146 bytes / 356 lines | 20,505 bytes / 460 lines | +4,359 bytes / +104 lines |

The Lean interface is infrastructure for replacing repeated site computations;
it is not an immediate source-size reduction. The independent source audit
finds all 15 old executable definitions and 22 old explicit theorem statements
unchanged; typed clients also check section-inferred parameters.

Do not infer a compile-time gain from the Rocq byte saving. In the accepted
local run the core and adapter took 0.296 + 2.238 seconds, versus 1.881 seconds
for the baseline numerical proof. The complete Lean component check sums to
75.38 seconds. These observations are not full-endpoint paired benchmarks.

An existing 52-step numerical Rocq proposal is smaller than this generic core
plus adapter. The shared 58-step version is useful for common maintenance and
reuse across encodings; no minimal-proof claim is made.

## Contents

| Path | Contents |
| --- | --- |
| `report.tex`, `report.pdf` | Complete paper, with proofs, evidence, integration steps, and research questions |
| `lean/` | 29 minimal sources, semantic interface patch, prefix/suffix modules, concrete example, typed clients, build driver, receipts |
| `rocq/` | Shared derivations and generator, generic core, numerical adapter, exact dependencies, source patch, build driver, receipts |
| `baseline/` | Pinned table and source inputs used in the report and census |
| `evidence/` | Independent review, declaration comparison, historical receipt audit, and decoder census |
| `audit_snapshot.py` | Recompute table/source structure and counts |
| `verify.py`, `MANIFEST.json` | Check artifact integrity and accepted source/log bindings |
| `LICENSE`, `NOTICE.md`, `licenses/` | Project terms and inherited attribution |

There are no compiled proof objects, toolchains, or repository clone in this
archive. The two component READMEs specify precisely which files to integrate.
Do not copy the unchanged dependency snapshots over a newer checkout.

## Reproduce the checks

From the archive root:

```sh
python3 verify.py
python3 audit_snapshot.py --check
python3 evidence/decoder_prefix_census.py
python3 rocq/build.py --coqc /path/to/coqc --coqchk /path/to/coqchk \
  --out /absolute/path/to/fresh-rocq-output
python3 lean/build.py --lean /path/to/lean-4.32.0-linux/bin/lean \
  --out /absolute/path/to/fresh-lean-output
make report
```

The Python integrity checks do not invoke a kernel. The formal builds recompile
the included sources serially under the repository's shared build lock.
The Lean build requires Lean 4.32.0 and its standard library; it needs no mathlib,
network download, or preexisting project cache. The local Rocq receipt is from
Coq 8.18.0; production incorporation still requires the maintained Rocq 9.1.0
endpoint gate.

## Incorporation plan

1. Review the small Rocq patch and generator extension. Add the new core to
   production compile order and manifest/regeneration accounting, then perform
   the complete production endpoint and recursive kernel check.
2. Apply `lean/KSim.patch` while retaining all existing Boolean coverage checks.
   Add the three prefix/suffix modules and keep the compatibility client as an
   audit. Rebuild the affected endpoint closure with correct dependency invalidation.
3. Migrate one existing site block to suffix execution from exact decoder ports.
   Retain every branch and target; measure wall time, peak memory, source size,
   and object size separately against a paired baseline.
4. Expand to all 6,176 outcomes only after the block experiment passes. Then
   replace repeated suffix families by parameterized primitive contracts where
   complete continuation semantics can be shared.

The current source has 4,751 leaves, 23 primitive kinds, and 202 distinct
subtrees. These small syntactic counts do not discharge the occurrence-sensitive
runtime contracts. The census of existing decoder-block clocks totals 213,945
physical prefix-witness steps when counted once for every branch outcome;
that is not a count of kernel reductions or a promised speedup.
