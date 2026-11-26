# Source-only extraction for the transfer analysis

**Status: UNBUILT here.** No `lake build`, Lean elaboration, kernel check, or
`#print axioms` command was run on this extraction in the producing environment.
The verified facts are the local import closure, unchanged upstream file bytes,
pinned revision identities, and package checksums. The commands below are the
reproduction procedure, not a record of commands already executed.

## Origin and contents

Upstream repository: <https://github.com/lsernau/grh-lean>

Pinned upstream commit:
`72fead102f663d5c7a407964a13dc0cf9d977207`

Edition: `grh/` (the readable edition).

This project contains the full transitive **local** Lean import closure of:

1. `New.Congruences.Selmer.GeneralTheorem`
2. `Lib.Cyclotomic.OddSha`
3. `New.Reduction.Lattices.TwistedLattice`

The union has **216 unchanged Lean source modules**, comprising **125,047 lines**
and **7,510,657 bytes**. The individual closure counts, including each root,
are 208, 90, and 109. Shared files are stored once. The only external import
root is `Mathlib`; it and its dependency sources must be obtained by Lake.

This is a source extraction of existing upstream theorems. It does **not**
contain Lean proofs of the new formal-series, Fitting-profile, sharper torsion
nonvanishing, or standard-cohomology comparison results in the accompanying
paper. Their exact status and remaining formalization work are documented in
`../../formalization/new_results.md`.

`src/ExtractionAudit.lean` is a newly written audit driver containing imports,
`#check`, and `#print axioms` commands for selected existing theorems. It has not
been compiled here. It is not a proof of any new result.

The RH/GRH endpoint modules `Main`, `Statements`, `New.Main`, and
`New.Reduction.OneSidedBound` are absent and are not in any extracted module's
local import closure. No `New.Reduction.Zeros.*` module is included either.
The selected theorems are ingredients of the upstream argument, rather than
imports of its final RH/GRH theorem.

## Reproduce the static package checks

Requirements: Python 3.11 or later. From this directory run:

```bash
python3 scripts/verify_extraction.py
```

This verifies all packaged SHA-256 values, the exact local source set, the
import graph, revision pins, the external import list, and the absence of
the endpoint modules. SHA-256 values cover every regular file initially
packaged under this directory except `provenance.json`, whose self-hash is
necessarily omitted. Files produced later by Lake, or local audit logs, are
not part of the original manifest.

To additionally compare every unchanged file against an independently obtained
checkout of the original revision, use:

```bash
git clone --no-checkout https://github.com/lsernau/grh-lean.git original-grh-lean
git -C original-grh-lean checkout 72fead102f663d5c7a407964a13dc0cf9d977207
python3 scripts/verify_extraction.py --upstream original-grh-lean
```

The comparison checks the upstream Git revision, actual file bytes, and Git
blob identities recorded in `provenance.json`. The clone is optional for the
ordinary checksum check and is not distributed in this package.

## Reproduce the Lean build and axiom audit

Requirements: an installed `elan`/Lean/Lake environment, a C/C++ build toolchain
as required by Lean dependencies, network access to the pinned dependency
repositories and Mathlib cache, and sufficient disk, RAM, and time.

Pinned Lean toolchain:
`leanprover/lean4:v4.35.0`

Pinned Mathlib revision:
`56a005855ea17e0b0958f73ec801ae140b0a1679`

The upstream `lean-toolchain` and `lake-manifest.json` are copied unchanged.
`lakefile.toml` retains the upstream compilation options and dependency pin,
but replaces the full project's `Main`/`Challenge` targets by
`Lib`, `New`, and `ExtractionAudit`. The unmodified configuration is retained
as `lakefile.upstream.toml`.

From this directory, run in order:

```bash
elan toolchain install leanprover/lean4:v4.35.0
lake --version
lake exe cache get
lake build Lib New ExtractionAudit
lake env lean src/ExtractionAudit.lean > axioms-output.txt
```

`lake build` without explicit targets is equivalent because the same three
libraries are the defaults. Do not run `lake update` as a substitute for using
the supplied lock file: it may change the dependency revisions. If cache
fetching is unavailable, compilation of the same pinned dependency sources
is the fallback; this package does not contain the dependency binaries.

The audit driver checks these **existing** upstream declarations:

- `New.Selmer.exists_rootsOfUnity_ellVal_eval_le_add`
- `New.Selmer.exists_rootsOfUnity_ellVal_eval_le`
- `New.Selmer.exists_anticyclotomic_twist`
- `New.exists_length_shaOdd_le`
- `New.TwistedLattice.covolume_add_index_nonneg`

A successful future build and its actual axiom output should be retained as
new evidence. The upstream full-project README's reported checks do not replace
a fresh build of this subset, and a static source scan is not a kernel proof.

## Licenses and provenance

`LICENSE`, `NOTICE`, and `ATTRIBUTION.md` are copied unchanged from the upstream
readable edition. They preserve the upstream copyright and attribution notices,
including notices referring to the full project. Those references do not imply
that the full project or its endpoints are included here. `README.upstream.md`
is also retained unchanged as historical project documentation.

The generated audit driver, modified configuration, and packaging documentation
are clearly identified in `provenance.json`; no upstream Lean source file has
been edited. The manifest records the upstream path, Git blob SHA-1, SHA-256,
and byte length of every unchanged file. It records SHA-256 and byte length for
all other packaged files too. No `.lake` artifacts, compiled Lean binaries,
credentials, or Git repository metadata are included.
