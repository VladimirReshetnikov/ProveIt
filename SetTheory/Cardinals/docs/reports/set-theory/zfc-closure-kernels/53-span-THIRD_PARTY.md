# Source attribution and license boundaries

This package is research material intended for integration into ProveIt. It
distinguishes new experiment code and reports from the inherited machine,
proof-program data, compiler, and proof interfaces. No upstream file has been
relicensed by its inclusion here.

## Frozen sources

- ProveIt snapshot: `43026ff42f0939f09b9e95495248cfadcad38e38`.
- Jeff's `busy-beaver` snapshot, as imported by ProveIt:
  `297ab8df7e5de329605c3875b4934643b371a5e3`.
- The public 253-state reduction by mira-emmy is PR 20, head
  `0d544f2a2e3c18f12278441a74b7879f31cbe856`.

The original 254-state machine is attributed to Mira-Cult; the verification
and imported development to Jeff and the upstream contributors; the public
compiler framework to Andrew James Wade; the public 253-state reduction to
mira-emmy; and the register permutation, subsequent proof closure, and
earlier diagnostics to the ProveIt investigation.

## Applicable notices

ProveIt's license text is retained at `upstream/LICENSE`. The explicit
upstream exclusion is retained at
`upstream/lib/jeff-busy-beaver-zfc254/README.proveit.md`.
The pinned `busy-beaver` snapshot has no declared repository-wide license.
Its machine and Coq program data are **outside ProveIt's blanket MIT-0
grant**. This research package preserves that boundary and their attribution.

Andrew James Wade's `TMBuilder.py`, `tm.py`, and `tmdb.py` are separately
distributed under the retained MIT-0 `LICENSE.wade` in each `backend/`
directory. Those notices apply to those files, not to every imported source.

The new experiment drivers, report, and supporting research artifacts are
prepared for contribution under ProveIt's existing project terms. This
statement does not extend those terms to inherited material. For subsequent
redistribution, retain this notice together with the applicable inherited
notices and the source provenance.

## Scope of the input snapshot

`upstream/` is a curated collection of source inputs and reference notes. It
is not an entire repository, a Git checkout, or a complete Lean/Coq build
closure. Files in `semantics/reference/` whose role is an endpoint audit are
read-only references. The new Python/C++ controls need no network and do not
invoke a proof-assistant compiler.

Component manifests record the exact input hashes, and
`SOURCE_MANIFEST.json` maps staged files to their source identities. Package
integrity is recorded separately by `SHA256SUMS.txt`. An input SHA-256
identifies bytes; it is not a replacement for an applicable license or a
semantic proof.
