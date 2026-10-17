# Attribution and provenance

This package was prepared for the requested incorporation into ProveIt.
New report text, mathematical constructions, diagnostic scripts, and
search extensions are distinguished from the selected existing inputs.
No authorship of the public253/public254 machines is claimed.

## Existing machine and compiler inputs

- Mira-Cult: original attributed 254-state construction.
- Jeff (`jeff87654`): busy-beaver repository and formal verification.
- mira-emmy: the public 253-state reduction, generator, and proof.
- Andrew James Wade: register-program/Turing-machine compiler framework.
- Vladimir Reshetnikov / ProveIt and the attributed source-04 report:
  retained machine literals, prior-search notes, and affine-checker adapter.

Exact upstream pins:

| Material | Commit |
|---|---|
| Jeff 254 proof/table snapshot | `c132d7eae8158cd3a9850ea3eb7251158c3dd821` |
| mira-emmy public253 | `0d544f2a2e3c18f12278441a74b7879f31cbe856` |
| ProveIt comparison snapshot | `2c74914bdfc98920ddcc3ff7c092cce10db4d709` |

`machine/provenance.json` records per-input paths and hashes.
`provenance/foundation_source.json` identifies the exact separately
retrieved `Z_main.v` bridge. Selected proof excerpts are for the report
and finite comparisons; they are not a complete Coq or Lean installation.
Existing source notices and applicable upstream licenses retain their
force. This package does not relicense those inputs.

## Existing mathematical calibration

The unrestricted PSC/EPSC calibration, hereditary saturation, two-parameter
EPSC result, exact-hull equivalence, and outgoing-profile observations
predate this report in the pinned ProveIt corpus. The two calibration
accounts retained in `provenance/` are attributed existing documents;
their relative repository links refer to the source repository.

The new mathematical contribution is the unary finite repair and direct
EPSC transfer, together with the normalized support counterstructure and
full support-deletion obstruction. Relevant historical literature is
cited in the report. Novelty is stated relative to the inspected corpus,
without asserting historical priority over all unpublished or published work.
