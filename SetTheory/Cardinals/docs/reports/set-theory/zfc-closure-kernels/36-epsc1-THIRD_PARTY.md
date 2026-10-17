# Attribution and third-party material

The report distinguishes new results from the existing ProveIt source
ledger at commit `2c74914bdfc98920ddcc3ff7c092cce10db4d709`.

## Included unchanged source

`reproduction/sources/proveit/` contains only the selected files needed to
reproduce the compiler controls and local-window audit. Their original
paths, exact bytes, and Git blob SHA-1 identities are retained. ProveIt's
MIT No Attribution license is included at the root of that snapshot.

The vendored `lib/jeff-busy-beaver-zfc254/` subtree retains the selected
Andrew James Wade generator files and `LICENSE.wade`, as supplied by the
ProveIt snapshot. Their upstream SHA-256 pins are checked by the inherited
recovery script. The `.v` files are parsed as finite program data; no proof
assistant execution is performed by this reproduction.

## Public253 input data

The table `reproduction/zf_audit/zfc_253.tm`, generated program
`reproduction/zf_audit/upstream/Prog254.v`, and upstream README are copied
from the pinned mira-emmy PR head. Original attribution to Mira-Cult,
mira-emmy, Jeffrey, and Andrew James Wade is preserved. Their exact URLs and
hashes appear in `PROVENANCE.json`. The root license for this report does
not replace or enlarge any upstream grant for those inputs.

## Generated controls

All generated tables inherit the attribution of their source theory,
program, and backend. The 268-state table reproduces a pre-existing
ProveIt result. The 290-state outgoing-equality table is a new measured
compiler control and is not claimed as a verified consistency machine.

## New report material

The ordinary separation proof, new diagnostic and experiment drivers,
report source, and newly written reproduction orchestration are supplied
under the MIT No Attribution terms in `LICENSE`. Upstream material remains
subject to its own notices. Bibliographic references retain attribution
to their original authors; the papers themselves are not included.
