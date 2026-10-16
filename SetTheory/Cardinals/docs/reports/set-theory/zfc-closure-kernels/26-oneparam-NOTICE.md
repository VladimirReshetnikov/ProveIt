# Attribution and source boundaries

This is a research contribution prepared for Vladimir Reshetnikov and the ProveIt project with ChatGPT. The new mathematical arguments, diagnostic programs, and manuscript remain reviewable research, with their verification status stated in the report.

## Prior work used

- **Mira-Cult** designed the original 254-state machine, its logical architecture, and the nonextensional consistency theory.
- **Jeff and the busy-beaver contributors** supplied the upstream verification and supporting source development.
- **mira-emmy** supplied the public 253-state reduction and table-specific verification in upstream PR20. The present work does not claim this reduction as new.
- **Andrew James Wade** supplied the compiler framework. Its original MIT-0 license is retained at `research/baseline/busy-beaver/ZF/generator/LICENSE.wade`.
- **Vladimir Reshetnikov and ProveIt contributors, including the attributed incoming manuscripts**, supplied the prior EPSC/PSC calibration, hereditary-saturation argument, two-parameter consistency proof, finite-sort obstruction, and engineering controls. The report specifies which results are inherited and which reductions are new relative to the inspected snapshot.
- **The Coq Library of Undecidability Proofs and busycoq contributors** supplied vendored proof and machine semantics used in the source audit. Their original license files are retained in the selected upstream audit tree.
- **Ralf Schindler and Philipp Schlicht**, **Azriel Levy**, **Harvey Friedman**, and **Adam Yedidia and Scott Aaronson** are cited for relevant primary-source background. Their papers are referenced, not republished in this archive.

## Borrowed files

`sources/ProveIt/` contains selected exact bytes from the pinned ProveIt commit. `provenance/proveit_sources.json` records their original paths, URLs, Git blob identities, and SHA-256 hashes.

`research/baseline/busy-beaver/` contains selected literal machine, generator, design, and proof-source files used for the baseline audit. The 16-file replay manifest identifies all inputs needed for the new machine experiments. `research/baseline/helpers/` retains the attributed ProveIt parsing/affine-case scaffolding.

`research/bridge/upstream/` is a twelve-source audit snapshot, with original vendor licenses and a source note. Exact source identities and their roles are in `bridge_contract.json`. This selection is not a full Rocq build closure and should not be represented as one.

The borrowed files retain their existing authorship and license conditions. No blanket relicensing of ProveIt, Jeff's Rocq sources, busycoq, or other vendored code is intended. A vendor license applies to its original scope; it is not extended to unrelated files by being present in the archive. Apply the destination repository's contribution policy to the new report and new code.

## What is not asserted

This archive contains no newly certified sub-253-state complete machine, no proof of global machine minimality, no Lean/Rocq build reproduced during this work, and no serialized arithmetic certificate for the final internal machine equivalence. These limits are part of the scientific result, rather than exceptions to the reported evidence.
