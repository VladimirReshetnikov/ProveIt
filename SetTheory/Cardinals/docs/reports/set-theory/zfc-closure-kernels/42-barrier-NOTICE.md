# Provenance and integration notice

New report text, mathematical arguments, Python code and Lean modules are
provided for incorporation into ProveIt under the MIT No Attribution terms
in `LICENSE`.

This work reuses and credits:

- Mira-Cult's original 254-state machine and proof-search construction;
- mira-emmy's public 253-state reduction, PR 20, pinned head
  `0d544f2a2e3c18f12278441a74b7879f31cbe856`;
- jeff87654/busy-beaver's end-to-end Coq development, pinned main
  `297ab8df7e5de329605c3875b4934643b371a5e3`;
- the existing runtime252 fold and short-gap checkpoint from the prior
  ProveIt research archives;
- the framework attributed to Andrew James Wade;
- Friedman's assignment/class representation method in *Impossible Counting*;
- ProveIt's full equality-free PSC/EPSC calibration, arbitrary-start
  completeness and earlier FAK12 finite kernel.

The new 252-state result is the completed blank-bootstrap analysis and
protected-stack calibration of that previously known runtime table. The
901-bit finite theory is a separate new compiler input; it is not the logic
implemented by the 252-state table.

The original FAK12 generator and its output are retained in `provenance/`
under the applicable ProveIt license. `CantorOccurrenceOrder.lean` reproduces
the exact inspected command-code definitions and adapts the short Cantor
injectivity proof, with module-level attribution.

Selected upstream files in `machine/vendor/` retain their own authorship
and licensing status. They are not relicensed by this archive's root license.
The same applies to the unmodified selections in
`provenance/inherited_bridge/` and `provenance/earlier_enumerator/`.
See `machine/NOTICE.md` and `machine/source_manifest.json` for exact paths,
revisions, hashes and the scope of their inclusion; the two provenance
subdirectories also contain their own source manifests. No theorem-prover
binaries or unrelated prior research archives are included.
