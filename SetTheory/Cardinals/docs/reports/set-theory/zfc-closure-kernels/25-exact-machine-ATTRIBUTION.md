# Source attribution and license boundaries

The principal input repository is Vladimir Reshetnikov's
[ProveIt](https://github.com/VladimirReshetnikov/ProveIt), inspected at commit
`de047657e193ec605e930eaf149a44a38031820b`. All files under `vendor/ProveIt/`
are unchanged copies selected from that commit, with individual paths and
SHA-256 digests in `SOURCE_MANIFEST.json`.

The Python TM generator is Andrew James Wade's 2025 implementation, under
the MIT No Attribution license retained as `LICENSE.wade` and at its original
vendored location. ProveIt's own license is retained as `LICENSE.ProveIt`
and `vendor/ProveIt/LICENSE`.

The original 254-state machine is Mira-Cult's design; Jeff's
`jeff87654/busy-beaver` project supplies the referenced verification lineage.
The 253-state literal machine is mira-emmy's reduction, from
[upstream PR 20](https://github.com/jeff87654/busy-beaver/pull/20), head
`0d544f2a2e3c18f12278441a74b7879f31cbe856`. The baseline table is included
byte for byte. This package does not claim authorship of either machine and
does not relicense the tables, upstream proofs, or other upstream material.
Its finite bootstrap replay is separate from those attributed full proofs.

The closed-word Re-Pair compressor and independent operation checker are
retained prior work from the repository's source-08/source-14 research
packages. The EPSC frontend and macro-return analysis are also retained
source-14 work. The corresponding original source headers are preserved.

`lab/context_search.py` and `lab/analyze_table.py` are unchanged support
modules from the source-04 engineering package. `lab/fuse_states.py` extends
that method to symbol-wise selection of the merged rows and records the
bounded checker's first-failure reasons. `measure_fixedpoint.py` constructs
and measures the report's EFPC normal forms using the retained grammar,
frontend and compiler. `reproduce.py` adds the offline packaging/replay driver.

The 270-state EPSC table is a byte-identical reproduction of the prior
source-14 control, not a new state reduction. The 271-state EFPC table and
its measured exact recipe are new experimental outputs for the mathematical
normal form; their limitations are described in the report and README.

No blanket license asserted for this supplement supersedes third-party
rights or notices. New report-specific code and results are supplied to the
requesting user for inspection, reproduction, and continued development.
