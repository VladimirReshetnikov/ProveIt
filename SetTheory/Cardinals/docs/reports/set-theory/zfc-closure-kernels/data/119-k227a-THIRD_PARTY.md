# Attribution and source scope

The pinned K230 checkout is reproduced under `reference/k230-rocq` at commit
`3142e4dd980f0be12f4abb636c4ae2528afc17eb`. Its original `THIRD_PARTY.md`, `LICENSES/`,
manifest and provenance are preserved unchanged. They describe inherited BusyCoq,
LibTactics, Undecidability, Wade, and custom proof-source attribution and licensing.
This package does not assign a blanket license to that checkout.

`verification/source_tools.py` is an unchanged copy of the ProveIt235 package's
`build_zfc235.py`. `verification/verify_state_fold.py` and
`verification/audit_source_graph.py` are retained from that package. The two files
under `verification/engine/` are unchanged from its retained236/237 dependency.
The original ProveIt license materials and attribution are preserved in
`reference/proveit_licenses/` and `reference/ProveIt_ATTRIBUTION.txt`.

The older machine/source inputs and source-only alternatives are attributed to
their exact pinned packages in the report and respective research notes. Counts
and proof claims from those packages are identified as inherited, rather than
as newly constructed binary machines.

New construction, verification, report, and discovery material was prepared for
incorporation into the ProveIt repository in this investigation. Upstream notices
remain attached to the corresponding reused material. Source availability and
attribution alone are not assertions of a repository-wide license.
