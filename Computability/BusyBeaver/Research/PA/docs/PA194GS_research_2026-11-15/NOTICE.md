# Attribution and proof provenance

This research response builds on Vladimir Reshetnikov's ProveIt repository and the research contributions it preserves, including the inherited James Chang and Wade machine/calculus infrastructure. The original license texts are retained under `licenses/`; this notice does not replace or broaden them.

The source snapshot for the comparison is commit `7c0bb454cf73c29ca1c385f9fec856ddd236a7cb` of <https://github.com/VladimirReshetnikov/ProveIt>.

The immediate construction and verification dependency is the pinned incoming `docs/incoming/PA194ORH_research_2026-11-15.zip` packet. Its provenance manifest is copied to `reference/ORH_PROVENANCE.json`. In particular:

- `vendor/construction/{compiler.py,symbolic_runtime.py,support.py}` are retained from its `construction/vendor/`.
- `vendor/construction/{engine_helpers.py,engine_foldscreen.py}` are retained from its `research/engine/`.
- `vendor/literal/` is retained from its `verification/vendor/`.
- `verification/check_literal.py` adapts that packet's verifier only for package paths and explanatory text; its literal symbolic rule implementation remains in the retained vendor modules.
- `vendor/relative_inspection.py` is the retained ORH finite-inspection helper; the new gate-specific driver calls its general `inspect()` routine, not its ORH-specific main function.
- `reference/inputs/` and `reference/AX11H/` contain its frozen AX11H construction data and parent execution certificates.

The ten calibration manuscripts in `reference/calibration_AX11H/` were retained from the copy embedded in the incoming AX11HC4/C32 packet. They correspond to the revised filed `pa194_ax11h_research_2026-11-14_2` calibration. Their own source manifest, claim manifest, Foundation pin and original licenses are preserved. Their historical proof-status claims remain attributed to that packet.

The new work is the gate-interface exposure and reassociation, the resulting PA194GS table and finite bindings, independent source/startup checks, the gate-specific relative proof and polynomial witness-map instantiation, the fresh literal-corpus comparison, and the documented reduction experiments. Some research engines adapt the inherited ORH annealer or history-fold helper; their local READMEs identify those dependencies.

No authorship of the inherited numerical calculus, proof-search source, compiler, list-traversal method, or absolute PA calibration is claimed. No new end-to-end Lean compilation is claimed. The source identities, literal runtime receipts, polynomial arithmetic checks, and written mathematical proof have the separate scopes stated in the main report.

Historical exploration notes preserve some original workspace paths as provenance. The main entry point `verify_all.py`, the positive builder, and the explicitly documented research replay commands use package-relative inputs. The raw 100-packet research collection is not redundantly included; the exact 550 representative tables needed for offline structural comparison are included.
