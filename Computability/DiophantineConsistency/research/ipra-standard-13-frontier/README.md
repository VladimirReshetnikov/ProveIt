# Standard iPRA endpoints for the two 13-variable frontier equations

This develops standard-theory clients for the existing 13-variable degree-36,
87-operation sum-of-squares equation `../../equation36.pdf` and degree-56,
86-operation product equation `../../equation86.pdf`. Both clients state
equivalence to the selected native mapped refutation predicate and to the
selected Foundation ZFC consistency sentence under the recorded embedding and
Gödel–Gentzen translation. The two named native endpoint modules previously
used for these presentations are absent from the audited AQ29 parent.

The joint extension rebuilds the four standard-theory modules, the 87-gate
Lean literal and its native client, and two new standard clients in one
overlay. The 86-gate native statement is obtained directly from the AQ29
parent's `HAAdaptiveDirectOrdinate86.polynomialBridge`; no separately compiled
native-86 object is imported. `check_graphs.py` independently matches every
Lean input, port, operation and output against the two pinned graphs, including
three mutations for each. Its initial section-delimiter failures and the final
actual exit are in [graph-observation.json](graph-observation.json).

An exploratory single-author run rebuilt all eight additions in a fresh
AQ29-parent overlay; actual tool session 96804 exited zero. The captured
[logs](exploratory/terminal-observation.json) include five native and three
standard reports for the square-sum client, and the parent bridge plus one
native and three standard reports for the product client. Only Lean
metatheory's `propext`, `Classical.choice` and `Quot.sound` appeared; these
are not additional object-theory axioms. The complete source and object
hashes are in the [exploratory receipt](exploratory/receipt.json).

The `/tmp/ipra-standard-13-frontier-exploratory-20261101` overlay links only
to the audited historical AQ29 author project and the historical Foundation
package provider, then builds the eight additions in order. It did not guard
all inputs before and after execution. It is not a guarded or matched
extension, a current-source result, or formal PDF semantics. The parent
snapshot's source drift, package-transitive, dynamic-load, between-observation
and unobserved Foundation wrapper-exit limitations remain; the displayed
decoder and rank recipe retain the manual-transcription boundary.

`build_manifest.py --source-commit <full-commit>` freezes these eight exact
additions and the 13 requested diagnostic names for the guarded runner. A real
guarded run must use a fresh overlay, not the exploratory objects, and a
later independent artifact audit and matched peer remain separate work.

The source-frozen manifest pins commit `72bb86f99414925806059a74f0bf77be7d1c5fc5`
and has SHA-256 `2a4749c34750dbff650e19b5e5fc7effd98a64774c4051852f3db39221b2f134`.
The guarded runner's source policy accepted all eight additions and 13
diagnostics; the actual validation exit is recorded in
`manifest-observation.json`. The manifest alone is not a guarded replay.
