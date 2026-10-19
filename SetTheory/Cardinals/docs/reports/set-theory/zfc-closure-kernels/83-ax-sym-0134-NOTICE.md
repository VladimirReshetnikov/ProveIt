# Attribution and scope

The two search scripts and their recorded full runs were produced in this
research session for Vladimir Reshetnikov's ProveIt project. Their portable
copies change only input/import/output paths. The full-run JSON files are
preserved unchanged. Pins and adaptation descriptions are in `pins.json`.

The source DAG and physical dictionary fixtures come from the supplied
ProveIt research archives. Mira-Cult designed the compact calculus and
original 254-state machine; Jeff Ketchersid supplied the verification and
symbolic machinery; Andrew James Wade supplied the compiler framework.
The public 253-state reduction is credited to mira-emmy. ProveIt's physical
register permutation, prefix reductions, source reconstructions, and prior
grammar investigations retain their respective earlier attribution.

The original specification `spec.py` is retained unchanged. The minimal
`theory_backend_experiment.py` dependency retains only the two required pure
functions, with their original bodies unchanged. No original authorship is
claimed for these imported definitions, fixtures, or methods. The optional
detector synthesis script is an unchanged prior research tool with a new
recorded invocation.

This auxiliary package does not relicense upstream material or broaden any
existing license grant. The source origins are retained so the applicable
ProveIt and upstream notices can be resolved in the containing repository.
No complete historical package is represented as being included here.

The searches did not improve the existing source/dictionary baseline. Their
outputs are syntactic cost records, not newly verified binary Turing-machine
candidates. No new state bound, state minimality result, unconditional
nonhalting result, or PA/Lean endpoint is asserted by this package.
