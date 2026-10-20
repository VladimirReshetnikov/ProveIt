# Search material and its scope

The positive construction uses the fixed grammar in
`../portable/machine/grammar223.json`. Its reproduction requires no heuristic
search. The files in this directory record alternative inputs and measured
search results for future research; they are not additional proof premises.

`formula_variants.json` contains 720 exact arithmetic expressions and their
postfix emitter words: three K root forms, three conjunction-order choices,
six bundle orders and five helper choices. `formula_request_variants.json`
adds 1,440 existential-premise and contrapositive request variants. The two
native-decoding receipts check constructor side conditions across these inputs,
without claiming all were compiled into calibrated machines.

The portable generator reproduces both input files exactly. After extracting
the included K224 predecessor, run:

```sh
python3 -B research/generate_formula_variants.py \
  --emitter-contract /path/to/K224/portable/theory/emitter_contract.json \
  --output-dir /tmp/k223-formula-inputs
```

Its original output-root expression and full 71-macro word must match the pinned
K224 emitter contract before the new inputs are written. The output directory
must initially be empty. `../verification/formula_generator_replay.json`
records the exact 2,160-expression replay.

`output_grammar_search.json` and `conditional_grammar_search.json` retain 144
screened layouts each. Their metric is `[weighted_score, zero_run, depth,
distinct_subtrees]`. A weighted score does not establish a literal machine
count unless address limits, alias contexts and engine ports also verify.
`request_screen/results.json` records the six nearby request-rewrite layouts.
`open_rotation_search.json` records the independent 3,300-trial source search.

`discovery_summary.json` distinguishes console-observed search totals from
counters saved only when a better layout appeared. The former were not retained
as complete stdout logs. They are exploratory history, not independently
replayable proofs of exhaustive coverage.

`alternative_findings.md` explains the measured helper choices, calibrated K
forms, support-free obstruction and directions that remained conceptual. Its
subtree counts include primitive leaves unless explicitly qualified. For the
selected machine,209 total subtrees consist of 23 leaf kinds and 186 internal
subtrees; twelve contextual aliases reduce the decoder to 174 states.

The final report also assesses finite class theories, reflection and Ackermann
presentations. No new NBG, Ackermann or direct-reflection binary machine is
claimed in this packet. No negative search result is a state lower bound.
