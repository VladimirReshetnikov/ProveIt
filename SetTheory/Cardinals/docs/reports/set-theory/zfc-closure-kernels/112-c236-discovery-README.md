# Discovery records and their limits

The proof of the236-state machine is in the enclosing report and verification
directory. These files preserve how candidates were found and rejected.
Finite profiles are underapproximations and are never promoted to universal
facts without a separate proof.

## Positive discovery

`positive236/` is a complete, curated replay of the successful no-helper
fold on the source-rotated237 table. Its README gives exact commands,
profile scope, pins and original attribution. Its `further235_scope.json`
records the bounded negative follow-up on the new236 machine.

## Rejected syntactic236 tables

`negative236/` contains four distinct tables and their source lists, with
complete counterexample configurations in `counterexamples.json`.
All four fail a generic source-runtime frame. These are not blank-run
claims and are not proofs that every conceivable calibration fails.
Source leaf indices are zero based.

## Source-only search

`source_search/` retains the source structures, exact control-signature
reassociation engine, stochastic search code, both completed logs and
selected receipts. The million-iteration run allowed temporary225-node
sources; a150,000-iteration run allowed226. Neither found223 source nodes.
The successful machine instead preserves224 source nodes and uses the
resulting decoder row in a contextual fold. Source-search outputs labeled
SOURCE_ONLY are not machine correctness certificates.

The transfer and jump-recalibration receipts describe further semantic
rewrite families. Their universal conditions are in
`../formalisms/source_rewrite_lemmas.tex`. They are not used in the236 machine.
The unfinished semantic decoder compiler was deliberately omitted.

## Head-offset and transient-bit maps

`offset_and_tag/` retains the pinned original237 input, finite radius-five
profile, neutral helper domain, seven C++ searches and their exact logs.
The map families are same-tape head shifts by two cells; shifts of both
merged states; a flipped predecessor bit; and combined flips/shifts.
Three searches also allow one individually neutral helper-row change.
All yielded empty candidate output in the recorded finite scope.

For example, from that directory:

```sh
c++ -O3 -std=c++17 offset_domains.cpp -o offset_domains
./offset_domains input237.tm profile237.txt 5 65
c++ -O3 -std=c++17 offset_helpers.cpp -o offset_helpers
./offset_helpers input237.tm profile237.txt neutral237.txt 5 65
```

The analogous `tag_domains`, `double_offset_domains`, and
`offset_tag_domains` programs use the first form. The `tag_helpers` and
`offset_tag_helpers` programs use the second. The data paths and finite
window/fuel arguments must be supplied explicitly. These exploratory
programs assume the pinned input conventions; they are not general-purpose
proof checkers. Empty output means that this finite candidate generator
found nothing, not that a state bound has been proved.

The exploratory C++ code adapts the inherited finite-context discovery
approach. The enclosing license and source-attribution notices apply.
