REPRODUCING THE EXECUTABLE EVIDENCE
=================================
From the extracted package root:

    python3 tests/verify.py

This needs only the standard Python library and no network or repository
checkout. Exact published source metrics use CPython 3.12.14; other versions
can change ast.unparse results. The script regenerates evidence/metrics.json
and evidence/verification.json. It checks all supplied complete programs in
ordinary Python and python -O, with the same acceptance criterion: exit 0 and
exactly ACCEPT followed by one line feed.

Examples:

    python3 code/checker_tokens.py < tests/fixtures/stream/uniform/tokens__global_guarded_induction_with_used_hypothesis.jsonl
    python3 code/checker_ast.py < tests/fixtures/stream/uniform/ast__global_compound_implication_elimination.jsonl
    python3 code/checker_bytes.py < tests/fixtures/bytes/uniform/direct_zero_seed.json

translate.py is an untrusted proof producer. It instruments the old global
stream or local array control and inserts the new terminal packets. It checks
the fixed-point invariant for every replayed source entry; it does not claim
to translate arbitrary noncanonical accepted raw aliases.

    python3 tests/translate.py tokens < tests/fixtures/stream/control/global_computation_zero.jsonl
    python3 tests/translate.py ast < tests/fixtures/stream/control/global_compound_implication_elimination.jsonl
    python3 tests/translate.py bytes < tests/fixtures/bytes/control/direct_zero_seed.json

No measured proof checker imports translate.py, verify.py, an evidence file,
or any other project module. The three optimized profiles have different
certificate protocols: do not interchange their general input files.
