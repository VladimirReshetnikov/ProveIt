# Shared-grammar experiment

This new experiment reorganizes all closed sequential regions of source09's
202-node decoder. It performs 11,200 trial evaluations; repeated candidate
grammars are possible. It finds no decoder with fewer nodes.

The retained source is the actual public source09 candidate, not the
original 203-node control. The exact input and two unchanged source helpers
are recorded in source_manifest.json.

## Recorded searches

Run these commands from the grammar directory; outputs are relative to it:

```sh
python3 grammar_search.py --seeds 200 --greedy --output greedy
python3 grammar_search.py --seeds 500 --exponent 8 --balance weighted --output weighted8
python3 grammar_search.py --seeds 500 --exponent 4 --balance right --output right4
python3 grammar_search.py --start 500 --seeds 5000 --exponent 8 --balance weighted --output weighted8_extended
python3 grammar_search.py --seeds 5000 --exponent 4 --balance weighted --output weighted4_extended
```

The five best tuples (decoder nodes, maximum zero-run, depth) are:

- (212, 13, 30)
- (203, 13, 31)
- (206, 8, 99)
- (203, 13, 31)
- (205, 15, 32)

The input tuple is (202, 7, 35). These are register-decoder measures,
never inferred Turing-machine state counts.

## Check the selected results

```sh
python3 verify_grammar.py
```

This regenerates the selected certificates, checks both directions using
the unchanged source09 verifier, and rejects a deliberately corrupted
initial relation entry. The boundary relation matches register increments
between decrement tests and checks both zero and positive exits. Thus the
result concerns all initial register vectors, not a bounded sample of
register executions. It does not prove any binary compiler simulation.

The final source files have their exact pinned Git-blob bytes. During the
initial downloads, one surplus final newline had been appended to these
text inputs; it was removed after checking against the original blobs.
The parsed program, selected outputs and certificate results are unchanged.
The independent review record documents that normalization and the replay.

