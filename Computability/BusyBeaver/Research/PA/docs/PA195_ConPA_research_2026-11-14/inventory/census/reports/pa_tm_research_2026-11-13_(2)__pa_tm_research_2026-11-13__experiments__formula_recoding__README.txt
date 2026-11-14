Source-level investigation: disequality parity and tag swapping

No verified machine with fewer than 196 states is claimed.

New mathematical construction: disequality_parity.tex.
  Preserve base-four implication, membership, and universal constructors.
  Interpret tag 3 as disequality and replace primitive equality by its
  negation. This makes every odd code refutable at the zero assignment,
  allowing parity acceptance without changing pairing multiplication or
  the modus-ponens decoder. The note gives an injective proof recoding.

Quick reproducible validation (under one second):
  python3 check_witnesses.py
This pins the inherited Program.lean and checks all ten retained grammar
witnesses by exact expansion, word equality, and grammar-node counting.
The result is retained in witness_check.json. It also passes python3 -O.

Finite experiments:
  python3 tag_swap.py
    20,000 randomized parses with U/E tags swapped; best 73 AX grammar
    nodes, 211 tokens (original: 68 nodes, 201 tokens).
  python3 disequality.py
    30,000 randomized parses of the disequality presentation; best 75 AX
    grammar nodes, 210 tokens. A baseline dictionary parse also has 75.

These scripts run from this directory, write their grammar witnesses here,
and use Python's standard library plus the copied source-scoring modules.
They do not produce or validate a sub-196-state TM. Randomized grammar
costs are upper bounds from a bounded search; physical helper allocation,
engine invariants, and startup have not been verified for these candidates.

Copied inputs and scoring scripts come from the incoming archive
pa_tm_extended_research_2026-11-13.zip, itself retaining the original
James Chang PA196 source at commit 407cdc356f6b586635e71ac92be394255f4bfea4.
The base-four source file remains byte-identical to the current pinned
ProveIt import. The new experimental scripts are tag_swap.py and
disequality.py. No upstream file was changed.
