# Joint equality/DNE and source-order research

These experiments concern alternative AX source words. They are separate from the successful QT244 loop rotation and supply no independent smaller machine claim.

The source generators compose inherited native-equality orientations, complete-row permutations, single-read rho8 role permutations, and contextual double-negation transfer. Their actual emitted stack and input-read contracts are checked symbolically.

From this directory:

```bash
python3 -B generate_combined.py \
  --equality-source reference/converse_source.json \
  --dne-checker reference/check_dne_variants.py \
  --output /tmp/joint-source-variants.json
python3 -B generate_orders.py \
  --dne-checker reference/check_dne_variants.py \
  --output /tmp/row-order-variants.json
python3 -B generate_rho8.py \
  --dne-checker reference/check_dne_variants.py \
  --output /tmp/rho8-variants.json
```

The three families contain 2,048, 107, and 36 exact source words, respectively. The full emitted records are retained. The 96 joint equality/DNE seed inputs are under `seeds/`. Only the 32 mask-32 representatives received the recorded bounded searches: their outputs, independent audits, commands, and logs are under `search32/`. Their 14,867,173 proposals retained 128 rules for the inherited control and at least 129 for the changed sources. This is a search outcome, not a lower bound.

Historical command lines in JSON logs include their original workspace paths; those are evidence, not required replay locations. To run a fresh bounded search with the included portable fine backend:

```bash
c++ -O3 -std=c++17 anneal_fine.cpp -o /tmp/joint-anneal
python3 -B search_seeds.py --seeds seeds --fine ../grammar/fine \
  --executable /tmp/joint-anneal --output /tmp/joint-search \
  --seconds 30 --jobs 4 --dne-mask 32
```

The search path depends on elapsed time and compiler speed. Every output is independently audited, and the retained dictionaries are reproducible witnesses without rediscovery. Grammar role counts with the fixed 117-role framework are charged estimates; each changed source would still need its own exact binary runtime and logical initialization checks before becoming a consistency-machine result.

`reference/converse_encodings.tex` and `reference/dne_calculus_transfer.md` preserve the inherited transfer arguments. Original source and licensing provenance is recorded in the enclosing packet. No optional heuristic search is needed to verify the primary 244-state machine.
