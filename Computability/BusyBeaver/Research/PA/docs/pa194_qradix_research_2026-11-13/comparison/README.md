# Comparison population and reproduction

The census is pinned to ProveIt commit
`317b07268681b44ff352d173a162e2a8c241b2fe`. It covers all 51 current
placed packet roots under `Computability/BusyBeaver/Research/PA/docs/`
and all three current incoming ZIPs under `docs/incoming/`, recursively
including their nested archives. It is a current-file audit, not the
repository's historical pre-deduplication manifest population.

## Counts and classifications

- 1,402 recognized complete numeric literal table occurrences.
- 721 byte identities and 497 spanning-root action-graph classes among them.
- 7,192 JSON files examined, yielding 85 explicit complete table occurrences
  in 73 normalized serializations.
- Four additional graph classes appear only in the JSON scan, giving 501
  combined classes. Counts include experiments, raw tables, and fixtures.
- Forty existing 194-state classes: 26 with supplied ordinary PA argument
  and physical evidence, ten auxiliary/exploratory, and four rejected.
- Fifty-four principal packet records, each with a contribution/status and
  source/proof-boundary note.

The census canonicalizes arbitrary working-state labels and forgets the
designated start by considering every spanning root, retaining read/write
and direction labels. Its class count is deliberately more fine-grained
than the final novelty check. The latter also allows global reflection,
global bit complementation, and disregards the final halting write/move.
It compares all forty representatives under that larger equivalence.

`packet_ledger.json/.csv` compare every principal delivery, including larger
designs and negative research. `frontier194.json/.csv/.tex` compare each
194-state graph class. The source paths identify duplicates even when a
packet uses a different name. In particular, the placed cached-only NS=HS
and incoming sum-guard NS are different; the JSON-only N_AD auxiliary
table supplies the fortieth graph representative.

The complete literal and JSON ledgers are in `current_census/census.json`
and `json_census/census.json`. `json_census/new_classes.json` lists the
JSON-only additions. Every 194-state representative is included under
`frontier_tables/`. The literal scanner stores encountered tables with at
most 196 states under `current_census/tables/`; larger tables remain
identified by source paths and hashes in the ledger. The full original
repository is not duplicated in this compact archive.

## Fresh scans (optional)

A fresh corpus scan requires the pinned external checkout. The literal
scanner also uses `git` and `rg` (ripgrep). With the checkout available:

```sh
python3 comparison/literal_inventory.py \
  --repo /path/to/pinned/ProveIt --output /path/to/new/literal_census
python3 comparison/json_inventory.py /path/to/pinned/ProveIt \
  --output /path/to/new/json_census
```

The optional `--output` argument on the JSON scanner is a packaging
improvement; it changes no table-recognition logic. `enrich_ledger.py`
likewise accepts explicit `--repo` and `--ledger` arguments. It applies the
reviewed contribution mapping to an existing ledger, validates exact
coverage of the placed directory set, and writes that JSON and its sibling
CSV. It is an editorial comparison assembly step, not a proof checker.

The combined count can be checked offline from the included identity lists:

```python
import json
from pathlib import Path
c = Path('comparison')
a = json.loads((c/'current_census/census.json').read_text())
b = json.loads((c/'json_census/census.json').read_text())
x = {r['graph_hash'] for r in a['identities'] if r['graph_hash']}
y = {r['graph_hash'] for r in b['identities'] if r['graph_hash']}
assert (len(x), len(y-x), len(x|y)) == (497, 4, 501)
```

The root `reproduce.py` includes this offline check. It also checks both new
tables against all frozen frontier representatives, so validating the new
constructions requires no external checkout.

## Scope limits

Recognition accepts complete numeric binary one-halt tables in the
documented text and JSON formats. It does not execute every arbitrary
generator, interpret every possible bespoke encoding, or independently
reprove all older mathematical claims. Tiny scanner fixtures, rejected
quotients, and raw compiler outputs are not consistency machines merely
because their transition tables are recognized.

`MACHINES.md`, `MACHINES.tsv`, and `PA_README.md` are attributed copies of
the pinned repository's own overview and historical deduplication record.
Their occurrence counts have a different population and must not be
subtracted from this current census. `packet_catalog.md` retains research
notes and qualifications used during comparison.
