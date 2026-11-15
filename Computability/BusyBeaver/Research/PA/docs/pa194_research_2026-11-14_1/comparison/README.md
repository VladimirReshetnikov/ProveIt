# Complete current PA comparison

Pinned source: `e6a84f8dd2702f5f8c7db3ca53a8cbacb1d89f4f` of VladimirReshetnikov/ProveIt.

- `packet_ledger98.csv/json`: all 93 integrated packets and five current incoming archives.
- `named_designs85.csv/json`:85 distinct named 194-state tables, with attributed mechanisms, status, exact original identities and current packaged representatives.
- `frontier194.csv/json`:522 spanning 194-state action-graph classes, including unnamed research inputs; these are not 522 consistency theorems.
- `tables/`: one literal representative per spanning class plus the two nonspanning 194-control encodings (524 files).
- `summary.json`, `fresh_census.log`: the fresh pinned text/explicit-JSON/recursive-ZIP census; all 139 historical 194-state classes recovered, no parse errors.
- `comparison_notes.md`, `inherited_families26.json`: mechanisms, aliases, negative results and proof boundaries.
- `PROVENANCE.json`: source identities and attribution.

Run the exact offline novelty comparison from the package root:

```sh
python3 -B comparison/check_novelty.py machines/PA194GD_SF/machine.tm machines/PA194GDH_SF/machine.tm machines/PA194GDHS_SF/machine.tm --output comparison/new_machines_novelty.json
```

The test allows state renaming, any spanning root, tape reflection, global symbol exchange and erased terminal-entry action decorations. It compares exact integer-profile or full canonical-tuple witnesses, not just hash digests. Symbol exchange is a structural novelty screen; it does not preserve zero-blank semantics.

To reconstruct the source enumeration using the pinned Git objects:

```sh
python3 -B comparison/census_tools/current_frontier.py /path/to/ProveIt e6a84f8dd2702f5f8c7db3ca53a8cbacb1d89f4f
```

This writes a fresh `comparison/census_tools/frontier/` directory. The recognizers do not execute arbitrary generators or recover tables printed only in prose. The full 19-MB scratch census object is omitted from the delivery; all current 194 representatives, their occurrences and the census code remain available. The original licenses are retained in the package's `licenses/` directory.
