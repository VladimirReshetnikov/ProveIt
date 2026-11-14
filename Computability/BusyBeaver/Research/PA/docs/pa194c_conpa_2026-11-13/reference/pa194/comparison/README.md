# Pinned comparison corpus

The comparison is frozen at ProveIt commit `5ed5a41fa5932433111eea096311364c6087e8e3`.

- `source_archives.json` lists every one of the 32 top-level incoming archives, with its exact byte length and SHA-256.
- `census.json` contains the complete recognized table inventory, including nested archive references and all native/dense aliases.
- `existing195_classes.json` identifies the nine existing 195-state graph classes: three positive manuscript constructions and six rejected or diagnostic constructions.
- `existing195/` contains all 14 literal byte forms for these classes, including rejected negative controls. Their inclusion is not a claim of correctness.
- `comparison_notes.md` summarizes each archive, the three positive 195-state families, earlier reductions, rejected diagnostics, prior search coverage, and the formalization boundary.

The fresh census read all 32 top-level ZIPs and recursed through 45 distinct ZIP bodies (73 references, maximum depth 8). It recognized 2,360 complete numeric binary single-halt table occurrences and 582 byte forms. The 195-state part contains 37 occurrences, 14 byte forms and nine graph classes. No 194-state table occurs in this recognized corpus.

The classifier preserves read labels, write bits, L/R movement, and the halt control. It considers every possible root reaching the complete working graph. Among all recognized tables there are 421 such root-free graph classes, with two disconnected synthetic controls left unclassified. These are not 421 established consistency machines: the corpus includes ancestors, experiments, and rejected controls.

## Reproduction

With a checkout at the exact pinned commit and the direct PA `.tm` files present, run:

```sh
python3 -B comparison/census.py --repo /path/to/ProveIt --output /tmp/pa-census
```

The script reads incoming archives through Git, so the ZIPs need not be expanded or present in a sparse working tree. It does not modify the repository. It recognizes complete numeric `.tm` and `.txt` tables with one undefined halt destination. Arbitrary code/JSON-embedded tables and a four-state no-halt synthetic control are outside this census format. Distinct ZIP bodies are traversed once; the member counts therefore do not count repeated nested payloads repeatedly.

The bounded searches summarized in the report are not lower bounds on possible machine sizes.
