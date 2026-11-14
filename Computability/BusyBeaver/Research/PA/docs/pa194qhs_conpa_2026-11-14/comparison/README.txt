PINNED CORPUS COMPARISON

Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: 2337ce611a26e308697ccbddb2a1636f989f01c3

The authoritative census is census_full/, not an earlier snapshot.
It covers all complete numeric five-column binary tables in .tm/.txt/
.csv/.tsv files under PA and recursively nested ZIPs, plus the five incoming
archives. Sources and JSON-only encodings are outside the literal parser;
the packet narrative comparison is broader. Repeated archive bodies are
expanded once while their container occurrences are retained.

Important files:
  packet_ledger.csv          All 61 filed + 5 incoming deliveries.
  frontier_review.csv        All 193/194 graph classes and status sources.
  frontier_tables/           Exact representatives, including rejected ones.
  census_full/tables.json    Every recognized byte form and its locators.
  census_full/occurrences.json
                            Every recognized table occurrence.
  review_summary.json       Definitive counts and status attributions.
  qhs_novelty.json           Fresh no-match result against 634 byte forms.
  qhs_source_proof.txt       Independent universal block-preservation proof.
  qhs_source_certificate.json
                            Exact finite binding of that proof to the sources.

To rerun candidate novelty from the release root:

  python3 -B comparison/compare_candidate.py machine/machine.tm

To independently check the exact source replacement:

  python3 -B comparison/check_qhs_source.py \
    construction/inputs/parent_QH.instructions.json \
    machine/instructions.json

To regenerate the full census against an actual checkout of the pinned
revision (replace /absolute/path/ProveIt with that checkout):

  python3 -B comparison/audit_inventory.py \
    --repo /absolute/path/ProveIt \
    --incoming /absolute/path/ProveIt/docs/incoming \
    --out fresh_census

Canonicalization on spanning graphs ignores the chosen root for duplicate
detection, then separately tests global reflection and bit interchange.
Machine claims still retain their specified blank initial states.
The graph key for nonspanning fixtures is only a maximal reachable rooted
component, not a general graph-isomorphism certificate; such fixtures are
excluded from the complete 76-class 194-state frontier.

Proof-status classifications attribute what the packets actually supply.
Fresh structural comparison does not mean every historical PA proof or
Lean project was rebuilt. No rejected or auxiliary table is silently
promoted to an accepted consistency construction.
