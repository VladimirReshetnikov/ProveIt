# Scope and reproduction of the comparison

`full_census.json` is the preserved initial-snapshot census, pinned to ProveIt
commit `32d0d8b7d93a63ad4106c18cdb29b37927acdad2`. It covers literal and
explicit JSON tables under the PA tree and recursively inside the incoming archives at that snapshot. The recognizers do not execute arbitrary generators or
extract tables printed only in TeX. The 82-packet narrative also reviewed
the packet README documentation; a graph count is not a consistency theorem.

The fresh census verifies 12,551 tracked Git inputs and records 15,172
direct/archive payloads, 3,606 table occurrences, 778 normalized labeled
tables and 658 complete spanning one-halt graph classes. Of these classes,
94 have 194 states and 53 have 193 states. Six nonspanning normalized tables
and 50 incidental one-state JSON fragments are recorded separately. No
source or parse errors were reported. Consult the report for the different
conventions used by the repository's older 662-class index.

`representatives/` freezes all **279 classes at 193 through 196 states**:
53 + 94 + 27 + 105. Other state counts are represented by their full source
locators, identities and hashes in the census, not by a frozen table here.
In particular, every one of the 94 prior 194-state graphs used in the novelty
test is present locally.

The packet annotations and graph annotations are in `packet_ledger.*` and
`frontier194_annotated.*`. Their evidence categories are attributed to the
historical packets. They do not certify the packets' mathematical claims.
`new_machines_novelty.json` preserves the initial broad comparison of the
four original-primary LC graphs and GAX11 against these 94 references.
The final snapshot adds 16 prior graphs; GAX11 now matches AX11G.
`../late_snapshot/novelty.json` supersedes that initial novelty result and
checks the five actually new LC graphs, including LC_AX11H, against all 110.
The final census, archive identities and addendum are in `../late_snapshot/`.

From the archive root, graph checks need only Python:

```sh
python3 -B late_snapshot/check_novelty.py --out /tmp/pa194-novelty.json
python3 comparison/check_control_quotients.py \
  --corpus comparison/full_census.json --out /tmp/control-quotients.json
```

To regenerate the full Git-blob census, provide a repository containing the
pinned objects (including the incoming ZIP blobs):

```sh
python3 comparison/census_tool/audit_repository.py \
  --repo /path/to/ProveIt --output /tmp/pa-census
```

The census tool does not rely on a worktree file's presence. Its SHA-1
checks bind the bytes returned by `git cat-file` to the pinned Git objects.
Its output representatives are deliberately limited to state counts
193–196, as above. Licenses and recognizer attribution are preserved under
`census_tool/`.
