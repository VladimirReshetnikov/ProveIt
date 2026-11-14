# Scope and reproduction of the current census

Use the ProveIt checkout at commit
`2337ce611a26e308697ccbddb2a1636f989f01c3`, including all files under the PA
research tree and the five ZIPs listed in `packet_ledger66.json` as incoming.
The source scanner was adapted from the supplied reduction-study archive;
its exact provenance is recorded in the package-level `PROVENANCE.json`.

```sh
python3 -B comparison/audit_inventory.py /path/to/ProveIt /tmp/pa-census \
    --incoming /path/to/ProveIt/docs/incoming
```

The script scans `.tm`, `.txt`, `.tsv`, `.csv`, and complete textual or
five-column-array tables inside JSON, and recursively traverses distinct
ZIP payloads. It records all recognized locations and byte digests. It does
not reconstruct tables encoded only in arbitrary transition dictionaries,
program code, prose, or unmaterialized parameterized generators.

The broad recognizer also finds diagnostic fragments whose rows happen to
match the syntax. Counts of spanning one-halt graphs are separated from
the broader fingerprint count. In a disconnected graph, a maximal-root
fingerprint is not a canonical encoding of every disconnected component;
such objects are not included in the claimed count of complete spanning
graphs. The one disconnected 194-state fixture cannot be isomorphic to the
connected candidate under any state renaming.

Historical evidence categories in `frontier194_all.json` and contribution
summaries in `packet_ledger66.json` are attributed to the original packets.
The current audit structurally rechecked every official catalogue table;
it did not rebuild all historical consistency proofs.

For a standalone novelty replay, the checkout is unnecessary:

```sh
python3 -B comparison/check_novelty.py
```

This checks the hashes of all 77 included frontier representatives and
compares exact full tuples, including all graph-spanning roots and the
listed cosmetic transformations. It does not rely on hash equality as a
substitute for graph comparison. The candidate's self-match is a positive
control. Graph novelty does not imply semantic inequivalence, historical
priority outside this corpus, or a lower bound on possible state counts.
