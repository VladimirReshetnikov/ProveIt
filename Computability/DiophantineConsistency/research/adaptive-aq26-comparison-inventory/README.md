# Bounded graph comparison inventory

The scan below examines JSON files under `research/` having a top-level
`witnesses` list, `source` list of four-field binary-operation rows,
`fixed_numerals` list and `output` name. It propagates a **syntactic upper
bound** on witness degree (ports are degree zero), and reports graphs with at
most 33 witnesses, at most 164 rows and bound at most eight. It does not infer
the witness domain, fixed-port identity, exact degree, or proof provenance;
those must be checked in each graph's own record. It cannot find graphs stored
in other formats, or graphs whose loose syntactic upper bound exceeds eight.
Its observed 12 paths are preserved in [result.txt](result.txt), including the
new 26/148 natural graph and its positive parent. Re-run from
`Computability/DiophantineConsistency` using:

```
python3 -I -S -B research/adaptive-aq26-comparison-inventory/scan.py
```

The result is a dated workspace inventory, not a reproducible global
minimality certificate; new files can change it. In particular, an operation
count for a positive graph must not be compared as a natural graph without
adding or otherwise accounting for shifts. Exact degree and endpoint assertions
in the [33/164 comparison](../adaptive-named33-natural164-signed-cancel/README.md)
come from the linked candidate records, not this scanner.
