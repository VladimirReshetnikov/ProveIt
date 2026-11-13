# Selected 196-state archive machines

[catalog.py](catalog.py) identifies sixteen distinct rooted,
action-preserving transition-graph classes among selected tables in
`docs/incoming`. It checks each pinned member's full SHA-256, every transition
row, start and halt convention, and graph reachability of all 196 working
states. [catalog-receipt.json](catalog-receipt.json) records the archive
member names and canonical graph hashes. Reproduce from the repository root:

```sh
python3 -B Computability/BusyBeaver/Research/PA/pa196-vs-u208/archive-audit/catalog.py > /tmp/pa196-catalog.json
```

The selected list contains the published PA196 machine; two explicitly
experimental MP variants; the earlier alternative196; four closing-command
variants; two rotated layouts; one regrouped layout; the A/D register-swap
layout; two variants from `pa_consistency_reduction.zip`; and two explicitly
rejected layouts. A status of `candidate` means that an incoming archive
presents the table as a positive research candidate with executable checks; it
is **not** a Lean-checked iPRA consistency equivalence. `experimental` is the
archive's own caution for the MP variants. These sixteen selected tables are
not claimed to enumerate every 196-state file in every archive: research
catalogs include many exploratory tables, duplicate encodings and rejected
variants. Graph nonisomorphism alone says nothing about halting behavior.

The two rejected tables are important controls: both are 196-working-state
machines, but both **halt on blank tape**. Their complete finite traces are
Lean-checked in [rejected196](rejected196/README.md). They must not be treated
as consistency candidates merely because they occur in an incoming archive.
The check is an external standard-natural-number result, not an iPRA theorem.
