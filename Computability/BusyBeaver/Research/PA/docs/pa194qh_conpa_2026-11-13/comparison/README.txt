COMPARISON AND NOVELTY

The corpus is pinned in PROVENANCE.json. packet_ledger.csv covers all56 deliveries; frontier194_annotated.csv describes all42 prior194-state classes. Table_classes.json summarizes all505 current table groups (502 spanning one-halt graphs plus3 diagnostic controls). These are counts of recognized literal tables, not counts of proved consistency machines.

Replay the exact novelty check, from the package root:
  python3 -B comparison/verify_novelty.py machine/machine.tm

Expected:42 pairwise distinct prior graph classes; candidate194 working states and no prior match. The comparison allows every spanning root, state renaming, reflection, global bit interchange, and arbitrary halt-edge actions. Equality is decided on full canonical tuples.

Positive duplicate control:
  python3 -B comparison/verify_novelty.py comparison/reference_tables/PA194Q.tm

Expected: matches PA194Q, structurally_new=false. pa194qc_novelty.json records the actual rejected QC attempt with exactly those same bytes.

To rescan the complete pinned repository, use its PA subtree and current incoming ZIPs:
  python3 -B comparison/audit_corpus.py --repo /path/to/pinned/ProveIt --incoming /path/to/pinned/ProveIt/docs/incoming --out /new/census

This larger replay requires the source repository; the candidate/frontier novelty check above is entirely offline and self-contained. The full table occurrence inventory is reproducible by that scan rather than duplicated here. Old delivered occurrence counts differ because the repository removed duplicate tables when filing packets. Some comparison graph fixtures use dense labels without preserving start zero; the unrooted census prevents counting them as new machines. Definitive machine starts are fixed separately.
