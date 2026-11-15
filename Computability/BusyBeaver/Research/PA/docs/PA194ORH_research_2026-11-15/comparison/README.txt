Current PA machine comparison
=============================

Source pin: VladimirReshetnikov/ProveIt
43d9041f5571936c45c583f7f9d7f6eed9e0fd84.

Read comparison_findings.txt and comparison_summary.json first.

Deliverable data:
  packet_ledger97.csv/json       All 93 filed and four incoming deliveries.
  named_designs83.csv/json       Principal/supplementary named constructions.
  family_comparison29.csv        Main mechanism families and proof obligations.
  frontier194_annotated.csv/json All 520 spanning graphs plus two diagnostics.
  current_census/summary.json    Exact scan counts and recognizer rejections.
  current_census/occurrences.json, identities.json, frontier.json
                                Source provenance and exact class crosswalks.
  current_census/representatives 576 complete literal tables: 520 spanning 194-state classes,
                                two disconnected 194-state diagnostics, and
                                54 rejected/unproved 193-state candidates.
  current_census/rejected_diagnostics.json
                                Explanation of every rejected .tm fragment.

The graph counts include uncertified research inputs. They are not counts
of independently proved PA consistency machines. Every semantic/proof-status
description is attributed to its supplied packet. No Lean endpoint or new
mathematical calibration is proved by these comparison scripts.

Reproduce the structural census using a checkout of the pinned revision:

  python3 -B census.py REPO/Computability/BusyBeaver/Research/PA \
      REPO/docs/incoming --output current_census
  python3 -B assemble_comparison.py

The corpus scanner recognizes numeric complete one-halt binary L/R tables
and explicit JSON schemas, recursively through distinct nested archives.
It does not execute arbitrary generators or parse TeX-only tables, JSONL,
or opaque binary representations. See census.py and comparison_findings.txt.

Compare an additional literal candidate:

  python3 -B check_novelty.py /path/to/candidate.tm --output novelty.json

Use --recompute to independently regenerate every frozen canonical form;
the default verifies representative content identities and uses the freshly
computed signatures from this census. Signature equalities are confirmed
by exact canonical tuples. Structural novelty is independent of correctness.

Data assembly is portable. prior_classes139.json, prior_named74.json and
prior_families26.csv are attributed mechanism metadata copied from the
latest supplied loop-return packet; current literal identities were
recomputed. incoming_physical_corpus_meta.json is supplied provenance for
uncertified syntactic compositions and closed-macro inputs. The 93-filed
packet ledger was parsed from the pinned current PA docs README. Current
incoming filenames and dense table hashes were checked against the exact
four source archive bytes. No table files in the source checkout were changed.

SCANNER_ATTRIBUTION.txt identifies the reused explicit-table scanner source.
primary_positive_control.json records a meaningful positive check of the
comparison procedure. incoming_census/ and its log are an intermediate
partial scan and are not needed to reproduce the final full census.

New result and relative proof
-----------------------------
PA194ORH_novelty.json and PA194ORH_novelty_portable.json record the new
PA194ORH table's absence from all 520 supplied spanning 194-state classes.
The two disconnected diagnostics cannot be graph-isomorphic to its spanning
graph. These counts concern the supplied corpus, before adding PA194ORH.

From the delivery root, the portable checks are:

  python3 -B comparison/check_novelty.py machines/PA194ORH/machine.tm
  python3 -B proof/relative_ORH_check.py

The relative proof is proof/relative_ORH.tex. Its inspector includes explicit
polynomial witness clocks. The revised parent calibration is retained exactly
in reference/calibration_AX11H.zip, with separate provenance and licenses.
calibration_review.txt records the independent written-proof audit. The
Foundation, source binding, literal, and source-integrity rerun receipts are
in this directory and its two *_rerun subdirectories.

family_comparison29.tex is a compact three-column longtable for the report.
It requires longtable and booktabs and defines no custom macros. The CSV has
the complete design-name and physical-change columns.

Portability
-----------
Source locators are repository-relative where possible. In inherited metadata,
provider-local: marks a path reported by an earlier packet; it is provenance,
not a required local input. No comparison script requires those old paths.
The census producer changes only locator formatting from the attributed
scanner; parsing and graph canonicalization are unchanged. The full source
checkout and original incoming ZIPs are needed to recreate the source census.
The delivered representative tables suffice to rerun candidate novelty checks
without a network connection or that checkout.
