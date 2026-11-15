COMPARISON AND FINITE-TABLE NOVELTY
===================================

Pinned ProveIt commit:
883da8d55452ea097910ed2509a1eefc833ce292

This folder compares the two requested source trees: the PA research tree
and docs/incoming. It contains the complete prior named-design and packet
ledgers, exact graph representatives needed for offline novelty checking,
and a manifest binding the directly read source files to Git object IDs.

PRIOR CORPUS
------------
106 delivered packets: 100 filed packets and six current incoming ZIPs.
104 distinct named 194-state designs in 35 explanatory mechanism groups.
All 91 byte payloads in the inherited named roster were recovered exactly;
the six incoming packets add thirteen distinct principal/supplementary tables.
Mechanism descriptions and prior mathematical claims remain attributed to
their source packets. A named-design count is not a count of completed
formal proofs of consistency equivalence.

Fresh recognized-table audit: 7,907 occurrences, 1,413 distinct byte payloads,
1,193 whole action-graph classes across all sizes; 61 classes at 193 controls,
550 at 194 controls (548 spanning, two disconnected diagnostics), 31 at 195,
and 106 at 196. The corpus includes rejected experiments and auxiliaries.
State counts count all working controls, excluding terminal labels.

All 1,178 selected direct Git blobs were verified against their pinned Git
SHA-1 identities; SHA-256 byte identities are also included. The 75 archive
references include repetitions at distinct containment paths. The recognized
tables include every tracked .tm file in the two trees and complete numeric
five-column text tables encountered inside recursively nested ZIPs. The
fresh incoming JSON supplement examined all six ZIPs and their nine distinct
ZIP payloads: 1,379 JSON occurrences, 1,066 distinct JSONs, and no additional
complete 193/194-control table in the documented explicit matrix/record
schemas. It is not a fresh audit of all standalone JSON files, arbitrary
generators, Lean declarations, TeX-only descriptions, or opaque encodings.

STARTS AND DISCONNECTED GRAPHS
-----------------------------
Graph identity here deliberately forgets the initial control. It preserves
read symbols, writes, moves and terminal-entry actions. A full rooted graph
traversal over every working control yields an exact renaming invariant.
For a graph without a spanning root, maximum-component hashes are insufficient;
the audit partitions those buckets by full-bijection isomorphism after color
refinement. The two disconnected 194-control diagnostics are kept separate.
Explicit start comments and the dense-zero convention are distinct metadata.
Dense numbering is not authoritative for native tables, notably some HAZ copies.

THE TWO NEW TABLES
------------------
PA194OM and PA194OMF are bundled under new_machines only for self-contained
comparison. They are NOT included in any prior-corpus count. The main report
and main machine folder own their construction and semantic proof evidence.
new_designs.json binds the copies to their SHA-256 identities.

OFFLINE CHECK
-------------
With Python 3.10+ and its standard library, run from this folder:

    python3 -B verify_novelty.py

Or supply the main deliverable's two files, from its top-level directory:

    python3 -B comparison/verify_novelty.py PATH_TO_OM.tm PATH_TO_OMF.tm

The checker verifies all 550 representative file digests; checks state and
transition counts; recomputes graph signatures; compares each new table
against every prior class after forgetting starts, permitting global L/R
reflection and global read/write bit exchange, and erasing writes/moves
on terminal-entry transitions. It also compares the new pair, checks a
renamed positive control, and confirms the two nonspanning diagnostics
are not isomorphic. Symbol exchange is an enlarged structural test, not
a claim about computation from an all-zero initial tape.

No network, Git client, proof assistant or arbitrary repository code is
invoked by this check. It writes a JSON receipt only if --output is supplied.
Finite structural novelty establishes neither halting equivalence nor the
inherited arithmetic calibration. See the main report for those arguments.

INDEX
-----
packet_ledger.csv/json       all 106 prior deliveries with attributed claims
named_designs.csv/json       all 104 named constructions and byte/class binding
families.json/tex            the 35-group explanatory comparison
named_designs.tex            detailed LaTeX appendix for all 104 prior designs
comparison_text.tex         concise narrative and scope ready for the report
frontier194_index.json       all 550 prior whole 194-control classes
representatives/*.tm        one verified complete table per prior class
all_classes_index.json      1,193-class cross-size census and occurrence links
table_occurrences.json      every recognized table occurrence and byte digest
source_manifest.json        pinned direct Git-blob and SHA-256 provenance
archive_references.json     recursive ZIP-path and SHA-256 ledger
incoming_json_*.json        fresh incoming explicit-JSON recognition evidence
sources/                    attributed older roster and placement index
new_designs.json             the two new identities, separate from prior counts
novelty_receipt.json        recorded run of the standalone checker
inventory_tables.py        literal-table parser and complete-tree census entry point
exact_graphs.py             exact graph isomorphism for disconnected diagnostics

ATTRIBUTION
-----------
The 550 retained prior machine tables and inherited descriptions come from
VladimirReshetnikov/ProveIt at the pinned commit, with the individual paths
shown in frontier194_index.json and the source manifests. Their underlying
work and licenses remain attributable to Vladimir Reshetnikov, James Chang,
Andrew James Wade, Elliot Glazer and the contributors credited by those
packets. The larger deliverable preserves the relevant upstream notices and
licenses. This comparison does not claim those prior constructions as new.
