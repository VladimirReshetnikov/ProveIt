PA CONSISTENCY MACHINES: COMPARISON AND INVESTIGATION BELOW194 STATES
===================================================================
Report date: 14 November 2026 UTC
Repository snapshot: 567266818aaeceb0f3a8f82debf303c8d84bddaf

RESULT
------
No verified binary, single-tape, blank-start machine with fewer than 194
working states was obtained. The requested strict state reduction remains
unachieved. This archive does not present a 194-state reference table as a
solution, and does not claim a general lower bound of 194.

WHAT IS INCLUDED
----------------
report/report.pdf and its complete LaTeX source give the comparison, proof
audit, new all-offset obstruction, failed source alternatives and exact
scope of the finite searches. All 55 filed packets and six incoming archives
are included in the packet ledger. There are 49 distinct 194-state graph
classes: 33 reported constructions, 11 auxiliaries and five rejected tables.
Those status labels describe the supplied evidence; we did not rebuild all
33 historical consistency proofs.

The new mathematical theorem shows that EVERY nonnegative constant equality
offset e fails for I=3p, M=3p+1, U(d,A)=3p(A,d)+2, E=3p+e, when the remaining
listed heads and rules are retained. The numerical calculus derives code 1.
The proof is ordinary mathematics with declared proof-template dependencies.
It does not rule out different encodings or lower-state machines in general.

DIRECTORY GUIDE
---------------
report/                  Complete article, PDF, TeX sections, generated tables.
comparison/              61-packet ledger, 531-class census, 49 frontier tables,
                         exact hashes, starts, status notes, scanner sources.
research/physical/       Reproducible finite contraction screens and receipts.
research/logic/          Brouwer-only failed lead and corrected explosion run.
research/mixed36/        Disjoint mixed 3/6 source profiles and saved audits.
research/split_gate/     Guarded-gate repair, failed contract and pricing code.
research/rejected193_refutation/
                         Inherited primitive proof refuting the known 193-state
                         shortcut. This rejection is not a new contribution.
research/ordinary_PA_proof_audit.md
                         Independent audit of the inherited PA argument.
verification/            Delivery audit, exact numeral certificates and Boolean
                         obstruction checks, with explicit logical boundaries.
references/              Unmodified proof-source extracts and their provenance.
licenses/                Inherited notices.
PROVENANCE.json          Snapshot, attribution and interpretation boundaries.
MANIFEST.sha256          SHA-256 hashes of the delivered files.

QUICK REPLAY (Python 3, no network)
--------------------------------
From the archive root:

  python3 -B verification/replay.py

This checks the packet/census summaries, all 49 literal frontier hashes,
complete rows, designated-start reachability, rooted and root-free graph
identities, twenty new arithmetic refutation certificates, 10000 supporting
pairing identities, the Boolean countermodel, and the inherited 73,393-step
primitive refutation. If present, it also verifies the file manifest.
It does not rerun stochastic searches or establish a new consistency theorem.

The optional 328-screen physical replay and source-context reconstruction
have separate instructions in research/physical/SEARCH_NOTES.txt. Source
and search replay instructions also accompany research/mixed36/ and logic/.
The full corpus census requires a local checkout of the exact pinned commit;
instructions are in comparison/REPRODUCE.txt.

REBUILD THE MAIN PDF
-------------------
Use a normal TeX Live installation with Latin Modern, AMS, geometry,
microtype, booktabs, longtable, array, enumitem, xcolor, fancyhdr, xurl and
hyperref. From report/:

  python3 generate_tables.py
  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex

Some supplementary .tex files are section extracts or inherited reference
sources and require their surrounding preamble. The main report is complete.

STATE AND PROOF CONVENTIONS
--------------------------
Counts exclude the terminal halt label and include the start control. Tape
alphabet is {0,1}, input is an all-zero two-way infinite tape, every transition
moves left or right, and no program tape or free initialization is assumed.
Graph identity deliberately forgets the start only when comparing graphs.
The separately recorded start is essential to the machine's actual claim.

PA-provability is the requested mathematical standard. The unfinished
end-to-end iPRA/Lean goals are distinguished from ordinary written PA proofs.
Neither finite testing nor an unverified optimistic grammar score is
promoted here to an accepted consistency machine.
