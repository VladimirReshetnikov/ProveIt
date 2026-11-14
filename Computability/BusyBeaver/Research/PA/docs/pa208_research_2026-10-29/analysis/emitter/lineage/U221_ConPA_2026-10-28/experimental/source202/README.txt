SUPPLEMENTARY SOURCE RESULT: 202 DISTINCT SUBTREES
=================================================

Status
------
This directory contains a logically equivalent power-covering emitter whose
complete counter-program source has 202 distinct subtrees instead of U222's
204. Both have 3,891 primitive occurrences, maximum address depth 45, and
maximum consecutive-zero address run 6.

This is a SOURCE-ONLY result. It is not the source of the delivered U221
transition table. No physical transition table is certified here, and no
bound better than the delivered 221 working states is claimed from it.
A source-node reduction need not reduce physical states: the compiler also
has to satisfy contextual arithmetic routing, helper sharing, and complete
runtime obligations.

The proof in proof.tex exchanges two implication antecedents inside the
lower cover clause and exchanges the upper/lower outer antecedents. All
variable labels and quantifier scopes are unchanged. The proof therefore
covers every selector c, including c=0 and c=1. The gates and surrounding
membership-vacuity component remain unchanged.

Files
-----
sites.json                  Exact selected source (order1-commute1, rank 0).
recipe.json                 Exact deterministic closed-macro recipe.
check_commuted_source.py    Independent symbolic/primitive-CFG auditor.
audit.json                  Successful independent audit receipt.
proof.tex                   Mathematical proof fragment for this variant.
transport_proof.tex         Explicit uniform PA proof transport through the numerical calculus.
reproduce_source.py         Portable deterministic reproduction and audit.
reproduction.json           Receipt from reproduction outside the package cwd.
dp_results_beam12.json      Recorded bounded-search results (12 retained alternatives).
dp_summary.json             Compact rank-zero comparison of the four variants.
search_source.py            Optional portable bounded-search heuristic.

Deterministic reproduction
--------------------------
From the package root:

  python3 -B experimental/source202/reproduce_source.py

The script locates ../../inputs/U222_ConU_2026-10-28.zip relative to itself,
checks its digest, extracts it to a temporary directory, runs the parent's
original build_source.py on recipe.json, and compares the result byte for
byte with sites.json. It then runs the independent auditor and requires its
result to match audit.json. No network access, optimizer, or external Python
package is required. The current working directory is immaterial.
Use --output PATH to save a new receipt; otherwise the script only prints it.

The independent audit checks all 737 replacement primitives and every
resolved control edge, all 3,154 exterior primitives and control edges, the
exact closed-macro parenthesization, and the exact symbolic constructor word.
Inherited arbitrary-input contracts of the K215 macros remain a mathematical
proof dependency. A successful source audit is not a physical TM simulation
certificate or a newly compiled proof-assistant endpoint.

Optional search
---------------
After extracting the parent archive yourself, a bounded heuristic can be run:

  python3 -B search_source.py --parent /path/to/u222_consistency_machine \
      --output-dir /path/to/new-source-candidates --beam 12

This produces the three best retained source candidates per semantic variant
and a summary; it does not create transition tables. The beam limit is a
construction heuristic, not a completeness or global-optimality guarantee.
The deterministic recipe is the authoritative reproduction route.

Identity
--------
Source SHA-256:
  bc70b28ff4628db5b9b0c9bd87f560697223e4887f2568b0ece801906713db8f
Parent archive SHA-256:
  d23e80857214900f8e0806f03f6df752af501dd0108eb92c6ed7a49795802652

Attribution
-----------
The source macros and deterministic recipe language originate in the parent
U222/K215 construction included under ../../inputs. Their original license
and attribution notices are preserved in that archive. The parent package's
NOTICE.txt also applies. The new exchange-based source optimization,
independent audit, proof, and portable reproduction script were prepared for
this research package on 28 October 2026.
