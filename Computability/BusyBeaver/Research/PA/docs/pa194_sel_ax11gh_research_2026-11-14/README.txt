PA194SEL and PA194AX11GH
=======================
Two new 194-state binary Turing machines, comparison, proofs and research
Prepared for Vladimir Reshetnikov, 14 November 2026 (UTC)

RESULT
------
No verified machine with fewer than 194 working states was obtained.
This archive supplies two materially different 194-state constructions.
The main contribution is PA194SEL's direct written proof in iPRA of
halting/nonhalting equivalence to the pinned primary PA194. This relative
theorem does not assume the absolute consistency calibration.

For the exact meaning of the proof claim, begin with the PDF:
  report/pa194_research_report.pdf
The complete LaTeX source is report/main.tex and its included .tex files.

PA194SEL reorganizes two recurring decoder pairs into history selectors.
The complete eight-row change is checked independently twice. A whole-tape
local identity, a primitive-recursive clock and quantifier-free induction
prove:
  iPRA proves H_primary <-> H_SEL, and not H_primary <-> not H_SEL.
An old halt by t gives a new halt by 3*t; a new halt by t gives an old
halt by t. Consequently any established primary iPRA calibration to
Con(PA) transfers directly. There is no extra source-calculus premise.

PA194AX11GH combines four-field eleven-entry AX, an explicit generalization
binder, no-push MP, and cache-only Shift. Its changed source command has an
all-natural effect and runtime proof. Its compiler works on every store,
including early halts and the zero-pairing alias. All 4,778 source outcomes
pass construction and independent literal symbolic checks. The command
scheduler's iPRA proof and physical certificates are supplied separately;
internalizing the complete physical simulation remains an obligation.

ABSOLUTE PROOF BOUNDARY
-----------------------
The pinned repository explicitly says that neither machine-specific
direction of the primary PA194's iPRA consistency equivalence is yet
established. Its written ordinary PA calibration and its unfinished Lean
endpoint must not be confused with a completed iPRA theorem. This archive
does not close that inherited gap. SEL supplies a complete direct relative
mathematical proof. AX11GH additionally requires the stated physical
internalization. No new end-to-end Lean compilation is claimed for either.

MACHINE CONVENTION
------------------
Both tables have exactly 194 working controls and 388 rows. The tape is
two-way infinite and binary, initially all zero; the initial head position
is zero. Each step writes a bit, moves exactly one cell L or R, and enters
the next control. Dense tables start at 0, use working labels 0..193 and
halt at 194, which has no rows and is excluded from the count. Native tables
start at 74 and halt at 254. There is no external initializer or program tape.

Principal dense tables and SHA-256:
  machines/SEL/machine/pa194sel.tm
  5121f0b417ea025af140804b59e50a9d2fc3c461612e98b2f0ac86742c76a75b

  machines/AX11GH/machine/machine.tm
  513e9c8b28e0dd41e6003bb8d82c80ff3dac5fb3c5274cd2f709a3bba8c3e9e1

Their blank initializations take 58,208 and 57,922 steps, respectively.
Exact complete tape endpoints, native/dense maps and startup receipts
are included. A long trace alone is never used as a nonhalting proof.

COMPARISON SCOPE
----------------
Pinned repository: VladimirReshetnikov/ProveIt
Commit: 603c58ca3bd6bf3222fcfc4e308e6b079f65d573

All 82 filed PA packets and five current incoming deliveries are indexed.
The explicit census reads 695 tracked PA .tm files and 874 incoming .tm
members (1,569 occurrences, 802 distinct byte payloads). The 194-state
frontier contains 110 spanning graph classes, including research and
rejected designs. Annotations distinguish historical claims from checks
replayed here. This is not a claim that all 110 have established calibrations.

Both new graphs are different from all 110 historical graphs and from each
other. Complete tuples establish comparison; hashes are identifiers.
The stronger comparison allows state renaming, global reflection, symbol
exchange and ignored final write/move. It is a structural novelty test,
not a claim that symbol exchange preserves the fixed zero-blank semantics.
Each historical graph and both new graphs still have 194 classes under
ordinary control bisimulation. This is not a lower bound against contextual
reductions or a redesigned source calculus.

REPLAY
------
Python 3.10 or later, standard library only. Keep assertions enabled.
No network or original checkout is required for the release verification.
From this archive's root:

  python3 verify.py --full

The verifier uses a private temporary copy, checks reconstructed bytes
against the frozen deliverables, and writes a structured release receipt.
Without --full it omits the longest independent literal symbolic replay.
Use --help for the receipt-path option.

The frozen all-design graph comparison can also be run directly:

  python3 comparison/census.py verify machines/SEL/machine/pa194sel.tm machines/AX11GH/machine/machine.tm

Each machine directory has its own README and individual replay commands.
Optional discovery searches are under research/. Some require C++17.
Their negative outcomes are restricted to the stated finite search models;
they do not establish that 193 states are impossible.

To rebuild the PDF on a standard TeX installation with pdfLaTeX:

  cd report
  python3 generate_tables.py
  pdflatex -interaction=nonstopmode -halt-on-error -jobname=pa194_research_report main.tex
  pdflatex -interaction=nonstopmode -halt-on-error -jobname=pa194_research_report main.tex

Recollecting the repository census requires the pinned checkout and safely
extracted five incoming ZIPs. The census and ledger scripts accept these
paths; their exact frozen outputs and all 110 representative tables are
already supplied. Original incoming archives are not duplicated here.

DIRECTORY MAP
-------------
  report/          PDF, full LaTeX, complete 388-row tables for both machines,
                   proof sections, 110-design and 87-delivery appendices
  machines/SEL/    Constructor, parent bytes, both forms of the new table,
                   two independent finite checkers and exact receipts
  machines/AX11GH/ Constructor, full source, literal runtime checker,
                   word/source/emitter/Shift checks, exchange certificate
  comparison/     Exact census, all 110 historical .tm representatives,
                   annotated CSV/JSON ledgers, source-integrity records
  research/       Optional finite discovery searches and scoped outcomes
  references/     Pinned project status and relevant inherited documents
  verification/   New novelty and release-replay receipts
  RESULTS.json    Machine-readable result and proof-status summary
  SHA256SUMS      Every archived file except this checksum manifest

PROVENANCE
----------
The numerical calculi, PA calibration work, primary machine, compiler and
symbolic runtime frameworks are inherited from ProveIt and the referenced
research packets. Their provenance and license files are retained.
New contributions are the exact simultaneous SEL design and proof, the
AX11GH combination and all-store command argument, independent checks,
current corpus reconciliation, and the documented discovery experiments.
This is AI-assisted research, supplied for independent mathematical review.
The copied Lean files are inherited references, not new compiled endpoints.
No claim of global priority or a 194-state minimum is made.

No repository commit, pull request, issue or external message was published.
