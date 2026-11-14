PA194AX11QH4L / PA194AX11QH4R research package
============================================
14 November 2026 (Pacific time)

RESULT

Two new 194-working-state binary, blank-start, one-tape Turing machines.
No verified machine with fewer than 194 working states was obtained.
Both implement exactly the 3,671-instruction PA194AX11QH source program.
Each passed all 4,778 outcomes of an independent universal literal-tape
audit and a complete 58,088-transition blank initialization check.

The report gives an ordinary computer-assisted mathematical relative
iPRA proof, with explicit halting-witness bounds. With P the parent and
L,R the new machines:

  HaltBy(P,t) implies HaltBy(L,2t).
  HaltBy(L,t) implies HaltBy(P,t).
  HaltBy(P,t) implies HaltBy(R,2t).
  HaltBy(R,t) implies HaltBy(P,2t).

This preserves any eventual iPRA calibration of the parent to Con(PA).
The pinned project's absolute machine-specific calibration is still open.
This package does not close that gap and contains no newly compiled Lean
or Rocq endpoint for the relative or absolute machine theorem.

START HERE

  report.pdf                  Complete report, proof, comparison and tables.
  report.tex                  Main LaTeX source.
  report_parts/               Included proof, tables and full packet ledgers.
  construction/AX11QH4L/       First new machine and its certificates.
  construction/AX11QH4R/       Second new machine and its certificates.
  construction/inputs/        Exact parent inputs and supplied certificates.
  construction/rebuild.py    Deterministic reconstruction and verification.
  verification/               Independent verifier, references and fresh logs.
  comparison/                 82-delivery, 95-class inventory and representatives.
  research/local/             Scoped local state-fold synthesis experiments.
  research/grammar/           Mixed-integer grammar and association experiments.
  research/logical/           Quantified-gate exchange note and proof certificates.
  SUMMARY.json                Compact machine-readable results and proof status.
  MANIFEST.json               SHA-256 and size of every included content file.
  SHA256SUMS                  Standard checksum list (excludes itself).

MACHINE CONVENTION

The main files are construction/AX11QH4L/machine.tm and
construction/AX11QH4R/machine.tm. A row is:

  current_state read_bit write_bit L_or_R next_state

There are 194 working states numbered 0 through 193 and 388 rows. State 194
is terminal and has no rows; it is excluded from the working-state count.
Initially the two-way infinite tape is all zero, the head is at coordinate
zero, and the control is 0. Native versions instead start at 74 and halt
at 254; the full bijections are included as labels.json.

Dense table SHA-256:

  L: c825ec97fdaa36868d1830b601863d255853ebe061af8b22f432d55233763659
  R: 9ea0169880ecaea748d11217c829420aa8694948d2578b8fc28adcc3bcf76815

REPRODUCTION

Python 3.10+ and its standard library suffice for all main checks. From
this directory, with assertions enabled:

  python3 -B verify.py --quick
  python3 -B verify.py

Quick mode verifies every retained file identity, reconstructs both new
tables, checks source equality and simultaneous contextual folds, checks
the clock certificates, freshly replays all three startups, and rebuilds
both finite quantified-gate certificates. It omits the independent universal
tape reruns and the complete historical graph comparison. Full mode adds
those checks; allow several minutes. Outputs are temporary and do not
overwrite the retained evidence. Never run with Python -O or PYTHONOPTIMIZE.

Both new independent universal audits and the novelty comparison were
freshly executed during this investigation. The parent's universal outcome
certificate was retained and hash-bound; it was not freshly rerun. To do so:

  python3 -B construction/verification/check.py construction/inputs

That optional command writes a fresh independent/ directory beside the
parent inputs. Save a separate working copy if preserving every checksum
is important. The independent checker imports neither the construction
compiler nor arithmetic-box oracles.

To compile the main PDF in a normal TeX Live installation with the listed
packages, run twice:

  pdflatex -interaction=nonstopmode -halt-on-error report.tex

The standalone logical note can likewise be compiled twice from
research/logical/ using logical_research.tex. The included logical PDF
uses the same content. Its source has received font/layout-only adjustments
after the logical proof audit; the final content hash is recorded.

SEARCH REPRODUCTION

The archive includes the actual C++ and Python sources, initial data,
receipts and logs of the unsuccessful reduction searches. Optional search
experiments require a C++17 compiler or SciPy/HiGHS as documented in their
own directories. These are finite heuristic or restricted-model searches,
not lower bounds on arbitrary machines. Revisit counts are not counts of
distinct candidate graphs. Projected state counts are not accepted machines.

SCOPE AND PROVENANCE

Everything is pinned to VladimirReshetnikov/ProveIt revision:

  32d0d8b7d93a63ad4106c18cdb29b37927acdad2

The inventory combines the current authoritative filed .tm catalogue with
a fresh literal/explicit-JSON scan of all five current incoming ZIPs. It
does not claim to execute arbitrary generators or reprove every historical
packet. Some stored graphs are auxiliaries, rejected experiments or diagnostics.

The new constructions combine inherited four-increment reassociation and
predecessor-bit folding with AX11QH. Those methods are attributed. The two
exact complete graphs and their relative certificates are new within the
stated corpus and graph-equivalence scope. The supplementary outer quantified
gate exchange is separately certified; its search did not yield a <=194-state
physical implementation. See NOTICE.txt and per-directory provenance files
for the inherited material and licenses.
