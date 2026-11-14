PA194AX11QH4L and PA194AX11QH4R
==============================

These are two new 194-working-state physical implementations of exactly
the PA194AX11QH source program. They do not establish a sub-194 result.
They supply a relative halting theorem; the unfinished calibration to
Con(PA) remains a separate dependency. No new end-to-end Lean theorem is
claimed.

Both are binary, single-tape machines with a two-way infinite initially
zero tape. Dense start is 0, halt is 194 (excluded from the working count).
Each complete table has 388 rows in the format

  current_state read_bit write_bit L_or_R next_state

The main tables are AX11QH4L/machine.tm and AX11QH4R/machine.tm. Native
numbering, complete bijections, raw 202-state tables, all eight folds,
source sites/instructions, and receipts are alongside them. Input parent
tables are in inputs/.

New deterministic construction and source checks:

  python3 -B rebuild.py --receipt fresh_rebuild.json

Independent literal-tape replays, without compiler or arithmetic-box
oracle imports:

  python3 -B verification/check.py AX11QH4L AX11QH4R
  python3 -B verification/check.py inputs

These write independent/ receipts beside the tables. Assertions must be
enabled: do not use Python -O or PYTHONOPTIMIZE. Python 3.10+ and its standard
library suffice. The two new literal audits were freshly executed and
passed all 4,778 arbitrary-register outcomes. The input-parent independent
data are retained from its supplied packet; a fresh parent replay can be
performed by the last command.

The optional absolute polynomial clock-bound check is:

  python3 -B check_clocks.py --output fresh_clock_bound.json

The stronger factor-two transfer check is:

  python3 -B check_clock_comparison.py --parent inputs --left AX11QH4L --right AX11QH4R --output fresh_clock_comparison.json

It compares matched parent/new duration polynomials and unchanged frame
effects, and freshly replays all three blank startups. See also
relative_proof.tex. The latter is a LaTeX fragment
for the main report, not a standalone document.

Each source graph has 3,671 instructions, including 61 four-increment blocks.
The two new implementations preserve every instruction and successor.
Each reaches the exact canonical blank-start source frame after 58,088
literal transitions. Both pass 32 two-cell quotient cases, with each old
step taking 1, 3, or 5 literal transitions and arbitrary exterior tape.

The construction count is 135 fixed controls + 67 AX readers - 8 folds = 194.
The distinct four-increment associations recur in the implemented source
decoder. Both graphs differ from each other and from all 95 recognized
current 194-state corpus classes under the tested graph symmetries; see
NOVELTY_RECEIPT.json and the main comparison artifacts.

research/ records three new unsuccessful searches: 2,136,175 proposed
mutations, 94,689 accepted mutations, zero projected sub-194 hits. These
heuristic counters include revisits and imply no lower bound.

PROVENANCE.json maps pinned inherited inputs to repository archives and
members. Original compiler/runtime licenses are preserved in licenses/.
