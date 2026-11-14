PA194AX11: an eleven-entry AX protocol
====================================

Literal machine
---------------
machine/machine.tm has 194 working states, 388 binary transitions, start 0,
and terminal halt 194. It starts at head 0 on the all-zero two-way infinite
tape. Rows are: current-state read-bit write-bit L-or-R next-state.

SHA-256:
1a7defae031c322a5577a3f2cb77d4c3bbc3242c7246f35f073d4dcf12a191d0

The native table uses start 74 and halt 254. labels.json is the exact dense
conjugacy. Relative to the primary PA194 native table, only two rows change:

  (164,1):  1 R 98  becomes 1 R 114
  (2066,1): 0 L 302 becomes 1 R 19

The first removes the successful-MP dummy push. The second replaces AX's
terminal break by the ordinary Cantor-stack push, so AX pushes its guarded
gate and falls into the MP field reader. The complete decoded AX consumes
one MORE parameter z than the older command. Its effect is

  (t,w,d,h) -> (0,[G,Gamma,L6,...,L1,rho,U(d,h),t ; w],z,0).

The list has eleven entries, including the saved incoming top t. This z is
an explicit additional encoded parameter; it is not implicitly zero. The
proof compiler deliberately supplies z=0 when it needs cleared registers.
The command-level proof and formulas are in the accompanying report.

Physical verification
---------------------
From this directory, with Python 3.10+ and the standard library:

  python3 -B build.py
  python3 -B check_source.py
  python3 -B verification/check_literal.py

These commands write fresh receipts to temporary directories unless given
--output. Assertions are required: do not use Python -O or PYTHONOPTIMIZE.

The builder reconstructs the machine from a pinned raw parent, grammar and
seven folds. It checks all 28 simultaneous fold cases, all 4,779 arbitrary-
register source outcomes, and complete blank startup. The independent
checker imports no compiler or arithmetic-box oracle. It rederives four
generic finite-list lemmas directly from the literal rows and checks all
source outcomes with arbitrary natural registers, an affine zero gap and
an arbitrary nonempty finite spare list.

The independent source checker expands the source tree independently and
resolves every jump by two algorithms. Of the old 3,673 instructions,
3,653 are unchanged with the same relocated edges. The old terminal AX
break at 3553 becomes nineteen push instructions 3553..3571. The old MP dummy
push 3634..3652 disappears. AX now enters the MP field reader at 3572.

This package is executable mathematical evidence for the source and literal
machine layer. It does not contain a newly compiled end-to-end Lean/Rocq
consistency theorem. The report separates the inherited PA calibration,
the new command compiler, and the exact physical simulation.

Provenance
----------
Inputs are pinned to ProveIt commit 2337ce611a26e308697ccbddb2a1636f989f01c3.
PROVENANCE.json identifies copied utilities and the two new source edits.
Inherited license notices are retained under licenses/.
