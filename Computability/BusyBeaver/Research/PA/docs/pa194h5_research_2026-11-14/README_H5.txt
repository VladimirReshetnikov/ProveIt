PA194H5: coefficient-five formula codes and the cached-test/no-push controller
============================================================================

This construction has 194 working states and one external halt label. It is
a two-symbol, one-tape deterministic Turing machine, started on a completely
blank (all-zero) two-way tape. The dense start state is 0 and halt label 194;
there is a transition for both read symbols in each working state 0..193.

The ordinary mathematical claim is

    PA |- Halt(PA194H5, blank) <-> exists p Prf_PA(p, code(0=1)),

and therefore PA proves that its nonhalting is equivalent to Con(PA).
The construction does not establish a sub-194-state result. It does not
claim a newly compiled end-to-end Lean/iPRA theorem. The mathematical
calibration and its scope are documented in proof/ and calibration/.

What changes
------------

The inherited M5 formula constructors use I(a,b)=5*p(a,b), with Cantor
pairing p; membership, universal and equality constructors have tags 1, 2, 3.
The inherited H controller has successful MP return (b,w,b,0), without
pushing a dummy zero. Its Shift tests the cached formula h=1, then returns
(h,tl(w),d,hd(w)). These are composed here with the unsymmetric comparator.

This is a new combination of known mechanisms. The corpus already contains
M5/N5 and H/H6, and neither the arithmetic coefficient nor the H controller
is claimed as a new idea. The combined literal graph differs from every
one of the 76 frozen spanning 194-state graphs, even allowing state renaming,
arbitrary spanning start, tape reflection, symbol interchange, and arbitrary
terminal write/move effects. The difference is substantive: formula codes
change relative to H/H6 and proof-store operations change relative to M5/N5.
For example I(1,0)=5; Shift(1,0,0,0) does not halt under the cached test.
The nearest H6 table differs in one native transition: on state 190/read 1,
the target changes from 330 to 99. That reused decoder edge changes every
formula-constructor body to five increments instead of six. The small row
delta is reported explicitly in machine/nearest_H6_difference.json; this
is a new verified member of the existing architecture.

Exact construction and checks
-----------------------------

  135 fixed controls + 67 AX reader states - 8 simultaneous folds = 194.
  388 transition rows; 32 exhaustive local history/read fold cases.
  3,714 resolved source sites; 4,815 physical source outcomes.
  61 constructor blocks widened from four increments to five.
  All 3,409 outside source sites and their outgoing edges relocate exactly.
  Complete blank initialization: 58,088 steps, source entry 25, logical
      registers (2,0,0,0,0,0,0,0,0), and 26 unit spare blocks.

The separate literal-table checker reconstructs four register-list lemmas
from the transition rows (no arithmetic-box oracles), checks every outcome
for arbitrary natural registers and an arbitrary nonempty spare list, and
checks dense/native conjugacy and the entire blank-start tape.
Its run uses 1,121,654 symbolic operations; longest case 403; minimum positive
physical-duration constant 3. These are universal symbolic certificates,
not tests on sampled register values or evidence from a long blank run.

The source emitter and command checker covers all 190 AX tokens, all ten
pushed entries, both MP outcomes, zero stack/implication aliases, arbitrary
old caches, the seven direct head selectors, guarded gate selector,
dominated rho selector, generalization, the reserved-zero MP suffix, and
final contradiction detection through Pop. The ordinary proof gives the
all-store compiler needed because candidate trials carry the store forward.

Reproduce
---------

Python 3.10+ and its standard library suffice. Run without Python -O.

    python3 verify_all.py

This rebuilds in a temporary directory, compares all generated table/source
artifacts to the packaged versions, independently replays the physical
contracts, and repeats the source binding and symbolic command checks.
It writes verification/replay.json. The independent audit takes several
minutes on a single CPU. Set TMPDIR to a writable directory if needed.

To repeat corpus novelty after obtaining the inventory's frontier_tables:

    python3 verify_all.py --frontier /path/to/frontier_tables

The already recorded novelty result is machine/novelty.json. The frozen
corpus is at commit 2337ce611a26e308697ccbddb2a1636f989f01c3. Full comparison
and corpus inventory are supplied by the enclosing research report.

Files
-----

  machine/machine.tm           Dense literal transition table.
  machine/machine.native.tm    Equivalent inherited state labels.
  machine/raw.native.tm        202-state parent before the eight folds.
  machine/receipt.json         Builder and startup receipt.
  machine/independent/         All physical contracts and literal replay.
  machine/novelty.json         Exact comparison with the 76 known graphs.
  construction/               Portable builder and pinned upstream inputs.
  proof/                      Source/word certificates and ordinary proofs.
  calibration/                Inherited radix and PA calibration chain.
  verification/               Separate literal-table checker and replay.
  PROVENANCE.json              Credits, exact Git blobs, and proof boundary.

Dense table SHA256:
417e3940a77a6222ccd06885209cc853e572ac48b64acbabf581942f142304c9

Native table SHA256:
4448d94a91c04443a34b1d99015c13ee514fd1a9d2cff091616eb60aeece726e

Copyright/licensing notices for inherited sources are retained beside them.
No sub-194 lower bound or exhaustion of all possible designs is asserted.
