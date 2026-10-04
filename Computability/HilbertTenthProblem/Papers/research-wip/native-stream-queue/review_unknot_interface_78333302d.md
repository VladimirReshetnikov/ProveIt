# Bounded computational-interface review of the imported knot reports

The selected report passages clearly separate practical exact recognition from the unimplemented quasi-polynomial target. Neither their timing results nor their conditional hierarchy iteration count supplies a universal Diophantine compiler. This is an interface review, not a correctness audit of the recognizers, a review of all six source archives, or verification of the external topology literature.

The immutable snapshot is adaptation commit `78333302d9babf0efb1a5d218e122f13c35bb306`, following the history import at `bbded8874`. The fresh receipt authenticates three files under `Topology/UnknotRecognition/`: the complete root README, the complete synthesis README, and exactly four ranges of `synthesis/report.tex`: **1–240, 384–433, 489–525, 580–612**. The combined read scope is **546 lines**. Working bytes read in this turn match those immutable blobs. Other manuscript sections, included TeX files, source implementations, PDFs, archives, test results and external references are outside this review. Searches and commit metadata do not enlarge that scope.

## Claims and hypotheses preserved

The root guide and synthesis explicitly call the quasi-polynomial implementation target open. The selected hierarchy discussion distinguishes an iteration bound `L(g+1)^L` from a running-time bound: representation size, work per cut/rebuild, restart count and bounds on both hierarchy depth and pattern complexity are additional obligations. This distinction is necessary. Taking `g` polynomial in input size and `L=O(log n)` would bound the displayed iteration factor quasi-polynomially, but the formula alone supplies neither those hypotheses nor the cost of an iteration. The report lists the missing compressed representation, cutting/provenance, bounded-surface, weak-reduction, depth and cost ingredients.

The exact recognizer's stated correctness proposition requires a **validated one-component diagram** and separates a user ceiling's `UNKNOWN` from either final verdict. Its proof appeals to topology theorems, chain-homotopy transformations and a homology-detection criterion. This review reads that interface but does not certify its implementation or imported facts. Likewise the stated exponential worst-case cost and practical scan-width discussion are reported claims, not fresh benchmark or complexity proofs here. The text explicitly declines a general proof of the empirical scan-width estimate and notes the potentially exponential output multiplicity.

The experiment-status guide preserves material limitations: one grid experiment was stopped after size9; the final four-strand scan section did not run; certain baseline rows came from a changing working tree and are excluded. These are not new execution results. Nothing was rerun. The statement that all cited PDF results come from completed portions remains the guide's attributed statement; it was not checked against every data file or table.

No concrete mathematical correction is asserted within this read scope. In particular, the imported preprint's present publication status, exact external hypotheses and historical implementation/test claims remain unverified. The report's own unresolved grid move-set obligation also remains unresolved; its detailed section was not read in this pass.

## Consequence for universal Diophantine research

There is a simple conditional boundary. Let `D` be any total decidable predicate on finite diagrams, and let `f` be a total computable map from machine/input pairs to diagrams. If `D(f(M,x))` were equivalent to whether `M` halts on `x`, composing the decider with `f` would decide halting. Thus **a total exact finite-diagram recognition predicate cannot by itself serve as a universal halting target under a total computable many-one reduction**. This argument uses only the hypothesized totality/decidability, not any unreviewed topology theorem. It applies equally to the predicate's complement.

This does not exclude topology as a computational substrate, nor does it forbid a Diophantine representation of a decidable topological predicate. An unbounded family can instead express `exists T: D(g(M,x,T))`, provided one actually proves that this family captures accepting histories. To improve this repository's arithmetic frontier, one would still need:

1. an effective, finite integer encoding of the chosen machine/input and certificate;
2. a proved sound and complete representation of unbounded computation, including the quantified horizon or compressed history;
3. an explicit fixed-arity polynomial source with every arithmetic operation and domain condition charged.

The selected knot-report interface provides none of those three bridges. A short inequality such as a hierarchy threshold is a numerical test on already supplied structural data; obtaining and verifying that data is a separate cost. Scan-width speedups and reported wall-clock improvements also do not bound the arithmetic size of an unbounded universal polynomial.

No new arithmetic source, witness bound or universal-operation bound follows. The established84-operation polynomial and the unresolved83-operation candidates keep their prior status.

## Fresh evidence

Only the newly authored `/tmp/review_unknot_interface_78333302d.py` ran. It reads immutable Git objects, hashes exact text spans and checks equality to the working files that were read. Its receipt has SHA-256 `da5e6ed5a8ef9c507197957739cec761e24790ff5694db75757386e3ae667930` and records the helper hash. No supplied, archived, committed/frozen or copied predecessor program was executed or imported. No build, benchmark, archive extraction, external-source fetch or repository mutation was part of the collector.
