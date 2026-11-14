# Three U208 submissions: two machines, not three independent folds

Pinned commit: ef5a23e04b0285e321ceec5f4b329223cee0ab57.
All three original ZIP downloads were verified against the Git blob IDs and
SHA-256 identities recorded in archive_identities.json. This compact bundle
retains table/source snapshots, not the complete original archives.

## Exact comparison

There are six supplied 208-state tables (primary and Compatibility variant in
each release). They form exactly two rooted transition-graph isomorphism classes.
Conditional Context and Entry Context have byte-identical primaries
b348a466a2c316511e0037ea3824de29d4c6ad37338404fbc98a3968fdb25135
and byte-identical Compatibility alternatives
5f936da0cf393548cdd1eeebcaf7490d7a42f4ccca115f865a7bcc045463eb52.
History uses other native labels, including the opposite representative for
the merged 172/211 roles, but has an exact graph conjugacy to each corresponding
machine. The checked maps preserve start, halt, read, write, direction, and
all targets, hence transfer execution on every common tape.

Every table has 208 graph-reachable working states and 416 complete binary
transitions. All six sources preserve the identical ordered word of 3909
primitives and 5083 guarded ordinal CFG arrows. Two independent source
resolvers agree. Primary source depth is 42 and alternative depth is 41.
Nonisomorphism does not assert different computed behavior.

All three proposals use the SAME conditional tape-history reduction. They
cannot be stacked to obtain 207. In Joint native labels, delete172, redirect
116/read0 to211, and replace211/read0 by(0,L,217). History instead keeps172
and renames the corresponding helper, giving the same graph.

## Proof audit

The parent entry invariant uses five states:116 and217 have a one immediately
left;172 has preceding bits10;163 has a one in at least one of its two left
positions;211 has a one either under the head or immediately left. All incoming
physical rows are enumerated. Induction from state0 is valid on arbitrary
initial tapes. In particular,211 scanning0 implies a left-hand1.

The four exceptional blocks take7,1,3,1 steps for old(172,0),(172,1),(211,0),
and(211,1), respectively. Their complete effects agree with one old step,
including unchanged exterior and head; no block visits halt internally.
The remaining414 old rows commute with the quotient in one step. Positive
bounded durations prove halt reflection as well as preservation. No invariant
is falsely imposed at internal visits of candidate211 during its seven-step
block. The clock is Tnew=Told+6*N(172,0)+2*N(211,0), measured at old boundaries.

This is an ordinary PA-formalizable finite simulation theorem, not a newly
exported PA proof. The claimed Con(U) and Con(PA) endpoint still depends on
the inherited numerical proof-search, startup suffix, and interpretation
calibration. The machine enumerates unrestricted weak cover plus irreflexivity,
not literally only the unary U instances. The supplied reports explicitly
retain PA-verifiable finite-refutation translations between those theories.
K215's separate ZFC formalization is not repurposed as a certificate for U208.

## Reproduction scope

Run `python -B check.py` and `python -B -O check.py` here. These verify the
compact snapshots, hashes, graph conjugacies, graph census, source-word identity
and dual-resolver CFG identity. Full runtime and release replay receipts, when
present in receipts/, record separate fresh executions against the complete
original inputs. This small bundle by itself does not rerun those complete
archives or prove their inherited logical calibration.
