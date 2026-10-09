# Claim ledger

## Proved in the article

**Polynomial support (Lemma 2.2).** Coordinatewise positivity of weighted AHT
orbit vectors produces the incidence signatures. The existing compressed
weighted-output theorem bounds their number polynomially in the binary interval
input. This is a corollary of established theory, not a new weighted orbit
algorithm. See the actual numbering in the compiled article if references change.

**Positive residual recovery.** Minimal positive residual sets identify whole
coefficients, with O(s*r) requests and no prior support bound. The generic query
order is already known for coverage recovery; the article supplies a separate
minimality proof and implementation.

**Balanced deletion.** An emitted d-port signature needs
O(1+d*log(1+r/d)) deletion trials, at most 2*r-1. This changes query policy, not
the answer or the worst-case polynomial classification.

**Sparse certificate soundness.** Source-bound coned counts, one zero witness per
retained port, each atom weight, and total mass certify the exact histogram.
This relies on the nonnegative measure supplied by an actual equivalence
relation. It is not an arbitrary-function coverage tester.

**Parity support reuse.** Every lift component projects onto its base component;
full-preimage ports preserve support. At most s+1 further orbit counts recover
all lifted weights. For a binary parity cover, consistent = lifted - base and
inconsistent = 2*base - lifted, separately for every signature.

**Conditional global accounting.** Q incidence calls with description length L
cost Q*poly(L). Quasi-polynomial Q and L give a quasi-polynomial contribution
from this subsystem. The article does not establish those hypotheses for a
complete recognizer or account for other hierarchy operations.

## Checked computationally

- 21 local unit-test methods, with 500 random graph systems under both strategies,
  1,000 generic measures under both strategies, and 300 signed graph systems.
- All 256 Boolean histograms on three ports: 512 additional native-dense/sparse
  comparisons and independent sparse replays.
- Eight primary benchmark output digests checked against analytic fixture counts.
- Exact JSON replay at N=2**16000 with the decimal limit unchanged.
- Unsigned and signed replay with count/recovery producer functions disabled.
- Additive patch applied and checked in a local work tree against exact native
  snapshots, including its 21 proposed native-style test methods.

See receipts for the actually executed checks. Tests are not formal verification.

## Measured, not universal guarantees

The primary 10-port disjoint-block workload reduces 1,024 physical orbit counts
to 26 and certificate bytes from 2,498,706 to 26,538. Uncertified split query time
is about 100 times smaller in the primary run and about 107 times smaller in the
longer-batch follow-up. The baseline is the exact maintained dense code using the
same native kernel, not literal enumeration of the huge universe.

The full-support six-port control has no query reduction, takes longer in sparse
split mode, and has a larger sparse certificate. Gapped 128- and 256-port
controls exceeded a five-second cooperative allowance. No speed ratio is claimed
for unrun dense or unfinished cases. Raw A/A controls and the earlier aborted
exploratory log are retained.

## Not claimed

No general quasi-polynomial unknot recognizer; no new polynomial classification
for weighted AHT; no complete weighted AHT implementation; no proof-assistant
formalization; no exhaustive novelty certification; no whole-knot timing gain;
no full maintained-repository test run; no automatic integration or remote
commit; no knot-exterior provenance; no recovery of attachment order, slope,
point multiplicity, or future attachment maps from incidence alone.
