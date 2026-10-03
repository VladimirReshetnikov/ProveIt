# Canonical first-visit certificates

New sibling research packet, 3 October 2026. No earlier release, research source, or publication file was changed.

## Result

Conditional on the reviewed sparse mass-at-most-four orbit normal form, the stationary-frame visited-site set has an effective ordinary integer polynomial of degree at most four with exactly one natural witness tuple for each visited signed external site, and none for any unvisited site. First-arrival time is canonically recoverable, can be an external argument, or can be one more canonical witness.

The expanding-clock specialization needs only one shared natural cycle witness beyond the membership certificate. For B final disjoint Presburger clauses with I,H,C total inequality, equality, and congruence occurrences:

- Membership: W=B+I+2C; R=1+I+H+2C
- External first time, expanding: W=B+I+2C+1; R=3+I+H+2C
- Internal first time, expanding: add one witness to the preceding count
- External first time, affine: W=B+I+2C; R=2+I+H+2C

W counts natural witness slots; R counts squared residual slots before identity deletion. These are fixed-rule/fixed-input, potentially large finite counts. Empty domains use polynomial 1 and no witnesses.

The same proof covers fixed Presburger observation schemas, including complete canonical finite-configuration targets and anchors of a fixed finite pattern, including prescribed zeros. The prefix hit domains may be infinite and are handled by disjoint Presburger sets. No first-hit spatial growth assertion accompanies this extension.

## Contents

- `PROOF.md`: full elementary compiler, shared-counter specialization, observation-schema corollary, assumptions, counts, and provenance
- `independent-review.md`: independent mathematical audit and pinned proof hashes
- `audit.py`: deterministic finite algebra fixtures; requires Python and SymPy
- `audit-results.json`, `audit-results-optimized.json`: byte-identical ordinary and `python -O` receipts
- `MANIFEST.sha256`: file integrity checks

## Replay

Run `python audit.py` and `python -O audit.py`; compare their output to the supplied receipts. The guard self-test confirms that correctness checks remain active under optimization. The fixtures check 164,025 bounded membership-witness tuples, canonical signed quotients, polarization/denominators, wrong-time rejection, single-coordinate witness perturbations, and 61 shared-counter cases. Symbolic checks include external variables when computing total degree and verify all integer coefficients.

Finite fixtures test the displayed algebra; they are not a general CA-to-normal-form compiler, Presburger QE implementation, formal proof, or exhaustive test over unbounded natural witnesses. The unrestricted uniqueness theorem is proved mathematically in `PROOF.md`.

## Scope

No generic single-fold MRDP theorem, uniform-over-input arity bound, arbitrary original-frame expanding extension, novelty claim, or efficiency guarantee is asserted. Affine original-frame tails remain covered because their full timed occurrence relation is Presburger. Earlier reports remain unchanged.
