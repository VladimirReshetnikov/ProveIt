# Four-attachment symmetry and integer-face coverage audit

## Verdict

APPROVED: all recorded automorphism/self-duality actions, all zero/positive population orbits, all component reductions, and the complete outstanding-gap task list.

The independent standard-library checker `audit_face_orbits.py` reconstructs the full domain from the already audited template and gamma data. It verifies:

- 131 distinct variable actions across 76 templates
- All 84,614 population zero/positive masks
- Exactly 24,342 pairwise-disjoint complete face orbits
- Exactly 3,583 structurally reduced orbits
- Exactly 19,657 gap-two and 19,710 gap-three outstanding tasks
- Exact equality with all 39,367 entries of `face_tasks.tsv`

This does not prove positivity for those outstanding tasks. The shifted target-polynomial export and any subsequent positivity certificates are separate audit layers.

## 1. Actions are genuine support-preserving symmetries

For every four-vertex permutation p and duality flag, the checker independently tests whether simultaneous relabeling, and reversal when requested, fixes the complete core relation and attachment directions. It reconstructs the induced map on every legal neighborhood type. The complete set of distinct variable maps equals the supplied action set; each recorded core-permutation/duality witness is verified separately.

The variable map sends old coordinate i to its new coordinate. Every map is bijective; identity and closure under composition are checked. As an additional exact check, all five gamma coefficient arrays are invariant under each induced permutation of quota vectors. Reversal is legitimate because swapping the tail and head endpoint sets preserves support counts.

Thus these are symmetries of the actual all-population polynomials, not merely symmetries suggested by numerical evaluations.

## 2. Orbit coverage and transport direction

An action sends a face mask to the mask with its active coordinates carried to their images. Every listed member/action pair is checked in the recorded direction: the action maps the representative to that member. Each representative is the least mask in its full orbit, and its complete member set is independently regenerated using all valid actions.

The orbit sets are disjoint and their union is all 2^d masks for each d-variable template. No mask is discarded because it lacks a provided representative or transport. Duplicate witnesses for the same member are harmless in principle; the actual record contains exactly one member entry per mask.

On a positive face M_i=1+y_i, variable permutations simply permute the y coordinates as well. Zero coordinates remain zero. Therefore the same orbit transport is valid after the positive-face shift.

## 3. Structural reductions hold throughout each face

For every representative, independently construct the one-clone graph containing exactly its active types. Compute all components, bipartiteness, active attachment sets, and the exact maximum-population rank formula

|active attachments| + ν(residual core).

This reproduces every structural flag without replacing matching rank by the producer's shortcut. With fewer than four active attachments, the maximum rank is at most three; with all four it equals four. The arguments in `KERNEL_COVERAGE_AUDIT.md` prove the formula is attained by four copies per active type and is an upper bound for every population, not a conclusion from population sampling.

A structurally omitted face has only bipartite components or components of rank at most three. The established component theorems and ULC product closure apply for every positive integer value of its active populations. Symmetry preserves these graph properties, so all members of its orbit have the same reduction.

## 4. Nonnegative binomial coefficients justify the other omissions

The two gap arrays have already been independently verified as exact polynomials in the basis ∏ binom(M_i,q_i). Setting an inactive M_i to zero eliminates precisely those terms whose exponent support meets an inactive coordinate. Distinct surviving terms remain distinct in the active coordinates.

If no negative coefficient survives this restriction, the gap is nonnegative for every nonnegative integer active population, hence in particular for all positive integer populations of the face. The checker independently reconstructs every negative exponent-support set and tests survival on each nonstructural representative. It also verifies that this test is invariant throughout every orbit.

The resulting outstanding gap list matches every `remaining_gaps` field and the complete task TSV exactly, with no missing, repeated, or extraneous tasks. These omissions establish integer-population positivity only; they do not imply positivity for arbitrary fractional populations between zero and one.

## 5. Reproducibility

`face_orbit_audit.json` records all counts and pins every authoritative input, checker, and per-orbit coverage ledger by SHA-256. Digests are verified unchanged across the run. The checker imports no producer module, uses exact Python integers, and independently computes automorphisms, component matching bounds, orbit membership, gamma invariance, and all task eligibility tests.

The subsequent 39,367 target inequalities remain explicitly unresolved by this audit. Coverage of a finite list must not be reported as positivity of that list.
