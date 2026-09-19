# Proof audit

This records the written argument's dependencies and the scope of the checks.
It is not an independent referee report or a machine-verification certificate.

## Main theorem (Theorem 1.1)

**Statement.** For each fixed oracle Z and computable nondecreasing unbounded
budget b, construct A,B <=_T Z'' that are individually 1-generic relative to Z,
obey the budget at every prefix, and have common total-function lower cone
exactly the functions computable in Z.

**Finite conditions.** Equal-length string pairs, with the count bound checked
at every prefix. Equal-tail extension preserves this invariant by monotonicity.
Every extension of one coordinate is possible by copying only its new suffix
into the other coordinate. Previously fixed bits are never changed.

**Reserve.** After common zero padding to a length M with b(M) >= d+1, any two
new tails at Hamming distance at most one give an admissible pair. This is a
reserve for mathematical comparisons; it is not a permanent ban on later
additional disagreements.

**Requirement cases.** For fixed programs e,j:

1. If a first-coordinate extension forces divergence at some input, use it.
2. Otherwise, if a second-coordinate extension does so, use it.
3. Otherwise, if an admissible finite pair gives unequal halting values, use it.
4. Otherwise, convergence is dense in both full coordinate subtrees and all
   cross comparisons agree. Add the one-disagreement reserve.

In Case 4, compare any two convergent first-coordinate prefixes. Equalize their
lengths and join their tails by a one-bit path. Append one common finite suffix
to make the finitely many first- and second-coordinate computations halt. Dense
convergence supplies this suffix by sequential extension. Diagonal comparisons
and adjacent cross comparisons are all admissible and force equal values along
the path. Thus a Z-computable search for any convergent value is total and
unambiguous. All total outputs above the selected first prefix are that same
Z-computable function.

**Critical quantifiers.** No blockers means that for each input, above every
finite prefix there is some convergent extension. It does NOT assert convergence
on every infinite oracle. The synchronization step is finite, at a fixed input.
It does NOT find one suffix for all inputs. The values may be natural numbers,
not only bits; the equality-path proof handles an arbitrary output alphabet.

**Oracle bound.** Testing one candidate blocker is decidable in Z'. Existence
of some blocker is c.e. in Z', hence decidable in Z''. Finite cross-disagreement
and genericity-extension existence are c.e. in Z, hence decidable in Z'. This
justifies Z'', not Z', for constructing the pair.

**Hardcoded finite data.** The common-output program in Case 4 uses Z and a
fixed finite prefix. The prefix may have been selected using Z'', but finite
constants are legitimate program data. No uniform ordinary extraction of the
prefix or the output program's index is needed to conclude that the output is
Z-computable.

**Limit.** All stages are genuine admissible extensions. Lengths tend to
infinity. Hence each final prefix obeys the budget and every settled requirement
applies permanently to the final pair. Genericity requirements meet or avoid
all Z-c.e. sets of strings. Genericity also rules out Z-computability, so the
relative minimal pair is nontrivial and incomparable.

## Non-coarse-computability

For each binary C <=_T Z, rational q<1, and length threshold m, strings whose
disagreement proportion with C exceeds q after m form a dense Z-decidable set.
A relative 1-generic meets these dense sets. The upper disagreement density
is therefore 1. Any natural-valued coarse description could be clamped to binary,
so allowing functions does not create an exception.

## No least degree (Corollary 1.2)

Use the logarithmic budget to get density-zero disagreement. A and B then have
identical coarse-description classes and are uniformly coarsely equivalent.
A least Turing representative would be computable from both, hence computable.
Applying its coarse reduction to itself would give a computable coarse
description of A, contradiction. This handles both uniform and nonuniform
classes. It does not show the absence of all minimal elements.

## Spectrum identity (Proposition 3.1)

Every actual coarse description is uniformly equivalent to f. Every
nonuniformly equivalent representative computes an actual coarse description
of f. Coding an arbitrary higher oracle into computable density-zero positions
then makes that description's degree exactly the higher degree. Hence the raw
description spectrum is upward closed and equals both representative spectra.
The conclusion is about degrees; it does not assert that the two equivalence
classes themselves are equal.

## Block code and least-degree characterization (Section 8)

Every coarse description of the constant-on-dyadic-blocks code J(g) has strict
majority g(n) in all sufficiently late blocks. Finite correction gives a Turing
reduction to g. The correction is nonuniform and no stabilization bound is
claimed. This yields the nonuniform embedding and the least-degree/image
criterion. The text never uses arbitrary Turing reducibility to infer coarse
reducibility without checking descriptions.

## Prescribed infimum (Theorem 9.1)

Apply the main theorem relative to Z, then interleave J(Z) with A and with B.
Every coarse description recovers Z from its even positions; every coarse
representative computes such a description. No representative is computable in
Z, since its odd projection would give a Z-computable coarse description of A.
The two displayed representative degrees meet at Z, so the entire spectrum's
infimum is exactly Z and is missing. The coarse relation remains unrelativized.

## Sparse-cover obstruction (Proposition 7.3)

A relative computable density-zero cover of disagreements would let both
oracles compute their common values off that cover (zero on the cover). The
relative minimal-pair property would make this a Z-computable coarse description
of A, contradiction. Allowing finitely many uncovered disagreements does not
help: the finite exceptions can be added to the cover as constants.

## Verification status

- Conventional proofs: included in full.
- Actual finite tests: run successfully; see `checks/results.json`.
- Infinite oracle construction: not run as an ordinary computable algorithm.
- Proof assistant: not formalized or compiled.
- Independent review: not obtained.
- Novelty: not established; the basic negative answer follows from HJKS (2016).
- Effective-dense analogues and prescribed arbitrary spectra: not proved.
