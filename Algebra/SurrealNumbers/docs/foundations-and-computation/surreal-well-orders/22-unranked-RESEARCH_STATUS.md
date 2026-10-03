# Research status and proof boundaries

## Extensions developed in this manuscript

1. An exact topological invariant table for every fixed enumeration length of a
   rich infinite alphabet, including the transitions at mu+2 and mu+3.
2. A residual-cylinder identity, first-disagreement cofinality formula, and endpoint
   character transfer; exact character spectra for finite tails and tail omega.
3. The finite factorial-block topology, dense isolated points for finite tails of
   size at least three, and its one-step Cantor–Bendixson derivative.
4. Recovery of ordinal prefix height from unranked cylinder incidence in the ambient
   class set theory, using set-sized ancestor orders.
5. A proper-class crossed-node criterion for an injective global branch, with
   label coverage for exhaustive branches.
6. An elementary pair-swap trace decoder and faithful recovery of same-set class
   realizations with shared baseline and global enumeration parameters.

These are extensions relative to the inspected repository guide and two prior
continuation manuscripts. No claim of historical priority is made.

## Inherited inputs and mechanisms, explicitly credited

- The sign-sequence representation and small-cut separation property.
- General-alphabet cardinality, universality, and ordinal spectrum.
- Supported-prefix completion and the surreal-sized dense core.
- The finite-residual mechanism behind adjacency.
- Direct common-head comparison of raw class well-orders.
- Global-choice issues, elementary diagonal obstructions, and the full-model
  raw-to-set-like nonembedding phenomenon.

The article re-proves the finite-residual, supported-prefix, raw-comparison, and
embedding mechanisms used in its new arguments. Its fresh separator lemma uses
the previously established sign-cut theorem. It does not rely on the earlier
minimal-stratum cut spectrum to prove the new all-length topology table.

## Logical levels

- The set-alphabet and fixed-stratum results are in ZFC.
- Supported codes, unranked branch recognition, and trace decoding are in GBC with
  fixed global-choice parameters. They use elementary comprehension and set-valued
  constructions, not class-valued elementary transfinite recursion.
- Comparing complete available class realizations is a metatheoretic statement
  about models sharing the same set universe and parameters.
- The inaccessible-universe example is conditional on an inaccessible cardinal in
  the external metatheory; that hypothesis is not used for the set-alphabet results.

## Limitations

No full classification of nonprincipal cuts at arbitrary nonminimal lengths,
no complete automorphism-group classification, and no reconstruction from the
bare linear order are claimed. Height recovery is definability in the ambient
set/class theory, not an assertion of first-order definability in the pure
incidence language alone. Fixed coding parameters remain essential hypotheses
of the class-realization comparison as stated.

No new Lean proof was produced or checked. Source inspection identifies actual
existing foundational declarations but does not substitute for a Lean build.
The manuscript is AI-assisted and unrefereed. Its ordinary proofs are provided
for scrutiny, not presented as independently certified results.

## Executable and document checks

The Python suite passed 1,388,197 assertions. It tests finite comparisons,
residual cylinders, unranked finite injection-tree inclusion and height,
pair swaps and trace decoding, and a forced-last-label counterexample.
It does not test cardinal arithmetic, infinite cofinalities, class comprehension,
or the class-realization theorem.

The PDF was rendered for visual inspection. The final LaTeX log has no warnings,
overfull boxes, undefined references, or undefined citations. A programmatic
check found no gross text-boundary violations or replacement characters.
