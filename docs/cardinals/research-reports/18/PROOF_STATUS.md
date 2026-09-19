# Mathematical status and dependency audit

## Claimed deductions in this report

1. **Cofinal-orbit rigidity (Theorem 5.3).** An ultraexacting lambda admits a finite-difference class q for which every nonempty OD_{V_lambda;q} family of short cofinal sets has cardinality at least lambda. This lower bound is attained by q.
2. **Simultaneous trace dichotomy (Theorem 6.1).** Every OD_{V_lambda;q} subset of D_lambda has trace on q of size zero or lambda.
3. **Small families (Theorem 6.4).** The same trace dichotomy holds for every member of a definable family of fewer than lambda subsets of D_lambda, even when its members are not individually definable.
4. **Quotient non-compression (Theorem 7.2 and Corollary 7.3).** A small definable family of homomorphisms must send the distinguished input class into target classes of size at least lambda. In particular, targets all of whose classes are smaller than lambda are excluded.
5. **Preserved-enrichment obstruction (Theorem 8.1).** A self-embedding of a transitive inner model containing all of V_{lambda+1}, fixing lambda, and having critical point below lambda cannot preserve a lambda-thin complete section.

The precise hypotheses, including parameter conventions and ambient cardinalities, are in the PDF. No result assumes a common bound below lambda for the sizes of all short sets or all target equivalence classes.

## External dependencies

The new obstruction arguments require the local set-sized Kunen inconsistency and the standard characterization giving ultraexact witnesses at arbitrarily high sufficiently correct heights. The later consistency calibration additionally imports the I0/ultraexacting equiconsistency and the forcing result preserving ultraexactness while making V_lambda a subset of HOD.

The supplied synthesis's Prikry-forcing and cover-exacting consistency claims are not used as proof inputs.

## Sensitive steps checked explicitly

- A small family of short sets is not flattened until its fixed order-type spectrum is known to be bounded.
- Fixedness of a family is not confused with pointwise fixedness of its members.
- The original ordinal parameters are not presumed fixed. Uniform reflection and minimization of parameter rank produce a fixed least counterexample.
- Ultraexactness, not ordinary exactingness, puts the critical sequence in the elementary submodel.
- The quotient class and the full quotient are not treated as elements of V_{lambda+1}.
- The inner-model family argument uses an absolute order-type test, not an internal test for externally small cardinality.
- A formal consistency assumption is not strengthened to the existence of a transitive model.

## Not established

There is no proof here that ultraexacting cardinals or I0 are inconsistent. Optimality of ultraexactness as a hypothesis is not established. The countable-family question for selectors on finite subsets of the quotient is not settled; such selectors differ from transversals inside equivalence classes. Nor are the strongly-compact/cover-exacting or global cardinal-preserving embedding problems resolved.

These are unrefereed, non-formalized proofs. The literature check does not establish first-publication priority.
