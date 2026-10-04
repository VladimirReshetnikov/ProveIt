# Source and proof audit

Prepared 4 October 2026.

## Sources actually used

1. Elliot Glazer, *A Topological Tennenbaum Theorem*, arXiv:2311.13699 (2023).
   https://arxiv.org/abs/2311.13699
   This supplies the research connection to Borel regularity and topological
   arithmetic. None of its remaining open questions is claimed solved here.

2. Khodr Shamseddine and Martin Berz, *Analysis on the Levi-Civita field, a brief
   overview*, Contemporary Mathematics 508 (2010), 215–237.
   https://www2.physics.umanitoba.ca/u/khodr/Publications/RS-Overview-offprints.pdf
   This supplies background and standard terminology. The field and completeness
   facts needed here are independently proved in the article. The article's
   coefficient Borel structure is explicitly defined; it is not the special
   Levi-Civita-valued measure/integration theory discussed in that literature.

3. Salma Kuhlmann and Mickaël Matusinski, *Hardy type derivations on generalised
   series fields*, arXiv:0903.2197v4 (2012; manuscript dated 2011).
   https://arxiv.org/abs/0903.2197
   This provides the existing strong-summation derivation background. Its
   generalized-series setting and rank conventions must not be identified
   without qualification with the rational rank and left-finite supports here.

4. Christian Rosendal and Luis Carlos Suarez, *Aspects of automatic continuity*,
   arXiv:2406.12143v2 (2025).
   https://arxiv.org/abs/2406.12143
   This provides context for classical Polish-group automatic continuity.
   The particular Borel additive functional lemma is proved in full here.

5. Olivier Bournez and Quentin Guilmant, *Surreal fields stable under exponential
   and logarithmic functions*, arXiv:2201.08199 (2022).
   https://arxiv.org/abs/2201.08199
   This provides a modern primary-source connection to the normal-form view
   of surreal subfields. No exponential-closure assertion about L_Gamma is
   inferred from that source.

6. ProveIt root README and Algebra/SurrealNumbers/README.md, read through the
   GitHub connector from the public main branch on 4 October 2026.
   https://github.com/VladimirReshetnikov/ProveIt
   https://github.com/VladimirReshetnikov/ProveIt/tree/main/Algebra/SurrealNumbers
   The initial inventory returned Git TREE identifier
   3c25fbb5515748040decb853139ed39543885b90 (not a commit identifier).
   A later main-branch inspection returned COMMIT
   4f03443e018a4c882d288b950928943b7d92892a and tree
   d4b916d25a8f3e102040d85df1e2bc46ae89792e: main was advancing during preparation.
   The article therefore uses dated documentation citations, not an assertion
   that every source read came from one immutable pinned commit.

## Core proof dependencies

- Borel additive real-valued functionals on countable real products are
  continuous and depend on finitely many coordinates: full Baire-category
  proof supplied.
- Generic-support lemma: a countable intersection of dense open nonvanishing
  sets prevents cancellation from concealing a forbidden union of supports.
- Uniform matrix cutoff: escaping input columns give a left-finite slice;
  generic support plus finite rows yields a contradiction.
- Derivation bound: integer translation of every exponent into one bounded
  interval converts valuation continuity into one common lower bound on
  logarithmic values. Divisibility of Gamma is not assumed.
- Exact coefficient continuity: output row lambda is
  d_h(lambda) - d_h(h), after reindexing h = lambda - gamma.
- Wild derivations: an elementary factorial-gap proof yields transcendence;
  extending the resulting derivation uses a transcendence basis and separability.
- Exponential/logarithm: positive gain makes each output-cutoff calculation
  finite; a polynomial identity in a scalar parameter proves log is a derivation.

## Boundaries and counterexamples checked in the text

- The full additive Borel group is not Polishable when Gamma is nonzero.
- Coefficient topology is different from valuation topology.
- Borel derivations need not be coefficient-continuous.
- Arbitrary algebraic derivations need not preserve formal sums or be Borel.
- In infinite rational rank, a common lower bound on monomial logarithmic
  values is necessary; arbitrary tuples are not allowed.
- Left-finite supports are not all well-ordered Hahn supports.
- The surreal interpretation is a set-sized coded subfield, not the proper
  class of all surreal numbers.

## Novelty boundary

The supplied arguments are original derivations in this response, but that
fact does not establish historical originality of the resulting statements.
The targeted literature search did not settle priority. Some keyword searches
returned irrelevant results; search coverage must not be treated as exhaustive.
Specialist review should concentrate on the exact additive matrix theorem,
the uniform logarithmic bound in arbitrary countable rational rank, and the
finite-support/diagonal coefficient-continuity criterion.

Finite-rank Euler formulas, classical residue obstructions in Laurent-series
normalizations, and formal filtered exponential identities should not be
advertised independently as new inventions.

## Computational boundary

The exact-rational script passed 1,640 deterministic finite checks. It is
not a proof assistant and does not check Baire category, infinite-support
classification, or novelty. No Lean file or claim of a kernel-checked proof
is included.
