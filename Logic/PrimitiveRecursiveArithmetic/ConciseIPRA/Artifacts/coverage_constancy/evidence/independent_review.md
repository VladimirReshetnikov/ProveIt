# Independent review of the coverage/constancy model

Reviewed against the core-proof draft (subsequently incorporated into
`report.tex`) and repository snapshot
`95d3dd192e97a19bd4f8783c764331ec41126264`.

## Verdict

The mathematical argument is sound as a written model-theoretic proof. It is
not a Lean/Rocq formalization, and finite numerical simulations cannot verify
its essential nonstandard step. It supplies a negative result for the proposed
constancy replacement, not a positive axiomatization below the current checker
frontier.

## Points requiring care, and why they are satisfied

1. **The staged signature does not require a universal PR evaluator.** For each
   fixed finite body, its interpretation on the PA-definable ambient domain B
   is a fixed primitive-recursive map with the parameter c. Its iteration is
   another fixed primitive-recursive map. This construction is performed
   externally, one finite term at a time. No target-language variable ranges
   over all function descriptions.

2. **The actual carrier M is external, but is a substructure for every fixed
   operation.** The invariant proved in ambient PA says that a branch output
   has the label of an input branch and rank at least that input's rank. The
   iterator case needs an internal induction over its entire iteration count;
   a merely external finite induction would not suffice. The stated proof
   supplies the internal induction. Nonstandard-ranked inputs therefore cannot
   produce standard-ranked branch outputs.

3. **Intermediate states, not only final outputs, stay in M.** Apply the same
   preservation invariant at every count i in A, or use the term with main
   counter (i,0). This makes later use of a premise holding only throughout M
   legitimate along internally long trajectories.

4. **Constancy does not silently quantify over external maps.** It is proved
   for maps denoted by finite term templates, which extend to arithmetic-
   definable maps on B. On the main chain the premise is an internal universal
   equation, so PA induction yields constancy. Starting at a nonstandard branch
   rank n, every point of the internally indexed interval from n to c is still
   nonstandard-ranked and belongs to M. Therefore the external assertion that
   the target premise holds at all M-points really entails that A satisfies
   the bounded arithmetic universal statement needed for the second induction.
   No formula defining the external set M is used.

5. **Arbitrary logical contexts are allowed.** Fix one assignment satisfying
   the context in M. Freshness of the rule variable leaves that context true
   for all its possible values. Only equations between term values are then
   transferred into the ambient arithmetic argument; the context itself need
   not be interpreted as a formula of A.

6. **Coverage is genuine.** A branch rank n is nonstandard, so n-1 is also
   nonstandard and is below c. Its predecessor remains in M. Main nonzero
   points have their main predecessors. This is precisely the point at which
   the earlier standard three-copy construction failed.

7. **Successor really merges distinct points.** Both (c-1,0) and (c-1,1) belong
   to M, are different, and have successor (c,0). The clock equation fails at
   every branch point, while its induction base and step are derivable directly
   from the two computation equations.

8. **The optional laws use no discarded points.** For body extensionality,
   compare the two internally indexed trajectories using the pointwise
   equality premise on the first trajectory, whose states lie in M. For
   fusion, use its premise on H^i(a), also in M, and induct internally on
   F(H^i(a))=K^i(F(a)). Fixed-point preservation and seed shift are simpler
   instances of the ordinary internal iteration laws.

9. **Automorphisms preserve the whole signature.** A swap of two unused
   positive branch labels is primitive recursive on B, commutes with successor
   and the actual equality test, and preserves rank. The conjugacy argument for
   iterators is an internal PA induction on the count. Thus the swap respects
   every staged function symbol, not just the displayed primitive maps.

10. **Finite parameters and quotient interpretations do not avoid the
    obstruction.** Collect all source parameters, representatives of reverse-
    interpretation parameters, and return-map parameters. Two positive
    standard labels can be chosen outside this finite collection. Their swap
    is a nontrivial involution fixing the parameters. Interpretations transport
    it to an involution of an iPRA model; the parameter-free definable linear
    order makes that involution trivial. The definable return isomorphism
    forces the induced automorphism map to be faithful, a contradiction.

## Novelty boundary

The current article already proves constancy plus a successor-comparison law
equivalent to iPRA, already identifies that comparison law with successor
injectivity, and already supplies a standard three-copy model without coverage.
Those are inherited results and must not be advertised as new.

The new part is the ambient nonstandard arithmetic construction, the deletion
of standard-ranked branch points while retaining every internally needed orbit,
and the resulting coverage-preserving countermodel. The article's conclusion
to its scalar-constancy obstruction explicitly says that it does not address
the scalar interface with coverage. Searches of the inspected article and the
five incoming packages found no existing copy of this branch construction.
This is a relative novelty check against the supplied repository, not a claim
of priority over all mathematical literature.
