# Principal reconciliation decisions

## Keep three notions of computability distinct

The structurally computable field uses hereditary effective Conway-cut
presentations. Its real trace is the hyperarithmetic reals, according to the
attributed structural classification. It is not the same notion as ordinary
numerical computability of real coefficients.

The two numerical fields are also distinct. The Puiseux field `P_c` requires one
finite ramification denominator for each series. The effective left-finite field
`L_c` permits unbounded rational denominators but requires a computable complete
finite candidate list below every rational cutoff. Both have real trace exactly
the ordinary computable reals. The report proves `P_c` is a proper subfield of
`L_c`; no unproved structural-to-numerical name converter is presumed.

## Reconcile completeness by stating the field and modulus

A computable valuation-Cauchy sequence can leave `P_c` even when a computable
stabilization modulus is supplied. With such a modulus, the `L_c` representation
constructs the limit. Without a computable modulus, even a uniformly computable
sequence of rational polynomials may have a noncomputable limit. A separate
coefficientwise real-Cauchy limit theorem is retained; it is not valuation
convergence. Thus none of the different completeness claims is used to contradict
another claim about a different field or different limit data.

## Preserve complementary proofs rather than repeat them

The Hensel/valuation proof of real closedness is retained for `L_c` and `P_c`.
The Newton–Puiseux proof for `P_c` is retained independently, including the full
finite-jet lemma that turns a finite branch seed into one coefficient algorithm.
Merely knowing that every coefficient individually is a computable real would
not justify uniform computability of the coefficient sequence.

## Correct a genuine omitted hypothesis

A's original TeX lines 1083–1093 state that every real surreal root of a polynomial
over `L_c` stays in `L_c`. The zero polynomial is an immediate counterexample to
the statement as written. The merged corollary explicitly requires a **nonzero
polynomial**. C already includes that restriction.

## Retain the strongest compatible obstructions

The report keeps the left-finite decidable-support convolution counterexample,
the distinct singleton-convolution-fiber example, and the sharp one-halting-oracle
coefficient upper bound. An oracle-computable convolution output need not be an
ordinary computable product. By contrast, a halting oracle can select finite
leading data after which the inverse or square-root program is ordinary.

Positive square-root failure and branch-independent quadratic-root failure are
both included, as are the modulus obstruction, the full structural-validity
classification, and the signed computable-order example preserving any c.e.
Turing degree. All index-complexity statements specify validity promises.

## Integrate results unique to one report

The merged development also retains both finite-rank towers, coefficientwise
limits, finite-jet branch certificates and worked examples, residue/kernel/image
identities, the vector-space quotient by the derivative image, an unsolvable
in-workspace differential equation, and the oracle-relative Puiseux hierarchy.
The same explicit degree-encoding proof is supplied for the left-finite hierarchy.
The derivative-image quotient is a vector-space quotient, not a field quotient.

The left-finite construction answers C's stated request for a real-closed support
enlargement beyond bounded Puiseux denominators. Research questions are updated
to concern support classes beyond this already established case.

## Provenance and limitations

Appendix B provides original source-line locations and a topic crosswalk. The
original TeX manuscripts are not redistributed; `data/provenance-manifest.json`
records their input hashes and line counts. The three original verification
programs are retained unchanged under `code/`. Bibliographic status and
repository scope are documented explicitly.
The three original suites and a new cross-model suite pass, but no finite check
is presented as a proof of the infinite theory. No new Lean verification or
literature-wide novelty claim is made.
