# Independent mathematical and reference-code review

Reviewed by the framework-mathematics subtask. Snapshot reviewed: current files under `deliverable/ipra_presentations_to_witnesses`, 15 November 2026 client date. No staged root paper section was changed by this review.

## Files reviewed in full

- `python/certified_points.py`
- `python/verify_points.py`
- `paper/sections/02_framework.tex`

The existing `validation/point_enumeration_checks.json` was inspected as recorded finite-run evidence. The universal theorems are justified by the written proof, not by that file. The reviewer had independently checked all eight polynomial residual identities and the fifteen-candidate elliptic example with exact SymPy arithmetic before reading the package's verifier.

## Outcome

No mathematical soundness or completeness error was found in the reviewed reference enumerator or its featured certificates. No logical error was found in the framework section's fusion, relational simulation, or finite reconstruction claims.

## Enumeration implementation

1. `check_certificate` checks both the unit identity and every multiplication residual by exact sparse polynomial equality. Matrix dimensions, polynomial arities and witness dimensions are checked. There is no oracle for ideal membership: the input must supply the coefficient-polynomial witnesses.
2. The orientation agrees throughout: evaluation vectors are rows, and each matrix column represents multiplication of one generator. The radius uses maximum absolute **column** sums, as required by the maximum-component proof for row eigenvectors.
3. `denominator_bounds` takes an exact common denominator using lcm; multiplying every Fraction entry by this integer gives an exact integer. The use of `int` at that point is exact because divisibility is established by construction.
4. `enumerate_rational_zeros` checks the certificate before computing a grid, enumerates all mixed-radix tuples, and tests the original equations exactly. Fixed positive coordinate denominators make the map from integer grid tuples to rational tuples injective, so the output contains no duplicate rational tuples.
5. `primitive_evaluation_witness` is appropriately a diagnostic for retained points. It is not the mathematical source of completeness and does not need to be invoked to justify the grid.
6. The checker intentionally does not require commuting matrices or independent generators. Both omissions agree with the theorem. The supplied redundant `(1,x,x)` fixture really uses noncommuting matrices and valid polynomial witnesses.
7. The unit supplied by the linear combination of `(2,3x)` is valid; no generator need be literally 1. The localization fixture's identities for `(x,y,t)=(1,0,1)` were checked algebraically. The original unlocalized equations have a positive-dimensional component; the equation `tx−1=0` removes that component, so the fixture's name and interpretation are accurate.
8. Repeated roots, nilpotent quotient, no rational roots, zero radius, and differing rational denominators are covered by meaningful featured cases. The rejection checks cover false action data, an invalid unit, a missing residual witness and dimension mismatches. The test descriptions correctly limit their claims to finite implementations.

## Coverage clarification

The human paper proves a general PR constructor from separated monic annihilator identities. `certified_points.py` implements the univariate companion special case and explicit supplied multivariate certificates, but not the general separated-annihilator constructor. Descriptions should retain this distinction. It is not a mathematical gap because the general constructor is completely specified and proved in the paper; it is a difference in executable coverage.

The reference API uses Python finite data and Fraction, not a byte-level canonical natural-number coding of every malformed input. Its use as an executable diagnostic is correctly distinguished from a completed `Prf PRAAx` certificate checker and from formal proof of all-input program correctness.

## Framework section

- The fusion proof uses a quantifier-free equality as its induction invariant, with initial state and parameters free. The construction uses supplied local derivations and syntax operations, not semantic reflection.
- The relational simulation theorem likewise preserves quantifier-freeness after substituting the current iterates. Putting validity and arithmetic guards in the relation prevents applying local laws outside their domain.
- The repeated-squaring corollary is valid without associativity; identifying its recursively defined values with ordinary powers is explicitly separate.
- The finite reconstruction theorem does not mistake a grid containing an observable image for the exact image. Its finite preimage-list hypothesis is sufficient and necessary for the asserted enumeration method.
- The difference between a schema for fixed PR program syntax and a fixed polynomial-data evaluator is correctly maintained. The diagonal argument against a total universal PR evaluator is valid.

Two editorial suggestions were sent to the root agent:

1. The reconstruction proposition introduces `C(q,p)` but never uses it; delete it.
2. The sentence about Boolean-fold equivalences can explicitly identify permitted induction: soundness keeps an arbitrary index free, and completeness under a fixed bounded-universal premise uses the guarded quantifier-free invariant `t≤B → A(a,t)=1`. This is a clarification, not a counterexample to the stated claim.

## Stronger scope obstruction added to the mathematical draft

The paragraph “A stronger algebraic obstruction for a whole plane curve” was added to `research/framework_math.tex`, immediately after the enumeration scope warning.

If F is monic of positive degree in Y, then Q[X] injects into Q[X,Y]/(F): a nonzero multiple H·F has positive Y-degree and cannot equal a nonzero polynomial in X alone. A size-D finite spanning certificate would reduce 1,X,...,X^D to D-dimensional coefficient vectors, producing a nontrivial rational dependence and contradicting that injection. Thus such a full-coordinate certificate is impossible for the whole monic plane-curve ideal, even if the rational point set is finite or empty. The empty rational curve `Y²+X²+1=0` illustrates the distinction.

This is stronger and more accurate than saying only that an infinite rational point set cannot admit the certificate. It prevents the new method from being mistaken for a certificate-search strategy that must succeed whenever Faltings happens to imply rational finiteness.

## Integration follow-up

After this review, the general constructor was implemented in `python/annihilator_code.py`. Its recorded run accepts seven constructed certificates, verifies 37 action identities, and rejects five invalid inputs. This closes the executable-coverage difference identified above. The two editorial suggestions were incorporated into the final framework section.
