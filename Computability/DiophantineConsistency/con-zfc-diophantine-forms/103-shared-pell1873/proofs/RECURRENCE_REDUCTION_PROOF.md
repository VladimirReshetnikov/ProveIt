# Three Pell index certificates replaced by exact recurrences

## Result and inherited scope

The refined common-certificate compiler encounters forty positive power calls and nineteen distinct exponent expressions. Three of these expressions differ from already occurring ones by one or two. Instead of introducing another private finite Pell-index certificate for each, compute its Pell coordinates from the earlier coordinates by the exact recurrence.

With the independently supplied signed encoded-row source simplification, the retained domain-inference rules, and the final signed-index theorem, the released literal polynomial has **1,873 unrestricted integer variables, degree four, 1,468 quadratic residuals, 77,523 collected monomials, and coefficient height 1,323,565,948,780,873,728**. There are 245 semantic inputs, of which 146 are constrained nonnegative and 99 have unrestricted domains; 1,153 nonlinear wires, 37 affine-support wires, and 438 nonnegativity witnesses complete the variable count. These are exact metrics of the emitted polynomial, not a global optimality claim.

The implementation chronology separates the two arithmetic improvements. The recurrence optimization alone reduced the source-optimized common-certificate polynomial from 2,042 variables to 1,969, a saving of 73. It removed twelve natural semantic inputs and their thirty-six guard witnesses, as well as net twenty-five nonlinear wires. That intermediate equation had 1,500 residuals, 77,971 monomials, 178 explicitly nonnegative semantic slots, 67 unrestricted slots, and 534 guard witnesses. The subsequent signed-index theorem removed the two comparison-coordinate sign requirements for each of sixteen seeds: 32 guards and their 96 extra witnesses. This gave the final 1,873-variable equation, with the counts stated above. The recurrence proof itself is unchanged; it composes with the signed-index theorem, refined batching theorem, and inherited source/compiler calibration.

## Exact exponent relations

Write H for the actual factorial scale argument and N for the positive row-count parameter. The actual nineteen exponents contain

| Derived exponent | Existing seed exponent | Difference |
|---|---|---:|
| H+2 | H | 2 |
| N+2 | N | 2 |
| N+1 | N | 1 |

The emitted metadata also records the actual node identifiers and tags, but the builder does not hardcode them. It computes exact affine forms over nonlinear DAG atoms and checks that the two forms differ by the indicated constant. This accounts for the nested representation of H without treating expected semantic identities as syntactic equalities.

Sixteen exponent classes remain seeds. Their main coordinate pairs remain natural, while their comparison pairs use the signed finite-index theorem proved in `SIGNED_INDEX_THEOREM.md`. All three derived pairs receive no additional semantic coordinates, domain guards, or Pell norms.

## Universal recurrence identities

Let A>=2 and D=A^2-1. The Pell coordinates satisfy

    X_A(k+1)=A X_A(k)+D Y_A(k),
    Y_A(k+1)=X_A(k)+A Y_A(k).

For a second step it is cheaper to use

    X_A(k+2)=2A X_A(k+1)-X_A(k),
    Y_A(k+2)=2A Y_A(k+1)-Y_A(k).

These are integer polynomial identities, and no division occurs. The second-order expression is identically equal to

    X_A(k+2)=(2A^2-1)X_A(k)+2A(A^2-1)Y_A(k),
    Y_A(k+2)=2A X_A(k)+(2A^2-1)Y_A(k).

For the N family, the N+1 pair is shared by the N+2 construction. The H+1 pair is an ordinary intermediate arithmetic value used to produce H+2. Its wires are included in the exact count.

Multiplication by A+sqrt(A^2-1), or direct expansion, proves the first recurrence preserves X^2-DY^2. The second-order formula follows from the first and its preceding step. The independent verifier checks these free-polynomial identities and checks that every emitted derived pair is exactly the stated polynomial in the actual seed pair and common A.

## Soundness and completeness

First apply the refined batching proof, using the signed-index theorem, to each of the sixteen seed index certificates. This identifies each seed pair with the true pair at its supplied positive exponent. The exact recurrence identities then identify each derived pair with its true Pell pair at H+2,N+2,N+1. In particular its coordinates are natural, its ordinate is at least its exponent, and its abscissa is positive. These properties follow from the now-proved Pell identities; no additional domain guard is necessary for a deterministically computed wire.

The power criterion is consequently available for every one of the forty calls, including calls whose exponent uses a derived pair. The common product P need contain only the sixteen seed ordinates: the divisibility Y_j^2|V and the common CRT modulus are required only when invoking the finite-index criterion. Derived pairs need no such criterion.

Conversely, the true Pell pairs chosen in the batching completeness proof automatically satisfy the recurrence formulas. Discard the three redundant private certificates and use their computed pairs in the power congruences. The common auxiliary norm and CRT construction apply to the product of seed ordinates. No cofinality, positivity, or source choice changes.

Thus replacing the three private certificates preserves existence in both directions. After quadratization and nonnegativity representation the final polynomial retains the same no-zero/Con(ZFC) interpretation through the inherited ordinary proof chain.

## Exact verification and limits

`verify_recurrence.py` imports neither the builder nor its sparse-polynomial utility. It independently:

1. checks the complete free-polynomial first/second-step identities;
2. checks all three actual affine exponent differences;
3. checks the complete emitted X/Y recurrence subcircuits under the exact A/seed cuts;
4. checks that P is precisely the product of all sixteen seed ordinates;
5. expands every quadratic residual square, collects every integer coefficient, and compares the entire result with the delivered sparse polynomial;
6. checks exact degree, all-variable liveness, coefficient height, and a changed-coefficient rejection control.

The scope is exact recurrence and polynomial assembly. The separate source and batching proofs are still needed for the semantic consistency interpretation. This package supplies ordinary proofs formalizable in ZFC; it does not claim a new Lean or object-language ZFC proof certificate.
