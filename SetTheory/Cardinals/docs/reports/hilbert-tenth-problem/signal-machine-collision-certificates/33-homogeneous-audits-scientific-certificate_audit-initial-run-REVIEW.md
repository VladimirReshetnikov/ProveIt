# Independent native Diophantine-certificate audit

Date: 2026-10-04 UTC

## Verdict

PASS within the assigned scope. No mathematical or literal-DAG defect was found in PROOF.md §8–8.2 or either certificate JSON. The equivalence to physical realizability is conditional on the realization theorem in §1, which this audit does not independently prove.

The fresh checker passed 737 named assertions. It was written independently, displayed and inspected before execution, and uses only the Python standard library, exact integer coefficients, sparse polynomial expansion, and a permutation-form determinant. The author's static_algebra.py was neither opened nor executed. No upstream scientific program, simulator, saved physical schedule, or Lean was executed. JSON evidence was consumed only as inert data. Consumed source-file SHA-256 values are recorded in REPORT.json and were unchanged after checking.

## Mathematical certificate

For a signed integer 3-by-3 matrix K, the displayed F is exactly the sum of these five squared residuals:

1. (Kg)_1-h_1
2. (Kg)_2-h_2
3. (Kg)_3-h_3
4. det K-(2b-3)d
5. (b-1)(b-2)

The eight positive integer witnesses are exactly g_1,g_2,g_3,h_1,h_2,h_3,b,d. If F=0, nonnegativity of integer squares makes all five residuals zero. The gate forces b=1 or b=2; positive d then forces det K=-d or det K=d, respectively. Thus det K is nonzero and Kg=h>0 with g>0.

Conversely, if det K is nonzero and there is real g>0 with Kg>0, the feasible set is open and has a rational point. Multiply that rational vector by a common positive denominator. The resulting g and h=Kg are positive integer vectors. Choose d=abs(det K), and b=1 for negative determinant or b=2 for positive determinant. These values make all five residuals vanish. This proves the exact arithmetic equivalence for all K, beyond the finite fixtures.

For q>0, det(K/q)=det(K)/q^3 and (K/q)g>0 is equivalent to Kg>0. Thus a fixed or optional external positive denominator imposes no extra polynomial condition and does not add a witness. Its positivity is a domain assumption, not a fact enforced by F.

## Exact degree

Joint total degree, counting matrix-input variables and witness variables, is exactly six. The five residual degrees are 2,2,2,3,2. In the signed polynomial, k11^2*k22^2*k33^2 has coefficient 1. Therefore degree six cannot cancel. The exact expansion has 71 nonzero monomials.

After k_ij=a_ij-c_ij, the coefficient of a11^2*a22^2*a33^2 remains 1, and the exact expanded polynomial has 1,166 nonzero monomials and total degree six. Every integer k has a positive-pair encoding, for example a=max(k,0)+1 and c=max(-k,0)+1.

The stated degree is a joint input-and-witness degree; specializing a matrix first need not leave degree six in the witnesses alone. The packet's stated accounting is joint and is correct.

## Literal DAG verification

Signed JSON:

- Exactly nine external signed matrix leaves and the eight positive witness leaves: 17 variable leaves
- Constants exactly 1,2,3
- 26 multiplications, 11 additions, 11 subtractions: 48 operations
- Output v48
- Row residuals v06,v12,v18; determinant/sign residual v36; gate residual v39

Positive JSON:

- Exactly eighteen external positive matrix leaves and the same eight positive witness leaves: 26 variable leaves
- Constants exactly 1,2,3
- 26 multiplications, 11 additions, 20 subtractions: 57 operations
- Output v57
- Row residuals v15,v21,v27; determinant/sign residual v45; gate residual v48

Every node was schema-checked; every operand is an earlier node, one of the exact expected leaves, or an allowed constant. Node identifiers are unique. Every node contributes to the final output; there are no dead gates. Exact polynomial expansion of each residual and each whole graph agrees with an independently constructed permutation-determinant formula. The positive DAG is literally the nine entry differences followed by a node-renamed copy of the signed DAG. The denominator is absent from both graphs.

These are integer expression graphs with unrestricted intermediate values. Their nodes are not additional existential witnesses and do not describe a physical collision schedule. Positive input leaves do not imply positive intermediate subtraction outputs. The two operation counts apply only to native gap-coordinate matrix inputs and include multiplication by 2 and one multiplication per square. They do not include centered-coordinate conversion and do not claim minimality.

## Centered-coordinate conversion

The displayed S and B were checked exactly:

- SB=BS=9I
- det S=det B=27
- det(SMB)=729 det M identically in all nine entries of M

Since S=3H and B=3H^-1, H(M/q)H^-1=SMB/(9q). The centered polynomial is exactly the native polynomial under substitution K=SMB; its determinant residual is therefore 729 det M-(2b-3)d. No extra alias variables or witnesses are introduced. It has nine signed matrix inputs, eight positive witnesses, five residuals, joint degree six, and 269 expanded monomials. Its m11^2*m22^2*m33^2 coefficient is 729^2=531441. The packet correctly asserts no literal centered-DAG operation count.

## Evidence fixtures and scope

All four provided Diophantine fixtures, identity, swap, positive, and escape, have the exact expected input interfaces, valid positive witnesses, matching positive-pair encodings, five zero residuals, and zero output in both graphs. Scaling g,h by 2,3,17 leaves each fixture valid. Changing h1 by +1 or d by +1 produces F=1; replacing b by 3 produces F>0. These are supplementary regressions, not substitutes for the general algebraic argument.

Any valid tuple gives infinitely many distinct positive witness tuples by scaling g,h together. Thus no finite-fold interpretation is available. The represented property is the specific local one-pass, full-section realizability property conditional on §1; it does not establish infinite repetition, a universal machine, undecidability, minimal witness counts, or optimal arithmetic/physical resources.

## Files

- check_certificate.py: fresh independent checker
- REPORT.json: all 737 named assertions, exact ledgers, fixtures, and source/checker hashes
- RUN.txt: captured checker summary
- REVIEW.md: this review
