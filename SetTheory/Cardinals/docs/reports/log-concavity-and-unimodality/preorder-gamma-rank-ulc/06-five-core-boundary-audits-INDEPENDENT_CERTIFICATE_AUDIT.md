# Independent audit: rank-four faces of five-core universal-sink polynomials

## Four active tails: PASS

The standalone standard-library checker independently reconstructs Boolean endpoint supports using explicit injection witnesses. The tail set is restricted to vertices 0,1,2,3; vertex 4 remains eligible as a head. Every feasible endpoint pair contributes once, regardless of how many matching witnesses it admits. It forms the first three gamma coefficients using the stated rational sink moments and scales G_k=k! gamma_k.

The exact target is

2G2²−3G1G3 = 8(γ2²−(9/4)γ1γ3).

The four-active collection passed in full:

- 3,044 representative graphs
- 212,319 positive rational squares, all binomial
- 158 empty certificates, exactly the 158 coefficientwise nonnegative targets
- All exact remainders coefficientwise nonnegative, including exponents absent from targets
- 1,859,726 positive remainder coefficients in total; no identically zero remainders
- No u4 exponent in any target, multiplier, or squared polynomial
- Complete disjoint S4-orbit coverage of all 2^16=65,536 loopless relations from four active tail roles into five core head roles

The full pointed catalog contains 173 reflexive-transitive representatives under S4 fixing the head-only vertex. This count concerns the pointed, row4-zero catalog and should not be confused with the 139 S5 classes of unrestricted five-core preorders.

This certificate proof applies on the entire face u4=0, including further zero activities. Removing the outgoing row of vertex 4 changes no coefficient because its tail activity is zero; it does not remove its head role. Relabeling covers every face with at least one zero core-tail activity.

## Sink-moment scope review

For a finite nonnegative sink vector, set p_r=Σw^r, A=√p2, and B=p1−A. Both A,B are nonnegative. Newton's identities give E1=A+B and E2=AB+B²/2. Since p3≤p2^(3/2),

E3≤AB²/2+B³/6.

The coefficient of E3 in γ2²−(9/4)γ1γ3 is −(9/4)γ1 e3≤0. Therefore proving the substituted upper-boundary polynomial nonnegative suffices for the original inequality.

When at most four sink-head activities are positive, Cauchy gives p1²≤4p2. Thus B≤A, and C=A−B≥0. Substituting A=B+C gives exactly

E1=C+2B,
2E2=2BC+3B²,
6E3≤3CB²+4B³.

This nonnegative (C,B) cone is a sufficient enlargement of the finite-at-most-four-sink moment region. No sharpness, exact finite realizability, or converse claim is made. The zero vector is included.

## Actual-degree scope

The identity γ5=e5 E5 means that γ5=0 implies either at least one zero tail activity or at most four positive sink-head activities. The first branch is covered by the completed four-active certificate proof. The second requires the separate four-sink certificate collection. The two ordinary last-gap proofs and the actual-degree first comparison are separate logical inputs. These certificates alone do not prove the stronger normalization at actual degree three.

## Reproduction

Run:

python check.py four-active /path/to/data /path/to/four-active-receipt.json 4

For the second collection, when complete:

python check.py four-sink /path/to/data /path/to/four-sink-receipt.json 4

The data directory must contain the appropriate catalog and raw JSON certificate directory. The script accepts general polynomial squares for the four-sink case. Default source lookup is package-relative ../certificate-data; an absent default requires an explicit source. No prior research archive, solver, numerical tolerance, third-party package, or producer import is used.

## Bounded-four-sink collection: PASS

The complete second collection was independently replayed in 44.734 seconds:

- 9,608 representative graphs, including 139 reflexive-transitive representatives
- 1,755,474 positive rational polynomial-square terms
- 1,739,038 of these are binomials; the remaining 16,436 squares contain between 3 and 67 monomials
- 57 empty certificates, exactly the 57 coefficientwise nonnegative targets
- Every exact remainder is coefficientwise nonnegative, including absent target exponents
- 14,808,315 positive remainder terms in total; no identically zero remainder
- Complete disjoint S5-orbit coverage of all 2^20=1,048,576 labeled loopless five-core relations

The variable at index 10 was interpreted as C, and the checker directly used the rational moments E1=C+2B, E2=BC+3B²/2, E3=CB²/2+2B³/3. Its separate algebra check verified these as the A=B+C substitution in the universal-cloud envelope. Thus both certificate branches are now fully verified, and together they prove the first required interior gap on the entire gamma5=0 boundary.

Receipts: four-active-receipt.json and four-sink-receipt.json. Per-certificate SHA-256 manifests were written for both families. The current checker SHA-256 is 73730890fa42432ea07576b0f01452b123be9214bc3fa8ef1f55a25a46b194c6.

Final release remains subject to hash-bound article review and clean-extraction replay of the frozen archive. Earlier delivered archives were not modified.
