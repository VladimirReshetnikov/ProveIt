# Independent review: the unrestricted auxiliary nine-gate frontier

**PASS as necessary conditions at the stated paid cut.** The result does not claim a nine-gate construction or a ten-gate lower bound for all circuits. It removes the protected-row assumption from several exclusions and confines a remaining nine-gate circuit to5M+4A with one genuine monomial-producing cancellation from the stated17-value list. The global universal84 bound is unchanged.

The reviewer read the complete frozen helper and proof, including the exhaustive addition-placement cases, and inspected the full84 attaining source relation. The author pins are:

| File | SHA-256 |
|---|---|
| complete84_auxiliary_nine_gate_frontier.py | e4197911e04fe9379fb0801ce01559ec371e3955d025486a3f84644aa17d48e2 |
| complete84_auxiliary_nine_gate_frontier.json | 049de5ef5f2d46802801b6f88450a852b672b218040e224c262a2ac1e79341e1 |
| complete84_auxiliary_nine_gate_frontier.md | ae4925e8bf330fcd1a5d1c0f529e982f0c5df018690a7ef81e4ca27cc5ad4cd2 |

## Mathematical challenge

The multiplication-only lower bound is valid. Q and S are linearly independent modulo the original paid span because their W,Q coefficient matrix has determinant-1. The corresponding multiplication-output coefficient rows remain two independent scalar relations after Delta=i=0. Choosing largest-index pivots permits deletion of two products without introducing later dependencies. The remaining circuit computes V from the original specialized paid ports, so the inherited three-product bound implies at least five products before deletion. No multiplication output is assumed monomial in this argument.

For exactly three additions, any monomial-valued addition could be removed after supplying its value free, contradicting the inherited three-addition bound which already allows every monomial. All three additions are therefore nonmonomial. Unique factorization makes Q's cone monomial and forces V to occur at an addition itself, while the addition supplying S's nonmonomial factor must be P or Delta*P up to scalar. This leaves precisely the three chronological cases in the proof.

I checked the quotient arguments for the cases where S's core occurs before V. Modulo P with c,i inverted, each ordinary monomial stays a nonzero Laurent monomial, and V retains its three noncollinear terms. A surviving monomial times one binomial power has collinear support, so it cannot equal V. In the last case h=m*g^r+n, the T/R multidegree argument also handles r=1: cancelling one of the two terms from m*g would leave just the other term, not the required two-term core. For r>=2, one outside monomial cannot remove all unwanted multidegrees. Thus the two V additions and one S-core addition must have the separated structure established in the note; it is a conclusion, not an assumed circuit grammar.

The divisor counts then give seven products for any three-addition circuit. The unscaled S-core case separately charges multiplication by Delta and does not pretend the additional Q0 obligation is free in an attaining construction; ignoring it only weakens the lower bound. No newly computed monomial can be shared between Q and the listed V/W or V/f² targets, since their common divisors are already paid scalars or single variables. Consequently only5M+4A remains at nine total gates.

The i-specialization argument is particularly important. Two multiplication outputs whose values are nonzero monomials containing i both become literal zero at i=0. Deleting them leaves a circuit for V,W from the original ports; the four-product theorem excludes this in any five-product circuit. This applies anywhere in the graph, regardless of chronological interleaving. If the cancellation pivot U is i-free, two such product outputs still occur above U in Q's cone. Crucially, the proof retains and charges U's entire original computation when deleting those products. It does not introduce c³, c⁴ or another internally computed monomial as a new free port. This resolves the potential paid-interface loophole raised during review.

There is exactly one monomial-valued addition in the remaining budget: two would contradict the addition lower bound after their values were supplied free, and none would force the excluded pure-product Q cone. A scalar alias, zero, or already available monomial could be removed, leaving the excluded three-addition case. Thus U is a genuine cancellation, is i-containing, and divides Q. With at most one i-containing product left anywhere, Q above U can only be U, U times an i-free monomial, U², or U*i. Direct exponent comparison gives the15 choices with i exponent2 and the two stated choices with exponent1. Freeing all i-free divisors in this final enumeration is a legitimate relaxation for necessary shapes; it is not used in the counted-circuit deletion theorem. The17 values are not claimed sufficient or feasible.

## Source, evidence and limits

The new helper authenticates six predecessor files without executing or importing their programs. It independently reconstructs the full attaining84 splice, checks all four local polynomials and the only three external cut outputs, and verifies literal retention of every other row. The replaced intermediate registers are private. Every row and all25 supplied ports remain live, with47M+37A and18 positive witnesses. The complete polynomial and degree187 transfer by exact substitution.

Fresh normal and optimized exact receipt replays from `/` pass. The finite17-shape enumeration, support certificates and divisor checks agree with the symbolic proof; they are not advertised as a formal verifier for arbitrary circuits. No finite sample is used as the basis of an unbounded exclusion. No new native compiler tuple is materialized.

The proof concerns independent Delta,c,i,f,T,R plus exactly c² and Delta*c². Extra paid relations, changed output coordinates and whole-polynomial rewrites remain outside this theorem. No correction to the frozen packet is required.

A second independent mathematical challenge also passed. It separately checked the two scalar elimination pivots, all three-addition placements, the charged computation of an i-free cancellation pivot, and the seventeen possible i-containing pivot shapes. It did not repeat the software replay. Both reviews retain the same necessary-condition scope.
