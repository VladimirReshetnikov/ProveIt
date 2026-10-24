# Round 14 independent mathematical and literal review

## Review finding

I found no construction-level gap in the frozen 349-natural, centered 519-integer, and centered 517-integer endpoints identified below. Their new arithmetic transformations have complete forward and reverse ordinary mathematical arguments. Their literal polynomials, sign certificates, eliminations, and translations passed independent exact algebra checks.

This is a reviewer artifact, not the final report. It does not establish Con(ZFC), inconsistency of ZFC, global minimality, worldwide priority, or a new machine-checked logical calibration. The C222/ZFC calibration, original numerical rule predicates, and inherited Pell representation/classification results remain explicit dependencies. Conditional on those supplied ordinary proofs, the reviewed equations have zeros precisely when the calibrated calculus has a finite refutation.

## Frozen principal endpoints

| Artifact | Domain | Variables | Residuals | Degree | Monomials | Coefficient height |
|---|---|---:|---:|---:|---:|---:|
| architecture/derived16_cantor/natural | N including 0 | 349 | 268 | 4 | 12,768 | 86,915,503 |
| direct/integer519_centered | Z | 519 | 321 | 4 | 6,253 | 411,060 |
| direct/derived16_centered_shell | Z | 517 | 310 | 4 | 6,774 | 3,904,267 |

The centered 519-integer choice has lower support and height than the 517-integer choice. Neither dominates the other in every metric. Their construction chains are different:

- 519Z: original large-carrier reciprocal/prime-power hybrid, shell syntax; signed square-budget interpretation; redundant auxiliary nonzero guard removed; exact Horn factorization; integral monic contraction; fourteen integral translations.
- 517Z: shared factorial carrier plus derived polynomial-label range, shell syntax; the corresponding signed interpretation and factorization; integral contraction; thirteen integral translations.
- 349N: shared factorial carrier plus derived polynomial-label range, Cantor syntax; natural-valued certified contraction. It is not the natural version of the low-height 519Z polynomial.

## Independent implementation evidence

The three reviewer scripts import only the Python standard library and each other, never the construction generators or their checkers:

- `audit_literal_independent.py`: raw affine export, all SOS coefficients, rational-SOS/nonnegative contraction, exact counts, majorant recurrences, and syntactic exponent positivity.
- `audit_signed_independent.py`: square-budget atom binding, exact sign deductions and guards, presemantic seed positivity, exact Horn-factor identities and escape checks, full integral elimination, and all quartic coefficients.
- `audit_translation_independent.py`: every coordinate translation in both directions, integer-domain bijectivity, all transformed residuals, and every expanded coefficient.

Primary receipts are `DERIVED_LABEL_LITERAL_REPLAY.json`, `INTEGER519_REPLAY.json`, `INTEGER519_CENTERED_REPLAY.json`, `DERIVED517_REPLAY.json`, and `DERIVED517_CENTERED_REPLAY.json`. Each records exact input hashes. Further receipts retain the 360/361N, 350/351N, 522/523Z, and uncentered 519/520Z intermediate audits. Three corrupt natural-contraction certificates were deliberately rejected. Finite regression tests and producer reproduction are supplementary, never substitutes for the quantified arguments below.

### Reconstruction, not sample agreement

Every eliminated natural coordinate is restored in reverse step order by an integer polynomial proved nonnegative through positive rational affine squares and/or nonnegative monomials. Every eliminated integer coordinate has an integral monic restoration with no domain restriction. The reviewer checks a complete partition of deleted, retained, and unconstrained coordinates, the exact pivot row at every step, and all substitutions in all remaining rows. Thus the checks support existential equivalence in both directions, not merely equality on sampled values.

The factorization reviewer checks all eleven squared ordinary factors against their actual affine roots, the complete product chain, both bundled guard identities, and every possible external use of the modified intermediate wires. Signed roots are permitted only in the unrestricted-integer presentation. The final Horn value is unchanged exactly. The reviewer verifies the full target row list rather than trusting the supplied change ledger.

Every centering map is `old z = new z + s` with an explicit integer s and inverse `new z = old z - s`. No positivity property is presumed after translating the final Z equation. Direct forward and inverse polynomial substitutions pass row by row.

## Quantified mathematical audit

### 1. Reciprocal prime-power CRT

For F=t!, T=F², and 1≤i≤t, d_i=1+T/i is integral, exceeds one, and is congruent to one modulo F. Every prime dividing d_i exceeds t. A common prime of two distinct d_i would divide their index difference, which is impossible. Their product is exactly binom(T+t,t).

For every prime p and e,k≥1, p^e dividing binom(a,k) implies that a has a residue below k modulo p^e. The factorial-valuation proof is correct: in the absence of a multiple of p^e among the last k integers, every valuation summand from index e onward vanishes, and the total is at most e−1. No converse is used.

Soundness combines the free index congruence B | C+T+1 with the separate index range N | binom(C,t), N=B^K. Modulo a prime p dividing d_i, the congruence identifies i−1. The range lifts it to the same index modulo p^(K v_p(d_i)), because p>t. Coordinate ranges and polynomial congruences then give the local source value divisible by a modulus at least 2^K. The strict local bound makes that value zero.

Completeness uses CRT precision 2K, not K. The loss v_p(k!)≤k−1<K v_p(d_i) leaves at least the required K v_p(d_i) factors. Positive representatives at most B^(2K)=N² exist. The generator correctly retains the index range and does not use the invalid fixed index C=B−T−1. At t=2 that fixed index is 10, which is 0 modulo 5 but not modulo 25.

### 2. Factorial and digit bootstrap

The proposed factorial F defines rho=Ft², V=(rho+1)^t, and D=binom(rho+t,t). The raw ceiling equations give D=u+v+1 and DF=V+v. Once V is positive they force F≥1, before any binomial semantics is used. The self-bounding factorial lemma then identifies F=t! after D's exact digit is validated.

The free reciprocal index equation forces B>0 before B is identified with its binomial. After positive power recovery, N=B^K≥1 and q=N(N+V+1)^K>V². The first binomial's low coefficients are at most V. The second has low coefficients at most (F²+t)^t≤(Ft²+1)^(2t)=V². Thus both exact digits are carry-free in the required order, without presupposing the factorial or product under validation.

Only after this does B≥2 give N≥2^(2R). For ordinary representatives n≤rN² with r=9 or 10 and k≤R−1, r^k<16^R≤N² yields n^k<N^(2k+2)≤N^(2R)<q. The former coarse n≤N^6 estimate would not justify K=2R; the sharper estimate is essential. N divides q, so the fused quotient-multiple digit condition is precisely divisibility of the intended binomial.

### 3. Why the smaller amplification budget is unbounded

In the original carrier chart, M0+1=((t+1)^t)^ell with ell=2^22 implies R≥2^ell. E=2^23≤2ell and ell≥8 give R^E<2^R by a base check and integer induction using (1+1/r)^E≤sum(E/r)^j<2. Hence K=2R is sufficient.

In the factorial-carrier chart with t≥16, F≥16!>2^44. The literal E is again 2^23, and 44E<2^44 while 2E≤2^44. The same induction gives R^E<2^R<2^K. This argument is invoked only after F=t! is known; it is not used to bootstrap its own digit graph.

### 4. Shared-factorial Horn-flow soundness and completeness

Every positive label j≤t receives weight 1+jF. These weights exceed one and are pairwise coprime. Label 0 deliberately receives weight one and is ignored by valuations; this is harmless because truth 0 is freely derivable.

The source bounds every possible label in a row, not just the active branch. Overlapping beta equations with remainders at most y identify adjacent accumulator states. The endpoints are S_0=F+1 and S_t=1. Every selected rule branch has positive weights and satisfies S_(i+1) W_conclusion = S_i product(W_premises); consequently all accumulator states are positive. Multiplication and cancellation therefore give exact conclusion-minus-premise counts equal to one at falsity label 1 and zero at every other positive label.

To extract a derivation even from cyclic rule multisets, let D be the closure of truth under the finitely many selected valid rules. If falsity were outside D, every rule whose conclusion lies outside D would have at least one premise outside D. Total conclusions outside D could not exceed total premises outside D, contradicting the exact balance of one. This closes the possible cyclic-flow gap without assuming an ordered proof trace.

Conversely expand a finite refutation DAG to a proof tree. Choose t beyond its finite step count, every parameter and every complete branch-label sum, including the fixed truth-padding tuple, before choosing F=t!. Backward tree expansion gives a positive pending-multiset accumulator path; truth padding reaches exactly t rows. Choose y afterwards, sufficiently large and divisible by t!, and CRT supplies the beta encoding. Thus the horizon does not depend circularly on accumulator sizes or their encoding.

### 5. Derived polynomial-label range

Let J be the sum of all nine constructor codes, a+b, I(a,b), A(a,b), and one. It is positive and bounds every label. The modified local majorant is explicitly for L+J+t+x+y+1; both decoded L and J are strictly below 2^K.

The added condition N | binom(J(A),t+1) gives a residue r≤t modulo each decoding prime power. Polynomial congruence and the independent bound 0≤J(local)<2^K≤p^e force J(local)=r. This is exact range decoding, not an unjustified lifting of a small-prime congruence. Completeness again uses precision 2K and requires K≥t+1, which the actual K=2R satisfies. The general lemma should state this hypothesis explicitly.

J(A) is not an independently chosen CRT representative and is correctly excluded from the aggregate bound, which retains exactly nine summands despite ten range requests. Its own positive-DAG certificate gives J≤(n+1)^ell with ell=2^22 and n=max(A_a,A_b,A_c,A_d). From n≤9N² and N≥10, n+1≤N³ and J(A)≤N^(3ell). The exact base inequality 2*16!≥3ell*17 persists for all t≥16 by induction, giving 3ell(t+1)≤2F<K. Therefore every required coefficient of binom(J(A),t+1) is below N^K<q. The ordinary representative bounds are never incorrectly applied to J.

### 6. Signed powers: the essential orientation repair

The signed square-budget graph bounds the absolute value of every power port, and the inherited signed indexed-Pell lemma determines |X_k| and Y_k once the index is positive. A base n≥2 fixes X_k's sign: the wrong conjugate would force m n^k=-1 after the strict frame bound, which is impossible. A base n=1 does not suffice by itself.

The modified graphs retain F≥0 but initially allow B=1. Thus neither the first factorial numerator base Ft²+1 nor B alone may be claimed to orient a fresh index. The following noncircular order repairs both issues without extra variables:

1. The raw ceiling bound D=u+v+1 gives D≥1. The raw exact-digit output bound q=D+oslack+1 gives q≥2, before any powers or binomial values are interpreted.
2. The existing denominator request q^t orients the t pair. Recover V=(Ft²+1)^t≥1 using that oriented pair. DF=V+v forces F≥1, hence V≥2.
3. B≥0 is retained, and C+F²+1=B*iq with C≥1 forces B>0. K is already positive. The signed B^K request has only two possibilities: N=B^K≥1, or the exceptional inverse case B=1,N=−1. In either case N≥−1.
4. Therefore N+V+1≥2. Its request with the SAME K pair orients that pair positively and excludes the exceptional inverse case. Hence N=B^K≥1 and the common radix has its intended value.
5. All remaining positive exponent ports now have bases q or q+1, both at least two; their seed signs and outputs are recovered. Derived indices use the already oriented t pair.

This argument is necessary. Merely stating B>0 anchors K would leave a genuine missing base-one case. All needed raw inequalities and retained signs were checked against the literal domain certificates.

### 7. Why the auxiliary nonzero guard is redundant here

Unlike the older prime-power release, all seed exponents in these new graphs are positive before any power output is interpreted. F≥0 is retained. In the factorial chart y=F+r0+1≥1. In the original carrier chart M0+1 is already an exact square of an integer, so M0≥−1 and y=M0+r0+2≥1; moreover R=2+t+x+r0+2(M0+1)>0. The remaining exponent ports are positive representatives, positive bound successors, Ft²+t, F²+t, or the positive label polynomial J.

The reviewer independently verifies either the exact positive expansion certificate or the v2 compositional gate lower bounds, including the endpoint/square premises. Every seed row Y=k+e with e≥0 then gives Y≥1. The common product row forces its auxiliary V>0; its Pell norm with A≥2 gives |U|≥2. Therefore the old extra three-variable U²−2 guard is genuinely unnecessary, not simply omitted without replacement. This proof depends on the retained natural F and positive exponent structure; it must not be generalized to the older signed-factorial source.

## Issues found, disposition, and remaining boundary

- Fixed canonical-index substitution: rejected; all reviewed endpoints retain the free index and its range.
- K=2R with old coarse radix bound: repaired by the sharper r^k<N² bound; reviewed proofs use it.
- Signed base-one orientation: repaired by the raw-q anchor and the two-case K argument above; final explanatory text must retain this argument.
- Generic derived-range lemma: explicitly requires K≥t+1. Actual emitted systems satisfy it.
- Reentrant syntax selection: the builder initially failed to reset Cantor syntax after a shell call in the same Python process. The author corrected all constructors and restored monkeypatched construction hooks; frozen CLI coefficients were unaffected. This was a generator API hazard, not a false equation.
- Reproduction of the early t≥32 factorial snapshot: all equation and coefficient bytes match the current generator with `--horizon-minimum 32`; only explanatory floor-certificate metadata was generalized. `FACTORIAL_GENERATOR_REPRODUCTION.json` records the exact distinction.

No source-level counterexample or unresolved construction-level gap remains in the principal reviewed artifacts. The exact scope is delimited by the receipt hashes. Later edits require replay. The unbounded arithmetic arguments remain ordinary mathematical proofs; the independent finite checks do not formalize the inherited proof-calculus calibration, decide consistency, or prove an optimality claim.
