# Independent adversarial audit: five-signal Diophantine certificate 58

4 October 2026 UTC. Fresh root-assigned mathematical and exact-source audit.

## Verdict

**PASS, with no required correction to the frozen certificate.** The native three-positive-input circuit has exactly **81 positive integer witnesses, 44 equations, 344 binary arithmetic gates (136 multiplications, 110 additions, 98 subtractions), and exact total degree 12**. The paid Cantor one-positive-input circuit has exactly **85 positive witnesses, 46 equations, 367 gates (144 multiplications, 118 additions, 105 subtractions), and exact total degree 12**. They recognize exactly the stated integer predicates, subject to the explicitly inherited physical theorem and the pinned constructive Pell theorems identified below.

All equation residuals were independently reconstructed from the mathematics and matched as exact multivariate integer polynomials against each raw DAG. The literal output is exactly their sum of squares. Every gate and leaf is graph-live; stronger, every declared input and witness also occurs nontrivially in the fully expanded output polynomial. The optional quartic variants also pass, with their separately paid counts.

This audit is a conventional mathematical specialization and inert-source audit. It is not a new proof-assistant build, an independent reconstruction of the prior physical collision proof, or a numerical verification of all nonzero-exponent Pell witnesses. No author emitter/checker, prior saved program, upstream program, physical simulator, trajectory replay, or Lean executable was run. Only freshly written, inspected standard-library exact algebra was executed; author programs were read as inert text. The author's review and internal audit were not used as specifications.

## 1. Frozen objects and dependencies

The audited packet is `/workspace/shared/five-signal-diophantine58-20261004`.

| Object | SHA-256 |
|---|---|
| `PROOF.md` | `b55f301d2b1531f348163f026b3c1f7f827669d266afb77d854eef7ceb21c482` |
| `emit_certificate.py`, read inertly | `2093773340d3e7a9891d786e99711a2662a61b952b1c40a8bb1af5392d33ac6d` |
| `sources/SOURCE_PINS.json` | `11d2372f087c5fb75fd23473d09839b595fe7ec5484cbbb9cb55bd202f203a48` |
| Native linear DAG | `707721d1a8dca21b29acda57df8df6e763a1df89761f513122bec5edd9261ccc` |
| One-input linear DAG | `b64a268cc03033c13c020abc0cb12c1c81f9ba630aa75812ac84b08e2971efc3` |
| Native quartic DAG | `11c1a3d6eca23af2a9ede232e1a5ab36ba395a3235a424ef76ff14d5e19f14d0` |
| One-input quartic DAG | `3d2fe384ea6564950e0ca4b392396e3fa4489d88e1974dfd269a42610428ed24` |

All eight local source-copy hashes and byte lengths agree with `SOURCE_PINS.json`. The physical audit copied into the packet is byte-identical to `/workspace/shared/five-signal-obstruction-independent-audit-20261004/INDEPENDENT_AUDIT.md`, SHA-256 `b119df1c0be8685078b011c14e3c71decabce343f9ba9041ee6f97b4c58a5226`.

**The physical result is explicitly inherited.** Its audited complete-macro predicate, including the omitted triple contact and the direction of the excluded orbit, is the input theorem here. This report does not infer physical validity from a simulated orbit, nor independently re-prove every collision rule. The inherited theorem's qualifications about its precise five-live-signal machine, positive homogeneous gaps, and complete collision word remain in force. No at-most-four-population or sharp-threshold theorem is needed or established here.

The constructive arithmetic dependency is the supplied mathlib4 file `Mathlib/NumberTheory/PellMatiyasevic.lean`, identified with commit `ac77769fabe23cb237559e7f56578dbead91499f`, SHA-256 `993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a`. Independently hashing its Git blob gives `6ede8ed67569fc1ddf2b4c09f0feb30ca42fca7e`, also matching the supplied record. The local source text, not a newly authenticated remote checkout or kernel run, is the audited dependency. Its theorem statements and constructive proofs at lines 760–847 and 860–928 were checked for the exact specialization.

## 2. Independent geometric-to-arithmetic reduction

For positive integer gaps, let D=g1+g2+g3, A=3g1−D, and B=3(g1+g2)−2D. The normalized centered physical point is w=(A+iB)/(3D). The inherited critical radius is rho²=4/1845 and the tangency point is p=(4/205,−26/615)=(2/615)(6−13i). Direct rational calculation yields

- rho²−|w|² = [4D²−205(A²+B²)]/(1845D²)
- w/p = [(6A−13B)+i(13A+6B)]/(2D)
- (6A−13B)²+(13A+6B)²=205(A²+B²)

Thus delta=4D²−205(A²+B²) has exactly the inherited radius-deficit sign, and eta=(U+iV)/(2D), for U=6A−13B, V=13A+6B. There is no orientation, scale, or factor-of-three mismatch.

The inherited physical theorem is exactly

`delta>0`, or `delta=0` and `eta != ((3−4i)/5)^m` for every natural m.

A negative deficit is invalid; a boundary point in the inverse orbit is invalid even though its radius is correct. In particular, equality of radius is not by itself acceptance. This distinction is preserved by both the natural radius slack and the strictly positive final slack.

## 3. Outer domains, primitive denominator, and valuation

Every external input and witness leaf is a strictly positive integer. The seven outer naturals are represented by positive leaf minus one; each of eight outer signed quantities is the difference of two positive leaves; the six other outer quantities are directly positive. These adapters are surjective onto exactly their intended integer domains and are charged in the raw source. There are 7+16+6=29 outer leaves. Outputs P and T are counted inside their two 26-leaf POWER modules, giving 81, without double counting or an uncharged defining equation.

The equations U=h*u, V=h*v, 2D=h*q and a1*u+a2*v+a3*q=1 force gcd(u,v,q)=1. Since h>0 and 2D>0, they therefore force h=gcd(U,V,2D), including all signs and zero-component cases. Conversely, dividing by that positive gcd gives a primitive triple and a three-term integer Bezout identity. The signed-pair adapters represent its coefficients without a sign restriction.

The same Bezout identity proves the exact least common positive denominator, rather than merely a common denominator. If d clears u/q and v/q, q divides d*u and d*v; multiplying the identity by d shows q divides d. Conversely q plainly clears both. At U=V=0, one obtains h=2D, u=v=0, q=1; a3=1 suffices. There is no singular center or zero-numerator exception.

The first POWER module gives P=5^n, with n natural. The positive remainder equations give r=5k+s with k natural and s+t=5 with s,t positive. Therefore s is exactly one of 1,2,3,4 and 5 does not divide r. Together with q=P*r this forces n=v5(q), including q=1 and n=0. Conversely the ordinary division algorithm supplies all witnesses. Positivity of *both* s and t matters: allowing either zero would admit the forbidden zero residue. The quartic alternative forces precisely the same four s values over integer witnesses.

## 4. Bounded extraction is exact

Let Cn+iSn=(3+4i)^n and P=5^n. The modulus identity gives |Cn|,|Sn|<=P. Put b=4P+1. Reduction in Z[X]/(X²+1), evaluated at X=b modulo b²+1, proves

`(3+4b)^n == Cn+b*Sn mod (b²+1)`.

The second POWER module supplies the ordinary power on the left. The four natural bound slacks enforce the **closed** bounds −P<=C,S<=P. If another bounded pair satisfies the congruence, its differences dC,dS from Cn,Sn satisfy

`b²+1 | dC+b*dS`, and `|dC+b*dS| <= 2P(1+b) = 8P²+4P < 16P²+8P+2 = b²+1`.

The expression is therefore zero. Then |dC|<=2P<b forces dS=0, since any nonzero integer dS would have |b*dS|>=b; hence dC=0. This establishes uniqueness of the extracted coefficients, without imposing any unjustified bound on the signed quotient kappa.

At n=0, P=1, b=5, T=1, C=1, S=0. The true pair can sit on a closed bound, so the natural, rather than positive, bound slacks are necessary for completeness. No negative, zero-base, or zero-exponent exceptional branch has been omitted.

## 5. The final strict equation is the required iff

For m>=1, the Gaussian integer 3−4i is congruent to 3+i modulo 5, and (3+i)²=3+i in (Z/5Z)[i]/(i²+1). Therefore both numerator coordinates of (3−4i)^m are nonzero modulo 5. The joint denominator of ((3−4i)/5)^m is consequently exactly 5^m. No assumption that this quotient ring is a field is used. At m=0 the denominator is 1 and the point is 1.

If eta is forbidden, the exact reduced denominator forces r=1 and m=n; its primitive numerator is exactly (u,v)=(C,−S). Conversely r=1 and that numerator equality give eta=((3−4i)/5)^n. Hence the nonnegative integer

`delta²+(r−1)²+(u−C)²+(v+S)²`

vanishes exactly at a forbidden boundary point, among inputs whose radius slack is natural. Setting it equal to a **positive** J gives precisely physical validity. In particular the sign is v+S: reversing it would exclude the forward orbit instead.

For soundness, a zero of the output sum of squares forces every equation, hence delta>=0, correct powers, exact fraction reduction/valuation, unique extraction, and a nonzero final sum. The inherited physical theorem then gives validity.

For completeness, a valid gap triple supplies its natural deficit, positive gcd, primitive quotients and signed Bezout coefficients. Its positive q gives canonical n and r and the positive remainder witnesses. Both constructive POWER instances have witnesses. Choose the true complex coefficients, their four nonnegative bound slacks, and the integral signed remainder quotient. The final sum is positive either because delta>0 or because the boundary point is not forbidden, so it supplies J. Every adapter can then be filled with positive leaves. All equations hold simultaneously.

The certificate makes no uniqueness or finite-fold claim. For example, simultaneously increasing both positive leaves of any signed quantity preserves its value and gives infinitely many witnesses whenever a solution exists.

## 6. Exact POWER dependency and positivity audit

`POWER_AUDIT.md` in this directory contains the full independent subsystem audit, theorem line references, both-direction specialization, and raw native DAG check. Its central points were reviewed as part of this report:

1. With base B0>=2 and e natural, the module sets k0=e+1 and m0=B0*out. Both lie in the positive branches required by the theorem.
2. Equations 1–9 are exactly the nonzero branch of `Pell.matiyasevic` at local source lines 760–766. Its natural truncated Pell subtractions equal the displayed integer equalities because their results are 1. Natural quotient pairs encode all four congruence signs.
3. Equations 10–15 give the positive branch of `Pell.eq_pow_of_pell` at lines 860–864, especially its strict m0<M. A positive Jp encodes this strictness.
4. Before invoking the theorem, equation 13, w>=B0>=2, and positive g imply a²>w², hence a>w>=B0. Thus the polynomial a−B0 agrees with the theorem's natural subtraction.
5. The theorem gives B0^(e+1)=B0*out, and cancellation of positive B0 gives out=B0^e, including e=0.
6. Conversely the constructive theorem supplies w,a,M,g. Its g cannot vanish without forcing a=1. The other Pell theorem supplies natural auxiliary coordinates; x,u,s are positive by their Pell equations, y>=k0>=1, v>0 explicitly, qv=v/y²>0, qb=(beta−1)/(4y)>0, and t cannot vanish because t==k0 modulo 4y and 1<=k0<=y<4y. Thus all stricter positive domains preserve completeness.
7. Both actual calls satisfy hypotheses before their semantics: base 5, and base 16P+7>=23 from P's positive leaf; their exponent is the same natural adapter.

Each module has exactly 13 directly positive leaves, 2 shifted-positive leaves, and 11 natural-adapter leaves: 26 total, including its output. Every raw module equation side matches the specialization, and each body contains 70 gates (31 multiplications, 24 additions, 15 subtractions). There is no exponentiation primitive or unexpanded oracle in the final DAG.

## 7. Paid one-input transport

For natural a,b,c,j, the two decoding equations are exactly

- 2j=(b+c)(b+c+1)+2c
- 2(z−1)=(a+j)(a+j+1)+2j

with a=g1−1, b=g2−1, c=g3−1. Thus j=pair(b,c) and z−1=pair(a,j). For each natural N, the unique integer d with d(d+1)/2<=N<(d+1)(d+2)/2 gives offset s=N−d(d+1)/2 in [0,d], and the unique pair (d−s,s). Applying this twice proves a total bijection between positive z and positive gap triples. No code-validity promise, rational division operation, or branch selector is hidden.

The raw one-input DAG adds exactly three positive gap witnesses and one natural-adapter leaf, two degree-two residuals, 17 body gates and 6 assembly gates. Its increase is exactly 4 witnesses, 2 equations, and 23 gates (8 multiplications, 8 additions, 7 subtractions). Its input is an ordinary positive integer, but its meaning is the transported predicate, not a native three-gap input silently recounted as one variable.

## 8. Exact source equality, liveness, and formal degree

`audit_exact_source.py` was written freshly for this audit. Its sparse-polynomial specification spells out the mathematics independently of the emitter, DAG ports, module metadata, or author receipts. It validates leaf declarations, integer constants, permitted binary operations, topological references, and all named residuals. It then expands the actual output and compares it with the independently constructed sum of all residual squares.

It separately verifies the *literal topology*: for each equation the tail has a subtraction gate, then its self-product, followed by the chain summing all squares. The tail has exactly 3E−1 gates, so no residual is omitted, duplicated, or assigned an unchecked weight. Graph traversal finds every gate and leaf live. The support of the fully expanded polynomial includes every declared input and witness, showing algebraic liveness too.

The computed exact degree is 12 for all four sources. Stronger than a syntactic degree upper bound, the entire degree-12 homogeneous component is exactly

`power5.w^8 * power5.g^4 + power_complex.w^8 * power_complex.g^4`.

Both coefficients are +1. This follows from full coefficient collection, and agrees with the mathematical observation that each POWER residual 13 has leading term −w^4*g^2. All other residuals have smaller degree. Therefore cancellation cannot lower the degree. Degree is measured jointly in independent positive input and witness leaves; aliases introduce no new variables.

| Source | Inputs | Positive witnesses | Equations | Multiplications | Additions | Subtractions | Gates | Expanded terms |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Native linear | 3 | 81 | 44 | 136 | 110 | 98 | 344 | 772 |
| One-input linear | 1 | 85 | 46 | 144 | 118 | 105 | 367 | 802 |
| Native quartic | 3 | 80 | 44 | 139 | 109 | 102 | 350 | 775 |
| One-input quartic | 1 | 84 | 46 | 147 | 117 | 109 | 373 | 805 |

The canonical expanded-polynomial hashes, residual hashes/degrees, region operation counts, liveness results, and source-copy hashes are recorded in `exact-source-receipt.json`. The source-specific constant convention is observed literally: integer coefficients are leaves, but all displayed multiplication gates, including multiplication by constants, count. No minimality is established or claimed.

## 9. Independent finite challenges and complete witnesses

`audit_arithmetic.py` uses only exact integers and `Fraction`, with the inherited physical formula calculated independently in normalized rational coordinates. It does not reuse the author's semantic checker or formula functions. `arithmetic-receipt.json` records:

- All 15,625 positive gap triples with coordinates 1 through 25
- Both orbit orientations through exponent 100, at scales 1, 2, 7: 606 cases
- 820 rational critical-circle parameter cases
- 12,500 primitive-denominator and three-term Bezout cases, including zero and negative components
- All bounded coefficient pairs for n=0,1,2,3, with P=1,5,25,125; the pair is uniquely correct in every case
- 20,000 positive-code round trips and 8,000 positive-gap Cantor round trips

The required rejected fixture (217,167,231) gives delta=0, (u,v,q)=(1,0,1), n=0, r=1, (C,S)=(1,0), and J=0. The required accepted fixture (233,171,211) gives delta=0, (u,v,q)=(3,4,5), n=1, r=1, (C,S)=(3,4), and J=64. These check the contact and forward-orbit orientation directly.

Explicit malformed candidates challenge essential guards:

- At the rejected contact, n=0 and the false extracted pair (C,S)=(27,0) still satisfies the modulus relation with kappa=−1 and has a positive final sum. The upper bound P−C=−26 blocks it. A complete positive witness assignment for every other equation was evaluated on each raw DAG: its only failure is `complex.C_upper`, with residual −26 and output 676
- Dropping primitive Bezout would permit the contact fraction (u,v,q)=(5,0,5), choose n=1 and true (C,S)=(3,4), and falsely produce acceptance sum 20. Every possible Bezout combination is divisible by 5, so the actual system blocks it
- At forbidden eta=(3−4i)/5, undercounting n as 0 would give r=5 and false acceptance sum 36. It requires t=0 with s=5, or s=0 after carrying; both violate the actual positive domains
- Making J natural would admit the rejected contact with J=0; the positive leaf blocks this
- Allowing a signed radius slack would admit exterior examples such as (1,1,10), whose delta is −82449 despite a positive squared acceptance sum; the actual natural slack blocks it

Complete ordinary positive Pell witnesses were constructed independently for exponent zero, not merely substituted with a power oracle. For each base B0 in {5,23}, put w=B0 and choose a=x_w(w+1), with g=y_w(w+1)/w. Divisibility follows from the elementary recurrence x_j=1, y_j=j modulo w. At k0=1 use x=a,y=1,u=2a²−1,v=2a; choose beta==a modulo u and beta==1 modulo 4, then s=beta,t=1. The remaining quotients/slacks follow explicitly. The largest stored witness has 78 decimal digits.

For all four DAG variants, these complete witnesses were evaluated at the center (1,1,1), the accepted boundary eta=−1 with gaps (193,243,179), and the accepted boundary eta=i with gaps (231,191,193): twelve full zero evaluations. They are stored in `full-positive-witnesses.json`. Setting J=1 at the rejected contact leaves exactly the final residual −1 and output 1. Changing a paid code while retaining its gaps leaves the expected decoding failure. Every individual positive witness was also incremented by one; all non-neutral mutations failed, and the only neutral mutations were Bezout leaves whose coefficient was zero, as mathematics predicts.

These finite checks support the proof, not replace it. General nonzero-exponent POWER witnesses are supplied by the pinned constructive theorem; the orbit and outer arithmetic tests compute their true ordinary power outputs directly. No bounded sample is being promoted to an all-exponent proof.

## 10. Separate optional univariate-sign corollary

This corollary is valid but is not needed by, nor inserted into, the frozen proof. The one-input transported predicate cannot agree on all positive integers with a finite Boolean combination of univariate polynomial sign tests, even with real coefficients.

Each fixed univariate real polynomial has an eventually constant sign: zero identically, or the sign of its leading coefficient for all sufficiently large positive arguments. Therefore every finite Boolean combination of their sign atoms is eventually constant. Yet the codes of (t,t,t) give an unbounded accepted sequence, while the codes of (217t,167t,231t) give an unbounded rejected sequence for positive integer t. Both follow from the inherited homogeneous predicate and the polynomially growing Cantor code. Hence eventual constancy is impossible.

This is an elementary statement about the chosen integer encoding. It establishes no new physical threshold, undecidability, arithmetic-circuit lower bound, or obstruction to existential positive-integer witnesses. In particular it is fully consistent with the verified one-input degree-12 certificate.

## Final scope

Within the exact frozen sources and stated dependencies, the native and paid one-input theorems are correct, and all printed primary and optional ledgers match the actual arithmetic sources. No mathematical, domain, source-equality, boundary-orientation, or counting defect was found. No source changes are required by this independent audit.
