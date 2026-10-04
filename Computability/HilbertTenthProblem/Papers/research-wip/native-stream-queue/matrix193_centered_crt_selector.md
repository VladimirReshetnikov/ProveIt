# Centered coefficient spheres and a circle selector for the 193-matrix interface

This packet replaces the finite lookup component of `matrix193_crt_selector` by a complete **133-operation signed-integer countdown predicate**, down from154. Its synchronized component costs107 operations. For each fixed duration h≥1, the resulting positive-integer certificate costs **165h+7 operations**, uses31h+1 positive witnesses, and has degree at most10. This is a local/fixed-duration representation of the inherited directed matrix computation. It is not a fixed-arity representation of unbounded products, a universal-operation bound, or a real-exact certificate.

The saved numeric table is the same96 paired actions from the context-absorbed193-matrix fixture. The construction also gives the same local cost for arbitrary fixed contexts in the inherited group, by changing effective fixed numerals. It does not change the original fixed-semigroup/program distinction.

## 1. Authenticated interface and scope

The standalone helper reads these files as inert bytes/data, checks their exact SHA256 values, and executes or imports no predecessor code:

| File | SHA256 |
|---|---|
| `matrix193_crt_selector.py` | `eb2449443cb61ee7b158d2727a15bc94d83b41c56a20a53bbc8072a3510409b6` |
| `matrix193_crt_selector.json` | `7c2c1f5330838eb942fb36a15961920f079cd4fd2a306732ca9d8ae589383455` |
| `matrix193_crt_selector.md` | `3e8e8323f98712db79d791c80e0f8acf1f859231fbf80f02742fab6dd44d733c` |
| `matrix193_gamma1_recode.md` | `6349644283548af96f4a9582ee32d959a123c81bf1c2f902c45874ae45c96742` |
| `matrix193_context_absorption.md` | `d7492809ba00a011c8280172bb016f96f3f6c240de6a823ed717d82bda5e4f4b` |
| `matrix193_synchronized_rows.md` | `ab768aa392841add5dc6dfcd8ed62564ca17fae2fe80e5ec39f1f4ceb36559d2` |

For each table row i, write K_i and G_i as four entries in row-major order. They have determinant1 and upper-left entries congruent1 modulo5. In particular their upper-left pivots never vanish. The component relation is

    (X,Y) → (X K_i,Y G_i),    i∈{0,…,95},

where X,Y are two-component rows. All supplied states and local witnesses are signed integers unless positive conversion is stated explicitly. Exactly six columns are needed: K0,K1,K2,G0,G1,G2. The omitted fourth entries are recovered semantically by unimodularity, not by an uncharged variable operation.

The inherited group theorem gives first-row injectivity and the exact directed-word/matrix transfer. Those facts, the compiler's ordinary-input interpretation, and the context-absorption theorem are inherited from the pinned proofs; this packet rebuilds the finite selector and its paid polynomial interface, not those proofs or the original machine simulation.

## 2. A finite circle selector

Let N=5,928,325. The integer equation

    z²+b²=N

has exactly96 different z coordinates. This finite assertion is certified by an exhaustive integer scan of −2434≤z≤2434: each label is retained precisely when `isqrt(N−z²)` squares back to N−z². The receipt saves all96 labels and a nonnegative integer b for each. Every solution lies in this scanned interval, so the list is complete without a numerical approximation or an external existence theorem.

Order these96 labels increasingly, from −2434 to2434, and assign them bijectively to the original96 table rows in their unchanged order. Every original tile has a canonical label and every admitted label denotes an allowed tile. At a specified label, the recovered coefficient and its quotient are unique; the signs of circle witnesses and the sphere decompositions need not be unique.

Let L0 be the product of the distinct primes dividing at least one positive difference of two labels. Fresh exact trial division finds148 primes and a1221-bit product, from1721 distinct positive differences. Choose

    T = 2 max{|entry| : entry in the six retained columns}+1,
    L = L0 max(1,ceil((2T+1)/L0)).

Then T is odd, L>2T, and L has every prime factor of every label difference. Put

    m_z = 1+(z+2435)L.

All admitted m_z are positive and greater than2T. For two different labels, a common prime divisor of m_z and m_w is coprime to L, but divides (z−w)L. It therefore divides z−w and hence L, a contradiction. The96 moduli are pairwise coprime. This argument needs the prime support of the differences, not their prime-power divisibility in L.

In the numeric fixture, T=11910920894236737019571029638061 and already L=L0. The modulus is computed with exactly two gates:

    temp = L*z;
    m = temp + (2435L+1).

The parenthesized term is a fixed numeral. The circle residual costs2M+2A=4 gates, before its final square.

## 3. Centered doubled coefficients

For each of the six columns c, compile the least nonnegative CRT solution C_c satisfying

    C_c ≡ 2 entry(c,z)+T  (mod m_z)

at every admitted label. The standard finite CRT recipe, including exact modular inverses, is saved and recomputed from the authenticated table. Its fixed output `center_c=C_c−T` is a numeral binding in the variable source. No variable division occurs.

Supply an integer quotient q_c and compute

    A_c = center_c − m q_c.

Supply three integer roots s_c0,s_c1,s_c2 and impose

    A_c²+s_c0²+s_c1²+s_c2²=T².                    (1)

Soundness is immediate from the sphere: |A_c|≤T. Hence A_c+T lies in[0,2T], strictly below m_z. Also A_c+T=C_c−m_z q_c. Its residue is therefore the unique compiled representative, giving

    A_c = 2 entry(c,z).

The quotient is uniquely determined as well. There is no extra parity assumption on arbitrary zeros: parity follows from the recovered coefficient.

For completeness the intended A_c is even and |A_c|<T. Thus T²−A_c² is positive and is1 or5 modulo8. It is not of the form4^a(8k+7), so it is a sum of three integer squares. The exact external existence dependency is Legendre's three-square theorem. The [Archive of Formal Proofs entry by Anna Danilkin and Loïc Chevalier](https://isa-afp.org/entries/Three_Squares.html), dated3May2023, states precisely this criterion. This review read that entry's theorem statement, not the complete formal proof; neither this circuit nor the inherited compiler is claimed to be formalized there.

Each column costs two gates for A_c and eight for its sphere residual:5M+5A=10. The T² binding is an effectively computed fixed numeral; every multiplication by a supplied variable is present in the array.

## 4. Row action and complete local source

For a matrix [[a,b],[c,d]] with ad−bc=1 and a≠0, let A=2a,B=2b,C=2c. For current row(u,v) and next row(p,q), impose

    2p−Au−Cv=0,
    Aq−Bp−2v=0.                                (2)

If e0=p−au−cv and e1=q−bu−dv, these are2e0 and2(ae1−be0). The triangular transformation has determinant4a≠0. Hence the two equations are equivalent to the exact row action over the reals once the lookup coefficients have been recovered. Negative pivots are harmless. Without the determinant hypothesis, the second residual has the additional term2v(ad−bc−1); no off-node determinant identity is assumed.

The source applies (2) to K and G. Every doubling is paid as an addition. The four row residuals cost8M+12A=20 gates. Let U be the sum of the squares of the circle residual, the six sphere residuals, and these four row residuals. There are11 residuals. The complete synchronized ledger is:

| Cone | M | A | Total |
|---|---:|---:|---:|
| Common modulus | 1 | 1 | 2 |
| Circle residual | 2 | 2 | 4 |
| Six computed centered coefficients and spheres | 30 | 30 | 60 |
| Four row residuals | 8 | 12 | 20 |
| Eleven squares and ten joins | 11 | 10 | 21 |
| **Complete U** | **52** | **55** | **107** |

Thus U is globally nonnegative on real ports, and its integer-zero projection onto the eight state coordinates is exactly the union of the96 intended paired row actions. Completeness chooses a canonical circle label, the six unique quotients, and six three-square decompositions. Soundness recovers one common label and all six coefficients from the same modulus. The total local auxiliary count is26: z,b, six quotients, and eighteen square roots.

For comparison the packet also emits a supplied-coefficient version with six extra coordinates a_c and six explicit residuals `center_c−mq_c−a_c`. It costs125=58M+67A. Substituting the computed expressions for all a_c makes those six residuals vanish and gives the computed107-gate polynomial identically over all values. Both whole identities are checked by exact sparse expansion. The change from the older154-gate packet is only an integer-zero relation equivalence, not an all-value identity or a bijection between all auxiliary witnesses.

## 5. Countdown and fixed durations

The full LOAD residual sum is

    E = (X'0−X0)²+(X'1−X1)²
        +(Y'0−52891Y0−94920Y1)²
        +(Y'1+29036Y0+52109Y1)²
        +(n'−n+1)².

The complete countdown polynomial is

    P = E (U+n²+n'²).                           (3)

The26-row parent wrapper is retained literally up to register renaming and independently expanded against (3). It costs12M+14A, giving **133=64M+69A** in computed mode and151=70M+81A in supplied mode. Equation(3) is globally real nonnegative. On integers it vanishes exactly for LOAD, with no restrictions on lookup auxiliaries, or for a selected tile action with n=n'=0. In particular one must not require a valid selector in the LOAD branch.

Use the inherited paid-free initializer

    X=(35426321,−19628667),  Y=(1,0),  n=x,

where x is the ordinary natural input. The endpoint polynomial

    (X0−Y0)²+(X1−Y1)²+n²

is saved in full and costs3M+4A=7. At each LOAD the counter decreases by1; every tile requires current and next counter0. Reaching final counter0 therefore forces exactly x loads, all preceding every tile. Once a tile occurs, a later LOAD would leave a negative counter that no tile or LOAD can raise. Thus the trajectory is precisely LOAD^x TILE*. Signed counters do not create additional accepting trajectories. At x=0 an empty tile sequence is treated exactly as in the inherited row interface, including its endpoint condition.

For a fixed h≥1, sum h copies of P and the endpoint. Nonnegativity makes this a conjunction without squaring P again. The full ledger is134h+7, with31h signed witnesses: five next-state coordinates and26 auxiliary coordinates at each step. Current-state coordinates after the first step reuse the preceding next-state ports. Degree is at most10; a claim of exact degree after fixing initial/endpoint data is unnecessary.

Convert all31h signed witnesses at once with a single positive offset s and positive ports p_j, computing w_j=p_j−s. Every finite integer list has such a representation; conversely every positive assignment restores integers. This costs exactly31h additional subtraction gates, yielding **165h+7 operations and31h+1 positive witnesses**. The ordinary input is unchanged. The receipt emits the complete h=1 and h=2 sources, with172/337 gates and32/63 positive witnesses respectively. All reconstruction gates, repeated local arrays, endpoint rows and final joins are present and live.

For reference, supplied mode has152h+7 operations with37h signed witnesses and degree at most6. The synchronized computed relation with a supplied start/end row interface has108h+5 operations and30h signed witnesses, degree at most8. These growing-duration interfaces do not pay for a fixed number of witnesses covering unbounded computation.

## 6. Degree, domains, and coefficient tradeoff

The computed coefficients have degree2, their sphere residuals degree4, and U degree at most8. Set all state and root ports to0, z=t, and q_K0=t, with the other quotients0. The leading term of U is L^4 t^8. For P also set n=t,n'=0; the loader is(t−1)², so the leading term is L^4 t^10. The helper checks these exact univariate specializations with the actual fixed numerals. Thus computed degrees8 and10 hold for every context recipe with L>0.

In supplied mode set all states, roots, quotients and coefficients0 and z=t. The circle square supplies the degree4 monic term; the countdown specialization supplies degree6. The helper also fully expands the formal-constant source and reference polynomials, treating fixed numeral ports as degree0.

Integer exactness is essential. An explicit rational alias sets z=−2434,b=63, every A_c=0, q_c=center_c/(L+1), and each coefficient sphere's first root to T, with its other roots0. Put both current rows equal to(1,0), both next rows equal to(0,0), and n=n'=0 when present. Every local polynomial vanishes, although invertible matrices cannot map a nonzero row to zero. At least one quotient is nonintegral, as also verified directly. Consequently this packet supplies no real-exact improvement over the older real-safe1179-operation interface.

The arithmetic count reduction trades against fixed numeral size. The actual L has1221 bits; the CRT product has118159 bits and the largest bound fixed numeral has118158 bits. The prior154-operation fixture used much smaller numerals. All nine variable-source numeral bindings are saved exactly in hexadecimal with their bit lengths and SHA256 values; the complete finite recipe is replayed, not treated as an oracle. Fixed numeral preparation has no variable arithmetic cost in the declared model. This is not a bit-complexity, running-time, or coefficient-height improvement.

For arbitrary inherited contexts, `matrix193_gamma1_recode.md` and `matrix193_context_absorption.md` place all K_i,G_i in H'⊂Gamma1(5). Therefore the nonzero-pivot hypothesis persists. Recompute odd T, the multiple L, and the six CRT solutions from the new fixed table; the circle table, count, proof, and source shapes are unchanged. Only the selected fixture's numeric arrays are saved here. This uniform fixed-context recipe does not assert one unchanged193-generator language for every program.

## 7. Fresh bounded evidence and replay

The helper authenticates six dependencies, rejects duplicate JSON keys/noninteger JSON numbers, uses explicit checks unaffected by `python -O`, and compares expected receipts recursively with exact types. Its CLI writes new receipts exclusively and does not modify the repository. It is a bounded research replay, not a maintained general compiler API.

Fresh generation checks all four complete local arrays:516 paid gates, every register/port/numeral live, every residual, and12728 full-output formal coefficient entries. It verifies both complete supplied-to-computed pullbacks,576 coefficient/label CRT matches,4560 pairwise gcds, and768 exact row actions including rational states. It also checks48 full signed/rational source evaluations, including16 rational assignments, plus64 modular comparisons and all four exact-degree specializations.

Two actual labels—canonical table indices0 and95—have saved exact three-square decompositions for all six coefficient spheres. Direct integer squaring verifies all twelve decompositions; no probable-prime assumption enters these certificates. They give eight full integer tile zeros across the four arrays, with eight perturbed-state rejections. Four full LOAD zeros allow arbitrary lookup witnesses, and four complete rational aliases establish the domain limitation. These are component zeros, not newly certified ordinary-input machine histories. The two complete positive-duration arrays add509 gates and twelve full composition checks.

Normal and optimized exact replay commands, from any working directory, are:

```sh
replay_wip=/absolute/path/to/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue
python3 "$replay_wip/matrix193_centered_crt_selector.py" --root "$replay_wip" --expect "$replay_wip/matrix193_centered_crt_selector.json"
python3 -O "$replay_wip/matrix193_centered_crt_selector.py" --root "$replay_wip" --expect "$replay_wip/matrix193_centered_crt_selector.json"
```

Fresh writer generation and normal/optimized exact replays from `/` passed against the pinned WIP dependencies. Only this new helper was executed. The normal and optimized runs compared the complete receipt exactly.

Frozen author source SHA256: `091ea1a9fae724f7dd9cab551e6938b0524677766b39f0311d9e324f8837cd28`. Receipt SHA256: `51e304b13fbeea6d1b69a35ee8fbd3f359dfe050e2ceee177890b8b3d07d1d78`.
