# Degree-separated quadratic source: proof and exact certificate

This is a new source adapter at repository snapshot
`4b4349064a750ba6347293b55874a7f92abdd0db`. It is ordinary mathematics,
formalizable in ZFC, with an exact finite symbolic certificate. It does not
replace the inherited unbounded native compiler or the K215 calibration.

## 1. Structural change

The old source uses `(1+g)^2 D(B)`. This forces a supported linear monomial
to avoid collisions with all quadratic monomials. That condition is not
needed if source terms are separated by their ordinary degrees. We use

`F(B,y) = A2(B)*y^2 + A1(B)*y + A0(B) + B^(Q+1)*(y^2+1)`.

The last summand is a positive carrier above every tested output. It is
essential for unconditional positivity before the ratio bridge has proved
an upper bound on g. There is still only one packed input g. The three
channels are polynomials, not extra quantified variables.

Use the raw 31-positive-variable parent in `parent_quartic31.json`, rather
than expanding its positive-to-natural shift. Its 22 residuals are r_j.
If n_i are nonnegative packed digits, use

`ell(B) = sum_i B^w_i; y = g + ell(B)`.

Decoded y is the packed word for the positive coordinates n_i+1. This
retains the existing parent zero set exactly.

## 2. Frozen data

The source variable order is the order in the parent JSON. The weights are

```
104,76,79,60,108,8,99,55,36,54,98,11,7,10,44,32,
106,22,17,1,3,4,37,89,97,107,39,40,86,45,92.
```

Targets in original equation order 1 through 22 are

```
1081,1388,1366,763,850,546,1414,1147,1914,1093,821,
1861,39,1621,238,759,500,1711,1052,283,1343,368.
```

Thus W=108, Q=1914, K=Q+1+2W=2131, E=K+W+2=2241,
and H=E+W+23=2372. No optimality is claimed.

For each coefficient p_(j,alpha) of r_j, degree d=|alpha|, place a term
at exponent q_j-alpha.w in channel A_d. Its coefficient is

* 2*p_(j,alpha) for d=0 or d=1;
* 2*p_(j,alpha) for a square in d=2;
* p_(j,alpha) for a product of two distinct variables in d=2.

Every exponent is nonnegative. The frozen data contain 45 quadratic,
41 linear, and 8 constant records, hence 94 records altogether.
`degree_channels.json` supplies every exponent and coefficient recipe,
with the four native ports left as indeterminates.

For every channel d separately, every source-supported alpha of degree d,
and every monomial beta of precisely degree d, the finite certificate says

`q_j-alpha.w+beta.w=q_k` iff `j=k and alpha=beta`.

The quadratic comparison is against 496 pure pairs on 31 variables, the
linear comparison against 31 singletons, and the constant comparison against
the sole empty monomial. There are 39 distinct supported pure quadratic
pairs. The independent checker enumerates all 23,599 term/expansion
interactions, and independently reconstructs all 22 output polynomials,
including their formal native coefficient ports.

This condition also proves that reversed exponents are distinct within
each channel. If two reversed terms coincided, multiply by the monomial
of either term and use the isolation condition at its target. Exponents
may coincide across different channels, which is harmless.

## 3. Universal extraction identity

For indeterminates z_i, let Y(t)=sum_i z_i t^w_i and form F(t,Y(t)).
The multinomial coefficients of Y(t)^2 are 1 for squares and 2 for
products of distinct variables. The preceding coefficient factors
therefore prove

`[t^q_j] F(t,Y(t)) = 2*r_j(z_1,...,z_31)`.

All carrier exponents exceed Q, so the carrier contributes to no selected
output. This is an identity of polynomials over the ring of integer
polynomials in the four native coefficient ports, not a numerical test.

## 4. Fixed coefficient bounds and unconditional positivity

Choose ONE complete coherent native tuple. The compact39/44 tuple has port
bit lengths (590069,592884,590069,590070). Termwise absolute recipe bounds
have maximum bit length 1182955. Therefore use

`M=2^1182955, kappa=1182968, beta=2^kappa=8192M`.

The independent audit also checks the original31 tuple, whose corresponding
values are M=2^2134927 and kappa=2134940. No ports are spliced. All subsequent
proofs use only M>=2, even kappa, beta=8192M, and the supplied coefficient
bound |c|<M in each channel. The compact tuple's compiler adapter remains
an identified inherited dependency.

Let b>=2 and B=beta*b^2. Every A_d has degree at most Q, whence

`|A_d(B)| < M*B^(Q+1)/(B-1)`.

Write T=B^(Q+1), eta=M/(B-1)<1/4. For every integer y,

`y^2+|y|+1 <= (3/2)*(y^2+1)`.

Consequently the signed-channel part has absolute value less than
`(3/2)*eta*T*(y^2+1)`, and in particular

`(1/2)*T*(y^2+1) < F(B,y) < 2*T*(y^2+1)`.

This proves F(B,y)>0 for every integer y, with no hypothesis on the
packed code g or its size. It closes the proof-order issue that a merely
bounded-g positive carrier would leave open.

## 5. Carry source and all necessary ranges

Define

```
N0 = B^(W+1), Z = B^(K+1), ell = sum_i B^w_i,
At = sum_j B^q_j,
Mc = N0-1-(b-1)*ell,
y = g+ell,
Jc = 2*F(B,y)+At,
Sc = g+N0*Jc,
Tc = Mc+N0*(B-2)*At.
```

For every g>0, Jc and Sc are positive. The digits of Mc in base B are B-b
at the 31 weights and B-1 at the other positions through W; thus
0<=Mc<N0 and Tc>=0, without requiring b to be a power of two.

If g<4*b*B^W, then g<N0. Distinct weights give ell<2B^W, so
`y<(4b+2)B^W <= 5bB^W`. The preceding positivity bounds imply

`0<F(B,y)<52*b^2*B^K`.

Also At<B^K, hence

`0<Jc<105*b^2*B^K < B^(K+1)=Z`.

The last inequality uses beta>105. Similarly `(B-2)*At<Z`.
Integrality now gives `0<=Sc,Tc<N0*Z=B^E`.

## 6. Exact zero test despite signed borrows

When b is a power of two, B and N0 are powers of two. The low-bit condition
`g & Mc=0` together with g<N0 is equivalent to the unique decoding

`g=sum_i n_i B^w_i, 0<=n_i<b`.

Then y=sum_i z_i B^w_i with z_i=n_i+1, so 1<=z_i<=b and
z=sum_i z_i<=31b. If h_s is coefficient s of the full polynomial
F(t,sum_i z_i t^w_i), then

`|h_s| <= (M+1)*z^2 + M*z + M+1 < 2048*M*b^2 = B/4`.

For the explicit last inequality, M>=2 and b>=2 bound the left side by
`M*b^2*(1441.5+15.5+0.375)`, strictly below 2048*M*b^2.
The product degree is at most K. In the signed expansion of Jc the
coefficient at s is `2h_s+epsilon_s`, where epsilon_s is 1 at the targets
and 0 elsewhere.

Ordinary base-B Euclidean digit normalization has incoming carry always
-1 or 0: the strict bound |h_s|<B/4 proves this inductively, starting at 0.
At a target, the normalized digit avoids the mask B-2 iff h_s=0. Indeed,
for h_s=0 it is 0 or 1; for positive h_s it is at least2 and below B;
for negative h_s the normalization yields a digit at least2. An incoming
borrow does not change this equivalence.

Concatenation at N0 and the extraction identity therefore give

`Sc & Tc=0` iff `g=sum n_i B^w_i` and `r_j(n+1)=0 for all j`.

This is the complete unbounded source soundness theorem in the range
required by the ratio bridge. The AND symbol occurs only in the proof.

## 7. Two-block binomial adapter for nine unknowns

Put

```
L=4*b*B^2241,
N=2^(8*kappa-10)*b*B^1178,
R=(Sc+Tc)*L+L-1-Sc,
Gcap=32*b*B^108.
```

For ALL outer assignments b>=2,g>0, positivity follows from
`R=(L-1)*Sc+L*Tc+L-1`, so R>=8, N>=8 and 0<b<=R,N.
These statements precede power-of-two recovery and the g bound.

When the ratio bridge supplies g<4*b*B^W, the range proved above gives
Sc+Tc<2B^E<L. If b=2^k and B=2^v, the lower and upper blocks of R are
therefore disjoint, and

`pop(R)=log2(L)+pop(Tc)-[pop(Sc)+pop(Tc)-pop(Sc+Tc)]`.

The bracket is nonnegative, vanishing exactly when Sc&Tc=0. The exact mask
population is `(W+23)v-31k-22`, while `log2(L)=2+k+Ev`. Therefore

```
log2(L)+pop(Tc) = H*v-30k-20
 = 2*(8*kappa-10+k+1178*v) = 2*log2(N).
```

Legendre's formula then proves

`N^2 divides binomial(2R,R)` iff `Sc&Tc=0`.

No leading L^2 term is necessary in R. This adapter has the exact numeric
contract required by the inherited Jones ratio lemmas.

For completeness, a positive parent solution is represented by n_i=z_i-1.
At n=0 the fifth shifted residual is 1, so the source code is nonzero.
Choose any sufficiently large power of two b>max_i n_i. Since all weights
are positive, g>=B>=b, and g< bB^W. Thus 32g<Gcap, every required bit test
passes, and the above binomial divisibility holds for arbitrarily large b.

## 8. Audit scope and reproduction

Run `python3 verify_channels.py` alongside `degree_channels.json` and
`parent_quartic31.json`. It checks the exact source identity, positions,
nonnegative exponents, separate-channel injectivity, both coherent-tuple
coefficient bounds, the carrier's absence from outputs, finite signed-digit
regressions, and the exact parity-calibration arithmetic. It does not
run Lean/Rocq or claim to re-prove the inherited compiler calibration.

The search programs are discovery tools only. Correctness depends on the
small frozen lists and the exact symbolic audit. The final consistency
proof composes this source theorem with the chosen finalizer and the
explicitly pinned parent/compiler/K215 theorems.
