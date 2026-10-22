# Independent mathematical audit of the two twenty-eight-integer tradeoffs

Both `INTEGER28_AMALGAM_PROOF.md` and `INTEGER28_PROOF.md` pass the
signed-domain/root-recovery audit. They remain useful lower-degree or
lower-operation tradeoffs, conditional on their explicitly bound compiler
and package-14 signed-domain theorems.

## Normalized two-root merger, degree 258

The normalized strong factor `Ns=f^2-Delta(ic^2)^2` cannot be -1 by the
same mod-four argument as the main norm. Therefore Ns=1 is established
before using `K=Delta(f^2-1)=(Delta i c^2)^2>0`.

The retained main norm excludes zero square scale before any first-root
recovery. On the resulting positive scale, a>XY and c>kY give

    K>=Delta^2 c^4>L^4,
    1<A=1+L^2+Lk<1+2L^2<L^4<K.

Here L>k and L>=2 hold on the source geometry. Thus if t=0, the resultant
would force `K(A-V^2)=A-1`, contradicting `0<A-1<K`. This closes the only
new denominator branch caused by allowing signed t.

For t!=0, `tau=U/(2(K-1)t)` is rational with integral square A, hence
integral, and y=t-tau is integral. Expansion restores the exact auxiliary
norm. No sign of f,T,tau,y,gamma is needed. Canonical odd-i/square-w
completeness extends simply by t=tau+y.

The degree calculation is correct: the normalized strong factor has
degree 66; the root resultant has degree 140, with its unique leading
contribution U^2 and U led by dA. Adding the retained outer degrees
35,13,4 gives **258**. The displayed nonzero monomial coefficient
`-32 beta^80` agrees with direct leading-form multiplication.

## Gap-root norm, degree 426

The identity

    A-Bf=Q[V^2-(V+e)^2]+(V+e)^2-1

is exact when f^2=d and V=vf-b. Expanding its right side gives
`dv^2+b^2+2(Q-1)be-(Q-1)e^2-1-2vf(b+(Q-1)e)`, exactly A-Bf.

The weak signed-h bootstrap is sufficient for Delta>R and c>2. Thus
`Q-b=(Delta-R)d-Delta-c>1`, giving `2<b<Q-1`. Consequently
`r_gap=b+(Q-1)e` is nonzero for every integer e. This avoids a generic
nonvanishing assumption about the root denominator.

When T=0, the norm forces A=0 and therefore
`Qb^2-(Q-1)(e-b)^2=1`. Its integral second coordinate and 1<b<Q give
the stated consecutive-integer contradiction. Hence T is nonzero and
B=2v r_gap is nonzero. Rational reconstruction f=A/B then gives an
integer f, and y=V+e is integral without an additional saturation lemma.
The original signed normalized equations are restored exactly.

Canonical completeness uses the same odd-i/square-w witnesses and the
integral substitution e=y-V, with no sign restriction on e. The count
is seven positive triples plus seven unrestricted coordinates, hence 28.

The exact-degree calculation is also correct: cancellation makes A's
unique degree-165 leader `2Qeb`; A^2 has degree 330, strictly above dB^2
at degree 270. The outer product has degree 96, giving **426**. Direct
leading-form multiplication gives the asserted coefficient
`-8192 beta^134` for the displayed degree-426 monomial.

## Boundary of this audit

No mathematical gap was found in either signed-lift extension. This note
does not re-prove a newly selected coefficient compiler or replace its
whole-tuple transfer proof. The final circuit hashes, operation ledgers,
and selected fixed coefficient backend remain the responsibility of the
corresponding independent artifact checks and binding manifest.
