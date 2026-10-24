# Independent mathematical review of adaptive_centered12

Reviewed on 23 October 2026:

* `agent_pell/NEW_RESULT.md` and its 102-gate literal JSON circuit;
* source 61 `positive/PROOF13.md`, `positive/AUDIT12.md`, and
  `positive/SIGNED_INDEX_LEMMA.md`, fetched independently at ProveIt
  commit `9cca523d9f27ad39d52993f4065cbd7e58f8bdd4`.

The review found no error in the new unbounded existence reduction. This
is internal independent AI-assisted mathematical review. It is not a
proof-assistant certificate or external peer review. The source-44 compiler
and K215/refutation calibration remain inherited dependencies.

## Centered norm and exceptional branch

With `Delta=A^2-1`, `I=i*c^2`, `D=1+Delta*I^2`, and `t=A*I+n`, positivity
gives `I>=9` and `t^2>D`. If `L=2*(Q-1)*(V+t)=0`, then `V=-t` and

    U=(Q-1)*D-Q*t^2+1 < 1-D < 0.

Thus a zero of `U^2-D*L^2` cannot have L=0. The rational number f=U/L
satisfies the monic equation f^2=D, so f is integral. Subtracting Lf from
U yields exactly `(Q-1)*(V+t-f)^2-Q*V^2+1=0`.

The definition `V=D*(c*T-R)-c`, with `D>c+1`, implies |V|>1 without
assuming any equation: the integer `c*T-R` is either <=0 or >=1.
Consequently the recovered auxiliary ordinate satisfies |y|>|V|, and
`u=|y|-V>0`. Replacing f by |f| restores the source's normalized strong
equation. The recovered u restores its auxiliary residual exactly because
`u*(2V+u)=y^2-V^2`.

## Canonical positivity and the realized T coordinate

Source 61's independently inspected `SIGNED_INDEX_LEMMA.md`, Section 5,
provides the needed exact auxiliary witness. At canonical `R=3 mod4`, put
`S0=Delta*I`,

    V*=chi_S0(R)/S0,  y*=psi_S0(R),
    T=(V*+c+R*f^2)/(c*f^2).

The last expression is a positive integer by the two congruences
`V*=-c mod f^2` and `V*=-R mod c` and `gcd(c,f^2)=1`. Hence the new proof
does not assume that an independently chosen auxiliary V happens to be
realizable by its retained positive T variable.

For R>=5, `V*>S0^4=Q^2`. The auxiliary norm gives `y*<2V*` and

    y*-V* = (V*^2-1)/((Q-1)*(y*+V*)) > V*/(4Q) > Q/4 > I.

Also `f>(A-1)*I`, hence `A*I-f<I`. Therefore
`n=f+y*-V*-A*I` is positive. This proves the required centered completeness
without invoking an unspecified ability to enlarge an auxiliary witness.

## Adaptive main carrier

Before q|X is known, the first carrier already gives q^3|Y and C>0, hence
`3q<R<q^4-2`. Its J residue gives q=2 mod3. Since
`H=4Y(X+1)+3`, `gcd(q,H)=1`, `gcd(Y,H)|3`, and H is odd.
With `S=4qY`, `M=qS`, and `mu=S/gcd(S,H)`, one obtains

    mu >= 4qY/3 > R+1,
    S | 4XY^2,  M | 4XY^2.

These divisibilities use only q^3|Y, not the later conclusion q|X.
The new main residual gives an integer positive main root and
`M | H(SX-v)`, hence mu|v. First-Pell and signed-auxiliary index recovery
give the exact main rank p=R and
`mu | 2*n0-R-1`. The strict half-interval yields `2*n0=R+1`.
Thus v is a positive multiple of 4XY^2, hence of M. Returning to the
carrier gives q|HX, and gcd(q,H)=1 now gives q|X.

The restored old coordinate is
`gamma_old=gamma+X/q-v/M`. Its positivity follows from
`Dmain>(a+1)c` and c>X. Conversely a canonical source witness has
`v/M>=XY/q^2=wY/q>=w*q^2>w`, so
`gamma=gamma_old-w+v/M>0`. This closes both directions of the adaptive
carrier reduction.

## Finalizer and limitations

Each of the three residuals is a square modulo 4, because its subtracted
norm coefficient contains an even squared multiplier. A product
`(1+A0)(1+A1)(1+N)=1` therefore forces each factor to be +1; the -1
possibility would make a residual congruent to 2 modulo 4. The finalizer
does not require the residuals themselves to be nonnegative.

This review concerns the unbounded mathematical arguments. The agent's
separate exact sparse-polynomial/circuit checks establish the reported
degree and arithmetic count; the present note does not substitute random
evaluation for those checks. The inherited native semantic theorem and
logical calibration have not been re-proved in this review.
