# Inputless ordinary-strong reduction

Research derivation against ProveIt commit
`3b201cdea32d2c816f5f3d20734051f25fd3ef14`.

## Equations and metrics

Use the four fixed ports and the fifteen positive unknowns of package
06-blank67. Keep its definitions q, X, Y, E, k, c, a, H, Delta, D, C,
R, V and the first, main, index, and transport factors N1, N2, NI, NT.
Replace only the strong/auxiliary part by

    I = i*c^2,
    A0 = Delta*(f^2 - 1),
    NA = A0*(V^2 - y^2) + y^2.

The six equations are

    N1=N2=NA=NI=NT=1,   I^2=A0.

The literal source has 61 operations = 34 multiplications + 27 additions
or subtractions. Its six exact residual degrees, in that order, are
22,18,28,7,2,22. The six-square finalizer has 78 operations and degree56.

A particularly useful four-equation presentation is

    N1*NT=1,   N2*NI=1,   NA=1,   I^2=A0.

It has 63 operations =36M+27A and residual degrees24,25,28,22. Its sum
of four squared residuals is a single degree56 polynomial evaluated in
74 operations =40M+34A. These four equations are tuplewise equivalent
to the six equations on the declared positive domain: each factor in
either product equation is an integer unit, N1 cannot be -1 by the
consecutive-product negative Pell descent, and N2 cannot be -1 modulo4.
Thus NT=NI=1 as well. No high-level compiler theorem is needed for this
local four-to-six equivalence.

Another single equation is

    N1*N2*NA*NI*NT*(1+I^2-A0)-1=0.

It costs69 operations =39M+30A and has exact degree99. Its sign proof
is the ordinary-strong proof of02-system63 with the marker removed and
the inputless budget/transport of06. The strong unit
1+I^2-Delta*(f^2-1) cannot be -1 modulo4: when Delta=0 mod4 it is
1+I^2, and when Delta=3 mod4 it is I^2+f^2. Once it is+1, NA has square
coefficientI^2 and also cannot be -1 modulo4. The first/main norm signs
are as above, and the index/transport signs are resolved by the native
Pell-index proof. This product is not needed to establish the simpler
four-equation/SOS result.

### Signed bootstrap for P69

The following is the separate bootstrap required for P69; the earlier
paragraph does not import the six-system's C>0 hypothesis prematurely.
After the norm-unit signs have been proved, write NI=epsilon and NT=nu,
where epsilon,nu are ±1 and epsilon*nu=1. If C<0, then NT is at most
`-(K+w)+1-F<-1`, a contradiction. Hence C>=0. If C=0, its only unit
case at q>=16 is F=2,z=1,NT=-1; keep this branch until sign recovery.

The lower bound on G=q^2-C-qF is G>=2q-1 when C>0 (use
F+C<=q-1); in the exceptional C=0 case G=q^2-2q>2q-1. The simpler
upper bound G<=q^2-q and the mask bound
`(MC+q*MF)J<(1+2q)(q-1)` therefore give the deliberately weak estimates

    (2q-1)(q^2-1)<R<q^4-q^3+q^2-1,
    E>=q^4>R+q^3-q^2+1>R+5,    a>R+2.

The first/main norms supply p>n and
`2n=R+epsilon modE`, hence n>=(R-1)/2. The large-index estimate
c>A*Delta^2 and c>2p is unchanged. Also k=R+epsilon+hE>2R,
so c>2R. Thus f>c^2/A>2c and
`A0-(Rf^2+c)=(Delta-R)f^2-Delta-c>0` follow by exactly the ordinary
bootstrap given below, before using the auxiliary rank or step-down.
They exclude V<=1 and restore the same positive o,j. The relaxed rank
and signed step-down give p=R.

Now write 2n=R+epsilon+vE with v>=0. If v>=1, then
2n>=R-1+E>2R, contradicting n<p=R; hence 2n=R+epsilon. If epsilon=-1,
then p=2n+1. With Q2=chi_A(2)>P, Pell duplication gives
`psi_A(2n)=2A*psi_Q2(n)>2A*psi_P(n)=A*k`.
Consequently c=psi_A(2n+1)>A*k>k(Y+1), contradicting c=kY+eta and
0<eta<k. Therefore epsilon=nu=1. The exceptional C=0 branch is now
excluded, and all six ordinary equations hold. This proves the full
positive zero-set equivalence of P69 and the six-system, including its
ordinary strong square, without assuming a sign before it is recovered.

## Soundness of the six-equation system

The difference from normalized06 is real: ordinary strong does not
allow silently dividing i by Delta. Use the actual relaxed strong-rank
theorem in `Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md`, also used by
02-system63, rather than claiming coordinatewise equivalence with06.

1. The exact transport equation forces C>0. If C<=0 its left side is
   `(K+w)C+1-F-(z-1)(q-1)<=0`, contradicting equality to1.
   Thus0<C, F+C=q-alpha<q. The raw native-mask bounds give
   `(2q-1)(q^2-1)<R<q^4-q^3`, E>=q^4>R+q^3, and a>R+2.
2. Set A=a+2 and P=2XY^2+1. The positive first/main norm equations give
   k=2psi_P(n), c=psi_A(p), D=chi_A(p). P>A and c>k imply p>n.
   From k=R+1+hE and P=1 modE, 2n=R+1 modE, so
   n>=(R+1)/2. Elementary Pell growth gives c>A*Delta^2, c>2p,
   and c>2R. These conclusions precede every auxiliary argument.
3. The ordinary strong equation implies
   f^2=1+i^2*c^4/Delta and hence f>c^2/A>2c. With
   A0=Delta*(f^2-1), one has
   `A0-(R*f^2+c)=(Delta-R)f^2-Delta-c>0`.
   The auxiliary norm forces V>1 exactly as in02: any |V|>1 satisfies
   |V|>=2A0-1; the bound V>-(Rf^2+c)>-A0 excludes negative V, while
   V=0,+1,-1 are excluded by the norm and V=-c modf, 2<c<f/2.
4. The relaxed strong-rank theorem applied to c>A*Delta^2 proves
   `f=chi_A(m), p|m, c|m, i*c^2=Delta*psi_A(m), m>=c>2p`.
   It does NOT assert c^2|psi_A(m) or Delta|i. It does imply
   c^2|(f^2-1). Restore the proof-only positive integers
   `o=cT-Rf` and `j=Tf-R*(f^2-1)/c-1`.
   Then of=V+c>0, jc=V+R>0, V=of-c=jc-R.
5. The auxiliary Pell base is I=i*c^2 with I^2=A0. The half-parameter
   odd-index and signed step-down proof now applies with m>2p and c|m,
   and gives R=+p or-p modc. Since 0<R,p<c/2, p=R. The no-wrap
   argument using E>R+q^3 gives2n=R+1.
6. The lower ratio estimate gives Y>X^((R-1)/2)/3 and a>2^R.
   Projection moduloH=4a+3 and the main-root identity give X=2^R.
   Since q|X, q=2^t; R>3q>3t allows restoration of X/q^3.
   The retained Y=sq^3 then gives the original half-binomial population
   threshold, followed by the inputless native masks, synchronization,
   forced Start and finite accepting computation exactly as in06.

All ordinary-strong steps are generic arithmetic; the coefficient ports
must come from a valid inputless compiler. No fixed-marker coefficient
from02 is mixed with06's inputless coefficients.

## Completeness

Take the canonical normalized positive solution from06. Keep every
coordinate other than i, and set i_ordinary=Delta*i_normalized.
Then I^2=(i_normalized*Delta*c^2)^2=Delta*(f^2-1), so the strong and
auxiliary values coincide with the original ones. This proves existence
of all new forms whenever the original accepting computation exists.
No division by Delta or equivalence of arbitrary strong tuples is used.

## Exact degree certificate

Write Q=beta*J and k0=eta+zeta for highest homogeneous forms. The six
residual leading forms are

    N1-1:  -w^2*k0^2*s^4*Q^14                              [degree22]
    N2-1:   8*gamma*w^2*k0*s^3*Q^11                       [degree18]
    NA-1:   w^2*k0^2*s^4*Q^14*T^2*f^4                    [degree28]
    NI-1:  -h*w*s*Q^4                                    [degree7]
    NT-1:   w*(Q-F-alpha)-z*Q                             [degree2]
    I^2-A0: i^2*k0^4*s^4*Q^12                            [degree22]

In the four-equation SOS the unique degree28 residual is NA-1, hence
the exact degree56 leader is

    w^4*k0^4*s^8*Q^28*T^4*f^8.

This is nonzero for every beta>0. The P69 leading form is

    8*gamma*h*i^2*w^7*s^16*k0^9*Q^55*T^2*f^4
        *(w*(Q-F-alpha)-z*Q),

which is nonzero and has degree99.

## A quartic in33 positive unknowns

In the existing quartic34 lift, ordinary strong permits replacing
I=i*K by I=i*C2. The register K=D^2-1=Delta*C2 is then unnecessary.
Delete that variable and its two equations, and insert the one quadratic
equation D^2-Delta*C2=1. The result is24 quadratic equations in33
positive unknowns, emitted literally in ../circuits/ordinary_quartic33.json.
Projection gives the ordinary six-equation system above. All introduced
registers are positive on its solutions; in particular V>1 and
g=y^2-V^2>0 follow from the already established auxiliary norm. Conversely
every ordinary six-system solution extends to these registers. The sum
of their24 squared residuals has exact degree4, with coefficient1 on
tau^4. Shifting all33 coordinates by1 gives33 nonnegative variables.

## Logical status

This is an ordinary mathematical reduction using pinned compiler and
Pell lemmas. The finite algebra checks support circuit transcription
and degree/ledger claims, not Con(ZFC), nonhalting, or a kernel-checked
end-to-end theorem. The usual K215 calibration plus the native compiler
and this reduction are formalizable in ZFC and yield the requested
equivalence without a consistency premise.
