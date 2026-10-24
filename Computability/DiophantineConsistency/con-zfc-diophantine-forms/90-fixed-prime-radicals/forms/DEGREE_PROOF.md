# Exact degrees of the six completed norm circuits

All degrees count existential integer coordinates only. The six authenticated
ports are fixed numerals. The term `norm` below denotes the denominator-cleared
multiquadratic polynomial before a separate guard finalizer, where present.

## 1. Prefix degrees and nonzero leading forms

The ordered polynomial definitions in each packet give:

| Expression | Degree |
|---|---:|
| q,W | 1 |
| F,X | 2 |
| Y | 4 |
| R | 5 |
| E,a,H | 6 |
| k | 7 |
| eta,zeta | 11 |
| Delta | 12 |
| u=EYk | 17 |
| Afirst=u(u+k)+1 | 34 |
| m=(2r+1)c² | 3 |
| Df=1+Delta*m² | 18 |
| I=Delta*m | 15 |
| Q=I², delta=Q-1 | 30 |
| V=Df(cT-R)-c | 23 |
| D0=X+ac | 7 |
| Cmain=Delta*c²+1 | 14 |
| Nguard | 44 |
| Spositivity | 44 |
| rad_A=9H²Afirst | 46 |
| rad_B=81H²Df | 30 |
| rad_D=Cmain | 14 |
| rad_G=6561H²Spositivity | 56 |
| Cnum=729H²(QV²-1) | 88 |

These are exact, not merely syntactic bounds. To see noncancellation, write
subscript0 for the highest homogeneous part. Then q0=6 beta*j, W0=12w,
F0=W0*C-z*q0, X0=q0W0, Y0=2v*q0³, a0=E0=X0Y0,
H0=4a0, R0=-q0³F0, k0=hE0, u0=E0Y0k0,
m0=2r*c², Df0=a0²m0², Q0=a0^4*m0²,
V0=-Df0*R0. Every displayed factor is nonzero for the authentic beta.
Also eta0=-Y0k0, zeta0=Y0k0, and

    (Nguard)0=-(eta0*zeta0)²,
    (Spositivity)0=-24(eta0*zeta0)².

The guard's dominating term cannot cancel with its lower-degree native
determinant product. Thus both have degree44 and nonzero top form.

## 2. Exact norm identity and denominator clearing

For m ordinary core radicands A_i, let

    F_(2^m)(z)=product over all signs of (z + sum_i sign_i sqrt(A_i)).

This is a monic integer polynomial in z and the A_i. The supplied circuit
builds it by successive conjugation. If its Taylor expansion at z is
F(z+t)=sum c_j t^j, put n=2^(m-1) and

    E=sum_(j=0)^n c_(2j) Cnum^j delta^(n-j),
    O=sum_(j=0)^(n-1) c_(2j+1) Cnum^j delta^(n-1-j).

The circuit computes

    E²-delta*Cnum*O²
      =delta^(2^m) F_(2^(m+1))(z;A_i,Cnum/delta).

The displayed left side is a division-free polynomial identity. It is valid
as a rational-function identity and hence as a cleared polynomial identity.
The source prefix makes delta=-1 modulo3, so no zero denominator is admitted.

The DAG generators include scalar multiplications and squarings in their
binary-operation counts. Constants and register reuse cost zero. No claim
of arithmetic-circuit optimality or bit complexity is made.

## 3. Why the degree arguments are exact

Substitute each coordinate by t times an independent indeterminate and work
over the rational-function field in those indeterminates. Degree is the
highest exponent of t. Formal square-root expansions in its algebraic
Laurent-series extension calculate the norm's leading term exactly.
For a nonzero polynomial p(t) with even degree, sqrt(p(t)) has degree half
that degree and a nonzero leading coefficient in that extension. Selecting
the two signs accounts for all norm factors. This is a symbolic degree proof,
not a bounded numerical experiment.

For the ordinary root coordinates the needed expansions are

    sqrt(Afirst)=u+k/2+O(t^-3),
    sqrt(Df)=(a+2)m+O(t^-3),
    sqrt(Cnum/delta)=27HV+O(t^-1),
    sqrt(Cmain)=(a+2)c+O(t^-5).

The auxiliary expansion follows from

    Cnum/delta=(27HV)²+729H²(V²-1)/delta.

Here the correction radicand has degree28, versus degree58 for (27HV)².
The notation O(t^d) means a formal Laurent series of degree at most d.
All inequalities of degrees used below are strict.

## 4. Thirteen-variable degrees

The four integer core roots have degrees23,15,7,28. The auxiliary root has
degree29, and delta has degree30.

For the uncentered carrier z=D0+Hxi, degree7, every one of the32 norm factors
has degree29. Clearing delta^16 contributes480, so

    degree=32*29+480=1408.

More directly, the unique highest-weight monomial is Cnum^16, with nonzero
coefficient1. The exact leading form is (Cnum0)^16.

For z=D0+H(xi+27V), half the norm factors have the auxiliary root's large
branch, of degree29; in the other half that branch cancels and the
pentagonal guard root of degree28 dominates. Thus

    degree=16*29+16*28+480=1392.

Writing Wy=27HV, the exact leading form is

    delta0^16 * (2Wy0)^16 * (rad_G0)^8.

It is nonzero. The sign of rad_G0 is harmless: this is a formal algebraic
norm and its eighth power is nonzero. The result is a single polynomial;
there is no additional finalizer for the thirteen-variable endpoint.

## 5. Fourteen-variable degrees

The integer core roots now have degrees23,15,7; the pentagonal root is absent.
The retained integer joint-positivity residual g has degree44. The single
polynomial is (1+4norm)(1+4g)-1. Its degree is deg(norm)+44 because its
highest homogeneous part is16*norm0*g0, a nonzero product.

For the uncentered carrier, the16 factors all have degree29. Hence
deg(norm)=16*29+8*30=704 and the final degree is748.

For auxiliary centering alone, eight factors have degree29 and eight have
degree23. Hence deg(norm)=8*29+8*23+240=656, final degree700. Its norm leading
form is delta0^8*(54H0V0)^8*(rad_A0)^4.

For full integral centering

    z=D0+H[xi+27V+3u+9(a+2)m],

the factors split into eight of degree29, four of degree23, two of degree15,
and two of degree13. In the last pair the remaining first-root correction
3Hk/2 dominates the carrier remainder and main root (both degree7).
Consequently deg(norm)=232+92+30+26+240=620 and the final degree is664.
A nonzero leading product is

    delta0^8 (54H0V0)^8 (6H0u0)^4
       (18H0a0m0)^2 ((3/2)H0k0)^2.

For half-centering, all four radicands are multiplied by4 and

    z=2D0+H[xi+54V+6u+3k+18(a+2)m].

The large branches again contribute232+92+30. The remaining two factors
now have degree7, with leading forms H0*xi and H0*(xi+c). Therefore

    deg(norm)=232+92+30+14+240=608,
    final degree=608+44=652.

The corresponding norm leading form is

    delta0^8 (108H0V0)^8 (12H0u0)^4
       (36H0a0m0)^2 H0²*xi*(xi+c),

which is nonzero. This last carrier uses an existence-preserving integral
reparametrization, not a bijective change of xi: after extracting the roots,
the main congruence gives H | 2(D-D0); H is odd, so H | D-D0. Completeness
chooses the displayed integer doubled carrier. No parity witness is needed.

## 6. Finite certificate and its limits

`verify_final_forms.py` authenticates all fixed integer payloads, checks the
division-free DAGs, all input liveness and all operation counts, and evaluates
each whole polynomial after a specified linear substitution over F_p.
The computed nonzero leading coefficient at exactly the proved degree is an
independent exact lower-bound certificate. Fast polynomial multiplication
uses Kronecker packing with an explicitly checked carry bound; it is exact
integer arithmetic, not floating-point FFT interpolation.

Those finite checks supplement the unbounded proof above. They do not decide
consistency, prove the inherited native compiler, or supply a new complete
Lean/Rocq proof artifact.
