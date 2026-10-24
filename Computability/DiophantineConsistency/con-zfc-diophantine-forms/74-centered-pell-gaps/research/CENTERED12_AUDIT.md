# Independent audit of the centered twelve-variable elimination

This audit concerns the exact formulas supplied by the root researcher in the current session. It establishes a relative algebraic equivalence with the specified thirteen-variable source. It does not independently reprove the source compiler/refutation theorem or claim external peer review.

## Definitions

On the positive outer domain, let

    A=a+2, Delta=A^2-1, I=i*c^2,
    D=1+Delta*I^2, Q=Delta^2*I^2, d=Q-1,
    f0=A*I, e=1-I^2,
    V=D*(c*T-R)-c.

Assume `a>=2`, `c>=3`, `i,T>=1`; hence `Delta>=15`, `I>=9` and `d>0`. For a new positive variable n put

    x=n+f0+V,
    B=2*d*x,
    H=d*(n^2+2*V*n+e)-V^2+1,
    N=H^2+2*B*f0*H-B^2*e.

The old auxiliary/strong pair is

    f^2=D,
    Q*V^2-d*(V+u)^2=1,

with f,u positive.

## Exact identities and soundness

Since `f0^2+e=D`,

    N=(H+B*f0)^2-B^2*D.

Also, with `C=H+B*f0`, expansion gives

    C=d*(x^2+D)-Q*V^2+1.

If B=0 then x=0, and the latter formula yields

    H=Q*(D-V^2)-D+1
     =Delta*I^2*(Delta*(D-V^2)-1).

The last factor cannot vanish because Delta is an integer greater than one. Thus a zero of N necessarily has B nonzero. It gives the rational number `f=C/B` satisfying the monic equation `f^2=D`. Rational square-root integrality gives an integer f, and f is nonzero since D>0. Setting `y=x-f` and using the displayed formula for C recovers

    Q*V^2-d*y^2=1.

There is no hidden assumption on the sign of V. Indeed `V=D*b-c` with integer `b=c*T-R`, and `D>c+1`, `c>=3`, imply `|V|>1` in all three cases `b<0`, `b=0`, `b>0`. The norm then implies

    y^2-V^2=(V^2-1)/d>0.

Consequently `u=|y|-V` is a strictly positive integer. Replacing f by `|f|` restores the old positive pair, with the same outer coordinates. The old formulas use f only through f squared at this interface, so the sign replacement is legitimate.

## Completeness for the canonical source family

Let `M=Delta*I`. The canonical old witnesses use

    f>0, y=psi_M(R), V=chi_M(R)/M,

with odd `R>=5`. The Pell identity

    chi_M(R)=M*psi_M(R)-psi_M(R-1)

gives an especially short gap estimate:

    y-V=psi_M(R-1)/M
       >=psi_M(4)/M
       =8*M^2-4.

Since `Delta>A`, one has `f0=A*I<M`. Therefore

    n=f-f0+y-V>0.

It is an integer, and substituting it into x makes `x=f+y`; the old equations now imply N=0 exactly. The argument is for the specified cofinal canonical family. A positive inverse n for every arbitrary old positive tuple is unnecessary and has not been asserted.

## Modulo-four finalizer

The new B is even identically, so `N=H^2 mod 4`. If q is even, the retained first and second carrier moduli are even; hence their residuals A0 and A1 are squares modulo four as well. Therefore

    (1+A0)*(1+A1)*(1+N)-1=0

holds over integers exactly when `A0=A1=N=0`: each integral factor must be +1 or -1, and the square-modulo-four property excludes -1. No nonnegativity assumption about the residual polynomials is used.

Replacing `J=3j+1` by `J=6j+1` makes q even because beta is odd. Canonical J is odd and 1 modulo 3, so the canonical family still has J=1 modulo 6; sufficiently padded canonical J gives j>0.

## Exact degree audit

With all supplied variables of degree one and the coefficient ports of degree zero:

| Register | Degree |
|---|---:|
| Delta | 4 |
| c | 2 |
| I | 5 |
| D | 14 |
| Q,d | 18 |
| f0 | 7 |
| e | 10 |
| R | 4 |
| V,x | 18 |
| B | 36 |
| H | 37 |

The three displayed terms of N have respective degrees 74, 80, 82. The degree-82 term is uniquely `-B^2*e`; its leading form is nonzero because the leading form of e is `-I^2`. More explicitly, writing the leading forms as Delta_*, I_* and R_*, the leading form is

    4*Delta_*^6*I_*^10*R_*^2.

Thus N has exact degree 82. With retained residual degrees 15 and 13, the product finalizer has exact total degree 110. Polynomial rings over the integers are integral domains, so the product of the three nonzero leading forms cannot cancel.

## Finding

No flaw was found in the stated elimination, its handling of B=0, rational-to-integral recovery, sign recovery, canonical completeness, modulo-four finalizer, or degree count. The principal proof boundary remains the explicitly retained thirteen-variable source and its compiler/Pell semantic theorems.
