# Independent audit of the structured nine-variable finalizer

## Reviewed objects and conclusion

Reviewed the builder now packaged as `code/nine_structured.py`, its generated
`circuits/nine/nine_structured_dag.json` and degree certificate (included in
`circuits/nine/verification.json` under `degree_ledger`), and the original
package-18 `nine/nine_section.tex`. The final reviewed choices are

    MD=Y(U+1)(R^2+C^2),       MF=A E+1,
    MI=FD((j+2)C^2+r^2)+2FH^2+(F-1)A^2+1,
    r=bw+phi,                 V0=PK+1,
    V1=MD MF MI+1.

These omit the unnecessary +1 and +2 of the earlier MD/V0 draft.
The code factors MI as F(D*ch+2H^2+A^2)-A^2+1; this is exactly the same
integer polynomial.

The zero-existence equivalence to the original four ratio conditions is
valid on the eight nonnegative outer coordinates. The resulting equation
has exactly nine nonnegative unknowns and exact degree

    93264*5^33+288 = 10857358574867248535156250288.

The inspected live DAG has 668 additions, 23 subtractions and 19856
multiplications, totaling 20547 operations. It has the required nine
variable leaves. The formal degree and diagonal leading coefficient
are independently reproduced below. This audit concerns the new weights
and signed-divisor finalizer, not a fresh proof of the inherited Jones,
quartic compiler, or K215 calibration theorems.

## 1. Unconditional domain facts

All shifted coordinates g,h,s,w,i,j are at least one. The bounded index
recipe makes b=y_index+1+epsilon at least two. Put B=b^5 and
q=B^(5^(nu+1)), with nu=32. Direct reduction of the packed R formula gives

    R = (b-1)ell mod q.

Indeed N=q^16, so the first large summand of R is zero modulo q and the
second has multiplier -1. Its bracket reduces to -(b-1)ell.
Moreover 0<(b-1)ell<q. For example, ell is a sub-sum of
1+B+...+B^(5^nu), b-1<B-1, and 5^nu+1<5^(nu+1).
Hence R is nonzero on every allowed outer assignment. This argument does
not use a square condition, the divisibility condition, or positivity of
m.

Let scale=Y(U+1), so A=R*scale. Since U,Y>=1,
scale>=2 and |A|>=2. Therefore D>=1 and F>=1. Also

    P=2R^2Y^2U>=2,
    K=R+1+h(P-1)>=R+P>=1.

For R>0 the last claim is immediate. For R=-r<0 it follows from
R+P>=2r^2-r>=1. Finally A(4A-5)>0 for every integer |A|>=2, so AE>=0.
These sign facts all precede the finalizer; using them creates no circular
soundness argument.

## 2. Audit of the radical majorants

The first majorant is positive and

    MD^2-D
      =scale^2(R^4+R^2C^2+C^4)+C^2-1 >= scale^2-1>0.

Thus MD>=sqrt(D), including C=0 and negative R. Likewise MF>=1 and

    MF^2-F = 2AE+E^2>=0,

so MF>=sqrt(F), including E=0.

For the final radicand, H=(j+1)C-r and r>=0. Consequently

    |CH| <= (j+1)C^2+|rC| <= (j+2)C^2+r^2 = ch.

Since Gp=FCD+F-(F-1)A and F>=1,

    |Gp H| <= FD*ch+F|H|+(F-1)|AH|
            <= FD*ch+(2F-1)H^2+(F-1)A^2.

Here |H|<=H^2 for integer H and |AH|<=A^2+H^2. Now

    sqrt(|I|)
      =sqrt(|(Gp^2-1)H^2+1|)
      <= |Gp H|+|H|+1
      <= |Gp H|+H^2+1
      <= MI.

This includes H=0, Gp=0, negative I, and negative R. All the majorants
MD,MF,MI are positive integers. Since D,F are positive,

    sqrt(|a1|)=sqrt(D F |I|) <= MD MF MI=V1-1.

Also a0=(P^2-1)K^2+1<=P^2K^2 because K>=1, hence
sqrt(a0)<=PK=V0-1. We have V0,V1>=2. Therefore, for any integer square
roots r0,r1 of a0,a1 and any choices of signs,

    V0V1+r0+V0r1 >= 1.

## 3. Audit of the signed divisor and finalizer

Put

    u=JF, v=QF+J(H-C), M=Q^2+(H-C)^2+1,
    Omega=u(2m-1),
    Theta=u(n+M)+v-Omega(2M+V0V1).

Since J=4A-5 is a nonzero integer and F>=1, u!=0. Independently of any
divisibility condition,

    |v/u|=|Q/J+(H-C)/F|
          <=|Q|+|H-C|<=Q^2+(H-C)^2=M-1.

The final polynomial is the product of the four linear factors

    Theta-Omega(sigma sqrt(a0)+tau V0 sqrt(a1)),

over sigma,tau in {-1,+1}. Because Omega!=0, a zero supplies coherent
roots with s=Theta/Omega=r0+V0r1 rational.
If s!=0, then

    2s r0=s^2+a0-V0^2a1

makes r0 and then r1 rational, hence integral. If s=0, the root bound
|r0|<=V0-1 forces |r1|<1, so the integer a1 is zero and then a0=0;
again both roots are integral. In this concrete instance a0>0, so the
second case is actually impossible, but keeping it does no harm.

Let Z=2M+V0V1+r0+V0r1. Then Z>=2M+1 and the vanishing factor reads

    n+M+v/u=(2m-1)Z.

It first forces v/u integral, hence u|v. Its left side is at least n+1,
so is positive for n>=0. Since Z>0 this forces 2m-1>0 and therefore m>0.
Conversely, if the two radicands are integer squares, u|v, and m>0,
choose integer roots and set

    n=(2m-1)Z-M-v/u.

It is an integer and satisfies
n>=2M+1-M-(M-1)=2. Its norm factor vanishes. Thus zero-existence is
exactly equivalent to the original four conditions. No assumption about
the sign of u or v entered the argument. Finally u|v is equivalent to
the original u^2|v^2 condition. All eight original outer coordinates,
the fixed quartic, and the index recipe remain unchanged.

## 4. Independent exact-degree calculation

Put L=5^33 and specialize every unknown to the same indeterminate t.
Every fixed index/coefficient remains fixed. The following leading
coefficients are independent of those fixed values. The leading term
of R comes uniquely from lambda*B*q^11*N^2, so R has degree235L and
leading coefficient1. The remaining entries follow by the displayed
polynomial definitions.

| Expression | Degree | Diagonal leading coefficient |
|---|---:|---:|
| R | 235L | 1 |
| P | 950L+3 | 2 |
| K | 950L+4 | 2 |
| A | 555L+2 | 1 |
| C | 235L | 2 |
| J | 555L+2 | 4 |
| Q | 235L+2 | 6 |
| D | 1580L+4 | 4 |
| E | 2605L+7 | 64 |
| F | 6320L+18 | 4096 |
| Gp | 8135L+22 | 32768 |
| H | 235L+1 | 2 |
| I | 16740L+46 | 2^32 |
| a0 | 3800L+14 | 16 |
| a1 | 24640L+68 | 2^46 |
| MD | 790L+2 | 5 |
| MF | 3160L+9 | 64 |
| MI | 8370L+23 | 2^16 |
| V0 | 1900L+7 | 4 |
| V1 | 12320L+34 | 5*2^22 |
| u | 6875L+20 | 2^14 |
| v | 6555L+20 | 24576 |
| M | 470L+4 | 36 |
| m | 2221L+11 | -512 |
| Omega | 9096L+31 | -2^24 |
| Theta | 23316L+72 | 5*2^48 |

There is an important equal-degree subtraction in the final expression.
Theta^2 and Omega^2 V0^2 a1 both have degree46632L+144. Their leading
coefficients are respectively 25*2^96 and4*2^96. Their difference is
21*2^96, not zero. The omitted Omega^2 a0 term has lower degree.
Thus the square of that bracket has degree93264L+288 and leading
coefficient441*2^192. The final subtracted term
4 Omega^4 V0^2 a0 a1 has degree68624L+220, strictly smaller.

These degree upper bounds hold for the full multivariate circuit; the
nonzero diagonal specialization attains them. Therefore the total degree
is exactly93264L+288. The inspected certificate reports exactly this degree
and the exact integer

    441*2^192
    =2768201865305526216851583135634580889501138751008639220187136.

## Boundaries

The new proof establishes a replacement finalizer for the existing
Jones ratio reduction, and the audit checks its implementation and size.
The fixed quartic-to-K215 bridge and the calibration to syntactic ZFC
refutations remain inherited dependencies. Neither finite modular checks
nor this audit are new kernel formalizations of that chain. No global
nine-variable degree optimality is claimed.
