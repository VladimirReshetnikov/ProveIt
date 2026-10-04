# Deleting the first-index coordinate from current84 collapses every input

The complete candidate saved in the [receipt](complete80_first_index_deletion_collapse.json)
costs **80=45M+35A**, has **17 strictly positive witnesses**, and has exact degree
**180**. It is **refuted as a replacement for the inherited compiler**: for every
authentic fixed-program numeral tuple and every ordinary input x>0, it has a full
positive integer zero. In particular it admits every input for the compiler of
the empty c.e. set. This is not a universal operation bound; the sound84 polynomial
and its existing tradeoffs remain unchanged.

This extends Report41's complete normalized81 counterfamily to the actual
[scaled-strong84 source](complete84_scaled_strong_output.md). The earlier
[first-index scout](first_index_quotient_deletion_scout.md) proved only the literal
81/82 deletions and a subsystem obstruction; the subsequent
[scaled obstruction](first_index_scaled_obstruction.md) still left input and
auxiliary constraints uncompleted. Report41 supplies the missing uniform
completion. Its exact archived proof is independently challenged below rather
than inferred from its recorded test results.

## 1. Provenance, full source, and identities

The immutable archive is `docs/incoming/Failure_of_First_Index_Deletion_Package.zip`
at commit `c5612efa171fa62470285049ee45d1d06ee25578`, Git blob
`0717dc5ae5cf5f44afbee2b7fe14aa8da4a2f186`, SHA256
`1ace5ba39dd17fa53972420ba4db4171174def1244f1c377f31089f97921f2fd`.
The helper pins seven exact evidence members, including the complete
`FULL_COUNTERFAMILY.md`, `SOURCE_CORRESPONDENCE.md`, old scout JSON and compiler
recipes. Its old scout and normalized85 source bytes equal the pinned current
WIP files. All archive and predecessor programs are inert data.

From current84 delete exactly

    hpm1 = h*UM
    index_difference = R10b-hpm1
    norm_index = index_difference-r_lhs
    norm_product = norm_four*norm_index.

Change `all_units` to `norm_four*norm_transport` and remove supplied h. All other
79 rows remain literal, including the final subtraction of the computed
`A=Delta`. The only consumers of h and the three private index registers form
the displayed chain, and `norm_product` is consumed only by `all_units`. The
receipt contains all80 instructions; all instructions and free ports are live.

Write Nk=k-hE-R, let P5 be the product of the first, main, input, auxiliary and
transport factors, and let Ns=f²-Delta*i²*c⁴. These are proof abbreviations,
not supplied ports. The full outputs satisfy, over every commutative ring,

    F81 = P5*Ns-1,
    F80 = P5*(Delta*Ns)-Delta = Delta*F81,
    F84+Delta = (F80+Delta)*Nk.                         (1)

The helper reconstructs the actual old81 coefficient cone and checks every
common producer. Its `R16=Delta²*i²*c⁴` is unchanged by the current84 sharing;
the current scaled strong factor is Delta times the old strong factor. Literal
producer induction and the complete six-factor finalizer prove(1), without
unit equations or division. Whole signed/rational evaluations and full
coefficient specializations supplement those identities.

Before any zero equation, positive current source inputs give
q=(B-1)J+1>0, X=wq>0, Y=sq³>0, a=Y(X+1)>0 and
Delta=(a+1)(a+3)>0. Thus the80 and old81 positive zero sets on their identical
17 coordinates coincide. No inference that arbitrary factors must be units
from a product equaling Delta is used. The counterfamily below explicitly
sets the five unscaled factors to1 and the scaled strong factor to Delta.

## 2. Authentic fixed numerals and a factorial radix

Fix an arbitrary authentic numeral tuple of the inherited compiler and x>0.
Use its actual contract

    B=2^d>=16, ell=2d, b positive odd, K=Kconstant>0,
    0<MC,MF0<B-1, MC=2 mod4, MF_source=MF0+B-1.

The six fixed ports are exactly `Bm1,Kconstant,twice_cell_bits,inner_bits,MC,MF`,
with values B-1,K,ell,b,MC,MF_source. Hereafter MF means the shifted source
numeral. All additional compiler hypotheses remain satisfied because no fixed
numeral is changed. Bounds on native MF0 must not be imposed on MF_source.

Put I=ell*x+b and W=2^I. Choose integer L>=max(1100d,16,K,W,ell*x), and set

    t=L!, N=t/d, q=2^t=B^N, J=(q-1)/(B-1),
    t=2^a2*m with m odd,
    Q=q²-1, M=(MC+q*MF)J.

N is a positive multiple of1100, t>=64 and a2>=4. For every odd prime power
r^v dividing t, both r^(v-1) and r-1 divide t and are coprime. Thus
phi(r^v)=r^(v-1)(r-1) divides t. Euler's theorem at each odd prime power gives
q=1 mod m. This argument does not require factoring a gigantic concrete
integer in the source; it proves a property of the existential choice L!.

Choose the unique e from e0,e0+m,e0+2m,e0+3m, where 0<=e0<m and e0=M mod m,
with e=3 mod4. Since m is odd,

    3<=e<4m<=t/4.

Let Z be the least strictly positive residue of e-M modulo2^a2. Because
q=0 mod4, J=1 mod4 and MC=2 mod4, Z=1 mod4. Define

    C=W+Z, F=(K+2^e)C,
    alpha=q-F-2Z-W-ell*x,
    R=(q²-Z-qF)(q²-1)+M.                            (2)

We have C<=2t and

    F+2Z+W+ell*x <= 2t²+2t*2^(t/4)+4t < 2^t.

For t>=64 the elementary bound t<=2^(t/8) bounds the first and last terms
together by2^(t/2), and the middle term by2^(t/2); their sum is less than2^t.
Hence alpha>0 and F+Z<q. Setting G=q²-Z-qF gives
2q-1<=G<=q²-q-1, while 0<M<(q-1)(1+2q). Therefore

    (2q-1)(q²-1)<R<q⁴-q³, in particular R>q>5t+5.   (3)

Modulo m, R=M=e because Q=0. Modulo2^a2, q=0 and Q=-1, so R=Z+M=e.
Consequently R=e mod t. Also B^20=1 mod55 and N is divisible by55*20.
Grouping J into blocks of20 terms yields J=0 mod55 and q=1 mod55. Thus
55 divides R. Since t is divisible by4, R=e=3 mod4. Write

    p=R=55u, u>0, u=1 mod4.                         (4)

These choices use the actual packed R, not an independently supplied main index.

## 3. Exact first/main ratio at that packed index

Define the ordinary Pell sequences by
chi_z(n)+psi_z(n)*sqrt(z²-1)=(z+sqrt(z²-1))^n. Set

    n=40u, X=2^p, Y=2^(33u-1),
    w=X/q, s=Y/q³, E=XY,
    a=Y(X+1), A_math=a+2, Delta=A_math²-1, H=4a+3,
    P=2XY²+1,
    D=chi_A_math(p), c=psi_A_math(p),
    tau=chi_P(n), k=2psi_P(n).

By(3), p>t and 33u-1=3p/5-1>3t. Thus w,s are positive integers and the
actual asymmetric scales X=wq,Y=sq³ hold. The first and main norm factors
are exactly1 by the Pell identities.

The required ratio is strict. Put L0=2XY and M0=4XY². The exponents give

    L0^(p-1)/(2*M0^(n-1))=Y.

For z>=2, the recurrence gives
(2z-1)^(r-1)<=psi_z(r)<(2z)^(r-1) when r>=3. Since

    2A_math-1=L0*(1+1/X+3/(2XY)),
    2A_math=L0*(1+1/X+2/(XY)),
    2P=M0*(1+1/(2XY²)), 2P-1>M0,

and p>n, the lower bound implies c/(kY)>1. Write
epsilon=1/X+2/(XY)<2/X. We have (p-1)epsilon<1/2, so the elementary
binomial estimate (1+epsilon)^j<=1/(1-j*epsilon)<1+2j*epsilon gives

    0<c/k-Y<4p*Y/X=110u*2^(-22u)<1.

The final bound holds at u=1 and decreases for positive integer u.
Therefore eta=c-kY and zeta=k-eta are positive integers, giving the literal
source k=eta+zeta and c=kY+eta. No deleted index condition enters this argument.

## 4. Shared input coordinates and transport

Let z_j=chi_A_math(j)-a*psi_A_math(j) and g_j=(z_j-2^j)/H. Direct recurrence gives

    g_0=g_1=0, g_2=1,
    g_(j+2)=2A_math*g_(j+1)-g_j+2^j.

It proves that all g_j are integers and g_j is strictly increasing for j>=1.
Since I>=3 and I<t<p, define

    kappa=psi_A_math(I), mu=chi_A_math(I),
    delta=(kappa-I)/Delta,
    rho=g_I, sigma=g_p-g_I.

For odd I, psi_A_math(I)=I mod Delta; for example the recurrence modulo
Delta has odd-index values2r+1 and even-index values2r*A_math. Pell growth
makes kappa>I, so delta>0. Also rho,sigma>0 by the displayed recurrence.
The source therefore gives exactly

    D=X+a*c+(rho+sigma)H,
    index_rhs=I+delta*Delta=kappa,
    exponent_rhs=W+a*kappa+rho*H=mu.

Its input norm is1, and its shared rho is unchanged. Substitution of(2) in
the retained original slack gives `marked_rhs=C` and `W=W`; the bound has
not been weakened.

Since p=e mod t, w=2^(p-t)=2^e mod(q-1), and p-t>e. Thus

    transport_quotient=1+C*(w-2^e)/(q-1)

is a positive integer. The actual transport factor becomes

    (K+w)C+q-F-transport_quotient*(q-1)=1.

Both its fixed K and its paid asymmetric w consumer are retained.

## 5. Positive auxiliary quotient and scaled strong factor

Set

    m_aux=2cp, f=chi_A_math(m_aux),
    i=psi_A_math(m_aux)/c²,
    S=Delta*psi_A_math(m_aux),
    y_aux=psi_S(p), V=chi_S(p)/S.

Expanding (D+c*sqrt(Delta))^(2c) shows c² divides psi_A_math(m_aux):
the linear term contains2c² and every higher odd term contains c³.
Thus i is a positive integer, S>c², and S²=Delta*(f²-1).

For odd p the quotient chi_S(p)/S is an integer polynomial Q_j(S²),
j=(p-1)/2. Its identities

    Q_j(1-A_math²)=(-1)^j*psi_A_math(p),
    Q_j(0)=(-1)^j*p

follow from the Pell recurrences (equivalently, the odd Chebyshev identity).
Here j is odd, S²=-Delta=1-A_math² mod f, and S=0 mod c. Hence

    V=-c mod f, V=-p mod c.

Pell growth gives V>=4S²-3>c>p. Define mathematical intermediates

    o=(V+c)/f, j_aux=(V+p)/c.

They are positive integers. As f²=1 mod c and of+p=c(j_aux+1), multiplication
by f modulo c proves c divides o+p*f. Consequently

    T=(o+p*f)/c

is a positive integer. Neither o nor j_aux is a new source port. Supply
`auxiliary_quotient=T`. Then

    c*(Tf-1)-R*f²=V,
    aux_coefficient_root=i*Delta*c²=S,
    norm_strong=Delta*f²-S²=Delta,
    norm_aux=S²*(V²-y_aux²)+y_aux²=1.                 (5)

The last equality is the Pell norm at parameter S. This verifies the actual
quotient and all of its consumers, not just an auxiliary subsystem with a
separately supplied V.

## 6. Complete zero, missing inverse, and exact degree

The full positive supplied tuple in source order is

    J,F,alpha,transport_quotient,f,i,T,s,w,tau,
    eta,zeta,y_aux,Z,delta,rho,sigma.

All17 entries are positive integers, all fixed numerals remain authentic,
and the supplied x is the originally prescribed input. Sections2–5 establish
all six actual factors [1,1,1,1,1,Delta]. The complete paid finalizer in(1)
is zero. These tuples need not encode accepted histories; that is precisely
the failure of this deleted candidate.

The forced inverse h is never integral. Since P=1 mod E, k=2n mod E, hence

    (k-R-1) mod E=25u-1>0.

This is the least positive remainder because E=2^(88u-1)>25u. Also
k>=80u>55u+1=R+1, so the forced h=(k-R-1)/E is positive rational. Equation(1)
and Delta>0 show that any parent84 zero over this retained tuple would require
Nk=1 and therefore exactly that h. This proves failure of the complete
positive inverse. The uniform all-input construction additionally refutes
the ordinary-input language for any inherited compiler with a proper language,
including the empty-language compiler. It is stronger than inverse failure alone.

The actual ledger is 74=40M+34A for the six-factor producer core, followed by
5M+1A for the complete finalizer, totaling80. Every supplied witness and x has
degree1; the six fixed numerals have degree0. The factor degrees are

    22,18,32,60,2,46,

summing to180. An independent uniform argument uses the pinned exact degree187
of F84 and(1). Nk has degree7 with leader -h*w*s*Q0⁴, where Q0=(B-1)J, while
Delta has degree12. Integral-domain multiplication therefore gives degree180
for F80 and the full leading form

    -32*Q0^107*(rho+sigma)*delta²*i⁴*(eta+zeta)^13
       *w^17*s^30*Ttransport*T²*f²,

where Ttransport=w*(Q0-F-Z-alpha-ell*x)-transport_quotient*Q0.
The monomial J^108*rho*delta²*i⁴*eta^13*w^17*s^30*transport_quotient*T²*f²
has coefficient +32*(B-1)^108, nonzero on every authentic slice.
No zero-only substitution is used. The separate syntactic gate-degree upper
bound is190. The older normalized81 and ordinary82 source degrees remain168
and124 respectively; this packet does not change their saved arrays.

## 7. Bounded evidence and replay

The fresh helper authenticates ten WIP files and seven exact archive members.
It reconstructs all80 rows, checks the private consumer chain and all ports'
liveness, and verifies the complete ring relations by literal producer
correspondence. It performs48 whole signed evaluations, including24 rational
ones, and two dense full coefficient executions that check both identities and
all six exact factor degrees. These numerical coefficient slices are explicitly
not asserted to be valid compiler instances; the uniform degree proof is above.

Independent finite arithmetic supplements comprise26 small factorial/CRT
component cases,15 grouped repunit cases modulo55,113 outer-margin samples,
three exact strict-ratio families with nine shared-input completions,72 projection
recurrence cases, and three positive auxiliary quotient completions. The largest
Pell subsystem is recorded using bit lengths and exact hexadecimal digests.
The small factorial cases are not claimed to meet the enormous genuine recipe
lower bound L>=W. No complete factorial-radix/Pell zero is numerically
materialized, and no finite test is substituted for the all-input proof.

The bounded CLI reads archive bytes either from the pinned historical Git blob
or an explicitly supplied `--archive FILE` with that exact hash:

    python3 /absolute/path/complete80_first_index_deletion_collapse.py \
      --root /absolute/path/native-stream-queue \
      --expect /absolute/path/complete80_first_index_deletion_collapse.json

`--output FILE` writes the receipt instead. No predecessor Python, archive
script, compiler, or historical suite executes. JSON duplicate keys and
noninteger/nonfinite numbers are rejected; receipt comparison is recursively
type-exact, with explicit exception checks active under `python3 -O`.

Writer and fresh normal and optimized exact receipt replays from `/` passed.
No repository or frozen predecessor bytes were changed.
