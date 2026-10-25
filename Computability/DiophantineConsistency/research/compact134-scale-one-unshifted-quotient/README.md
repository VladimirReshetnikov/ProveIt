# Delete the private T shift after removing the artificial Pell scale

This is a code-free ordinary theorem for the two complete ten-positive
polynomials of incoming package 134. Replace only `b=c(T+alpha)-R` by
`b=cT-R`. The four fixed ports and every other polynomial definition stay
at the whole directly indexed BFS943 radix-67 instance. Both new equations
have positive-zero sets in explicit bijection with their respective old
positive-zero sets. The proof of positivity of the inverse is included.

The prospective costs are **77 operations / degree 630** and **78 / 468**.
Those operation figures describe a hand-specified deletion from the literal
78- and 79-row parents. No new arithmetic circuit, emitted equation,
finite-check result, page-size result, or numerical endpoint is delivered.
In particular, the maintained fifteen-positive 66-operation degree-157
equation remains a different, lower-cost and lower-degree tradeoff.

This note includes an ordinary review of the entire package-134 proof and
both literal circuit JSON files, followed by a complete replacement of the
early sign argument. No incoming program, mathematical helper, import,
AST, evaluator, coefficient reconstruction, Lean, TeX or PDF application
was executed. Only inert reads/hashes and hand mathematics were used.
The author previously authored the pinned artificial-scale unshifted-T
proposals; this is not an independent review of those earlier notes.

## 1. Whole instance, complete equations, and theorem

The only independent inputs are

    J,F,alpha,i,T,w,s,n,eta,zeta in Z_{>0}.

The coherent fixed tuple is `beta,K0,MC,MF`, with

    beta>=31 odd, K0>0, 0<MC<beta<MF<2beta.

Its complete finite constant recipe is the pinned
`research/indexed-tile-enumeration/equation.tex`: radix `rho=2^67`,
`B=rho^8807`, `beta=B-1`, the displayed masks and finite indexed 943-tile
table, and its entire 436-character seed, alphabet and arithmetic decoder.
`MF` is the already shifted source mask, exactly once. The four raw integer
bindings in both package-134 literal circuits are:

| Port | Bit length | SHA-256 of canonical raw unsigned little-endian bytes |
| --- | ---: | --- |
| beta | 590069 | 0664a868cbfef9869ea05c40a1c445563f685ff857092594c1c1223bc4b21f9d |
| K0 | 592884 | 0a86821a704294199c2e1a50379d242c96840a3366e9d965689ba3d74605203f |
| MC | 590069 | 6007cabd5f5228618e8fb613f386d8fc3692a24520d6e4cd72af0262aae1ade4 |
| MF | 590070 | 48333b0d30a4edeb8579f44286cb59806c5622cb42b367f5b5f9ee827711c737 |

The raw hashes are retained source bindings, not newly recomputed numerical
certificates. No one port is transported to a different native theorem.
All subsequent symbols are polynomial abbreviations, not extra unknowns:

    q=beta*J+1, h=q-1, C=q-F-alpha, X=w*q, Y=q^3*s,
    k=eta+zeta, c=k*Y+eta, A=Y*(X+1)+1,
    Delta=A^2-1, H=4*A-5, D=Y^2, V0=X*D,
    E=1+V0*(V0+1)*k^2,
    R=[h*(q-F)+alpha]*(q^2-1)+(MC+q*MF)*J,
    e=k-R-1, Bt=(K0+w)*C-F,
    U=i*c^2, a=Delta*U^2*E, F0=1+a, G=E*F0,
    Fsq=1+4*a*F0, Q=Delta*(Fsq-1),
    b=c*T-R, V=Fsq*b-c, Kpos=X*(3*c-2*X)+2.

For the first equation put `L=V^2`; for the second put `L=b*V`. Set

    M=h*D*H,
    Z=h*D*[H*(n-L*Bt)+Kpos]-H*[D*Bt+h*e],
    RG=M^2*G,
    P=Q*(Z^2-RG*V^2)+(RG-Z^2).

The single equation is `P=0`. Write `P_old` for the corresponding literal
package-134 polynomial, whose sole differing definition is
`b_old=c*(T_old+alpha)-R`.

**Ordinary theorem.** For either weight, the maps

    T_new=T_old+alpha,    T_old=T_new-alpha,

fixing all other inputs and all ports, are inverse bijections between the
strictly positive zero sets. For the specified whole indexed instance,
positive-zero existence is therefore equivalent, by ordinary arithmetic
formalizable in ZFC, to a finite syntactic ZFC refutation. Its negation is
the retained ZFC-provable equivalence with `Con(ZFC)`. This asserts neither
consistency nor unsolvability separately, and supplies no new internal-ZFC
or Lean derivation.

## 2. Review of the unchanged package-134 arithmetic

The complete 346-line parent proof and both literal JSON circuits were read.
Every listed row agrees with its displayed polynomial interface: `Am1=A-1`,
`Hp=H`, `Dtau=E`, `DpI2=a`, `Df=F0`, `Fsqr=Fsq`, `Dg=G`, `cTR=b`,
`Bt=Bt`, `Mtot=M`, `Znum=Z`. In particular `bJ=h`, and `P1mu2=h*Y2`
is a legacy register name: its actual value is `hD`, not `q^3*h*mu^2`.
The carrier has exactly the minus sign and denominator `D` printed above.

The literal finalizer is the single product-square identity

    P=(Q-1)*Z^2-M^2*G*(Q*V^2-1).

There is no six-factor finalizer and no requirement here that six residuals
all equal one. In particular the low-bit-padding P66 closing-factor repair
belongs to another source and is not imported into this theorem.

The parent's valuation/descent argument, both shifted transport arguments,
staged first-index recovery, whole-product projection, fresh unscaled source
reconstruction and fresh doubled-period converse pass this ordinary review
relative to their named inherited calibration. Its use of the uniform ratio
lemma at scale one is legitimate. Its denominator deduction is `q^6|e`
followed by an index bound and then `Y^2|e`; it does not claim `gcd(Y,h)=1`.
Its doubled strong index may be even: the retained auxiliary converse has
no contrary parity requirement. Sections 3--9 give the whole replacement
chain so that the new theorem does not reuse the old shifted sign estimate.

This is an ordinary mathematical review, not a static review or release of
the incoming Python files and not acceptance of their replay receipts.
The omitted duplicate mathematical sources used here were read at the
exact repository paths in the package's `SOURCE_PINS.json`, with matching
whole-file hashes. That placement convention is not a missing theorem.

## 3. Sign-free root extraction and all main folding branches

Positive inputs give `q>=32`, `X>=q`, `Y>=q^3`, `k>=2`, `c>=3`,
`A>4`, `Delta>=3`, `U>=c^2`, `E>1`, `a>c`, `Fsq>2c`, `Q>c^2`
and `M>0`. For integral `b`, `V` is nonzero with `|V|>1`: `b=0`
gives `V=-c`, and otherwise `|V|>=Fsq-c>1`.

The literal identities

    Fsq=(1+2a)^2, Q=4*Delta^2*U^2*G, gcd(E,F0)=1

give `gcd(G,Q-1)=gcd(G,QV^2-1)=1`. At a zero set `z=Z/M` rational.
Prime valuations in `(Q-1)z^2=G(QV^2-1)` force every valuation of `G`
even. Hence positive integers `tau,f0,g` satisfy

    E=tau^2, F0=f0^2, G=g^2, g=tau*f0.

Set `y=|z|/g`. It satisfies `QV^2-(Q-1)y^2=1`. For completeness,
write `y=r/m` reduced. Then `m^2|Q-1`. For `v=|V|>1`,
`v<y<Qv/(Q-1)`. The norm-preserving transformation

    v'=(2Q-1)v-2(Q-1)y, y'=(2Q-1)y-2Qv

has integral nonzero first coordinate with `|v'|<v`, and preserves the
reduced denominator `m` of the second since `2Q-1=1 mod m`. Descending
on `|v|` reaches `v=1,y=1`, forcing `m=1`. Thus `y` and
`z=epsilon*g*y` are integers, for `epsilon` either sign.

The actual strong pair is

    f=1+2a, I=2U*g,
    f^2-Delta*I^2=1, Q=(Delta*I)^2, c^2|I.

No sign of `b,V,Bt,C,R,z` has been presumed. Pell classification gives
`f=chi_A(m), I=psi_A(m)` at a positive index. To spell out the signed
folding contract, put `S=Delta*I`. Auxiliary classification gives
`S|V|=chi_S(nu)` with positive odd `nu`. The odd-quotient identity
and `S^2=1-A^2 mod f` give `psi_A(nu)=+c` or `-c mod f`.
Folding this ordinate modulo `2m`, using the addition identities, gives
a signed representative `psi_A(p)` with `0<=p<=m`. Its parity is odd.
Since `c^2|I` and `c>=3`, `c<I`; also `f>2I` because `A>=3`.
Thus the endpoint `p=m` and zero endpoint are excluded, and no negative
residue can equal a positive one: `psi_A(p)+c<=I+c<2I<f`.
The remaining representative is exactly

    c=psi_A(p), p>=1 odd.

This proves the needed all-index folding without an odd strong-index
hypothesis. The first norm independently gives

    k=2*psi_P0(n0), P0=2XY^2+1, n0>=1.

If `n0=1`, then `k=2`, `eta=zeta=1`, and `c=2Y+1` lies strictly
between `psi_A(1)=1` and `psi_A(2)=2A`. Therefore

    n0>=2, k>=8XY^2+4, c>kY>k>8q^7, c>X, Kpos>0.

## 4. Exclude main index three at scale one

The odd index `p` cannot be one because `c>=3`. Suppose `p=3`, so
`c=4A^2-1`. If `n0>=3`, then

    kY>32X^2Y^5, c<4A^2<16X^2Y^2,

a contradiction. Here `A<2XY` follows from `X>=32,Y>=q^3`.
Thus `n0=2` and `k=8XY^2+4`. Put

    D0=(X+1)^2-2XY=1+X*r0, r0=X+2-2Y.

The exact identity `eta=c-kY` becomes

    eta=4Y^2*D0+8Y(X+1)+3-4Y.

If `D0>=2X`, subtracting `k` gives
`eta-k=4Y^2(D0-2X)+8Y(X+1)-4Y-1>0`, contrary to `eta<k`.
If `D0<=0`, its form `1+X*r0` forces `D0<=1-X`; hence

    eta<=-4(X-1)Y^2+(8X+4)Y+3
        <=(20-8X)Y+3<0,

where `Y>=4`. This contradicts `eta>0`. Consequently `0<D0<2X`,
so the integer `r0` is zero or one, equivalently `2Y-X` is two or one.
But `q` divides both `X` and `Y`, with `q>=32`. This is impossible.
Thus

    p>=5, c>c3:=4Delta+3.

The `D0<=1-X` refinement is essential at scale one. An artificial-scale
estimate that merely bounds a negative `D0` by zero would not prove this.
No carrier divisibility, decoded rank or transport sign entered this proof.

## 5. Every signed auxiliary branch and both transport weights

First `b=0` is impossible at a zero: it would give `V=-c` and

    y^2-c^2=(c^2-1)/(Q-1) in (0,1),

contrary to integral `y`. Thus `b!=0`, `sign(V)=sign(b)`, and
`|V|>|b|`. The exact identity

    a^2-g^2=E*[Delta*U^2*E*(Delta*U^2-1)-1]>0

gives `g<a`. Since `a>c` and `Fsq=1+4a(1+a)`,

    |V|>=Fsq-c>3a>3g, y<(3/2)|V|.

The weight `L=V^2` already satisfies `gy<L/2`.
For a bound valid for both weights, classify the auxiliary norm at
`S=Delta*I`, so `Q=S^2` and `|V|=chi_S(j)/S`. Its index `j` is odd
because even traces are `+1` or `-1 mod S`. Index one gives `|V|=1`,
excluded above. Index three gives `|V|=4Q-3`. Its two signs imply

    V=+(4Q-3) => Fsq*(b-4Delta)=c-c3,
    V=-(4Q-3) => Fsq*(b+4Delta)=c+c3.

Section 4 and `Fsq>2c` place both right sides strictly between zero
and `Fsq`. Neither is a multiple of `Fsq`. Hence `j>=5` and

    |V|>=16Q^2-20Q+5>8Q^2.

The last inequality holds for `Q>=4`, since the difference is
`8(Q-4)^2+44(Q-4)+53`. Also `Q>Fsq`, `Fsq>2c`, and `Fsq>g`.
The triangle inequality therefore gives

    |b|>(8Q^2-c)/Fsq>8Fsq-1/2>4Fsq>4g.

For `L=bV=|b||V|` this yields `gy<3L/8<L/2`.
This proof treats the main, strong and auxiliary norm branches before
any orientation of `V`, parity of `q`, or identification `p=R`.

## 6. Transport, inverse positivity, and exact zero-set maps

Use the rational proof notation

    kappa=Kpos/H>0, rho=e/D, t=Bt/h, W=1+hL.

The literal carrier gives `z=n+kappa-Wt-rho`. The new one-sided estimate

    b-e=cT-k+1>0, rho<b/D<=|b|/D

uses only `T>=1,c>k`; it does not assume `e>=0`. If the actual integer
`Bt<=-1`, then `Wt<=-L-1/h` and

    n=epsilon*gy-kappa+Wt+rho<L/2-L+|b|/D<0.

For `V^2`, the last step follows from `|b|<|V|`, `D>2`, `|V|>1`;
for `bV`, it follows from `L=|b||V|`, with the same two latter bounds.
This contradicts `n>0`. Thus `Bt>=0`, forcing `C>0` from its definition.
Only now the mask bound gives `3q<R<q^4-2` and `alpha<q`.
Since `c>8q^7>2R`,

    b=cT-R>=c-R>0, V>0.

The stronger auxiliary bound of Section 5 applies to both weights, so
`b>4g`. Moreover

    g^2=E+Delta*U^2*E^2>U^2>=c^4.

Consequently every new positive zero satisfies

    T=(b+R)/c>4g/c>4c>alpha.

This is a property of the full new zero set, not of the entire positive
orthant. All definitions preceding `b` are independent of `T`; every
later occurrence of `T` is through `b`. Thus the formal identity is

    P_new(...,T_old+alpha,...)=P_old(...,T_old,...).

The forward map is positive for every old positive zero. The inverse is
positive for every new positive zero by the inequality just proved. They
fix all other coordinates, preserve every derived register and are mutually
inverse. This establishes the claimed bijection. No private strong witness
is divided, and no unrelated native words are identified.

## 7. Full ordered rank and staged denominator recovery

For clarity, the complete new source decoding also works directly.
The normalized strong-rank lemma uses `c=psi_A(p)>2`, the actual strong
norm and `c^2|I` to obtain `f=chi_A(m),I=psi_A(m)`, `pc|m`, `m>2p`.
Positive Pell growth gives `c>2p`; Section 6 gives `c>2R`. With
`S=Delta I`, the signed auxiliary-index lemma uses

    S^2=Delta(f^2-1), c|S, V=-c mod f, V=-R mod c,
    0<p,R<c/2

and gives `p=R`. The second residue uses `f^2=1 mod c`, which follows
from `c^2|I`. Thus `R` is odd. If `J` were even, both summands in its
literal definition would be even; hence `J` is odd and `q` is even.

Integrality of `z`, with only `hH` cleared in its rational identity,
gives `D|hH e`. Now `q^6|D` since `Y=q^3s`, and
`gcd(q^6,hH)=1` since `h=q-1`, `H=4Y(X+1)-1=-1 mod q`.
Therefore `q^6|e`. The base-one recurrence gives

    k=2n0 mod 4XY^2, so q^6|(2n0-R-1).

Also `P0-A=Y(2XY-X-1)>0`. If `n0>=R`, monotonicity in index/base
would give `k/2=psi_P0(n0)>=psi_A(R)=c>k`, impossible. Thus
`1<=n0<R`, so `|2n0-R-1|<R<q^4<q^6`. The divisible error is zero.
Returning to the FULL recurrence only after `2n0=R+1` gives

    4XY^2|e, D|e, rho in Z.

No claim that `Y` and `h` are coprime is made. The intermediate modulus
is a known divisor of the existing `Y^2`, and adds no polynomial gate.

## 8. Whole-product projection and fresh unscaled source soundness

Write `R=2r+1`, so `r>=48`. The pinned ratio proof is uniform for
`lambda>=1`, with `A=lambda Y(X+1)+1`, `P0=2X lambda^2Y^2+1`.
At the actual `lambda=1` it gives, with `xi=(X+1)^(2r)/X^r`,

    xi<c/psi_P0(r+1)<xi*(1+1/[Y(X+1)])^(2r).

Since `Y<c/k<Y+1`, its lower bound gives `Y>X^r/3`, and hence
`H>X^(r+1)`. With integral `rho,z`, the carrier gives `H|hKpos`.
Set `Kquad=X[X+2(A-2)c]-1`. The identity
`Kpos=HXc-2Kquad` cancels only two through odd `H`. Universal Pell
projection then gives

    H|h*(X-2^R)*(2^R*X+1).

Put `T0=2^R`. Because `h<X`, the absolute value of this ENTIRE product
is less than `4T0^2X^3`. For `X>=32,r>=48`,
`X^(r-2)>=32^(r-2)>2^(4r+4)=4T0^2`, so the product's absolute value
is below `X^(r+1)<H`. Therefore it is zero, forcing `X=2^R`.
No selected factor was cancelled as a presumed unit of a composite modulus.
The same projection now gives integral `kappa`; the carrier then gives
integral `Wt`. Since `W=1 mod h`, `h|Bt`, and `t>=0` is integral.

The fixed-minus parity lemma uses `V>0`, the two retained residues,
`c>2R`, `f>2c`, `c|m` and `m>2R`; it forces `R=3 mod 4`.
The ratio upper error, bounded by the retained weaker `3/[Y(X+1)]`
estimate, and `X=2^(2r+1)` give the same half-binomial value of `Y`.
Explicitly `xi=Mbin+theta`, `Mbin` even, `0<theta<1/4`, and the ratio
places `c/k` inside `(Mbin/2,Mbin/2+1)`, hence `Y=Mbin/2`.

Reconstruct a FRESH source at `a0=Y(X+1)`, `Ao=a0+2`, not at the
present `A=a0+1`. Put

    co=psi_Ao(R), Do=chi_Ao(R), ko=2psi_P0(r+1), tauo=chi_P0(r+1),
    etao=co-koY, zetao=ko-etao,
    ho=(ko-R-1)/(XY), gammao=(Do-X-a0co)/(4a0+3), zsource=t+1.

The unscaled ratio/half-binomial bounds give `0<etao<ko`. The base-one
recurrence gives positive integral `ho`; projection and growth give positive
integral `gammao`. At `mo=Rco`, composition gives `co^2|Io=psi_Ao(mo)`;
set `io=Io/co^2`, `fo=chi_Ao(mo)`. The generic auxiliary reconstruction
gives positive `Tstar,uo` and `Vo=fo^2(coTstar-R)-co`.
Take `Tsource=fo*Tstar`, `yo=Vo+uo`. These fifteen strictly positive
coordinates satisfy all normalized source-61 equations, including
`(K0+w)C+(q-F)-zsource*(q-1)=1`, with `s=Y/q^3` unchanged.
The WHOLE indexed native/refutation theorem therefore yields a finite
syntactic ZFC refutation.

## 9. Fresh complete positive converse and actual native rank

Use the whole indexed radix-67 calibration, not only its port box. A finite
refutation supplies canonical outer data with `q=B^N`,
`N=581197^e>1` odd, `R=3 mod 4`, `X=2^R`, `q^3|Y`, the specified
half-binomial, `R>3q` and integral `t=Bt/h>=0`. The pinned indexed proof
rebuilds all 430 action/state and 943 typed-color/selector conjugacies,
the initializer `(3,436,4,4)`, copy/clause/carry/mask constraints, and its
actual-rank dummy controller. The controller uses the same whole new K0;
its retained units are 23,3359,404489 at primes 67,8807,581197. Its
rectangular/helical padding chooses independent large width and height,
and corrects the ACTUAL final rank modulo `dN`, `d=67*8807`.
No old packed `F,C,R` or a controller for a different K0 is reused.

Keep this fresh outer data and `s=Y/q^3>0`. At scale one choose

    c=psi_A(R), k=2psi_P0(r+1), tau=chi_P0(r+1),
    eta=c-kY, zeta=k-eta.

The uniform ratio error and half-binomial margin give `0<eta<k`.
The recurrence makes `e` a positive multiple of `4XY^2`, so `rho>=1`.
Projection gives positive integral `kappa`. Choose a positive period of
the determinant-one Pell matrix modulo `c^2*tau`, obtaining a seed pair
`f0,I0` with `c^2*tau|I0`. Set `i=I0/(c^2*tau)>0`.
Then `U=I0/tau`, `F0=f0^2`, `g=tau*f0`; double the actual seed:

    f=2f0^2-1=1+2a, I=2f0I0=2Ug.

The auxiliary reconstruction accepts this even strong index. Its explicit
positive integers are

    S=Delta I, Vstar=chi_S(R)/S, y=psi_S(R),
    Tstar=(Vstar+c+R*f^2)/(c*f^2).

The odd-quotient identities modulo `f^2` and `c`, with `gcd(c,f^2)=1`,
prove integral `Tstar>0` and the exact auxiliary norm. Set the NEW input
`T=Tstar`, not `Tstar-alpha`. For either positive weight choose

    n=gy+(1+hL)t+rho-kappa.

All terms are integers. Since `f0>(A-1)I0>Xc>kappa`, `g>kappa`;
with `y>=1,rho>=1,t>=0`, this gives `n>0`. Its carrier equals `gy`,
so the new polynomial vanishes. This is a full fresh positive converse;
it does not divide an arbitrary old private witness.

The inherited endpoint here is the indexed Wang/native blank-K215 to
syntactic-refutation calibration. The separate direct-C222 integer compiler
and its ports are not substituted into this four-port theorem. All syntax,
ZF/ZFC or machine-to-refutation calibration obligations remain exactly at
the retained named source boundary; no new transitive formalization is
asserted by this code-free local arithmetic proof.

## 10. Literal deletion, exact degree, prior art and remaining work

In BOTH complete package-134 circuits, row 47 is `[Tp,+,T,alpha]`,
and row 48 is `[cT,*,c,Tp]`. `T` occurs only in that addition and `Tp`
only in that multiplication. Delete row 47, change the sole operand `Tp`
to `T`, and shift subsequent row numbers down one. Every other operation
and consumer stays the same; `alpha` remains live through `C` and `R`.
The actual parent breakdowns are `(46,18,14)` and `(47,18,14)` for
products/sums/differences; the hand-proposed breakdowns are therefore
`(46,17,14)` and `(47,17,14)`. All original port/input uses remain live.
These are prospective layout counts until separate materialization/audits.

The degrees `q,X,Y,c,A,Delta,E,U,a,Fsq,Q,G,b,V,M,Bt` remain
`1,2,4,5,6,12,22,11,56,112,124,78,6,118,15,2`.
The highest `b` changes from `k0*q0^3*s*(T+alpha)` to `k0*q0^3*s*T`.
For `V^2`, `Z` has degree 253 and `QZ^2` is uniquely dominant of degree
630. For `bV`, `Z` has degree 141 and `-Q*M^2*G*V^2` is uniquely
dominant of degree 468. With `q0=beta J`, `k0=eta+zeta`, the ENTIRE
highest homogeneous forms are respectively

    2^14*q0^382*w^46*s^112*i^20*k0^64*T^4*(q0-F-alpha)^2,
    -2^10*q0^288*w^34*s^84*i^14*k0^46*T^2.

The selected coefficients at `J^382*w^46*s^112*i^20*eta^64*T^4*F^2`
and `J^288*w^34*s^84*i^14*eta^46*T^2` are respectively
`2^14*beta^382` and `-2^10*beta^288`, nonzero. This proves exact ordinary
degrees without evaluating or expanding a candidate polynomial.

Removing `T+alpha` itself is prior work: the pinned two unshifted-T
notes already prove artificial-scale variants, including a signed bV gap.
This note transports that mechanism to package 134's scale-one staged
denominator family, supplies the sharper scale-one main-index exclusion,
and proves the stronger positive inverse on this whole zero set. It makes
no claim of priority beyond this bounded repository comparison.

A future finite packet must independently materialize both complete graphs,
bind all old/new rows, all free-port identities and actual whole coefficients,
verify liveness/counts and full highest forms, exercise actual-model controls,
and reproduce normal/optimized evidence after separate static/runtime release.
No such execution is authorized or claimed here. A transfer to the smaller
49-bit tuple would require the complete whole-instance adapter and canonical
native/Pell promises at that tuple; it is not established by this note.
There is no page promotion, new minimum, or change to any frozen source,
probe, maintained equation, CURRENT, or paused Lean file.
