# Saving one auxiliary multiplication: a candidate and a kernel obstruction

Replacing the fixed-minus kernel coefficient `(i*c^2)^2` by `i*c^2`
saves exactly one multiplication. Applied to the complete
[76-operation source](FIXED_RAW_UNIVERSAL_76_PROOF.md), this gives a
**75=40M+35A candidate**, with the same **30 positive coordinates and
19 equations**. Its positive completeness direction follows by an exact
coordinate substitution. Its full soundness is **open**.

The resulting **42=24M+18A kernel**, considered with its usual preliminary
size hypotheses, is unsound: this note supplies positive solutions with
`q=16`, `r=259`, scale `q^3=4096`, and actual main Pell index `517`
instead of `2r+1=519`. All ten weakened kernel equations, including the
first norm, the strict ratio interval, and both fixed-minus congruences,
hold. Nevertheless `4096` does not divide `binom(518,259)`.

This does **not** establish a false input for the complete75 candidate.
The current packing excludes this particular rational family when the
tile alphabet is padded to even size. The spatial transport, actual
compiler masks and raw-input bridge have not been attached to the
counterexample. The published complete76 theorem remains unchanged.

The [checker](../verification/explore_single_product_auxiliary_scale.py)
and [receipt](../verification/explore_single_product_auxiliary_scale.json)
separate the exact source audit, finite materializations and the
parametric construction of the large kernel witness.

## 1. Exact source change and preserved completeness

Write `D0=q^3`, `X=w*D0`, `Y=s*D0`, `E=XY`,
`A0=a+2`, `Delta=A0^2-1`, `H0=4a+3`, and `J0=2r+1`.
The source register named `A` below represents `Delta`, not `A0`.
The ten weakened kernel equations are

    (E^2+X)(Yk)^2 = tau(tau+1),
    c = Yk+eta,
    k = eta+zeta,
    k = r+1+hE,
    a = E+Y,
    d = X+ac+ga(4a+3),
    d^2 = 1+Delta*c^2,
    i*c^2 = Delta*(f^2-1),
    Delta*(f^2-1)*((jc-J0)^2-y_aux^2) = 1-y_aux^2,
    jc-J0 = of-c.                                           (1)

All supplied coordinates are positive integers. Only the eighth source
equation changes. The ninth has the same normalized polynomial as before;
its direct straight-line evaluation uses the eighth equality.

The exact 42 instructions, in order, are:

| # | Register | Arithmetic |
|---:|---|---|
|1|wn2|w*n2|
|2|sn2|s*n2|
|3|UM|wn2*sn2|
|4|R12|UM+sn2|
|5|ksn2|k*sn2|
|6|UM2|UM*UM|
|7|scaled_norm_coefficient|UM2+wn2|
|8|ratio_product2|ksn2*ksn2|
|9|L9|scaled_norm_coefficient*ratio_product2|
|10|tauplus1|tau+1|
|11|R9|tau*tauplus1|
|12|R10a|ksn2+eta|
|13|R10b|eta+zeta|
|14|r1|r+1|
|15|hpm1|h*UM|
|16|R11|r1+hpm1|
|17|tr1|r1+r|
|18|cam2|c*a|
|19|D1|wn2+cam2|
|20|a4|4*a|
|21|a4m5|a4+3|
|22|gam|ga*a4m5|
|23|R14|D1+gam|
|24|a_square|a*a|
|25|A|a_square+a4m5|
|26|c2|c*c|
|27|Ac2|A*c2|
|28|R15|Ac2+1|
|29|L15|d*d|
|30|ic2|i*c2|
|31|L16|f*f|
|32|f_square_minus_one|L16-1|
|33|R16|A*f_square_minus_one|
|34|of|o*f|
|35|aux_u_rhs|of-c|
|36|jc|j*c|
|37|H17|jc-tr1|
|38|H2|H17*H17|
|39|aux_y2|y_aux*y_aux|
|40|aux_square_gap|H2-aux_y2|
|41|L17|ic2*aux_square_gap|
|42|P17|1-aux_y2|

Here `n2=q^3` is already paid for by the outer schedule. The comparisons
are `(L9,R9)`, `(c,R10a)`, `(k,R10b)`, `(k,R11)`, `(a,R12)`,
`(d,R14)`, `(L15,R15)`, `(ic2,R16)`, `(L17,P17)` and
`(H17,aux_u_rhs)`. Relative to the normalized ninth polynomial, the direct
`L17-P17` residual adds the eighth residual times
`(jc-J0)^2-y_aux^2`. This is an exact polynomial identity.

The complete schedule retains the old 19 outer operations, including the
transport relocated immediately after `wn2`, and all 14 input operations.
Thus its cost is `19+42+14=75`. The receipt checks every primitive, all
19 source equalities and the one residual correction explicitly.

For every positive witness of complete76, set

    i_new=(i_old*c)^2                                       (2)

and leave every other coordinate unchanged. Then
`i_new*c^2=(i_old*c^2)^2`. Every source residual is preserved exactly;
positivity is immediate. The witness construction in (2) is metamathematical
and is not an extra certificate instruction. Consequently the candidate's
completeness direction is already proved. This observation supplies no
new soundness argument.

## 2. An auxiliary extension without the old rank divisibility

Use the conventional Pell sequences

    chi_A(n)+psi_A(n)*sqrt(A^2-1)=(A+sqrt(A^2-1))^n.

Let `A>=2`, let `p>=3` be odd, and put
`c=psi_A(p)`, `d=chi_A(p)`, `Delta=A^2-1`, `g=gcd(p,c)`.
Let `J` be any positive odd integer below `c` such that `g` divides `J`.
Define

    m=2p,
    f=chi_A(2p)=2d^2-1,
    R=Delta*psi_A(2p)=2Delta*c*d,
    K=R^2,
    i=4Delta^2*d^2.                                        (3)

The Pell norm and doubling identities give

    K=i*c^2=Delta*(f^2-1).                                 (4)

In particular this counterexample has square `K`. It does not require a
classification of Pell-like equations with nonsquare `K`.

The parity recurrence gives `c` odd. Standard growth gives `c>2p` and
`c>2Delta`; also `gcd(c,d)=1`. Hence `c` does not divide `m=2p`.
Furthermore `c^2` does not divide `R`: otherwise `c` would divide
`2Delta*d`, and thus `2Delta`, contradicting `c>2Delta`. This is exactly
the lost requirement in the old coefficient `R=i_old*c^2`.

Put `sigma=(-1)^((p-1)/2)`. Choose a nonnegative integer `t` satisfying

    p+4pt = -sigma*J modulo c,
    (-1)^t = -sigma.                                      (5)

Since `c` is odd, `gcd(4p,c)=g`. Thus the first condition is solvable
exactly when `g` divides `J`. Dividing by `g` gives the explicit solution

    t = ((-sigma*J-p)/g)*(4p/g)^(-1) modulo c/g.           (5a)

The inverse exists because `gcd(p/g,c/g)=1`, and `c/g` is odd.
Choose the nonnegative representative in (5a), then add `c/g` if
necessary to obtain the required parity. Both conditions in (5) hold.
Set

    s_aux=p+4pt=p+2mt,
    U=chi_R(s_aux)/R,
    y_aux=psi_R(s_aux).                                   (6)

The quotient in (6) is integral. To retain the signs explicitly, define
the integer polynomial `Q_h` by

    chi_R(2h+1)=R*Q_h(R^2),
    Q_0(T)=1, Q_1(T)=4T-3,
    Q_(h+2)(T)=(4T-2)Q_(h+1)(T)-Q_h(T).

Its recurrence gives

    Q_h(0)=(-1)^h(2h+1),
    Q_h(1-A^2)=(-1)^h*psi_A(2h+1).                       (7)

These are the same polynomial identities used in the
[fixed-minus parity proof](EXPLORATION_FIXED_MINUS_INDEX_PARITY.md).
Here `s_aux=p` modulo4, so the sign in (7) is `sigma`. Since `c` divides
`R`, (5) and the first identity imply

    U = sigma*s_aux = -J modulo c.                        (8)

Equation (4) gives `R^2=1-A^2` modulo `f`. The Pell addition formulas
give `psi_A(z+2m)=-psi_A(z)` modulo `f=chi_A(m)`. Consequently

    U = sigma*psi_A(s_aux)
      = sigma*(-1)^t*c = -c modulo f.                    (9)

Therefore

    j=(U+J)/c, o=(U+c)/f                                 (10)

are positive integers. Indeed `R>f>2c`, `s_aux>=3` and
`U>=4R^2-3>max(c,f,J)`. The Pell norm at base `R` gives

    K*(U^2-y_aux^2)=1-y_aux^2.                           (11)

Equations (4), (8)--(11) establish all three weakened auxiliary source
equations and both fixed-minus signs with positive coordinates. They do
not force `p=J` or restore `c|m`.

The divisibility condition is also necessary for this prescribed family:
`s_aux=p+4pt` is a multiple of `p`, and (8) forces `g` to divide `J`.
This is an exact necessary-and-sufficient criterion for the construction
in (3), (5)--(6), not for arbitrary weakened-kernel auxiliary witnesses.
It is weaker than the former sufficient assumption `gcd(p,c)=1`.

For a small noncoprime example, take `A=2,p=3,J=9`. Then
`c=15,d=26,g=3,t=8,s_aux=99,f=1351,R=2340,i=24336`.
All auxiliary coordinates are materializable; `U` has 1,195 bits.
For a noncoprime example with odd `r=(J-1)/2`, take `A=4,p=3,J=15`:
`r=7,c=63,d=244,g=3,t=22,s_aux=267,f=119071,R=461160,i=53582400`.
Here `U` has 5,271 bits. These are auxiliary examples, not full encoded
kernel or raw-input counterexamples.

## 3. Attach all seven other kernel equations

The exact main/first construction is the previously proved
[rational-root wrong-index family](EXPLORATION_BASE_TWO_WRONG_INDEX_RATIONAL.md),
Sections 1--4. Its historical packing restriction is separate from the
current76 restriction proved in Section 5 below.

For an integer `H>=2`, set

    p=6H+1, t_first=3H+2, r=3H+1, J0=2r+1=p+2,
    X=2^p,
    Froot=(X+1)^(2H)/(X^H*2^(2H+1)),
    Y=floor(Froot)
     =sum_(j=H+1)^(2H) binom(2H,j)*X^(j-H)/2^(2H+1),
    a=Y(X+1), A0=a+2, Delta=A0^2-1,
    E=XY, Pfirst=2XY^2+1,
    c=psi_A0(p), d=chi_A0(p), k=psi_Pfirst(t_first).     (12)

The cited proof establishes `2^(4H)|Y` and `0<Froot-Y<1/5`. With

    R0=(2a)^(p-1)/(4XY^2)^(t_first-1)=Froot^3/Y^2,

it proves the exact inequalities

    Y<R0<Y+2/3,
    R0<c/k<R0+48H/(X+1)<Y+1.                             (13)

In particular the following are positive integers:

    eta=c-Yk, zeta=(Y+1)k-c,
    tau=(chi_Pfirst(t_first)-1)/2,
    h=(k-t_first)/E,
    ga=(d-X-a*c)/(4a+3).                                 (14)

The first Pell identity gives
`tau(tau+1)=(E^2+X)(Yk)^2`; the main norm is exact by construction.
The quotient in `h` is integral because `Pfirst=1` modulo `E`.
For `ga`, the sequence `chi_A0(n)-a*psi_A0(n)` agrees with `2^n`
modulo `4a+3`, and is greater than `2^p` at the indicated index. These
facts prove all seven nonauxiliary equations in (1), including their
strict positive quotient requirements. No asymptotic approximation is
substituted for the strict interval (13).

## 4. The exact q=16, r=259 witness

Take `H=86`. Then

    p=517, r=259, J0=519, q=16, D0=q^3=4096.             (15)

Formula (12) gives `D0|X,Y`, so `w=X/D0` and `s=Y/D0` are positive
integers. The preliminary bounds hold:

    q^2=256 <= r=259 < q^4=65536,
    r is odd, X,Y >= q^3,
    a>q^6>2r+1, XY>r+1.                                 (16)

The divisibility criterion in Section 2 holds here because the stronger
coprimality condition is exact and small to check:

    Y=10 modulo517,
    a=421 modulo517, A0=423 modulo517,
    psi_A0(517)=1 modulo517.                             (17)

Thus `gcd(p,c)=1`. The value of `Y` modulo517 follows directly from
the finite sum in (12), using the inverse of `2^(173)` modulo517;
the last residue follows by the Pell recurrence modulo517. The checker
also computes the exact 44,290-bit integer `Y` and confirms (17)
independently from it. In fact `v2(Y)=349`.

Use Section 2 with `A=A0`, `p=517` and `J=J0=519`.
Here `sigma=1`, so (5) chooses `t` odd. Equations (3)--(14) now define
every positive kernel coordinate, and prove every one of (1).
The actual main Pell index is `p=J0-2`.

On the other hand the exact central-binomial valuation is

    v2(binom(518,259))=popcount(259)=3<12=v2(4096).        (18)

Consequently the weakened kernel fails the implication from the usual
preliminary bounds to scale divisibility. Its failure persists with
`q` a power of two, `r` odd, positive `Y>=q^3`, both norm equations,
the strict ratio interval and both auxiliary congruence signs. Only a
separate argument using the complete packing could rescue the candidate.

## 5. The actual compiler's modulo-three restriction

This restriction prevents interpreting Section 4 as a complete75
counterexample. Let `a_tiles` be the tile alphabet size and `k_tiles`
the number of allowed windows in the compiler of76. Put `R=2^b`,
`B=R^L`, `q=B^N` and `Jrep=(q-1)/(B-1)`. Its odd `b,L` imply
`R=B=-1` modulo3. The packed source is

    r=(q^2-Z-qF)(q^2-1)+(MC+qMF)Jrep.                    (19)

It follows immediately that `r=0` modulo3 when `N` is even. When `N`
is odd, `q=-1`, `Jrep=1`, and

    r=MC-MF modulo3.                                    (20)

The exact native layout gives

    MF=1 modulo3,
    MC=2 modulo3 if k_tiles is even and a_tiles is odd,
    MC=0 modulo3 otherwise.                             (21)

Here is a direct proof that includes the compiler's dummy padding.
Its `m=2*popcount(mu)+12*a_tiles+2` is even, and the native population
`K=m+1` is odd. The nonanchor positions consist of selectors
`[0,k_tiles)` and a consecutive payload-and-dummy block beginning at
`k_tiles+3*a_tiles`, of length `t=K-4-k_tiles`. The anchor unit is
`M=k_tiles+t+6*a_tiles`, which is odd; all four anchors `M,3M,9M,27M`
are therefore odd. Summing `(-1)^e` over all native positions gives
`-5` in the exceptional even-`k_tiles`, odd-`a_tiles` case and `-3`
otherwise. Removing End's exponent1 adds1 to this sum. Since
`MC=B-1-sum_(e!=1)R^e` and `B-1=1` modulo3, this proves the claim for
`MC`.

For `MF`, the two center targets have opposite parity and cancel.
The vertical-copy positions are an even consecutive block of length
`6*a_tiles`. Each horizontal-copy row has an even consecutive block
of length `2*a_tiles`. Their contributions vanish. The two target
anchors `9M,27M` contribute `-2=1` modulo3. This proves (21). The
optional high `DC` monomial changes neither mask.

Thus the rational family `r=3H+1` is excluded whenever `a_tiles` is
even, for every `N`. Adding unused tile symbols can enforce even
alphabet size without changing the represented machine. With an odd
alphabet and an even number of windows the residue obstruction alone
disappears, but that is not a construction of a full witness. Neither
case proves or refutes soundness of complete75.

## 6. Verification and scope

The checker records all 75 primitives and 19 exact source maps, the
42-instruction kernel ledger, and the positive completeness map (2).
It replays exact nonauxiliary rational-family witnesses at `H=2,4,8`,
checks the primary `H=86` rational root and all stated small modular
data, and verifies the central-binomial valuation directly.

It also checks the reduced CRT and both polynomial congruence signs for
238 bounded `A,p,J` choices, including40 noncoprime cases, and records97
excluded `J` choices. Eight complete reduced-period enumerations
independently check that `g|J` is exactly the solvability condition,
including the parity requirement:250 target cases pass and110 fail.
Four complete auxiliary tuples are actually materialized:
`(A,p,J)=(2,5,7)`, `(2,7,11)`, `(2,3,9)` and `(4,3,15)`, with auxiliary
indices1665,11655,99 and267 respectively.
Their norms, integral positive `j,o` and fixed-minus equalities are
checked as exact integers. These small tuples are auxiliary tests,
not the primary whole-kernel example. Sixty compiler layouts check (21).

The primary `H=86` main Pell coordinates and its much larger auxiliary
coordinates are specified by exact formulas and proved to satisfy the
equations; the finite checker does not claim to materialize them. No
actual encoded computation, compatible temporal shift, input bridge or
full false raw-input witness is supplied. Complete76 remains the
established bound, while complete75 remains a candidate requiring a new
soundness proof or a counterexample compatible with all its equations.

Author and independent complete scoped proof/source reviews pass, and
fresh default verification matches the saved receipt. Dependency hashes
normalize CRLF to LF so the receipt is reproducible from Git's text blobs.
