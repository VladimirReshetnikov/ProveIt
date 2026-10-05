# A paid selector bound and ordered lane recovery give a complete U9 compiler in245 operations

The247 U9 source has a **245=129M+116A** successor, with43 positive
witnesses and total degree **at most936**. Both the four-program-parameter
and separate five-parameter interfaces retain their ordinary input,
fully paid unbounded history and native endpoint obligations. The separate
universal84 bound is unchanged.

Supply the positive selector group G12 directly, in place of the positive
hat of S2. Removing its sum and unhat rows saves two additions. A new
addition pays a bound on S1 in the global size P. Reusing the paid selector
sum J in the upper transport removes one further subtraction, for a net
two-addition saving. Soundness requires a new carry argument: the physical
mask may overflow into the first controller lane, but the last controller
lane remains exact and restores the missing subset condition first.

## 1. Positive group and exact coordinate map

The actual U9 loaded word begins cb. The frozen247 proof derives that
its first two matching tiles are P_c,D_b. Thus S0>0 and S2>0, in
particular G12=S1+S2>0. This is a conclusion about valid loaded matching
words, not an existence claim for rejecting inputs. The positive247
coordinates already include S0,ZU,ZV0 and hats Shat1,Shat2,Shat3,ZVhat1.

Replace supplied Shat2 by supplied positive G12. Keep Shat1 and put

    S1=Shat1-1>=0, S3=Shat3-1>=0,
    G03=S0+S3, J=G12+G03,
    P=HU+HV+ZU+ZV0+ZVhat1+g+Shat1.               (1)

The last addition is charged. All seven summands of P are positive.
Thus P>=7 and S1<P before using any equation. It is not assumed that
S1<=G12 or S1<=J before typing.

The inverse map into the247 polynomial is

    Shat2_old=G12-Shat1+2,
    g_old=g+Shat1,                                (2)

with every other supplied coordinate unchanged. The second coordinate
is positive on every positive child tuple. The first need not be;
Section3 proves it positive at every child zero before invoking the
complete parent theorem.

The old group sum Shat1+Shat2 becomes G12+2 and its unhat becomes G12.
The unchanged source row linear_group164 computes S0+Shat3=G03+1.
Consequently compute J by subtracting1 from
G12+linear_group164, instead of subtracting3 from the old selector sum.
The parent P equals exactly the new seven-summand expression(1).

## 2. Upper transport sharing and full polynomial identity

Let a=2^(beta+1)+1 be the old upper offset and A=2^(beta+2), so A=2a-2.
In247, upper_constant=A+3=2a+1. Write

    L0=2HU+(A-2)ZU.

Its upper transport form is

    L0+linear_group164+a*(Shat1+Shat2)-(2a+1).

Under(2), this is

    L0+G03+a*G12 = L0+J+(a-1)*G12.               (3)

Reuse the paid J in linear_sum166. Change the fixed upper_offset recipe
from a to a-1=2^(beta+1). Its multiplication by G12 remains charged.
Delete linear_constant168 and use linear_sum167 directly in the upper
update. The upper_constant fixed role is then dead and is removed;
the other ten fixed numeral roles remain live. The lower transport and
its fixed constant12 are unchanged.

The complete graph edits remove

    group_sum58=Shat1+Shat2,
    tree_group12=group_sum58-2,
    linear_constant168=linear_sum167-upper_constant,

and add

    group_global_slack=global_bound+Shat1.

Replace the P-row slack operand by group_global_slack. The group consumers
use supplied G12, the J subtraction changes3 to1, linear_sum166 uses J,
and the upper update uses linear_sum167. A topological reorder places
the existing J producer before its new transport consumer. The full static delta has236 literal retained row records, eight edited
records, three deleted rows and one new row. No row array is executed
to establish this identity.

All unchanged pack exits are still

    Ctree=G12+P*S0+P^2*S1,
    Zb=ZU+P*ZV0+P^2*(ZVhat1-1),
    Mtree=J+P*(J+(b-1)J*G12),
    Hb=HU+P*HV+P^2*HV, Mb=(b-1)Ctree,
    Hr=HU+P*HV, Mr=(1+P)(D-1)J.                   (4)

If fixed numeral ports are regarded as independent, include in the map

    upper_offset_old=upper_offset_new+1,
    upper_constant_old=2*upper_offset_new+3.      (5)

All other fixed roles agree. The actual recipes satisfy(5). Equations
(1)--(5) exhaust every changed producer/consumer interface. Hence over
any commutative ring the complete polynomials satisfy

    F245(new)=F247(Shat2=G12-Shat1+2,g_old=g+Shat1,others),      (6)

with(5) as part of the fixed-numeral map. No unconditional positive-domain
bijection is inferred from this algebraic identity.

## 3. Signed scalar bounds with the newly possible carry

At a positive child zero the geometry discriminant is positive, just as
in247: the low recoder prefix is unchanged. The supplied G12,S0,ZU,ZV0
are positive, S1,S3,ZVhat1-1 are nonnegative, and the raw history packs
in(4) are nonnegative. Thus the unchanged explicit positive joint input
and low-output decompositions apply. Cancel the geometry multiplier at
this zero to obtain sixteen unit factors in the unscaled parent form.

The signed global factor and(1) give

    P=(b-1)J+epsilon, epsilon in {-1,1},
    b=c_h D, c_h>=32, D>=1,
    J>=1, J<=P/6, b<=P+2, 0<=(D-1)J<P.           (7)

G12,S0,S3 and G03 are nonnegative and at mostJ. S1 is merely belowP.
All histories and selected products are belowP because P is their
positive sum with additional terms. These facts imply

    Ctree<P^3, Hb<P^3, Zb<P^3, Hr<P^2, Mr<P^2.

The signed mask expansion remains

    Mtree=J+P*(G03+(1-epsilon)G12)+P^2*G12.

Its coefficients are at most3J<=P/2<=P-2, hence

    Mtree<=(P-2)(1+P+P^2)=P^3-P^2-P-2.            (8)

The old smaller physical-mask estimate is unavailable because S1 may
exceedJ. Instead b-1<=P+1 and Ctree<P^3 give

    0<=Mb<(P+1)P^3,
    Mb+P^3*Mtree<P^3*(Mtree+P+1)<P^6.             (9)

This is the specific new estimate; it controls a possible physical-mask
carry without silently assuming disjoint packed lanes.

With T=P^8 define the actual unchanged words

    H0=Hb+P^3*Ctree+P^6*Hr,
    M0=Mb+P^3*Mtree+P^6*Mr,
    Z=Zb+P^3*Ctree+P^6*Hr,
    H=H0+2T, M=M0+T, Qhigh=bT.

Equations(8)--(9) prove 0<=H0,M0,Z<T. They also give the same
H-Z>=T+1, M-Z>=1, Qhigh-H-M+Z>=(b-5)T+2. Thus all four joint implicit
truth fields are strictly positive before typing, with their unchanged
residues1,4,2,8 and sum q-1. The native norm/rank/coupled-linear/index
proofs apply on exactly these scalar hypotheses.

Recover the joint dyadic scale first, then its positive factors b andP,
and the geometry/low-mask signs. The signed Mersenne argument uses only
(7) and these dyadic factors; it gives

    P=b^t, t>=1, J=(P-1)/(b-1), epsilon=1.         (10)

For completeness, write b=2^d and P=2^k with d>=5 and k>0. Modulo
2^d-1, P has residue2^(k mod d). It cannot equal -1, whose least positive
residue is2^d-2>2^(d-1); equality to1 forces d to divide k. This uses no
selector-bit typing. The native AND and low-block separation now give the exact high equality H AND M=Z. Do not yet split
its physical and controller masks into their old lanes.

## 4. The unaffected last controller lane restores the parent domain

Now G12,S0<=J and all coefficients of Ctree are belowP. Since
(b-1)G12,(b-1)S0<=P-1, the only possible overflow of Mb aboveP^3 is

    c=floor((b-1)S1/P), 0<=c<=b-2.                (11)

Write Mb=Mb_low+cP^3 with 0<=Mb_low<P^3. The effective controller mask
is Mtree+c. Its expansion from(10) is

    (J+c)+P*G03+P^2*G12.

There is no carry out of its lowest coefficient: for P=b^t>=b,

    J+c<=J+b-2<P,

because P-1=(b-1)J and J>=1 imply P-(J+b-2)=(b-2)(J-1)+1>0.
All three coefficients are therefore belowP. The range block is also
unchanged: (9) already excluded any overflow past the whole controller
region atP^6.

P is a power of two. Extract the top controller coefficient, at offset
P^5, from H AND M=Z. The H and Z coefficients both equal S1, while
the M coefficient is exactly G12. Hence

    S1 AND G12=S1, and in particular S1<=G12.     (12)

This extraction precedes the potentially contaminated lowest controller
lane. Equation(12) makes c=0, since (b-1)S1< P. It also gives

    Shat2_old=G12-S1+1>=1.

All virtual parent coordinates in(2) are now strictly positive. Equation
(6) is a genuine positive247 zero, so its complete soundness theorem
applies. Alternatively the zero carry restores every original controller
and physical mask exactly. No bitwise assumption about a negative old
selector was used to reach(12).

## 5. Complete converse and paid universal scope

Conversely take any positive247 zero on a valid U9 slice. Its matching
word has S2>0, hence G12=S1+S2>0. Set

    G12_new=Shat1_old+Shat2_old-2,
    g_new=g_old-Shat1_old,

and leave the other witnesses fixed. The first value is positive by
the forced D_b occurrence. For the second, the full247 typing yields

    g_old>=((c_h-4)D+3)J>=31J,
    Shat1_old=S1+1<=J+1.

Therefore g_new>=30J-1>=29>0. Equation(6) supplies the child zero.
The two maps are inverse bijections of complete positive zeros on valid
program slices, not merely an existential projection that changes native
fibers. No matching history is claimed on rejecting inputs.

Consequently every recursively enumerable set of positive integers has
the same effectively fixed ordinary-input program slice for F245 as for
F247. The four program coordinates, optional fifth duration coordinate,
43 existential witnesses, true variable-duration history and paid input
recoder all remain. There is no free input exponent or history loader.

The complete count is245=129M+116A in each interface. Its certificate
before the last subtraction is244=129M+115A with one comparison to the
already paid geometry discriminant. The map(2) is affine in supplied
coordinates and(5) changes fixed degree-zero numerals; the accepted247
bound therefore implies degree at most936. No array degree propagation
or exact-degree claim is used.

**Remark 1 (a group replacement alone does not supply the raw bound).**
It would be unjustified to replace Shat2 by G12 and retain the former
estimate S1<=J before typing. At positive G12=S0=1, Shat3=1 and
Shat1=1000, one has J=2 but S1=999. Paying Shat1 into P is essential to
the proof used here. This is a raw selector-cut counterexample, not a
full compiler zero or a proof that every other repair is impossible.

**Remark 2 (the smaller physical-mask estimate really fails).** Even
with the paid bound, take b=32,P=63,J=2,G12=S0=1,S1=8,S3=0,
HU=HV=2,ZU=ZV0=ZVhat1=1 and g=47. These are positive supplied values,
P has its new seven-summand definition, and P=(b-1)J+1. However
Ctree=31816 and Mb=986296>2P^3=500094. Its overflow is c=3. Thus the
old Mb<2P^3 estimate and a premature claim of all separate masks cannot
be reused. This is an untyped scalar counterexample, not a child zero;
(9)--(12) handle precisely this missing obligation.

## 6. Read scope and fresh evidence

The frozen247 proof and both source arrays, the complete248 proof and
relevant250 signed bounds were read inertly. The language fact is the
already pinned first-two-tile theorem from247, not a new literature
universality assertion. Fresh evidence below authenticates dependencies,
reconstructs both full source variants statically, and checks independent
handwritten cut, scalar and bit-extraction identities. No saved array is
evaluated, no saved degree is propagated, and no predecessor or frozen
program is imported or run. All author writes are in /tmp; only root
mutates the repository.

The fresh writer and exact receipt comparisons in normal and optimized
Python modes from `/` passed before freezing. The two complete245
sources contain490 rows. Six independently handwritten polynomial-cut
identities,640 signed prefix contexts (320 negative-sign and320
height-one), and148 dyadic top-controller-lane contexts pass. Among the
signed contexts,320 violate the old smaller physical-mask bound; these
are explicit diagnostics of Remark2's proof obligation, not source zeros.
The proof is all-size and does not infer universality from these checks.

Evidence SHA256:

- Helper: `d92508e8eb70639ce4a8cf2778eba29400077faa6610968068af81a62c628c61`.
- Receipt: `d9ddce2c7581243ff18a2e36c694bb5dd321e12286388c995ee4bc6ddadf4d38`.

The helper authenticates these inert dependencies under the common
`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue`
path, allowing the same-name frozen author /tmp file before repository
installation. Byte authentication does not broaden the proof-read scope.

| Dependency | SHA256 |
| --- | --- |
| `neary_woods_positive_first_production247_tesla.md` | `9cb9da3c211fecbe3129421b23a16c747d8d1bf7b6365cf6320c426733ffd56a` |
| `neary_woods_positive_first_production247_tesla.json` | `85e91368ddb3b4764879cd8591d730a60ed95e569026ec8ad7a0b6600739968e` |
| `neary_woods_positive_upper248_tesla.md` | `f3329cf28090e39a219ac4e3d8882b99fc5bab72ae0507647a193cbdb514d557` |
| `neary_woods_hierarchical_history250_tesla.md` | `1bb41ed9eae9e77b2a9236c49508a55538f2ff84d1cd245f3bccec4dee39a330` |
