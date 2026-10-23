# Shared kernel taps: two smaller nine-variable consistency equations

## Scope and exact statement

The primary circuit `generated/shared_taps_positive.json` is an integer
polynomial in the nine **strictly positive** inputs

    b, g, h, s, w, C, i, j, n.

It has exact total degree 1,675,396 and 458 live binary arithmetic gates.
The companion `shared_taps_economy_positive.json` has exact degree 1,738,228
and 457 gates. Natural-domain translations have the same degrees and 465,
464 gates, respectively. These are different polynomials. Intermediate
registers are abbreviations, not quantified variables.

The ordinary mathematical conclusion, using the same identified native
compiler, fixed-tuple calibration, and Jones ratio theorems as package 59,
is

    ZFC proves: no positive integer zero <=> Con(ZFC).

The new work is a fully specified source-encoding transformation and its
composition with that unchanged arithmetic finalizer. It does not claim a
new object-language ZFC derivation or a new end-to-end Lean proof. The
inherited semantic dependencies are retained as named results; finite
checks below certify their new finite input and the literal polynomial,
not the unbounded consistency statement by experimental testing.

The repository comparison is fixed at commit
`beb0192cb8dc36f78c369c080f2adfbc1887a486`. Package 59's primary nine-positive
point is degree 1,910,404 / 473 gates. The new primary lowers degree by
12.3015% and gates by 3.1712%; the economy point saves one further gate.
No absolute simplicity minimum, new variable-count bound, or literature
priority claim is made.

## 1. Coalesce equal coefficients instead of summing colliding records

Let the original 31-coordinate positive source have quadratic residuals
r_1,...,r_22. Its literal 65-gate syntax is `data/source_system65.json`.
It is the unshifted transport source: substituting the different 60-gate
source without its z-coordinate translation would change row 15.
Define rho_14=r_14+r_2, rho_15=r_15+r_3, and rho_j=r_j otherwise.
These invertible integer row operations preserve the common zero set.

For a degree-d source monomial p^alpha with coefficient a_(j,alpha), put

    c_(j,alpha)=2 a_(j,alpha)                if d=0 or d=1,
    c_(j,alpha)=a_(j,alpha) product alpha_i! if d=2.

Choose positive, distinct integer weights w_i and distinct nonnegative
integer targets q_j. For each d, define a partial table k_d(e) by the
requirements

    k_d(q_j - sum_i alpha_i w_i) = c_(j,alpha)

for **every** degree-d monomial alpha, interpreting c_(j,alpha)=0 when it is
absent from rho_j, and k_d(e)=0 for negative e. A table exists precisely
when all requirements at a repeated position agree. Require a nonzero
entry to have nonnegative position. Fill unspecified positions with zero.

This is the shared-tap lemma: equal nonzero requirements at one position
are one kernel coefficient. They are not added together. With

    D_d(T)=sum_e k_d(e) T^e,
    U_p(T)=sum_i p_i T^w_i,
    G(T,p)=D_2(T) U_p(T)^2 + D_1(T) U_p(T) + D_0(T),

one has [T^q_j]G=2 rho_j(p). Proof: the coefficient of p^alpha in that target
is k_d(q_j-sum alpha_i w_i) times the multinomial coefficient in U_p^d.
For d=2 it is 1 on a square and 2 on a cross product, which gives exactly
2a_(j,alpha) with the stated weighting. For d=0,1 it gives the same result
immediately. The requirement also checks every absent monomial, so an
unintended convolution contribution cannot enter a target.

The old source demanded no same-degree overlap of source records. The new
lemma permits compatible overlaps. This is a relaxation of the mathematical
coding condition. A search finds a finite certificate; the search program
is not a proof dependency.

## 2. The two finite certificates

Both variants retain package 59's 31 weights, in original variable order:

    1,7,61,36,16,85,20,67,43,11,34,13,96,80,29,50,
    2,109,110,112,116,91,53,55,27,101,92,9,107,37,60.

For the primary layout, the targets in *row order* 1,...,22 are

    1117,28,1442,1045,1841,1330,1819,614,267,1384,1379,
    889,337,1592,413,673,1115,772,1107,1413,1031,85.

`data/layout.json` records them in increasing-target order. The 89 weighted
source records coalesce into 84 unique taps:

| Degree | Exponent | Shared original row/monomial requirements | Coefficient |
|---:|---:|---|---:|
| 1 | 1324 | row 11: C2; row 10: Delta | 2 |
| 2 | 39 | row 22: g Baux; row 9: c a | -1 |
| 2 | 588 | row 8: tau^2; row 18: V^2 | 2 |
| 2 | 1032 | row 4: s N; row 19: i C2; row 17: f o | -1 |

The unique kernels, each with explicit coefficient polynomials in the four
fixed ports, are `data/kernels.json`. Their degrees are (1384,1739,1641),
with quadratic leading coefficient +1. Thus W=116, Q=1841 and
H=max(deg D_d+dW)=1873.

The economy certificate is `data/layout_economy.json` and
`data/kernels_economy.json`. It has 86 unique taps, kernel degrees
(1508,1816,1718), W=116, Q=1918, H=1950. Its shared degree-two taps are at
338 (the same row-22/row-9 pair) and 1169 (the same three-row group).

`verify.py` derives all source coefficients independently from the original
arithmetic syntax and checks 22*(1+31+496)=11,616 coefficient requirements
for each variant, including all missing monomials. It reconstructs the
inverse row operations and checks that the kernel tables have no unowned
extra terms. Mutating a shared coefficient is rejected by a target-identity
check. Verification remains active with Python's `-O` option.

## 3. Source positivity and sparse carries

Keep the whole original31 native tuple. Its port bit bounds are
(1,064,921; 1,070,004; 1,064,921; 1,064,922). Every weighted kernel coefficient
has absolute value below M=2^2134927. Put

    kappa=2134939, a=2^kappa=4096M, B=a b^2,
    ell=sum_i B^w_i, Us=ell+g,
    Gs=(D2(B)Us+D1(B))Us+D0(B), Targets=sum_j B^q_j,
    N0=B^117, Z=B^(H+1),
    Mask=N0-1-(b-1)ell,
    Scode=g+N0(2Gs+Targets),
    Tcode=Mask+N0(B-2)Targets,
    t=b B^116, Gcap=32t.

For all positive b,g one has Us>=B^116 and
D2(B)>B^(deg D2)/2. The linear and constant negative contributions,
relative to B^(deg D2)Us^2, are smaller than 2M/B^18 and respectively
2M/B^489 (primary), 2M/B^442 (economy). Both are less than 1/8.
Thus Gs>0 before digit recovery. The low mask is nonnegative and less
than N0, so Scode,Tcode>=0 unconditionally.

On the exact ratio-derived range g<4bB^116, Us<6bB^116. Geometric-series
bounds give

    2Gs/Z < 86 M b^2/(B-1) < 1/32.

Since H-Q=32, both Targets and (B-2)Targets are smaller than Z/64.
Also g<N0. Consequently Scode+Tcode<N0 Z=B^(H+118).
These are precisely the strict bounds needed by the inherited two-block
construction; the arbitrary-g range is not replaced by a smaller one.

If b is a power of two, disjointness from the low mask recovers

g=sum_i z_i B^w_i, 0<=z_i<b. Then Us encodes p_i=z_i+1>0.
Every coefficient of the source convolution has absolute value below

    M[(sum_i p_i)^2+sum_i p_i+1] <= 993 M b^2 < B/4.

Coalescing taps does not change this estimate: the bound applies to unique
kernel coefficients; it never adds the multiplicities of the requirements.
The inherited sparse +1 borrow lemma therefore makes Scode & Tcode=0
exactly when the recovered p_i satisfy all rho_j=0. The invertible row
operations give the original source zero. Conversely every source zero
works for all sufficiently large admissible b. The all-one tuple is not a
zero (row 5 is 1), so g>0; the digit bound gives g<bB^116, hence 32g<Gcap.

## 4. Exact binary calibration

Let E=H+118 and A_pop=H+255. Define

    delta=(A_pop-15) mod 2,
    lp=(22-A_pop*kappa) mod 2,
    nexp=(A_pop-15-delta)/2,
    cexp=((15+delta)*kappa+lp-22)/2,
    L=2^lp b B^E,
    R=L(Scode+Tcode+1)-Scode-1,
    N=2^cexp b^delta B^nexp.

All exponents are fixed nonnegative integers. The primary parameters are
(E,lp,delta,nexp,cexp)=(1991,0,1,1057,17079501). The economy parameters are
(2068,1,0,1096,16012032).

If b=2^k, B=2^v, L=2^u, then pop(Tcode)=139v-31k-22 and

    pop(R)=u+pop(Tcode)-tau,
    tau=pop(Scode)+pop(Tcode)-pop(Scode+Tcode)>=0.

Here tau=0 exactly for binary-disjoint source words. The formulas above,
using v=kappa+2k, give u+pop(Tcode)=2log_2 N, so Legendre's valuation
formula yields N^2 | binomial(2R,R) exactly when tau=0. The conclusion
includes k=0; b=1 cannot give a final zero because its low mask intersects
the positive g. The parity factors lp and delta are retained explicitly;
dropping them would invalidate the economy calibration.

## 5. The unchanged arithmetic finalizer

In the following formulas the input j is positive and j0=j-1. Put

    U=N^2 w, Y=N^2 s, M0=R Y,
    P=2 M0^2 U, K=R+1+h(P-1), A=M0(U+1),
    B1=2R+1, W1=bw, J=4A-5,
    Q=3W1 C-2(W1^2-1), D=(A^2-1)C^2+1,
    k0=i J C, E0p=k0 D C, F=(A^2-1)E0p^2+1,
    G=A+F(CD+1-A), H0=C+F(B1+j0 C), I=(G^2-1)H0^2+1,
    a0=(P^2-1)K^2+1, a1=D F I,
    m0=K^2(4t-g)-16t(C-KY)^2,
    V0=PK, V1=k0(8D^2-4D-1)G H0,
    Omega=J m0, E0=J(n+W1^2)+Q,
    Theta=E0-Omega(V0+V1).

The single equation is

    F9 = [Theta^2-Omega^2(a0+64a1)]^2
         -256 Omega^4 a0 a1 = 0.

There is no division or variable exponent in this definition. It is exactly
the literal DAG, not an equation with extra existential registers.

The finalizer proof is retained in `inherited/nine_free_proof.md`, sections
3--4. Its proof uses only the numerical outer hypotheses R,N>=8, b<=R,N,
the stated source range/completeness bounds and the exact divisibility
calibration, all verified above for both new sources. The Pell/CRT formulas
and quotient shift are unchanged. For clarity, its soundness ordering is:
strict unconditional root majorants give m0>0 from a norm zero; this gives
the old carrier range; separation then makes the rational radical sum
nonzero, hence both square roots integral; J|Q follows; Jones's ratio
theorem yields a power-of-two base and the source binomial divisibility.
Completeness chooses fresh Pell/CRT witnesses and a positive n. It is an
existence equivalence, not a same-witness identity with the old F9.

The integer radicands and positivity conditions in that argument use only
the unchanged finalizer and the newly checked outer numerical hypotheses.
No part of its proof depends on separate source-record ownership or on the
old kernel height 2161. Thus its composition with the present source
identities is a fixed, completed ordinary mathematical reduction to the
same native source predicate, not a conjectured wrapper transformation.

## 6. Exact degree after cancellation

Write r=deg R=4E-1 and q=deg N=2nexp+delta. Thus (r,q) is (7963,2115) for
the primary and (8271,2192) for the economy. The tempting raw-DAG degree
propagation overestimates the output because the leading norm terms cancel.
Resolve that cancellation with the exact identities

    Tpair^2-64DF=(8D+1)k0^2-64D,
    Delta1=V1^2-64a1
          =[(8D+1)k0^2-64D](G H0)^2+64DF(H0^2-1),
    inner=Theta^2-Omega^2(a0+64a1)
         =E0^2-2E0 Omega(V0+V1)
          +Omega^2[(K^2-1)+Delta1+2V0V1].

The unique largest term in inner is Omega^2 Delta1, with degree
52r+200q+4W+158. Its square has degree

    104r+400q+8W+316.

The final subtracted norm term has degree 76r+288q+8W+216, strictly smaller.
The primary diagonal leading coefficient is
2^186 a^837288 c^400 >0, with c=2^17079501. Therefore the upper bound is
attained for the actual fixed coefficients, giving exact degree 1,675,396.
The economy degree is 1,738,228, with a similarly positive leader recorded
in its exact certificate. `verify.py` independently checks the formula,
the strict inequality, and the full cancellation-resolved leader replay.
The degree-certificate DAGs are larger than the primary evaluators and are
not used as the operation-count claim.

## 7. Artifacts, reproduction, and limitations

`construct.py` rebuilds both literal positive and natural DAGs and their
resolved-degree companions. `materialize_fixed.py` rebuilds every nonliteral
coefficient leaf from the common four ports, recording signed little-endian
magnitudes and hashes. All 12 leaves of each circuit are supplied. The whole
native tuple is separately supplied with its original builder, transition
input, proof, and notices. Never mix a single port from the compact590069-bit
instance with this original1064921-bit instance.

Run `python3 verify.py` or `python3 -O verify.py`. The checker performs exact
source identities, coefficient binding, literal regeneration, independent
gate recounts, exact-degree checks, mathematical negative controls and
independent modular direct-formula evaluations. Modular evaluations are
transcription checks, not solutions or consistency evidence. The proof is
ordinary mathematics and named inherited mathematics, not experimental
extrapolation. Internal checks are AI-assisted rather than external peer
review.

Further research: optimize the compatibility tables jointly with source row
operations; use coefficient equality classes throughout the additive-code
search; port the shared-tap lemma to Lean; and retain the direct compiler
endpoint while formally composing the new source and finalizer. A separate
question is whether a different proof-system encoding can reduce the nine
unknowns or avoid the inherited Pell/Jones architecture altogether.
