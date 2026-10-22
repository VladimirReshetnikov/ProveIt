# Auxiliary gaps: lower degrees at essentially unchanged circuit size

This note uses the notation and established signed-domain theorem of
`ORDINARY_BLANK_PROOF.md`, and the root-reconstruction framework of
`ROOT_ELIMINATION_PROOF.md`. The coefficient ports and blank-input compiler
are unchanged. All degree statements treat those ports as fixed integers,
with beta=B-1>0. The compiler can be the original blank compiler or the
verified five-cell cross compiler, provided its stated interface holds.

## 1. The gap coordinate and its domain

Write

    U=Delta(f^2-1), V=c(Tf-1)-Rf^2,
    Na=U(V^2-y^2)+y^2.

Replace the supplied coordinate y by a new coordinate e, and compute

    y=V+e.

The exact identity is

    Na=V^2-(U-1)e(2V+e).                         (1)

In the emitted circuit only one additional addition is required: the
existing y-square now squares the computed quantity V+e. Moving that
square after the computation of V preserves the arithmetic dependencies.
The factored expression (1) proves the improved degree; the circuit does
not need to evaluate that expression separately.

For fixed remaining coordinates, the maps e -> y=V+e and y -> e=y-V are
inverse integer polynomial substitutions. Hence over the expanded signed
domain of the ordinary construction this is an exact bijection of zero
tuples. The nine positive coordinates are still

    J,F,alpha,z,i,s,w,eta,zeta,                   (2)

and the six unrestricted coordinates are now

    h,f,T,tau,e,gamma.                           (3)

Any all-positive gap zero is in this signed domain and is therefore sound.
For positive-domain completeness, use the canonical positive auxiliary
Pell point in the existing blank-compiler construction. It has V>0,y>0,
U>1, c>2R, and V=-R modulo c. The last congruence follows from the
normalized strong equation, or from c^2 dividing f^2-1 after ordinary
rank recovery. Thus

    V >= c-R > 1.

The auxiliary norm gives

    (U-1)(y^2-V^2)=V^2-1>0,

so y>V and e=y-V is strictly positive. Thus the canonical positive
witness also gives a positive gap witness. This is an existence theorem
for the positive domain; it does not assert that every positive original
tuple necessarily has a positive gap.

The transport coordinate is old z for the product, and z_new=z_old-1 for
the six-equation system and sum of squares. Its already-proved strict
positivity is unaffected by the new auxiliary coordinate.

## 2. Fifteen-positive-variable equations and their integer versions

Keep all five other factors of the ordinary product. Replace only its
auxiliary factor by (1). The resulting product has 70 operations, while
the corresponding system of six equations has 61 and its sum of six
squared residuals has 78. All gates and all supplied ports are live.

| Packet | Positive variables | Operations | Multiplications | Add/subtract | Exact degree |
|---|---:|---:|---:|---:|---:|
| `ordinary_gap_system61` | 15 | 61 | 34 | 27 | max 22 |
| `ordinary_gap70` | 15 | 70 | 39 | 31 | 93 |
| `ordinary_gap_sos78` | 15 | 78 | 40 | 38 | 44 |

The six factor/residual degrees are

    22,18,22,7,2,22.                             (4)

To give uniform leading certificates put Q0=beta J, k0=eta+zeta and

    T2=w(Q0-F-alpha)-z Q0.

The new auxiliary factor has leading form

    -2e k0 w^2 s^3 Q0^11 T f^3.                 (5)

Combining the inherited factors gives the degree-93 leading form

    -16 Q0^52 h gamma i^2 k0^8 w^7 s^15
        T f^3 e T2.                             (6)

Its coefficient at

    J^53 h gamma i^2 eta^8 w^7 s^15 T f^3 e z

is 16 beta^53, so it is nonzero for every valid compiler. The degree-22
leaders of the first, auxiliary and strong residuals are respectively

    -w^2 k0^2 s^4 Q0^14,
    -2e k0 w^2 s^3 Q0^11 T f^3,
    i^2 k0^4 s^4 Q0^12.                         (7)

The degree-44 leader of the sum of squares is the sum of their squares.
It cannot vanish as a real polynomial.

Applying nine disjoint substitutions

    Pos(u,v,t)=1+u^2+v^2+t(t+1)

to (2), and leaving (3) unrestricted, gives 33 integer variables. The
surjectivity proof for Pos is unchanged. Each substitution costs seven
gates. Weights two on (2) and one on (3) give exact weighted residual
degrees

    44,35,39,13,4,44.                            (8)

Consequently the integer results are:

| Packet | Integer variables | Operations | Multiplications | Add/subtract | Exact degree |
|---|---:|---:|---:|---:|---:|
| `ordinary_gap_system61_over_Z33` | 33 | 124 | 61 | 63 | max 44 |
| `ordinary_gap70_over_Z33` | 33 | 133 | 66 | 67 | 179 |
| `ordinary_gap_sos78_over_Z33` | 33 | 141 | 67 | 74 | 88 |

For the product the weighted leading form is still (6). For the sum of
squares, only the first and strong squares from (7) have maximum weighted
degree 88. The disjoint homogeneous substitutions x -> u_x^2+v_x^2+t_x^2
preserve nonvanishing: setting v_x=t_x=0 gives the injective monomial
substitution x -> u_x^2. These are exact degrees, not naive degree bounds.

## 3. Apply the gap before eliminating the normalized root

For the fourteen-variable construction retain normalized i, as in the
original blank P67. Remove f and replace y with e. Define

    Qstar=(Delta i c^2)^2,
    dstar=1+Delta i^2 c^4,
    bstar=c+R dstar, vstar=cT,
    Sstar=Qstar-1,
    rstar=bstar+Sstar e,
    pstar=dstar vstar^2,
    Astar=pstar+rstar^2-Qstar Sstar e^2-1,
    Bstar=2 vstar rstar,
    Kstar=Astar^2-dstar Bstar^2,
    P4=N0 N1 Nk Nt.

The proposed equation is

    Phi_gap=P4(1+Kstar)-1=0.                     (9)

The circuit computes dstar Bstar^2 as 4 pstar rstar^2, so it does not
construct Bstar explicitly. There are 49 root-free prefix operations
and 26 tail operations, for 75 total: 43 multiplications and 32
additions/subtractions. This uses the same number of gates as the old
fourteen-variable inner norm, while reducing its degree from 293 to 219.

The essential cancellation is the exact identity

    Astar=pstar+bstar^2
               +(Qstar-1)e(2bstar-e)-1.         (10)

If f^2=dstar and V=vstar f-bstar, the root remainder is

    Astar-Bstar f
      =Qstar[V^2-(V+e)^2]+(V+e)^2-1.            (11)

Thus this is the norm elimination of precisely the new auxiliary gap
equation, not of an unrelated lower-degree necessary condition.

## 4. Soundness, nonzero denominators, and completeness for (9)

On a zero of (9), P4 and 1+Kstar are integer units. Since Bstar is even,

    1+Kstar=1+Astar^2 modulo 4,

which cannot be -1 modulo 4. Hence P4=1 and Kstar=0. The usual first-Pell
and main-norm arguments give N0=N1=1. The outer transport-unit bounds
give 0<R<a<Delta, independently of root reconstruction.

In the positive domain, bstar>0, e>0 and vstar>0, so rstar>0 and Bstar is
nonzero. Therefore f=Astar/Bstar is a rational square root of the integer
dstar. A rational square root of an integer is an integer, and dstar>1
ensures f is nonzero. Identity (11) restores the auxiliary equation with
the possibly signed coordinate y=V+e. Also f^2=1+Delta i^2c^4.
The substitution i_ordinary=Delta i restores the signed ordinary product
exactly, since

    Delta(f^2-1)=Qstar=(i_ordinary c^2)^2.

Its established signed-domain theorem therefore proves soundness.

For the stronger domain theorem, retain positivity only for the same nine
coordinates (2), and allow h,T,tau,e,gamma to be arbitrary integers. Two
denominator factors now require a proof: vstar and rstar.

The identity Qstar=Delta(dstar-1) gives

    Qstar-bstar=(Delta-R)dstar-Delta-c
      >=dstar-Delta-c
      =1+Delta(i^2c^4-1)-c > 1.                 (12)

Here c>2, i>=1 and Delta>0 follow from the positive coordinates and the
outer bounds alone. Therefore

    2<bstar<Qstar-1=Sstar.

For any integer e, rstar=bstar+Sstar e is nonzero: its residue bstar lies
strictly between 0 and Sstar. This argument does not assume e positive.

If T=0 then pstar=vstar=Bstar=0. Equation Kstar=0 implies Astar=0, or

    Qstar bstar^2-(Qstar-1)(e-bstar)^2=1.         (13)

Write y0=e-bstar. Since bstar>1, (13) implies |y0|>=bstar+1. It would
follow that

    bstar^2-1=(Qstar-1)(y0^2-bstar^2)
                >=(Qstar-1)(2bstar+1),

contrary to 1<bstar<Qstar. Thus T is nonzero on every zero. The root
denominator is consequently nonzero even in this signed domain, and
the preceding root-restoration proof applies unchanged.

For completeness take the canonical positive normalized blank witness.
Section 1 proves e=y-V>0. Its normalized strong equation gives f^2=dstar,
and (11) gives Astar=Bstar f. Also P4=1. Deleting f therefore yields a
positive zero of (9). The existence condition is exactly the original
blank-halting condition; composing with the supplied K215 calibration
gives the same ZFC theorem relating absence of solutions and Con(ZFC).

The nine Pos substitutions and five untouched signed coordinates give
32 unrestricted integer variables and 138 operations, with exact degree
434 as proved below.

## 5. Degrees and a comparison with the outer norm

The positive and signed-domain weighted degrees are:

| Quantity | Ordinary total degree | Weighted degree |
|---|---:|---:|
| Qstar | 46 | 92 |
| dstar | 34 | 68 |
| bstar | 38 | 76 |
| vstar | 6 | 11 |
| pstar | 46 | 90 |
| rstar | 47 | 93 |
| Astar, using (10) | 85 | 169 |
| Bstar | 53 | 104 |
| Kstar | 170 | 338 |
| P4 | 49 | 96 |

The unique highest term of Astar is 2 Qstar e bstar. Its square has
degrees 170 and 338, while dstar Bstar^2 has degrees 140 and 276. Thus
(9) has exact degrees 219 and 434. Its ordinary leading form is

    32 h gamma e^2 i^8 k0^19 w^17 s^36
       Q0^131 (Q0-F)^2 T2.                      (14)

For example its coefficient at

    J^134 h gamma e^2 i^8 eta^19 w^17 s^36 z

is -32 beta^134. Formula (14) is also the weighted leader before the
homogeneous Pos substitution; that substitution preserves nonvanishing.

For comparison the direct outer norm is

    AO=P4(Astar+1)-1,
    BO=P4 Bstar,
    Psi_gap=AO^2-dstar BO^2=0.                   (15)

Its circuit also has 75 operations, now 45 multiplications and 30
additions/subtractions, and exact degree 268. Its 32-integer-variable
form has 138 operations and degree 530. Its leading form is

    256 h^2 gamma^2 e^2 i^8 k0^22 w^22 s^44
        Q0^160 (Q0-F)^2 T2^2.                   (16)

The coefficient at J^164 h^2 gamma^2 e^2 i^8 eta^22 w^22 s^44 z^2 is
256 beta^164. The squared term has degrees 268/530, whereas the other
norm term has degrees 238/468, so cancellation is impossible.

For clarity, (15) is valid but is dominated by (9) at the same number
of operations. It does not dominate the old 73-operation degree-342
outer form, since it uses two more operations. It is emitted to make
that comparison reproducible, not as a new Pareto recommendation.

To check its soundness, reduction modulo P4 gives Psi_gap=1 modulo P4,
so P4 is a unit. The same outer bounds give (12), hence rstar is nonzero.
If T=0 then AO=0 and P4 times the left-hand side of (13) equals 1. The
bracket cannot be -1 modulo 4 because Qstar is a square; hence (13)
holds and is impossible. Therefore BO is nonzero. Reconstruct the
integer f=AO/BO and use

    AO-BO f=P4{Qstar[V^2-(V+e)^2]+(V+e)^2}-1

to restore the full normalized product, then the ordinary signed one.
Completeness follows from the same canonical witness.

## 6. Reproduction and proof boundary

Run `python3 build_gap.py` or `python3 -O build_gap.py` in this directory.
The script imports the authenticated baseline builders, emits ten JSON
packets, checks every live gate and port, and records exact operation
counts. It verifies 100 signed/rational full-formula fixtures, 100 local
gap/root identity fixtures, 160 integer-substitution fixtures, and two
modular univariate degree diagnostics for each packet. It also compares
16 attained leading coefficients to independently written highest-form
formulas (6), (7), (14), and (16). Explicit exceptions keep all checks
active under `python -O`.

These finite diagnostics corroborate algebra and bookkeeping. They do
not substitute for the signed-domain, rational-root, canonical-existence,
or inherited compiler proofs above, and do not exhibit a halting K215 run.
