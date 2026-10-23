# A 31-positive-variable quartic by eliminating a packing register

## Result and dependency boundary

The pinned package-18 quartic32 source at ProveIt commit
`ae3007ca4467011e0e051c84acb4a1dd13971b0e` has 32 positive witnesses and
23 quadratic equations. One packing register is unnecessary. The following
construction has 31 positive witnesses, 22 quadratic equations, and an exact
quartic sum of squares. Its fixed compiler ports are unchanged.

This is an exact algebraic, tuplewise reduction of that source. Composed with
its ordinary Pell/compiler proof and K215 calibration, ZFC proves that the
new polynomial has no positive solution if and only if Con(ZFC). This is not
an end-to-end proof-assistant certificate. No truth of Con(ZFC), consistency
of ZFC, or global minimality is assumed or established.

The source's literal JSON and its hashes are preserved in `SOURCE_LEDGER.json`.
No upstream code was executed. Our `build_arithmetic.py` is newly authored.

## Exact equations

All 31 coordinates are strictly positive integers:

    J,F,alpha,z,f,h,i,o,j,s,w,tau,eta,zeta,y,gamma,
    N,E,P,c,a,X,D,C2,L,F2,V,g,I,Baux,Delta.

The four fixed ports beta, K0, MC and MF must be one complete authenticated
blank compiler tuple. MF is the shifted source mask. All coefficients remain
fixed integers, not quantified inputs. The following are affine abbreviations:

    q=beta J+1, k=eta+zeta, H=4a+3, C=q-F-alpha.

The 22 equations are:

    L=q^2-1,
    N=q(L+1),
    X=wq,
    a=E+sN,
    E=X(a-E),
    c=k(a-E)+eta,
    P=E(c-eta)+k,
    tau^2=P(P-k)+1,
    D=X+ac+gamma H,
    Delta=a^2+H,
    C2=c^2,
    D^2=Delta C2+1,
    k=jc-V+1+hE,
    jc-V=(q-F)(N-q)-CL+(MC+q MF)J,
    (K0+w)C+(q-F)-z(q-1)=1,
    F2=f^2,
    V=of-c,
    g=y^2-V^2,
    I=i C2,
    Baux=I^2,
    Baux=Delta(F2-1),
    y^2-Baux g=1.

Every displayed residual is quadratic after the four affine abbreviations
are expanded. Let r_1,...,r_22 be the left sides minus the right sides in this
order. The single polynomial is

    Q31 = r_1^2 + ... + r_22^2.

Its literal sparse data, including all coefficient-port exponents, are in
`quartic31.json`; `quartic31_expanded.json` contains the 306-term expanded
sum of squares. Because tau occurs only in r_8 and with term tau^2, the
coefficient of tau^4 in Q31 is exactly 1. The degree is therefore exactly 4
for every admissible tuple of fixed coefficients.

IMPORTANT: z here is the OLD positive transport coordinate, as in the pinned
package-18 quartic source. It is not the shifted z of package-22 retained59.
No tuple components or transport conventions have been spliced.

## Exact zero-set equivalence and sign obligations

The source has an additional positive variable G and the equations

    G=(q-1)(q-F)+alpha=q(q-F)-C,
    jc-V=LG+(MC+q MF)J.

The new packing expression obeys the polynomial identity

    L[q(q-F)-C] - [(q-F)(N-q)-CL]
      = (q-F)[q(L+1)-N].

Thus it agrees with LG whenever the retained N equation holds.

Forward direction: forget G from any positive source solution. The displayed
identity gives the new packing equation; every other equation is unchanged.

Reverse direction: a new positive solution has q>1. Its unchanged transport
identity gives

    (K0+w)C = F+(z-1)(q-1)>0.

Since K0+w>0, C>0. Define

    G=q(q-F)-C=(q-1)C+q alpha.

This is a strictly positive integer. Restoring this single coordinate now
satisfies both removed source equations, by the exact identity. All other
coordinates are untouched. The two maps are inverse: this is a bijection of
positive zero sets, not only an existence reduction.

No new negative-root or unit-sign branch is introduced. All original source
roots, quotient coordinates and equations remain. The only restored variable
is G, whose strict positivity was proved above. In particular alpha is NOT
eliminated or relaxed; all original outer bounds and native-window hypotheses
are inherited unchanged.

## Nonnegative normalization for the nine-variable compressor

Replace each of the 31 positive coordinates x by n_x+1. This preserves degree
4 and gives a polynomial over 31 nonnegative unknowns with the same existence
condition. At all positive coordinates equal to 1, the fifth residual is

    E-X(a-E)=1.

Hence the shifted polynomial is strictly positive at the all-zero tuple,
independently of the four fixed coefficients. This preserves the normalization
condition required by the pinned nine-variable compressor. Its witness-count
parameter can therefore be changed from 32 to 31; the compressor worker
separately audits the resulting coefficient and degree arithmetic.

## Operation counts and reproduction

The explicit equality-comparison circuit in `quartic31_system.json` has
65 binary gates: 33 multiplications and 32 additions/subtractions. Equality
comparisons are free, exactly as in the source's operation convention. Every
multiplication by a coefficient or small integer is charged. Every gate,
witness and coefficient port is live.

The complete SOS circuit in `quartic31_circuit.json` has 130 gates:
55 multiplications and 75 additions/subtractions. Its 65 additional gates are
22 residual subtractions, 22 squares and 21 additions. These are explicit
upper bounds from literal evaluators, not operation-minimality claims.

Run `python3 build_arithmetic.py` in this directory. The script checks the
packing identity as a zero sparse polynomial, compares every unchanged
residual with the pinned source's literal sparse terms, verifies all 22 new
residual degrees and exact quartic degree, checks the tau^4 and normalization
certificates, verifies the comparison and residual circuits symbolically,
checks gate/input liveness, and performs 1000 signed integer evaluations of
the packing identity. These are algebraic audits, not a search for a solution
or a substitute for the inherited unbounded arithmetic/compiler proof.
