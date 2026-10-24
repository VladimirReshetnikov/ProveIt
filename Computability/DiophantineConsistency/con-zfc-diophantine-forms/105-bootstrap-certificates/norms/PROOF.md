# Shorter exact radical norms

This packet gives arithmetic-circuit improvements to explicit Diophantine
consistency polynomials already present at ProveIt snapshot
`8f8fac484b976ba0ab75fd173282e838ca5a3b85` and the pinned incoming packages.
Every new circuit represents **the entire same polynomial** as its parent.
Its domain, degree, fixed coefficients and zero set are therefore unchanged.
No new native/compiler or internal-ZFC proof is asserted.

## Results

Binary additions, subtractions and multiplications each cost one; squares
and fixed-scalar multiplication are charged. Register reuse is free.

| Domain | Variables | Exact degree | Parent operations | New operations |
|---|---:|---:|---:|---:|
| Unrestricted integers | 13 | 1408 | 185 | 176 |
| Unrestricted integers | 13 | 1392 | 186 | 177 |
| Unrestricted integers | 13 | 1088 | 195 | 186 |
| Unrestricted integers | 13 | 1072 | 195 | 186 |
| Strictly positive integers | 11 | 211 | 111 | 110 |

The 1072-degree equation uses the reanchored guard in the latest incoming
`con_zfc_batched_certificates_2026-10-23.zip`; the 1088-degree predecessor is
retained for direct comparison. The first three integer parents come from
`ConZFC_13_Integer_Norms_2026-10-24.zip`. The eleven-positive parent is the
repository's adaptive-shear circuit. None of these improvements is a claim
of a globally simplest equation or a new source encoding.

The reusable free norm circuits use 18, 38 and 84 operations for three,
four and five roots, respectively; the inspected parent circuits use
19, 43 and 93 operations. The four-root circuit is supplied and checked
generically but has not been substituted into a separate complete endpoint
in this packet.

## Polynomial definition

Write

    F_m(x;a_1,...,a_m) = product over all independent signs
                        (x + sum epsilon_j sqrt(a_j)).

Every radical changes sign in pairs, so this is an integer polynomial in
x and the radicands. The notation is used only to prove identities; the
literal evaluators in `norms.py` contain no square roots or division.

The polynomial with one rational radicand is cleared as

    delta^(2^(m-1)) F_m(x;a_1,...,a_(m-1),C/delta).

Each identity below is an identity of integer polynomial rings, including
at delta=0. A rational interpretation of the norm in a semantic proof may
require delta nonzero; that condition is inherited unchanged from the
parent. The new identities do not divide by delta at any input.

## Three roots: a polarized form

Set

    z=x^2,
    G=delta(z+a-b)-C,
    U=delta^2 a z,
    V=delta b C.

Then the cleared three-root norm is exactly

    (G^2+4(U-V))^2 - 16 U G^2.

To prove the formula, take the norm of the two-root polynomial after
substituting x plus or minus sqrt(a). Equivalently, expand the standard
symmetric formula

    J=delta(x^2-a-b)-C,
    T=delta^2 ab, R=delta C,
    (J^2-4[T+R(a+b)])^2-64TRx^2.

The two expressions have exactly the same 35 coefficients in the free
variables x,a,b,C,delta. The alternative form saves one live gate after
all common-register sharing.

## Four roots: share the inner products

Let

    x2=x^2, d2=delta^2, s=a+b,
    q0=delta(x2+c-s)-C, q1=-2 delta x,
    T=d2 ab, R=delta C, z=64TR,
    A0=q0^2+c q1^2-4(T+Rs), A1=2q0q1,
    f0=A0^2+c A1^2-z(x2+c),
    f1=2(A0A1+zx).

The answer is

    f0^2-c f1^2.

Indeed, in the quadratic extension u^2=c, the cleared inner three-root
norm at x-u is f0+f1u. Multiplication by its conjugate gives the displayed
answer. Sharing a+b, T and R and factoring the common two in f1 saves five
gates relative to the inspected 43-gate implementation. No new number
theory is used; this is exact arithmetic reuse.

## Five roots: take the diagonal conjugates together

Let u^2=c, v^2=d, and put t=x+u+v. Define

    x2=x^2, cd=c d, s=c+d, ab_sum=a+b, delta2=delta^2,
    q0=delta(x2+s-ab_sum)-C,
    q3=2delta, q1=q3 x, q12=q1^2, q32=q3^2,
    T=delta2 ab, R=delta C, z=64TR.

The element q=delta(t^2-a-b)-C has components

    q=q0+q1u+q1v+q3uv.

The element q^2-4[T+R(a+b)] has components

    A0=q0^2+s q12+cd q32-4(T+R ab_sum),
    A1=2q1(q0+d q3),
    A2=2q1(q0+c q3),
    A3=2(q0q3+q12).

The cleared inner three-root norm is

    f=f0+2f1u+2f2v+2f3uv,

where

    f0=A0^2+c A1^2+d A2^2+cd A3^2-z(x2+s),
    f1=A0A1+d A2A3-zx,
    f2=A0A2+c A1A3-zx,
    f3=A0A3+A1A2-z.

Instead of eliminating u and then v independently, pair simultaneous
sign reversal first. The product of f(u,v) and f(-u,-v) is

    G+4uv H,

with

    G=f0^2+4(cd f3^2-c f1^2-d f2^2),
    H=f0f3-2f1f2.

The other two simultaneous conjugates give G-4uvH. Therefore the full
five-root norm is

    G^2-16cd H^2.

This diagonal pairing is the reason the half-sized odd components f1,f2,f3
can be retained without separately multiplying each by two. Together with
the q1=q2 symmetry and sharing the inner sums and products, it gives an
84-gate circuit. The exact 20,349-term coefficient dictionary agrees with
the retained 93-gate implementation.

## Substitution into complete equations

For every integer parent, the verifier first regenerates the unmodified
parent and compares its literal DAG with the retained incoming JSON. It
then changes only the norm evaluator. An exact shared-term comparison
checks the complete seven boundary registers

    center, scaled_Df, scaled_Dtau, main_radicand,
    scaled_Ag, scaled_Cy, delta.

The main radicand is Dmain for the non-CRT parents and scaled_Dmain for the
CRT parents. Both the old and new full DAGs are checked to substitute
these same seven polynomials into the old and new generic norm circuits.
The generic integer-polynomial identity then proves equality of the
complete parent and child polynomials at every integer tuple.

For the eleven-positive parent, every prefix and finalizer row is
unchanged. Its entire 19-row norm tail is replaced by the 18-row tail
above, and exact sparse expansion checks that substitution too.

Pointwise polynomial equality transfers all inherited degree certificates,
including their nonzero leading coefficients, and all zero-set theorems.
It is stronger than an existence-only equivalence or a change of witnesses.

## Verification and boundaries

Run

    python3 build_and_check.py
    python3 -O build_and_check.py

Only Python's standard library is required. Both runs compare every
coefficient of the generic norms, verify exact whole-prefix and norm
substitution, authenticate the actual six integer coefficient payloads,
rebuild the five complete polynomial DAGs, and record operation counts.
No bounded search for a zero is performed.

The ordinary parent consistency arguments and whole source coefficients
remain the mathematical dependencies. Retained parent sources and their
papers are under `upstream`; copied historical paths are not new
calibration claims. This packet supplies no new Lean/Rocq certificate or
encoded internal-ZFC derivation. The generic identities and their concrete
cost improvements are the new completed result.
