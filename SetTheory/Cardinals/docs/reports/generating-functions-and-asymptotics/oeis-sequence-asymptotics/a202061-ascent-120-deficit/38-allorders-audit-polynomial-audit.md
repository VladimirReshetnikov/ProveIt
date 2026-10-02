# Independent symbolic audit of the global action polynomials P3 and P4

Date: 2 October 2026. Result: **PASS**.

Both displayed polynomials in `action-expansion/proof.md` are independently
verified by exact symbolic substitution into the original duration and action
integrals. In particular, the qualification that P3 and P4 are merely
additional generated outputs can be replaced, in a downstream report, by
“independently verified action coefficients.” The source proof was not edited.

## Verified identities

With the source's normalization

\[
L=\log n,\quad \ell=\log L,\quad
B=\log Y_0-2\log3+2c+\frac73\ell,
\]

\[
P_3(B)=\frac{4B^3-105B^2+774B-2050-27\pi^2}{24},
\]

\[
P_4(B)=-\frac{7B^4-273B^3+3444B^2-19768B-189\pi^2 B
+1944\zeta(3)+999\pi^2+46290}{48}.
\]

These are identities in an arbitrary symbolic B, not fits at selected values.
The script also recovers P0=1, P1=B and
P2=-B²/4+7B/2-10, verifies zero duration residual through L^-4, and
checks the highest-degree coefficients of every polynomial through P4.

## Independence and method

`verify_p3_p4_direct.py` imports neither the producer generator nor any producer
verification code. It does not implement the producer's peak-k fixed-point
recurrence, nor its q=3k/L elimination formula. The defining row relation and
original duration/action parameterization are the mathematical inputs.

1. Derive p1, p2 and p3 afresh by cancelling successive powers of T^-1 in
   k-log k+log S(k)=T/2+c+log 2. The result is
   p1=2A-3, p2=-2A²+10A-33/2,
   p3=8A³/3-24A²+86A-120, where A=log T+c.
2. Write T=2L/3+H+U, with H=ell/3+log Y0 and
   U=u1/L+u2/L²+u3/L³+u4/L⁴. Keep H and B as independent symbolic quantities.
3. Taylor-expand k(T+log z)-k(T) directly using
   a_j=k^(j)(T)/(j! k(T)). Through L^-4 only a1, a2 and a3 enter.
   Their orders are L^-1, L^-3 and L^-4, respectively. Hence the integral
   corrections use exactly the moment pairs
   (r,m)=(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,4).
4. Recompute these convergent beta-log moments by a local Gamma-function jet,
   shifting only the reciprocal-Gamma denominator to a positive argument.
   This is a separate implementation from the producer's differentiated beta
   recurrence. Logarithms of formal series are computed by integrating f'/f;
   exponentials are computed from the coefficient equations for f'=g'f.
5. Let K=k/L and Im=2I_-/pi, Ip=2I_+/pi. Solve the original duration equation
   0=3U/2-log(3K)/2+log Im through L^-4. Then substitute the solution into
   log(action/(C F))=U/2+log(3K)/2+log((Im+2Ip)/3) and exponentiate.
6. Compare every exact polynomial with the displayed expressions. Every
   difference is identically zero, and both H and log 2 cancel completely.

The finite-order integral expansion and endpoint estimates remain those in the
source proof. This audit validates the algebraic coefficients; it does not
supply a new all-orders remainder proof or audit every analytic argument there.
Most importantly, it proves no reduction from the A202061 discrete coefficients
to the classical action, no prefactor, and no multiplicative equivalent.

## Reproduction

Run from any directory on the same workspace:

    python /workspace/shared/a202061-polynomial-audit/verify_p3_p4_direct.py

Tested with Python 3.12.14 and SymPy 1.14.0. The complete successful output is
`verification-stdout.txt`. All arithmetic in the coefficient comparison is exact.

## Audited source hashes (SHA-256)

- `proof.md`:
  `b061c02ad74debf6eec6ec58fb5f4d92a6971899195bee1380ac0d76cead5dd5`
- `generate_action_polynomials.py`:
  `86083628e173d48e1c458e235f3867eb19bf5a4e226e3fdfd9531c0f2fc7c4b8`

Both files are under
`/workspace/shared/a202061-allorders-research/action-expansion/`.
The generator's bytes were read only to record its hash; it was not executed or
imported by this check. The auditor inspected its implementation to ensure the
replay used a different computational route.
