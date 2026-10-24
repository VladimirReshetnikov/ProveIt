# Ten-integer polynomial shears

The three norm10 variants in the polynomial-shears arrival have sound
ordinary integer-zero-set bijections to the480-operation H1868 predecessor.
Their exact degree/operation pairs are1,179,788/484,1,114,252/487 and
1,081,125/521. They use the same ten unrestricted integers and all twelve
actual fixed leaves. No new sign, divisibility or canonical-witness premise
is needed for these transformations.

The archive is `docs/incoming/ConZFC_Polynomial_Shears_2026-10-23.zip`,
arrival440dd03ab8, SHA256
`978f7e8be846732c1330f3a75a0fe38871432f79951b8eaad6ef096f3e03e165`.
This review concerns its `norm10` component. Separate reviews cover its
integer residual systems and eleven-positive companion.

## Universal proof

The parent is

```
P(v,m) = ((Sigma*m-Theta)^2-Sigma^2*(a0+a1))^2-4*Sigma^4*a0*a1.
```

All symbols except m are polynomials in the other nine integer inputs.
For every integer polynomial R(v), substitution m_old=m+R is an integral
polynomial automorphism, with inverse m=m_old-R. Hence it carries the
entire zero set bijectively, including every signed or degenerate input.
No assertion about approximating a positive square root is necessary.

In the supplied source, A=2h and D=(A²-4)C²+4. Write u=C²,
E0=u*xi, E=D*E0 and a1=DFI. The short shifts are

```
R0=2*A*E*G*H,
R1=2*A*E0*(D-2*C²)*G*H.
```

The exact identities

```
DF-(2*A*E)^2 = D-16*E²,
DF-[2*A*E0*(D-2*u)]²
 = D+16*E0²*(u*(3*u-4)*A²-16*(u-1)²)
```

give the stated lower-degree defects. The six-term shift is an explicitly
printed26-monomial integer polynomial. Its complete2,306-term defect is
checked coefficient by coefficient; discovery by a formal radical series
is not an additional hypothesis.

The source degrees are deg(Sigma)=81,922, deg(Theta)=81,925,
deg(a0)=294,619 and deg(a1)=458,818. All shifts have degree229,409;
their defects have respective upper degrees426,050,393,282 and368,449.
Expanding the shifted center proves the advertised upper bounds. Actual
fixed-port leading residues are nonzero. In the six-term case the unchanged
cross term has degree1,081,125 while the square has degree at most1,064,586,
so no top cancellation is possible.

The odd cross degree also proves the manuscript's restricted optimum:
every final-coordinate polynomial translation has degree at least1,081,125,
because the other summand is a square and therefore has even degree. This
does not bound other coordinate changes or encodings.

## Finite replay and further exact saving

The three scoped stages `build.py`, `verify.py` and
`audit_independent.py` passed normally and with optimized Python in separate
scratch copies. All three rebuilt literals were byte-identical in both
modes. The independent audit uses SymPy1.14 and imports neither builder nor
standard verifier. The standard audit verifies every actual fixed leaf,
the exact shear transcription, liveness, degree identities and120 signed
modular controls per circuit. Those controls supplement the universal proof.

The receipts are retained in
[`norm-tail-sharing/NORM10_REPLAY.json`](candidates/norm-tail-sharing/NORM10_REPLAY.json).
That directory also supplies an exact one-gate saving in each variant:

```
(t²-s(a+b))²-4s²ab = (t²+s(a-b))²-4sat².
```

The resulting counts are483,486 and520, with identical polynomials and
degrees. The480-operation predecessor similarly becomes479. This does not
alter the inherited ordinary native/compiler/refutation theorem, prove
that theorem from scratch, or supply a new internal-ZFC/Lean certificate.
Lean formalization remains paused.
