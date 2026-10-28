# Further first-norm corrections: proposed13/92/90 and13/97/88

This is a bounded search and ordinary proposal, not a materialized candidate
or a new Lean endpoint. Frozen13/75/96 and13/84/92 remain unchanged. The
stdlib-only `search.py` was fully read before each execution; it imports no
project or incoming code, writes no graph/source, and assembles the complete
paid operation lists only in memory from the pinned75-row parent.

Parent graph SHA-256:
`48573f58aac3d60f706eb7f52e92f5c061bd74d41ad7e9e9ee3e2ea43dcd9ca1`.
Script SHA-256:
`9e6e7d02a7fac914aaa4feabff428c1f494cef0c4f0b46da3d6a754a1473f2a2`.
Captured result SHA-256:
`8a46d902b8a11c52a4dd617fb100624fc79141ecfda46b7b8158b27978b11d30`.
The separate data-only `leader_check.py` (SHA-256
`a9793a9170ff74bc6f0432a13ed4460e2fd2edce21d97ef863978bf4165a6944`)
was fully read and returned exit 0. It independently reconstructs the compact
A90 leader and checks the unique symbolic-port contribution at both selected
unknown monomials; its captured output is `LEADER_CHECK.json`.

## Exact candidate formulas and unchanged positive zeros

Use all parent75 definitions, in particular b=beta*J, q=b+1,
X=w*q, G=(K0+w)*C-F, V=f²*(c*T-R)-c and h=f²-1. Define

```
D = X*C-b*G = (w-b*K0)*C+b*F,
W = b*T*G*V,
A90 = 16*W*(W*h+2*f²*T*(V*C-b*G*f²*R)),
A88 = A90-32*f²*T²*V²*C*D.
```

For either coefficient A, set UA=U-A*(P-1) and
`pA=(P*Q)²+UA²+Z²-3`. The exact frozen generic
`ThirteenFirstNormCorrection92.correction_zero_iff` applies to any integer
A. On every positive assignment the existing P,Q negative-unit exclusions
hold, so either sphere zero forces P=1 before the correction is removed.
The new and parent75 entire positive zero sets therefore agree with
identity witness maps. There is no new sign assumption on UA, no semantic
oracle, and no need to establish U != -1 unconditionally.

The difference of the polynomials is always
`A²*(P-1)²-2*U*A*(P-1)`, generally nonzero. A new implementation would reuse
that exact generic theorem with a fresh polynomial evaluation/map theorem
and the actual current four-port endpoint; it would not modify the frozen
parent proof or claim a polynomial identity with it.

## Paid schedules and leaders

| Coefficient schedule | Operations | Multiplications/additions/subtractions | Degree UA | Degree pA |
|---|---:|---|---:|---:|
| A90 as displayed |92|55/19/18|45|90|
| A88 direct extension |100|61/19/20|44|88|
| A88 with shared16 factor |99|60/19/20|44|88|
| A88 factored below |97|59/19/19|44|88|
| Replacing b by q in A90 |92|55/19/18|47|94|

The last row is a negative lead, dominated by the accepted84/92. The100/88
and99/88 schedules are dominated by97/88 and should not be materialized.
The92/90 and97/88 points are nondominated relative to the currently accepted
13-variable operation/degree frontier. Fourteen-variable points do not
dominate them under the three-coordinate metric. No global optimum claim
is intended.

The97-row schedule uses the exact factorization

```
A88 = 16*T²*V*( (b*G)²*V*h
       +2*f²*(V*C*(2*b*G-X*C)-(b*G)²*f²*R) ).
```

It inserts precisely22 paid binary operations into the75-row parent prefix
before the sphere tail, and replaces only the old square of U. Their full
rows appear in the result under the `factored` variant. All constants2/16
multiplications, T², and every subtraction are paid. The script checks all
97 rows, all13 coordinates, and all4 ports reachable from the output. It
also verifies complete cut-polynomial identities among the100/99/97
coefficient schedules, not merely equality of their leaders.

The A90 auxiliary leader has75 terms; its square has639. Writing
B=beta*J, k0=eta+zeta and C0=B-F-alpha, its compact form is

```
32*B^20*k0^4*f^6*T^4*s^6*w²*C0*((w-B*K0)*C0+B*F).
```

This is exactly cancelled by the next coefficient term using D. The A88
auxiliary leader has302 terms; its square has7,112. The lexicographically
first unknown monomial of the A90 auxiliary has coefficient32*beta^20,
and that of A88 has coefficient-32*beta^19. Each is the unique symbolic-port
contribution at that unknown monomial. Consequently the corresponding
output coefficients are1024*beta^40 and1024*beta^38 and cannot vanish at
the actual beta>0. The output degrees remain90 and88 after specialization.

The algorithm retains the highest six homogeneous drops before correction,
with proven degree bounds at every gate; it fully expands the323-term main
norm Q and the small D=X*C-b*G cancellation. Once a nonzero corrected
auxiliary layer is found, only its exact leader is used by the final square.
All other output branches have degrees80/72. This is not a complete
expansion of either entire polynomial. Complete auxiliary leaders, all
gate degrees, output leader hashes, row counts and formula-refactoring
checks are in the result.

## Proposed next implementation boundary

Materialize92/90 and/or the strongest97/88 only after approval. Each needs
its own complete graph, ordinary proof, full source-bound finite auditor,
current2011 coefficient copies, actual dependence/corruption checks,
selected specialized coefficient proof, and small Lean leaf/checks over
the frozen arbitrary-correction theorem. Use the authenticated current
narrow-native dependency overlay and fresh current84/92 object; no broad
rebuild, frozen source edits, display change, or internal HA claim is
required. No such new candidate or Lean source has been created here.

## Rejected extra saving

A later hand count suggested factoring the common T out of A90 might yield
91 operations. Writing every binary row exposed an omitted multiplication:
forming T²*(bG*V) and then multiplying by the bracket costs two operations.
The full read-before-run `factor_t_challenge.py` returned exit 0 and confirms
92 operations, with the identical degree-45 auxiliary leader. Its captured
`FACTOR_T_CHALLENGE.json` preserves this negative result. No 91/90 claim is
made.
