# The exact 209-coordinate compilation

This note proves the algebraic part after the semantic signed-horizon lemma.
The latter replaces the incoming cofinal-horizon row by `t=2+4z`, and proves
that the modified210-coordinate system still has a zero exactly when the
calibrated numerical calculus has a finite refutation. Its unbounded proof is
separate; the coefficient checker does not establish that statement.

## 1. Frozen input and semantic source

The incoming principal210 equation is taken byte-for-byte from
`ConZFC_Pell_Growth_210_2026-10-25.zip` at ProveIt commit
`d123610bc98fef2006bff1c9466bc3f1221003e7`.
Its equation JSON SHA-256 is
`20a2108353a3756ed7d1ddfdc71695131dcf0b6d94039988d9565ac48e6e1f0a`.

The 210-coordinate input has150 residuals of degree at most two. Source row 125
is the old horizon `t-16-4z^2`. In the semantic source it is replaced by
`t-2-4z`. Every other residual is unchanged. The altered row is retained in
`source210/affine_horizon_equation.json`; its mathematical interpretation is
not conflated with an algebraic coordinate change of the old square horizon.

## 2. Eliminate the affine horizon coordinate

In the affine source, the old coordinate 178 is the horizon parameter z and
occurs only in row 125. The old coordinate 0 is t. Replace every occurrence of
t by `2+4z`, discard row 125, and keep z as new coordinate 0. Every other
coordinate retains its old order except that the redundant old coordinate 178
is deleted. Thus209 independent integer coordinates remain, and149 residuals.

The inverse map is explicit: reconstruct old t as `2+4*x0`, old z as `x0`,
and all other old coordinates from the recorded order map. This is a
bijection between integer zeros of the affine source and its projection.
Since the substitution is affine, every residual remains quadratic.

## 3. Saturate the forced power-of-two divisibility

Let d=2^19. The retained growth-divisibility residual is exactly

    F-d*t*(2u+1)=0.

The new horizon has t=2+4z and hence v2(t)=1 for every integer z. Both t and
2u+1 are nonzero. Therefore every zero satisfies

    v2(F)=20.

In particular F is divisible by every s=2^k with 0<=k<=20. For any such s,
put F=s*f throughout the remaining residuals and divide the
growth-divisibility residual by s. This division is coefficientwise integral:
F has coefficient s after substitution, and d*t*(2u+1) has all coefficients
divisible by s because t=2+4z.

The map from new zeros to old zeros sends f to F=s*f. The inverse on old zeros
is f=F/s, which is integral by the retained divisibility equation. These maps
are inverse. The substitution is linear, and scalar normalization does not
change a residual's zero set. Thus the operation preserves both integer
solvability and quadratic residual degree.

The sparse principal takes s=64. The low-height companion takes s=128 before
the residual basis change described next. This is not a claim that arbitrary
integer coordinates may be divided by 64 or 128; it uses the exact source
divisibility equation.

## 4. Use one residual as the carrier of the growth square

In the s=128 system, residual135 is the unchanged
`cap.pooled_index_residue` row. Its f^2 coefficient is128^2. Other residuals
containing f^2 have integer-multiple coefficients. For each such row R_j,
replace it with

    R_j - ([f^2]R_j / 128^2) R_135,

while leaving R_135 unchanged. Every multiplier is an integer. The inverse
adds the same multiple of the unchanged row. This is a triangular
determinant-one change of residual basis, so the simultaneous residual zero
set is unchanged. It need not preserve the sum-of-squares polynomial away
from that zero set, and no such claim is made.

The literal certificate lists each modified row and multiplier. It is checked
independently against the emitted residuals. The common integer zero set is
also exactly the zero set of the new sum of 149 squares, because a sum of
integer squares vanishes if and only if every summand vanishes.

## 5. Literal results and degree certificates

| Profile | Integer coordinates | Squares | Degree | Collected monomials | Coefficient height |
|---|---:|---:|---:|---:|---:|
| Incoming principal |210|150|4|5282|2^40|
| Affine209, F=64f |209|149|4|5486|2^32|
| Affine209, F=128f, changed basis |209|149|4|6654|2^30|

For the sparse principal, the coefficient of x0^2*x208^2 in the collected
polynomial is exactly 2^32. For the low-height companion it is exactly 2^30.
Both are nonzero, and all squared residuals have degree at most four;
therefore degree is exactly four in each case. Every one of the 209 variables
occurs in its literal polynomial specification.

The sparse principal trades 204 additional monomials for one fewer coordinate,
one fewer squared residual, and 256-fold smaller coefficient height. The
low-height companion has 1024-fold smaller height than the incoming principal,
at the cost of 1372 additional monomials. Neither dominates every known form.

The recorded finite search inspected ten scales, s=1,2,...,512 in powers of
two, with and without this specific carrier-row operation. It supports only
the listed finite comparison, not optimality over coordinate changes, bases,
or arbitrary Diophantine equations.

## 6. What the scripts establish

`code/build.py` reconstructs all new sparse rows, expansions, readable
residuals, metric files and transformation certificates from the frozen input.
`verify.py` does not import producer code. It independently expands the
substitutions term by term, verifies every residual-basis identity, collects
each sum of squares, checks all coefficients and metrics, and exhibits the
height-attaining quartic monomial. A separate clean rebuild compared 15
generated artifacts and both source stages byte for byte.

These are finite algebraic checks. The signed-horizon and cofinal-witness
proofs are ordinary unbounded mathematics. The C222/ZF/ZFC logical calibration
and the source's shared Pell, binomial, CRT and Horn-flow theorems remain the
identified inherited dependencies. No new end-to-end proof-assistant theorem,
consistency decision, or polynomial zero is asserted by these scripts.
