# Residual reductions after P76

This is a limited follow-up search, not a new equation or a global lower
bound. The checked fifteen-variable candidates remain P73/degree 80,
P75/degree 68 and P76/degree 64. The P76 construction is documented in
[`SHORT_REDUCED_STRONG.md`](SHORT_REDUCED_STRONG.md).

## The scalar first-residual correction has reached its degree limit

Write `R0=N0-1`, `Rs=Ns-1`, and let

```
S = Rs-(i*c)^2*R0.
```

This is the corrected strong residual used by P76. At nonzero `beta`, the
leading homogeneous forms in the actual fifteen unknowns are

```
R0_top = -w^2*s^4*(eta+zeta)^2*(beta*J)^14,       degree 22;
S_top  = -2*i^2*w*s^6*(eta+zeta)^4*(beta*J)^19,   degree 32.
```

No further scalar polynomial multiple of `R0` can lower `S` below degree 32.
Indeed, take any polynomial `D`. If its degree exceeds 10, then `D*R0` has
degree greater than 32, so `S-D*R0` has that larger degree. If its degree is
at most 10, its degree 32 homogeneous contribution is divisible by `w^2`.
It cannot cancel the displayed degree 32 part of `S`, whose `w` exponent
is exactly 1. This argument uses the integral polynomial ring and nonzero
`beta`. It applies to all corrections `Rs-C*R0`, because each can be written
`S-D*R0` with `D=C-(i*c)^2`.

This obstruction is an ordinary mathematical observation, not a newly
formalized Lean lower-bound theorem. It says nothing about changes to
several residuals at once, different encodings, or added witnesses.

## An auxiliary correction exists but does not improve the current frontier

Let `Ra=Na-1`, and keep `V=c*(T*f-1)-R*f^2`. The shear

```
A = Ra+(T*f)^2*(f^2-1)*R0
```

preserves the common zero set when `R0` is also imposed. Its degree 28
leading term cancels. The new degree is 27, with weighted leading form

```
-2*X^2*k*Y^3*T*R*f^5.
```

Here `X,Y,k,R` have degrees 2, 4, 1, 4 respectively. In actual coordinates,
the leading form of `R` is `(beta*J)^3*(beta*J-F)` and is nonzero.
The direct live schedule adds four operations: square the existing `T*f`,
multiply by the existing `f^2-1`, multiply by `R0`, and add `Ra`.
The degree 32 strong residual still dominates, so this does not improve
P76's degree 64. It has not been emitted as a separate candidate.

## Exact finite search and failed gate-saving routes

Run:

```sh
python3 Computability/DiophantineConsistency/tools/search_residual_shears.py
```

The stdlib sparse checker expands 405 strong corrections of the form

```
Rs-i^2*(A*(k*Y)^2+B*k*Y*eta+C*eta^2)*R0,
```

for `-2<=A<=2`, `-4<=B,C<=4`. All 81 cases with `A=1` have degree 32;
the other 324 retain degree 34. The P76 coefficient is `A=1,B=2,C=1`.
The checker also expands 45 auxiliary corrections
`Ra+(T*f)^2*(A*f^2+B)*R0`: the nine cases with `A=1` have degree 27,
and the rest retain degree 28. The exact leading forms above are checked,
not inferred from random evaluations. Results are saved in
[`circuits/residual_shear_search.json`](circuits/residual_shear_search.json).

The wave-six package 45
[`short/SEARCH_AUDIT.md`](con-zfc-diophantine-forms/45-multioutput/short/SEARCH_AUDIT.md)
also checks packed-index factoring, a positive first-root gap, main-norm
expansion, and an auxiliary-root gap. None saves gates under the shared
schedule. In particular, shifting the first root lowers its own residual's
degree but removes the leading first-norm term used by the P76 cancellation.
No 75-operation degree 64 evaluator is claimed by this search.
