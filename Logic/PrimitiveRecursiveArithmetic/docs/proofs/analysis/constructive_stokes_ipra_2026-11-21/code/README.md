# Exact-arithmetic reference implementation

Run from the package root:

```sh
python3 code/validate.py
```

Only the Python standard library is used. All mathematical comparisons use
`fractions.Fraction`; the decimal columns in the CSV are for display only.
These computations are executable validation of the formulas in the report.
They are not a formal proof of Stokes' theorem or an object-level iPRA derivation.

## The finite quantities

`stokes_reference.py` exposes three routines for a positive dimension `k`, a
positive grid size `N`, and fixed coefficient/derivative callables:

- `volume_sum(g, N)` computes the left-grid sum of the diagonal derivatives.
- `boundary_sum(a, N)` computes the signed sum over the outer coordinate faces.
- `telescope_sum(a, N)` computes the sum of all coordinate increments.

The coefficients use the flux convention
`omega = sum_i (-1)^i a_i dx_0 ... omit dx_i ... dx_(k-1)`.
Consequently, `boundary_sum` uses `a_i(upper)-a_i(lower)` for each coordinate.
The separate `cubical_boundary` routine uses the ordinary oriented cubical
boundary signs and preserves the order of free coordinates.

The callable interface is a programming convenience for checking examples.
The arithmetic theorem in the report is a schema in fixed primitive-recursive
definitions; the interface does not supply a total primitive-recursive
evaluator for all primitive-recursive programs.

## What is checked

1. Exact `T = B` for 36 independently generated finite rational tables, covering
   dimensions 1 through 4 and grid sizes 1, 2, and 3. Randomness is confined to
   deterministic seeded test-data generation.
2. Every coefficient of the double cubical boundary is zero in dimensions
   2 through 6.
3. Exact polynomial pullback and curl calculations for
   `sigma(u,v)=(u,v,u*v)` and `F(x,y,z)=(0,x*z,x^2*y)`.
   The four oriented edge integrals are `0`, `1`, `-1/3`, `0`, and the surface
   integral is `2/3`.
4. Direct grid sums at `N=1,2,4,8,16,32` agree with the closed formulas for
   `V_N`, `B_N`, and `B_N-V_N`.
5. Polynomial coefficient comparisons prove the finite algebraic identities
   used in those formulas, including the recurrences for sums of first powers
   and squares. These comparisons do not rely on sampling a few input values.
6. Forty-eight noisy-evaluation examples check every local derivative estimate
   on the chosen grid, exact telescoping of the same rounded samples, and the
   total bound `k*2^(-t) + k*(2N+1)*2^(-p)`.
7. Nineteen precision schedules use `t=r+5`, `n=r+9`, `N=2^n`,
   `p=2r+16`. Large grids are **not enumerated**: their exact sums are obtained
   from the independently checked closed formulas. The report proves the
   schedule for every natural `r`; the program checks selected instances.

The main example has max-norm Lipschitz bounds `7,4,13,6` for
`a_1,a_2,g_1,g_2`, respectively, so the common continuity modulus is
`mu(t)=t+4`. Its two diagonal Taylor remainders are bounded by `4h^2` and
`h^2`, so `tau(t)=t+2` suffices. The polynomial identities behind these bounds
are checked by exact coefficient equality and printed in the report.

## Outputs

- `validation/exact_validation.json` records every case, exact rational
  quantities, the Python version, and hashes of the two source files.
- `validation/curved_grid_table.csv` gives the directly enumerated grid data.
- `validation/precision_schedule_table.csv` gives the large-schedule data and
  explicitly records that these grids were not enumerated.

Re-running the script replaces those three generated receipts. Source hashes
are intended to make a receipt's source version inspectable; they are not a
proof-checker certificate.
