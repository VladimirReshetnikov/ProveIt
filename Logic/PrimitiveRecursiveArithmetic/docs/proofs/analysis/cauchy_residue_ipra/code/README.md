# Exact finite reference calculations

Run with Python 3.10 or newer; the standard library is sufficient:

```sh
python3 run_validation.py
```

The runner executes seven focused validation tests and writes
`validation_results.json`. All comparisons in the tests use exact integers and
`fractions.Fraction`. Decimal fields in the JSON are display aids only.

The code checks oriented midpoint-subdivision cancellation, complex-affine
boundary cancellation, every sampled uniform-differentiability inequality for
the polynomial example, and the resulting finite Cauchy estimate. It constructs
a 26-triangle grid filling of a rectangle with two square holes and verifies its
boundary equals the outer cycle minus the two positively oriented hole cycles.

The numerical example is `f(z)=1/z+2/(z-1)`. Each exact rational sample is rounded
to 32 binary fractional places, with taxicab error at most `2^-32`. Quadrature
errors include both this evaluation error and a conservative explicit
derivative-Lipschitz interpolation error. The latter is proved directly using
the exact rational identity
`(1-t)/u+t/v-1/((1-t)*u+t*v) = t*(1-t)*(v-u)^2/(u*v*((1-t)*u+t*v))`
and finite sums of squares. The identity is checked on reproducible randomly
generated rational samples, in addition to the other exact checks. The
bound is `K*sum(edge_length^3)/(12*4^depth)`, where
`K=2*sum(abs(residue)*(2/clearance)^3)`. The expected imaginary values are enclosed using
a rational interval for pi from a finite geometric series. The positive
recurrence used to evaluate that series is cross-checked against its finite
binomial expansion.

These computations validate concrete finite identities and examples. They are
neither a Lean formalization nor a proof of the universally quantified analytic
or iPRA metatheorems in the accompanying paper. The source mirrors the finite
algorithms, but it is not an implementation or size benchmark of an iPRA proof
checker.
