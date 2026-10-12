# Stieltjes product verification

From the bundle root:

```sh
python verification/stieltjes/code/verify_stieltjes_edge.py --mode exact
python verification/stieltjes/code/verify_stieltjes_edge.py --mode numeric
```

The script uses only paths relative to its own file. `code/` and `data/`
must remain sibling directories. The numerical suite takes longer because it
constructs high-order local expansions and an independent Stieltjes evaluator.

The exact suite constructs the local Gamma germ with formal ordinary-zeta
derivatives. It checks all 81 integration-by-parts identities for indices
between zero and two, plus four printed specializations. The exported table
includes the second-Stieltjes-index identity even though it is not one of
those four additional assertions.

The numerical left sides use local Laurent/logarithmic integration and
ordinary Gauss–Legendre quadrature. They do not call the completed product
kernel. Five products are checked at a splitting point of 1/8; a sixth
comparison repeats the first at 1/5. Four independent mpmath comparisons
check the stable argument-two Taylor evaluator. Working precision is 55
decimal digits. The five primary residuals are at most 3.972e−52; the second
splitting-point residual is 1.250e−46. None is an interval certificate.

`data/edge_exact.json` and `data/edge_numeric.json` are the actual successful
run records. The article fixes the finite-part coordinate and proves normal
local subtraction before differentiating parameters.
