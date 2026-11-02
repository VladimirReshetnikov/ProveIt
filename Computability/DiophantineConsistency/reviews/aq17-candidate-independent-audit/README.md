# Independent finite audit of the AQ17 candidate

This audit checks the 17-variable candidate against the pinned AQ22 circuit.
Both the [independent checker](audit.py) and the author's separate candidate
verifier exited zero; their observed exits are recorded in
[terminal-observation.json](terminal-observation.json). This audit does not
rerun the survey of all 31 subsets or verify its family-wide minima.

The checker validates all 99 child arithmetic rows, input names, topology,
liveness, and the output sum of eight squares. It independently builds
expression trees for the parent after simultaneous substitution and for the
child. All eight retained residual trees agree, and the five deleted binding
residuals have identical left and right trees. It verifies the five substituted
expressions depend only on surviving inputs and have the claimed positive
form when all 17 witnesses and beta are positive. Hence projection and positive
reconstruction preserve the existence of zeros in ordinary integer algebra.
Two numerical reconstructions exercise all residual identities; the argument
itself does not rely on those examples.

A separate sparse polynomial representation confirms maximum residual degree
16 and identifies the coefficient of the witness monomial
`J^8 X^2 Y^4 eta^2` in `A0` as exactly `-beta^8`, with no other fixed-port
monomials contributing. The checker decompresses the recorded actual beta,
checks it against the earlier independent AQ22 port binding, and confirms it
is positive; it computes the exact specialized coefficient's magnitude and
hash. The leading homogeneous sum of squares cannot cancel over the reals, so
the specialized equation has degree exactly 32. The same is true after the
positive-variable shift. Arithmetic-row, output-sign and replacement
mutations are rejected, as are zero witness or beta premises.

This is a finite external algebraic audit, **not a Lean proof of AQ17
transport or an internal iPRA theorem**. It makes no claim that AQ17 appears
in a PDF or is globally minimal. Its connection to the displayed AQ22 fixed
ports inherits the manually transcribed decoder, tile table, rank and port
recipe boundary recorded in the earlier historical PDF binding. The original
historical AQ22 Lean endpoint remains author-only, with the documented
provider and replay limitations.

Run with ordinary Python after moving only this packet's receipt aside:

```sh
python3 Computability/DiophantineConsistency/reviews/aq17-candidate-independent-audit/audit.py
```

The checker refuses to overwrite its receipt and rejects optimized Python.
