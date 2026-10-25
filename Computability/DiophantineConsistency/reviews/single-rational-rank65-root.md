# Root review of the single-rational rank evaluator

25 October 2026. I read the complete new proof and the complete change from
the previously read Laurent auditor. The new graph changes only the rank
tail, retains all other rows, and binds the whole complemented47 parent.
The fixed source MF is the once-shifted mask, not the native mask.

The identity is exact: with `q=beta*J+1`, `U=MF/beta`, `W=MC-MF`,

    (q²-1)*(G+U)+W*J = (q²-1)*G+(q*MF+MC)*J.

This holds in the Laurent polynomial ring before restricting witnesses.
The sole fractional computed register is `G+U`. Its product with `q²-1`
has integer coefficients because `q²-1=beta*J*(q+1)`. All later arithmetic
therefore stays integral on integer inputs. The fixed inequality
`beta<MF<2beta` proves that U itself is nonintegral. There is no hidden
division by a witness and no extra domain hypothesis.

The five rank gates have two products, two sums and one subtraction;
the full counts are37/15/13, total65. The earlier two-rational-leaf65
artifact used a different distribution of sums and differences. This
checkpoint simplifies rational intermediates and binds the newer tuple;
it does not lower65 to64 or establish an integer-leaf65 evaluator.

Root normal and optimized `audit.py --check` processes both exited0.
They check the full rank identity, unchanged prefix/suffix, the complete
323-term main-norm cancellation and56-term degree157 leader, all input
and gate liveness, all207214 raw coefficient bytes and four rejected
algebraic mutations. The proof and precise gate substitution justify the
whole-polynomial claim; sample evaluations are not used as a substitute.

The new graph is pointwise identical to its own complemented47 parent.
The ordinary consistency equivalence transfers with that parent's exact
calibration boundary. There is no new formal-kernel replay or global
minimality assertion. Raw bytes above measure the four original integer
ports, not a separate encoding of the derived rational constant.
