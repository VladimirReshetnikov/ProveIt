# Finite mixed-mask list and model transfer

The source defines a standard finite list of radix-B digits: the distinguished
slot has value B−4, the other members of a standard finite support have B−2,
and all remaining slots have B−1. For any B ≥ 4, Lean proves a symbolic
identity: `ofDigits B digits + weightedDefects + 1 = B^length`, where the
unexpanded weighted defect is 3 at the distinguished slot, 1 at other support
positions and 0 elsewhere. This proof works for arbitrary support and length;
it does not evaluate the large numeral.

For B=2^67, `ArithmeticMaskConstants.dig_ofDigits` and standard-index transfer
show in every model of IΣ₁ that each digit of the cast list-value below the
standard length belongs to the expected three classes and that the value is
below its word radix. If the length is positive, the distinguished slot is not
zero, and zero belongs to the support, the origin digit is `2^67−2`.

These are standard-list and model-level theorems. The source does not yet
specialize the actual 986-slot support, prove that its weighted defect is the
retained MC recipe, identify the retained MC payload or graph ports, simulate a
machine, or construct a PRA proof. The checked external recipe is separately
recorded in `compact44-selector-recipe-check`; its byte/hash checks do not
prove the required Lean equality.

The first exploratory check (session 63140, exit 1) lacked a geometric-series
import; the second (session 96597, exit 0) supplied the elementary finite
induction. The initial model-transfer check (session 5492, exit 1) failed on
cast subtraction; session 11520 exited 0 after using the established
cast-and-cancel argument. Session 32128 exited 1 because simplification
expanded the origin numeral; session 63420 exited 0 after using restricted
simplification. Failed source versions and all logs are retained.

The paired replay uses the independently audited 342-module endpoint
successor, checks direct imports, source hashes, matched objects and axiom
reports, and reruns its read-only audit before and after. The provider audit
does not authenticate full package-transitive or dynamic ancestry; sampled
resource monitoring is not a hard process-tree quota.
