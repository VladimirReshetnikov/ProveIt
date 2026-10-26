# Lean degree bounds for the counted H2082 polynomials

`GapPolynomialDegree66` proves total degree at most **1,845,940** for
the actual 443-operation positive polynomial, the 450-operation natural
polynomial, and both corresponding source-polynomial recipes. The circuit
bounds hold for every integer assignment to all eleven fixed leaves. The
source-recipe bounds therefore hold for every four-port tuple and half-height,
without assuming native calibration or a root.

The generic `ArithmeticDAGDegree` module checks a local degree inequality
at every stored node and proves it bounds the actual evaluator. The generated
`GapCircuitDegree66` supplies 484 labels for the pinned natural DAG; Lean's
kernel checks the entire finite certificate. Affine polynomial inputs are
allowed. The positive bound then follows from the checked translation
`positiveValue p x = naturalValue p (x-1)`.

The initial labels give the weaker output bound 2,063,116. Two cancellations
are needed. With the actual tail registers, the checked Pell identity is

```text
D*F = k^2*D^3*(D-1)+D,
I = (G^2-1)*H^2+1.
```

Consequently the defect of the majorant `V1=k*(8*D^2-4*D-1)*G*H` is

```text
V1^2-64*D*F*I
  = (k^2*(8*D+1)-64*D)*G^2*H^2 + 64*D*F*(H^2-1).
```

Its degree is at most 741,530. Recenter the finalizer at
`theta=E0-omega*(P*K+V1)`. Its inner expression becomes

```text
E0^2 - 2*E0*omega*(P*K+V1)
  + omega^2*(K^2-1+2*P*K*V1+(V1^2-64*a1)).
```

Its degree is at most 922,970; squaring gives 1,845,940. The other term
in the norm has a smaller bound. `FreeCarrierDegree` proves these generic
identities and bounds using supplied small weighted expression syntax;
`GapFinalizerDegree66` applies them to the literal circuit registers.

These are upper bounds. Exact degree and the nonzero leading coefficient
remain established by the separate finite candidate audit, not by the Lean
degree theorem. A regression check exhibits a cancelling circuit whose
certified label strictly exceeds its actual degree, and rejects invalid
labels for the H2082 circuit. The dedicated audit covers all generic and
applied degree theorems and uses only the standard Lean axioms.

Reproduce the generated labels with
`python3 tools/generate_gap_degree66.py --check` from this directory.
These proofs do not close native source calibration or the internal ZFC
biconditional.
