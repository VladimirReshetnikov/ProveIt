# Independent review of the unsquared-carrier probe

The pinned probe has exactly the claimed one-row deletion and operand redirection, and the stated natural assignment makes its output zero while the original 61-operation output is positive. No concrete error was found. This is a pointwise counterexample to the direct residual replacement, not a proof that the two graphs have different existential zero status or that the probe behaves similarly at the compact ports.

Independently evaluating every literal row at the stated ports and inputs gives `Bres=-N`, `firstres=3`, and `A1=-201471201792`, where

```text
N = 3² + 201471201792² = 40590645151512784011273.
```

The probe computes `-N+N=0`; the original computes `N²+N`, namely

```text
1647600473816028280482680991661814740975091802 > 0.
```

All graph inputs are natural. The checked values also satisfy the listed positive-port and mask inequalities, `C>0`, `X>0`, `k>q`, and the stated interval `2≤tau-ell≤k-2` (both sides equal 2 at this assignment). These checks do not make the first or main norm residuals zero: here they are 3 and `-201471201792` respectively.

The independent checker pins the 61 graph and probe, reconstructs the edit, verifies topology and liveness for both graphs, evaluates every row directly at the published inputs, compares all shared node values and checks the exact outputs and inequalities. It does not search for other witness maps or prove a general lower bound on equation size.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary10-divisible61-unsquared-carrier-independent/check.py | cmp - reviews/ordinary10-divisible61-unsquared-carrier-independent/receipt.json
```

No Lean, build, staging, provider or model validation was run.
