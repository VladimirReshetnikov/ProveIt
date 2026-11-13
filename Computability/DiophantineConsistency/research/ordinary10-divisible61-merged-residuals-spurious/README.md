# Merging the carrier and first residual allows exact cancellation

One tempting local encoding replaces the literal 61-operation sum of three
squares by

\[
(B_{res}+F_{res})^2+A_1^2.
\]

The associated 60-row `probe.json` is **invalid**, not a proved gate saving:
it has an exact natural zero at which the original graph is positive. Unlike
an obstacle based on ignoring the main norm, the counterexample below retains
\(A_1=0\) exactly and uses positive beta and K0, with the original mask
bounds. It does not prove an existential inequivalence or exclude other
witness transformations or circuit encodings.

## A general cancellation map

Let an original 61-graph zero have \(b=\beta J>0\), natural carrier
quotient h and normalized first root tau. Keep all other inputs fixed and set

\[
\tau'=\tau+b,\qquad h'=h+2\tau+b.
\]

Both new inputs are natural. Since the old carrier and first residuals are
zero, the actual new residuals are

\[
B'_{res}=-b(2\tau+b),\qquad F'_{res}=b(2\tau+b).
\]

They are nonzero and opposite. The main residual does not depend on h or
tau, so it remains zero. Hence the merged probe is zero at the new tuple,
while the original sum of three squares is strictly positive there. This is
a pointwise construction conditional on an original zero; it does not say
whether any original zero exists at the fixed compact ports.

## An exact positive-port instance

The [independently reviewed q=4 witness](../../reviews/ordinary9-even-index-q4-full-zero-independent/README.md)
is an actual original 61-graph zero at noncompact ports
\((\beta,K_0,MC,MF)=(3,1,1,1)\), with J=1 and b=3. The checker
independently reconstructs its finite Pell witnesses by binary powering,
including the actual main index 84 and gamma. Applying the displayed map
gives an explicit natural zero of the invalid probe with
\(B'_{res}+F'_{res}=0\), \(A_1=0\), and positive original output.
The ports satisfy beta>0, K0>0, MC<beta and MF<2beta; at the new tuple
C>0, X>0 and k>q also hold. No large decimal Pell witness is printed.

The literal probe removes `Bsq` and `firstsq`, forms their **signed** sum,
squares that sum, and retains `A1sq`; all 60 rows remain live. Its row count
is not an unconditional simplification. The checker pins the original graph
and reviewed witness, verifies the exact edits, reconstructs and evaluates all
rows of both graphs before and after the transformation, and proves the two
residuals are nonzero opposites. No Lean, build, staging, model provider,
original-parent reverse bridge or iPRA result is involved.

```sh
timeout 15s python3 -I -S -B research/ordinary10-divisible61-merged-residuals-spurious/check.py | cmp - research/ordinary10-divisible61-merged-residuals-spurious/receipt.json
```
