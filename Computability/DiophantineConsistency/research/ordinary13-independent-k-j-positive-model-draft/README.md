# Proposed J positivity for the independent-k child

`IndependentKJPositive.lean.src` is a source-only adaptation of the prior eta/zeta-natural J-positivity draft to the [exact independent-k child literal](../ordinary13-independent-k-unit-norm-draft/README.md). Its proposed theorem takes an actual `InternalZero` of that child expression and a tuple `p : Fin 4 → ℕ`, and concludes `0<v 0`. The natural tuple hypothesis represents **all four ports** as naturals; the proof uses only nonnegativity of its second port K0, and assumes no positive beta, no lower bound on K0, and no condition on k, eta, X, or the other witness slots. It does not claim a theorem for arbitrary signed ports.

At J=0, the exact graph has b=0, q=1, X=v6, and

```
Z = F − (1−F−alpha)(X+K0),  F=v1+1, alpha=v2+1.
```

The natural witnesses and K0 make the product nonpositive and F positive, so Z>0. The proposed child's `signed_norms` gives `Z²=b²*(...)`, hence Z²=0 at J=0, a contradiction. The copied source uses the explicit natural-port cast theorem `P72Root.cast_port` and the newly generated child unit/norm bridge; those provider and cast applications are unelaborated. In particular, no source-level inference is made from the parent literal's theorem to the different child literal.

The checker reproduces the child unit-bridge receipt, checks the exact import/namespace adaptation and theorem signatures, and verifies the J=0 root identity as an integer polynomial over **distinct** symbolic child inputs and ports. It also checks 500 exact finite graph valuations. This confirms the transcription and conditional arithmetic, not Lean elaboration, arbitrary-model factor extraction, provider selection, an axiom report, a zero map, or an iPRA endpoint. All four source port casts and `InternalZero` / `signed_norms` applications remain subject to coherent compilation.

From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B research/ordinary13-independent-k-j-positive-model-draft/check.py | cmp - research/ordinary13-independent-k-j-positive-model-draft/receipt.json
```
