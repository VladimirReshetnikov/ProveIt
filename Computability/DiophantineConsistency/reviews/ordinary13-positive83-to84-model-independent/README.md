# Independent review: positive 83↔84 conditional graph transport

The author receipt and the independent check reproduce for the pinned bytes.
The source is unelaborated; no Lean build, axiom/provider replay, positive
calibration cut or endpoint theorem is certified here.

The graphs use the same coordinates except 83's positive w is replaced by
84's positive X at position 6. Their q, Y and U agree after X=q*w. The 84
main shift adds `X*Y*q`; the 83 graph omits this term. Under the stated
coordinate relation and `gamma83=gamma84+w`,
`U*gamma84+X*Y*q=U*gamma83` because U=Y*q². All other graph rows agree as
authenticated by the author's exact row checker, so its formal polynomial
identity applies to the complete output. Our checker independently tests both
positive coordinate maps over 640 entire-graph evaluations; these are controls,
not a general model proof.

The 83→84 map uses X=q*w and gamma84=gamma83−w. Its strict hypothesis
w<gamma83 makes the model-natural truncated difference positive and allows
the claimed roundtrip. The 84→83 map explicitly requires q|X, chooses a
model-natural quotient w, and positivity of X entails w>0; it replaces
gamma by gamma+w. The equality-based map is sound when the stated q and
quotient equation hold. Mere positivity of X does not provide q|X.

`GammaCalibration` specifies one shared R, W, d for the natural rank bound,
the y- and x-coordinate Pell recurrence at that same R, k decomposition,
and subtraction-free main balance. Its arguments align with the inspected
`ModifiedCarrierGammaDraft.gamma_gt_from_modified_balance` source: q≥1,
Y>0 and U>0 give w≤X≤a; the same-index Pell bounds then yield w<gamma.
This transport packet assumes the graph supplies that calibration rather
than deriving it; its separate `GammaCut` and `DivCut` remain assumptions
of `sameNoZero` and `bridge83`. The optional native client also retains the
independent 81↔83 `CrossRootCut` and the exact 84 parent
`PolynomialBridge`. Subsequent source drafts may propose those obligations,
but they are not discharged or Lean-checked by this packet.

The two no-zero directions use the correct witness-map orientation and
positive-shift predecessor, conditional on their respective cuts. No
concrete arithmetic or premise-direction mismatch was found. Compilation,
provider coherence, axiom reports, fixed-port/file semantics and the selected
external consistency encoding require separate validation.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-positive83-to84-model-independent/check.py | cmp - reviews/ordinary13-positive83-to84-model-independent/receipt.json
```
