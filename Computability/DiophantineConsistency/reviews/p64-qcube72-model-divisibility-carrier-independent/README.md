# Independent review of model divisibility, carrier scale and graph shape

The retained source, direct guards, objects, complete logs and four receipts were reviewed read-only. Lean was **not** rerun. The [checker](check.py) compares each before/after guard and current direct path, authenticates runner/helper and copied receipt hashes, and checks the dependency links from generic divisibility to carrier scale and from the previously checked 72 graph to graph shape. Captured project/package transitive and dynamic ancestry and between-sample changes remain outside this review.

The successful generic theorem `dvd_of_cube_dvd_three` assumes only `q³ | 3h` for elements of a model of `IΣ₁` and concludes `q | h`; its source separates the three residues of `q mod 3` and uses explicit unit certificates or cancellation. `scale_dvd_carrier` separately requires `U>0` and `D²=U²N`, then concludes `U | D`. Both recorded reports list only `propext`, `Classical.choice`, and `Quot.sound`.

`FreeMainCarrierScale.of_carrier` is a further checked implication for model elements under **explicit** hypotheses: `q>0`, `U>0`, `Y=q³s`, `U=Y²`, `H=3+4(XY+Y)`, `D=Ub+Hh`, and `D²=U²N`. It concludes `q | h` by first deriving `U | D` and then `q³ | 3h`. These are not yet extracted from an actual 72-graph zero by a checked client. Its recorded report has the same three Lean metatheory axioms.

The checked `FreeMainGraphShape.output_shape` is an expression identity for the 72 graph; `M_eval` is an evaluation identity over arbitrary commutative rings. Each reports `[propext]`. Neither supplies the missing model graph-zero client on its own.

The first graph-client check, `graph01`, failed with Lean exit −6 and an interpreter memory exception at the configured `-M2400` limit. Its captured log contains no axiom report and it produced no object. The current rewritten graph-client source differs from that retained failed source and has **not** been checked; the review checker verifies that distinction. Therefore there is no checked actual-72-zero `q | h` theorem in these receipts. No reverse witness map, positive-zero equivalence or iPRA endpoint follows.

Read-only reproduction while the referenced `/tmp` objects and logs remain available:

```
python3 -I -S -B path/to/p64-qcube72-model-divisibility-carrier-independent/check.py
```

The deterministic review result is frozen in `result.json`.
