# Adjacent-Pell quotient for an 80-row graph zero

`Direct80Adjacent.graph_adjacent` proves the following for the exact Lean 80-row graph in every IΣ₁ model with the repository's `ORingStructure` interface. For arbitrary natural ports with `beta>0`, every strictly positive ten-coordinate valuation whose graph output is internally zero yields `tau,f,V0,Z0,y` with `tau,f,V0,y>0`, and

* `E=tau²` and `1+a=f²`, where `a=delta*U²*E`;
* the difference-ring evaluations of the signed graph expressions `V` and `Z` have squares equal to the embeddings of `V0²` and `Z0²`, respectively;
* `Z0=(M*tau*f)*y`;
* `Q*V0²=1+(Q-1)*y²`, where `Q=delta*(4*a*(1+a))` and model subtraction is truncated.

The theorem does not assume a sign for `V` or `Z`, a reduced fraction, scale divisibility, or an integral quotient. It uses the previous exact-graph factor positivity and product-root theorem, derives `Q>1` and signed `V≠0`, represents both difference-ring squares by model elements, converts the zero equation to the scaled adjacent-Pell norm, and invokes the [model-internal integral quotient](../ten-positive-adjacent-integer-prototype/README.md) proved by gcd normalization and least-number descent. The root `y` is shown positive. The graph's `E`, `M`, `U` and `delta` are defined in the [80-row graph/factor packet](../ten-positive-80-model-binding-prototype/README.md); its JSON-to-Lean comparison remains external, not a Lean file theorem.

This completes this **necessary arithmetic phase**, not the full Diophantine reduction. It does not yet prove the later Pell folding, signed mask/rank decoding, graph-to-machine or reverse witness implication, fixed-payload calibration, or an internal iPRA derivation. It does not establish the semantics of a PDF or claim that a graph zero exists.

Guarded author `observations/attempt02/` exited 0 with no warnings or `sorryAx`; its printed Lean metatheory axiom report is `[propext, Classical.choice, Quot.sound]`. Source SHA-256 is `eeb49f9915fe29863bdaa17883bc8f78b7b991efa5e660c552c4f55714c19e72`, and object SHA-256 is `26d181ad42cacd5f8749e0d97fcfae90660b87601574745d48fd2f815f8c98ad`. Attempt 01 failed on model inequality and local-abbreviation rewrites and is retained with its source and errors.

The runner pins 12 preceding prototype objects, selected `ArithmeticGcdNormalization`, source, runner and Lean binary before and after. Other direct imports, the remaining selected 90-operation provider, package-transitive and dynamic dependencies, and complete historical source-to-object ancestry are inherited. Resource observations are point samples, temporary objects may disappear, and this is not a paired replay or independent audit.
