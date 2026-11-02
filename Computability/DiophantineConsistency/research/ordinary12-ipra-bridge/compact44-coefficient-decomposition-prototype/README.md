# Exploratory finite selector/copy coefficient decomposition

For any IΣ₁ model `V`, the source proves that each natural payload and selector coefficient of the actual 943-row Lean table casts to the corresponding model payload and `1 + 2^10*(2^41−payload)`. It then proves for arbitrary functions `f : Fin 943 → V` and `b : Fin 41 → V` the identity

```
Σ_i selector_i*f_i + Σ_j 2^(10+j)*b_j
  = Σ_i f_i + 2^10*(Σ_i (2^41−payload_i)*f_i + Σ_j 2^j*b_j).
```

The finite sums and indices are external Lean data; the powers and arithmetic in the displayed identity are model-valued. The proof does not evaluate K or any huge integer. It assumes neither Boolean inputs nor NoCarry and does not itself identify this finite weighted sum with a graph column. Applying the existing decoder still needs Boolean selector/copy bounds, the copy word's `< 2^41` bound, and the appropriate local NoCarry premise. No claim is made that the dummy at 1063 is Boolean. Binding the symbolic K and the retained decimal/byte port, handling reflected shifts and collisions, deriving the graph column equation, machine semantics and an internal iPRA theorem remain open.

Successful single-side session 65789 actually exited 0, without warnings or `sorryAx`; its three declarations report `[propext, Classical.choice, Quot.sound]`. Failed sessions 60394, 17566 and 17701 and their exact source/log diagnostics are retained; their `sorryAx` reports are failures, not theorems. They respectively exposed cast/sum elaboration, numeral-cast normalization, and a missing import for `Finset.sum_mul`. The successful retry imports the already-present `ArithmeticWindowCarry` object.

The exploratory overlay copies the paired decoder and coefficient-mass objects over the author decoder provider; 115 shared parent `.olean` paths matched hashes at one point in time. This observation does not establish a fresh coherent paired build or full package/transitive/dynamic provenance. A source-frozen same-provider closure, paired replay, and independent artifact audit are still needed. `terminal-observation.json` records the exact source, outputs, invocation and provider object hashes.
