# Dominated exploratory correction: 13 inputs, 112 operations, degree 90

This records a finite algebraic observation, not a new accepted iPRA endpoint. It is dominated in both operation count and degree by the independently audited 13/87/36 candidate, so the 112/90 graph is not a preferred reduction.

Starting with the exact 84-row corrected-sphere graph, write `U84` for its `correctedU`, `P` for its first norm, and let `b`, `q`, `C`, `kY`, `f²` and the other symbols have their original graph meanings. Define

```
A2 = 16 (kY q⁴ w) f⁴ T³ (C−1)²
     (b k T s w − 2 k f² T s + 2 b f² w (q−F−1))
U90 = U84 + A2 (P−1)
(P Q)² + U90² + Z² − 3 = 0.
```

`polynomial.json` specifies all 112 binary operations, reusing every original row except replacing the input to `sqU`, and binds the same four materialized current-2011 ports. Its 72 multiplications, 20 additions and 20 subtractions include the final constant subtraction and count positive-input graph syntax. `check_degree.py` checks this parent-row relation and liveness, propagates exact top homogeneous layers, proves an upper bound 90 after checking the new degree-46 cancellation, and verifies the actual full-port diagonal has coefficient `24134822` at `t^90` modulo `1000000007`. Thus its finite calculation establishes exact degree 90 for this fixed tuple, subject to independent review; `degree-receipt.json` records the output. Flipping the new correction sign restores degree 92, while dropping its square lowers the tested degree. The checker is adapted from the independently reviewed 84-row degree audit and checks the same captured port payloads and source pins.

The intended no-zero argument is to use the existing `ModelThirteenSquares.correction_zero_iff` with correction coefficient `−A2`: the relevant square-sum zero forces `P=1`, so the added term vanishes. This transport for the new graph, its positive-shift binding, and its iPRA sentence have **not** been proved or replayed in Lean. No conclusion about global minimality follows. The degree calculation was run with:

```
python3 -I -S Computability/DiophantineConsistency/research/thirteen-second-norm-correction90/check_degree.py
```
