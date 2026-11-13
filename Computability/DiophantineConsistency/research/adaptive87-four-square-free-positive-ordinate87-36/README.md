# Positive-ordinate candidate: 13 variables, 87 operations, degree 36

**Identification:** This circuit is the existing
[`adaptive-square-sums` graph](../adaptive-square-sums/candidate.json),
presented in [`equation36.pdf`](../../equation36.pdf), after renaming its
ordinate input and final gates. It is not a new equation. A historical
[matched iPRA endpoint replay](../../reviews/ipra-frontier13-historical-pair-independent-audit/README.md)
has its own source-snapshot, provider, and document-binding qualifications.
The argument below is an alternative ordinary-integer witness proof, not a
new internal proof.

This is a **standard-integer zero-equivalence result**, not a checked Lean, all-model, iPRA, or Con(ZFC) theorem. The literal [graph](graph.json) is an operation/degree tradeoff relative to the current2011 [13/88/30 four-square parent](../adaptive87-four-square-current88-30/README.md): it uses 87 live operations and exact degree 36. It uses the same four fixed ports and thirteen strictly positive integer inputs. It replaces the old positive difference input `u` by a positive ordinate input `auxPositive`, deletes the row `g78 = V+u`, and sets `y2 = auxPositive*auxPositive`. Every other graph row is unchanged. In particular, the zero equation stays normalized as `output = 0`.

The mathematical maps below apply to **any integer values** of `K0`, `MC`, and `MF`, and any integer `beta >= 0`; each witness is strictly positive. Thus `q=1+beta*J >= 1`, and `U=Y*q² > 0`. For the actual current2011 tuple, the checker authenticates all four full binary port payloads and checks that the encoded natural `beta` is positive. No special rank, mask, or remaining fixed-port assumption is used in these maps.

## Common zero consequences

The parent and child outputs are sums of the squares of `A0`, `A1`, `Fa−1`, and `g72`. At either zero, all four vanish. Let

```
a = Y*(X+1),  B = a+2,  Delta = B²−1,
k = eta+zeta,  c = eta+Y*k,  I = c²*i,
Q = Delta*(f²−1),  V = f²*(T*c−R)−c.
```

Strict positivity gives `a >= 2`, `B >= 4`, `c >= 3`, and `I >= c² >= 9`. The strong residual `g72=0` gives `Q=I²`. The main residual `A1=0` is the exact graph identity

```
Dstar² = U²*(1+Delta*c²).
```

Since `U > 0`, the elementary integer square-divisibility fact `U² | Dstar² => U | Dstar` gives an integer `t` with

```
t² = 1+(B²−1)*c².
```

The next bound follows directly from the gap between consecutive integer squares. If `2 <= c < 2*B`, then

```
(B*c−1)² < 1+(B²−1)*c² < (B*c)²:
```

the two differences are respectively `c*(2*B−c)>0` and `c²−1>0`. No integer square lies strictly between those consecutive squares. As `c >= 3`, necessarily **`c >= 2*B`**, hence `Delta = B²−1 < c²`.

At a zero, `V=1` is impossible. It would give `f²*(T*c−R)=c+1`. Here `f >= 1` and `c+1 > 0`, so the integer quotient `T*c−R` is positive and `f² <= c+1`; hence `f²−1 <= c`. Using `Delta < c²` and `Q=I²` then yields

```
I² = Delta*(f²−1) <= Delta*c < c³ <= c⁴ <= I²,
```

where the last inequality uses `i >= 1`. This contradiction uses no sign assumption on `R` or `T*c−R` beyond the one derived from the displayed equality.

## Child zero to parent zero

Write the child's positive ordinate as `y=auxPositive`. The auxiliary residual `Fa=1` and `Q=I²` give

```
(I²−1)*(y²−V²) = V²−1.
```

We claim `y > V`. If `V<0` this is immediate from `y>0`; if `V=0` the displayed equation has a nonnegative left side and right side `−1`; and `V=1` was excluded above. If `V>=2`, the right side is strictly positive, so `y²>V²` and therefore `y>V` as both are positive. Thus the parent input `u_parent=y−V` is a strictly positive integer. Retain all other coordinates and ports. The old ordinate is exactly `V+u_parent=y`, so the four residuals and the entire output agree.

## Parent zero to child zero

Let the old ordinate be `y_old=V+u_parent`. It cannot vanish: otherwise `Fa=1` and `Q=I²` would give `I²*V²=1`, impossible for integer `V` and `I>=9`. Set `auxPositive=|y_old|`; it is strictly positive. Retain all other coordinates and ports. Since the graph uses the ordinate only through its square, the child and parent outputs agree exactly.

These maps prove equivalence of **existence** of positive-integer zeros for the two pinned graphs, and their zero-free statements, under the stated port assumptions. The maps change one witness and do not assert equality at a fixed identical valuation. They inherit the parent graph's external relation to its own predecessor. They do **not** establish the desired equivalence inside iPRA: transporting the quotient, square gap, ordered bounds, absolute-value representation, and exact evaluator bindings to every intended IΣ₁ model, and checking the resulting Lean and provider chain, remain open.

## Degree and reproducibility

The checker verifies the literal one-row deletion/rebinding, all 87 row topological dependencies, all 13 witness and four port leaves, and output liveness. Its syntactic degree propagation proves an upper bound of 36. At the actual current2011 ports, the diagonal substitution of the same indeterminate for all thirteen witnesses gives degree 36 and nonzero leading coefficient `57192905` modulo `1000000007`, proving the exact specialized integer-polynomial degree is 36. Operation counts are 48 multiplications, 21 additions and 18 subtractions. Compared with the 88/30 parent, replacing `(V+u)²−V²` by `auxPositive²−V²` loses the leading cancellation, which accounts for the degree increase.

Run from the DiophantineConsistency directory:

```sh
python3 research/adaptive87-four-square-free-positive-ordinate87-36/check.py > /tmp/adaptive87-ordinate-current.json
cmp research/adaptive87-four-square-free-positive-ordinate87-36/result.json /tmp/adaptive87-ordinate-current.json
```

The small deterministic witness-substitution controls in the receipt check evaluator wiring only; they do not prove either zero implication. The proof above supplies the ordinary integer argument. The checker runs no Lean/build and leaves parent evidence unchanged.
