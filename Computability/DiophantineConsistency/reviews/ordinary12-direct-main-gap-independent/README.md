# Independent review of the conditional direct-gap lemma and draft degree

`DirectMainGapBalance.gap_of_balance` is a **conditional** statement in every
model of IΣ₁. For model elements `U,X,a,c,H,G,R,k,main,w`, it assumes

* `0 < U` and `R+1 ≤ k`;
* `U*(X+a*c)+H*(U*G+R+1) = H*k+U*main`;
* `(a+1)*c < main`; and
* `X+H*w < c`.

Its conclusion is `w<G`. The proof uses nonnegativity of the model element
`H`, cancellation by the positive `U`, and ordered multiplication. It does
not take a graph zero as a hypothesis or establish the explicit growth bound
from one. The checked statement is model-level; Lean's reported metatheory
axioms are not axioms added to iPRA.

The checker also records an abstract natural-number counterexample to
dropping the growth assumption: `(U,X,a,c,H,G,R,k,main,w) =
(1,2,1,1,7,1,1,2,10,2)` meets the other displayed assumptions and has
`w ≥ G`. This is **not** claimed to be a zero of the candidate graph.

The first recorded author attempt exited nonzero with an error and `sorryAx`;
the second Lean invocation exited zero but emitted an unused-parameter
warning, so its runner rejected it. The third exited zero with no warnings
or `sorryAx` and reports `[propext, Classical.choice, Quot.sound]`.
`check.py` verifies the pinned source, all three source/log/receipt hashes,
the Lean binary, the accepted object and exact imported projection object.
It rehashes all 1,291 selected union paths before and after re-running the
earlier independent projection/norm review. The accepted preflight observed
one existing Lean process; both recorded execution samples observed two.
Sampling cannot rule out shorter overlaps or resource changes. No new Lean
process is launched by this review.

## External exact-degree check

Independently, `degree.py` checks the pinned 90-row shared DAG and its four
hash-pinned fixed coefficient payloads. All 90 operations are live: 50
multiplications, 23 additions, and 17 subtractions. Sparse integer polynomial
arithmetic verifies the exact cancellation
`h=(V+n)²−1−Q*n*(2V+n)`. Degree propagation then gives `deg Q≤14`,
`deg V≤8`, `deg h≤23`, `deg N≤86`, and `deg P12≤172`. Substituting witness
number `i` by `(i+2)*t` and evaluating fixed coefficients modulo
1,000,000,007 yields degree 172 with nonzero leading coefficient 960910299.
Thus the fixed-coefficient integer polynomial has **exact degree 172**.
These are external graph and arithmetic checks, not Lean file, polynomial
degree, PDF, graph-soundness, or iPRA theorems. The operation count is for
positive-coordinate evaluation, before any separate `x+1` substitution.

Run the read-only checks from any working directory:

```sh
python3 -I -S -B check.py
python3 -I -S -B degree.py
```

Their captured exit-zero outputs and input hashes are under
[`observations/attempt01`](observations/attempt01/). The artifact review
requires the recorded `/tmp` provider objects to remain available. It checks
the selected union and earlier receipts, not complete historical
source-to-object, package-transitive, dynamic-loading or continuous-resource
ancestry. Neither the conditional lemma nor the exact degree establishes the
90-operation graph's reverse existence implication, machine-halt
equivalence, or an internal iPRA proof.
