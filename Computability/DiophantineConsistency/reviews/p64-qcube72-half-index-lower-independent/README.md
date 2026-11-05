# Independent review of the generic half-index lower bound

**PASS within recorded direct-provider scope.** The no-Lean `check.py`
checks the successful attempt04 retained and terminal receipts/logs, source,
runner, helper, output object, and all recorded direct guards. The two
direct project inputs, `ArithmeticAdaptiveIndexComparison2011` and
`ArithmeticPellCommonUnit`, are pinned captured objects whose full
source-to-object and transitive ancestry is not independently rebuilt here.
The axiom report contains only `propext`, `Classical.choice`, and
`Quot.sound`. This is not a Lean replay; dynamic and between-sample ancestry
remains inherited.

For elements `X,Y,eta,zeta,n,m` of an `IΣ₁` model, the theorem assumes
`zeta>0`, `2*ycoord n (2*(X*Y*Y−1)+1)=eta+zeta`, and
`ycoord m (X*Y+Y)=(eta+zeta)*Y+eta`. It concludes `m<2n`. Subtraction is
the model's natural truncated subtraction. No extra positivity premise on
`X`, `Y` or `eta` is stated.

The proof sets `a=XY+Y` and `A2=2a²+8a+5`, verifies
`A2+2=xcoord 2 a` and `ycoord 2 a=2(a+2)`, and applies the captured Pell
composition identity to get
`ycoord n A2 * 2(a+2) = ycoord (2n) a`. Monotonicity in the base bounds the
first recurrence by that doubled-index recurrence. The first-coordinate
equation and `zeta>0` then give
`ycoord m a < (Y+1)(eta+zeta) ≤ ycoord (2n) a`; strict monotonicity in the
index yields the conclusion.

This generic result does not itself extract the indices from a graph zero,
prove the main index is the graph rank, derive the first-index congruence or
equality `2n=R+1`, construct a reverse witness, or establish an iPRA endpoint.
The “Unchecked draft” source header predates the successful attempt04 and is
retained byte-for-byte.

Run while captured temporary paths remain available:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/p64-qcube72-half-index-lower-independent/check.py
```
