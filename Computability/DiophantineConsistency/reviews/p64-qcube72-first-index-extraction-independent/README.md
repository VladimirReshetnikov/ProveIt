# Independent review of the actual-zero first-index extraction

**PASS within recorded direct-provider scope.** The no-Lean `check.py`
verifies the successful attempt01 retained and terminal receipts and logs,
source, runner, helper, output object, all recorded direct guards, and the
residual input against its successful producer receipt. The other direct
input, `ArithmeticPellFirstNorm`, is a pinned captured object; its complete
source-to-object and transitive ancestry is not reconstructed here. The
axiom report contains only `propext`, `Classical.choice`, and `Quot.sound`.
This is not a Lean replay; transitive, dynamic and between-sample ancestry
remains inherited.

In an `IΣ₁` model, for arbitrary natural ports and an actual positive
72-graph zero, the theorem defines `q=p₀v₀+1`, `Y=q³v₇`, `X=v₈q`,
`P=XY²` and `k=v₁₀+v₁₁`, and concludes that some model element `n≤k`
satisfies `xcoord n (2(P−1)+1)=v₉` and
`2*ycoord n (2(P−1)+1)=k`. Subtraction is model-natural truncated
subtraction. The proof extracts the first residual, derives the natural
norm `v₉²=1+P(P+1)k²` in the model, shows `P>0`, and invokes the captured
first-norm classification. No compact-mask or old-carrier assumption is
included.

This theorem does not itself compare `n` to the main Pell index, prove that
index equals the graph rank, derive the first-index congruence, construct a
reverse witness, or establish an iPRA endpoint. The source header calling it
an unchecked draft predates the successful attempt and is retained unchanged.

Run while the captured temporary paths remain present:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/p64-qcube72-first-index-extraction-independent/check.py
```
