# Independent review of generic three-divisibility obstruction

**PASS within recorded direct-provider scope.** The no-Lean `check.py`
checks successful attempt02 retained and terminal receipts/logs, source,
runner, helper, object, all recorded direct guards, and the captured
`ArithmeticPellRecurrence` object hash. Its full source-to-object and
transitive ancestry is not reconstructed here. The axiom report contains
only `propext`, `Classical.choice`, and `Quot.sound`. This is not a Lean
replay; dynamic and between-sample ancestry remains inherited.

In an `IΣ₁` model the theorem assumes `3|q`, `U>0`, and both the **main
Pell norm** `g²=1+delta(a)c²` and **free carrier equation**
`Ug=U(X+ac)+Hh`, where `X=wq`, `Y=q³s`, `a=XY+Y`, and `H=4a+3`.
It concludes `U∤h`. The generic statement does **not** require `U=Y²`, nor
positivity of `q,w,s,g,c,h`; it explicitly requires the norm, carrier and
positive `U` listed above.

For the proof, `3|q` gives `3|X`, `3|Y`, hence `3|a`, `3|H` and
`3|delta(a)`. If `U|h`, writing `h=Ut` and canceling the positive `U` in
the carrier gives `g=X+ac+Ht`, hence `3|g`. The norm then says a multiple
of 3 equals one plus a multiple of 3, a contradiction. The source formalizes
the final contradiction using model remainder modulo 3.

This generic theorem does not itself extract the hypotheses from an actual
graph zero or show any zero exists. It also does not prove the first-index
relation, settle a different-witness reverse map, or establish an iPRA
endpoint. The source's “Unchecked generic draft” header predates the
successful attempt and is retained unchanged.

Run while captured temporary paths remain available:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/p64-qcube72-divisible-q-obstruction-independent/check.py
```
