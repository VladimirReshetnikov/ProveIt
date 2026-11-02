# Exploratory straddling rotation digit

`RotationStraddling.straddling` proves the following in an arbitrary IΣ₁ model, where exponentials and subtraction are internal. Given `a<67`, `e=67*k+a`, `L=e+((67−a)+t)` and `X<2^L`,

```text
dig 67 (rot 1 L X e) k =
  (X % 2^(67−a))*2^a + (X / 2^(L−e+67*k)) % 2^a.
```

The identity also permits a=0; no positive-a hypothesis is needed. `StraddlingAdjacent.straddling_adjacent` additionally assumes `L−e+67*k=67*q+r` and `r<67`, and replaces the high quotient with the explicitly reduced combination of the two adjacent radix-67 digits. The source-cut-length and word-bound conditions remain explicit; no finite standard-model inference is used.

Single-author compiler sessions 39093 and 14237 actually exited 0, without warnings or `sorryAx`. Their named axiom reports use `propext`, `Classical.choice`, and `Quot.sound`. Session 36364 exited 1 on a rewrite and targeted modulus issue; its source and log are retained and its `sorryAx` report proves nothing. The fresh overlay inherits the author side of the graph-temporal/carry provider and locally compiled fractional/rotation sources from commits 5152fadc5e and ce88d22a4f. This is exploratory evidence, not a paired replay or independent artifact audit.

These conditional identities have not been instantiated at the graph witnesses. They do not prove a strict half-radix bound or clean predecessor, graph-column decoding, retained-K binding, or an internal iPRA theorem.
