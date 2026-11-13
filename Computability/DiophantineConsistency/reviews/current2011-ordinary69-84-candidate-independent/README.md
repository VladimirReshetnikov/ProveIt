# Independent review: 69/84 candidate graph

The pinned graph and its 70/84 parent share all 61 prefix rows and the same
witness and fixed-port metadata. The complete tails give respectively
`Na² + strong² + X(X−2)` and `Na² + (X−1)² + strong² − 1`, where
`X=N0*N1*Nt`. The review checker evaluates both tails as sparse integer
polynomials over five independent prefix cuts; it verifies their full
identity over every commutative ring. All 69 candidate rows and all 18 leaves
are live; the operations are 38 multiplications, 18 additions and 13
subtractions.

The checker follows the metadata's actual path relative to the candidate
folder and verifies gzip bytes, decompressed bytes, lengths and bit lengths
for all four fixed ports. It verifies the exact row structure that cancels
`(a*c)²` in the main norm, and uses that identity in an otherwise syntactic
degree upper bound of 84. Separately it substitutes one indeterminate for
all 14 witnesses, reduces the actual fixed bytes modulo 1,000,000,007, and
computes the complete graph polynomial. Its coefficient of degree 84 is
589,155,221, proving the upper bound is attained over the integers. The
candidate author's checker was rerun and its stdout matched the retained
result exactly. This review's check uses the same mathematical cancellation
and same modular ray; it is not an independent proof inside Lean.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/current2011-ordinary69-84-candidate-independent/check.py
```

It exited 0 and produced the retained [result](result.json). Its SHA-256 is
`496485715e7b129eaa55bb98bc0fa27b01f708758f03f23afccb120eba490f1c`;
the checker SHA-256 is
`23868d9e477c4038a67402a56c9378d4fca6ad020094672ae32d2e6c782edba8`.
The candidate graph hash is `c9781e95b9d8e3124afadfe3ee5874eb3eb76ce9f1aaef02c7b3bf49ed93e80a`;
the parent graph hash is `bb7df3586252e9c85be225a0373a8586c2c2f841683cc5f4b6f57f02175447e5`.

This is an external finite check of the literal JSON graphs, exact fixed-byte
degree, and polynomial identity. It does not establish a Lean binding of the
69-row graph or the internal iPRA transfer for that syntax. It does not
prove a global degree or operation minimum.
