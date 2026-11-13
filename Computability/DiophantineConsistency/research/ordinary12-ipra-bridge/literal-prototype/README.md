# Historical 100-row literal identity prototype

`Ordinary12Literal.lean` defines the exact 100-row parent graph with twelve
variables and four symbolic integer ports. `check_literal.py` compares every
row, variable, port, and exposed factor against the pinned graph; four
targeted mutations are rejected. The graph and its compact44 four-port
provenance are checked separately in `../port-binding/`.

Lean proves a definitional factorization of the literal and a separate raw
integer evaluation identity. For an `IΣ₁` model it also proves that an
internal zero of this literal yields product one for the three exact signed
factor pairs. It does not yet show those factors satisfy the hypotheses of
the generic exclusion theorem. Nor does it establish checker calibration,
rank recovery, an iPRA derivation, or equivalence to consistency.

The fresh bounded replay's actual session 76074 returned exit 0 and printed
`PASS_BOUNDED_ORDINARY12_LITERAL_IDENTITY
872730f7137015c6fb35b053b27ba634c630c4d1974058e925c1bfb45038c763`.
`replay-receipt.json` records the exact source, compiler output, direct
dependencies, object hash, and inherited bounded overlay receipt. The latter
records its two observed failed historical prototype attempts, followed by a
successful replay, and 20 authenticated linked project objects with absent
companion checks. This is a single-author historical source-declared overlay,
not an independently matched full-project build or a dynamic dependency audit.

An earlier exploratory compilation also exited 0 (session 75859); the same
source produced the same object hash as the replay. The actual compiler
reports appear in the replay receipt. The four-port graph check identifies
the reconstructed tuple, but does not certify the compact44 checker; the
different fixed β used by the older 2011 endpoint must not be substituted.
