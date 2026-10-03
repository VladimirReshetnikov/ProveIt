# A padding obstruction in the reviewed Grill encoding fragment

The corrected two-symbol encoding from the [primary-source audit](review_grill_encoding_e.md) cannot be used directly as an ordinary input decoder for the native existential-padding relation. There is a concrete fixed compiled program and an encoded positive integer whose intended encoded run **never halts**, while appending six terminal zero bits makes the same program halt after **2,274 steps**. Those zeros do not change the ordinary binary integer. Both widths satisfy the existing `P0>3x` condition.

This concerns the explicitly reviewed fragment and a particular proposed input interpretation. It does not refute Grill Tag universality, the complete creator construction, or the possibility of a different verified decoder. It converts one previously open compatibility question into an explicit counterexample to this direct embedding.

## Fixed program and finite local certificates

Use the source-pinned constructor in `review_grill_encoding_e.py`, SHA256 `66c64fc95574b4d938a3a05e443215f802825677129a17e3cd38fae4150a12f3`. Choose `a=84`, both symbol widths equal to one, and all four position/symbol production entries equal to `(0,0)`. These are the nonhalting two-symbol productions already covered by the corrected audit. The constructor emits 1,176 Grill exponents. Its two halves happen to be identical; we retain the literal full program.

Let E, L and R denote the corrected encodings of symbol zero with width one. Each is exactly 588 bits long. The complete program tuple and the three exact strings are included in the [receipt](grill_tag_encoded_padding_obstruction.json); no unspecified universal machine or source file is needed to reproduce them beyond the authenticated constructor.

Write `Gen_p(w)` for processing precisely the initial symbols of w starting in phase p, with outputs appended behind those symbols. Direct string equality certifies, for both `p=0` and `p=588`,

```
Gen_p(E)  = LR,    next phase = p+588 mod1176;
Gen_p(LR) = EE,    next phase = p.
```

The [checker](grill_tag_encoded_padding_obstruction.py) computes these words with its own literal generation loop and compares them with the pinned implementation. These are finite exact word identities. Concatenation of E blocks only alternates phases0 and588; LR blocks have length1176 and preserve phase. Therefore, for every positive k, two complete generations give

```
E^k -> (LR)^k -> E^(2k),
```

with the phase still in `{0,588}`. The generations remain nonempty forever. A queue cannot empty while an initial-generation suffix remains, and the next generation is nonempty at the end. Induction thus proves nonhalting of the real FIFO run from every `E^k`, rather than merely failure to halt within a simulation limit.

## Six zeros erase the next generation

Starting instead from `E^k 0^6` still produces `(LR)^k` during the initial generation: the extra zeros append nothing. Its phase is now6 or594. Two further exact local identities, each with preserved phase, are

```
Gen_6(LR)   = 0^504;
Gen_594(LR) = 0^504.
```

Hence the next generation is `0^(504k)`, which then empties without output. All first-halt times are exact because each preceding generation is nonempty. The total is

```
(588k+6) + 1176k + 504k = 2268k+6.
```

For k=1 this is2274 steps. A separately implemented deque simulation checks every actual FIFO step through the first halt for k=1 and2, recording deterministic trace hashes. The general family follows from the six local word identities, not from the six sample k values in the receipt.

Of all1,176 padding residues,474 erase every one in the second generation for k=1. The receipt lists these exact residues. This is only an erasure census: the remaining residues are not classified as halting or nonhalting by this test. Six is the first residue with this particular two-generation erasure property; no global minimal-halting-padding claim is made.

## Why the ordinary input is unchanged

Read the queue little-endian and let `x_k=value(E^k)`. Its ordinary binary bit length is `588(k−1)+345`; the E blocks end in243 zero bits. Thus x_k is positive, and the original width `2^(588k)` already exceeds `3x_k`. Appending six terminal zeros changes the numerical width to `2^(588k+6)` but leaves x_k unchanged. Both widths are allowed by the native strong-cone input definition. The weak-cone definition also permits both.

The original encoded run therefore has negative halting truth, while the native relation accepts the same ordinary integer through its padded halting run. The native polynomial is behaving exactly as its theorem specifies: it existentially permits all such paddings. What fails is the inference from correctness of the encoded run to correctness of this ordinary-input interpretation. A full universality proof must supply a decoder whose entire allowed padding-residue union is correct, or change the paid input interface. The abstract encoded universality assertion alone does not solve that obligation.

## Reproduction

The standalone checker authenticates and compiles the reviewed helper bytes, independently computes all six local word identities, checks six concrete family members and both exact FIFO traces, and enumerates the1,176 erasure residues. Saved-receipt comparison checks exact container and scalar types, including Boolean versus integer distinctions. It uses standard Python only and writes a receipt only with `--output`:

```sh
python grill_tag_encoded_padding_obstruction.py \
  --expect grill_tag_encoded_padding_obstruction.json
```

An isolated copy can select the pinned constructor with `--source /path/to/review_grill_encoding_e.py`. The source and receipt do not execute any downloaded code.
