# The once-shifted symbolic MF radix digits

`CompactShiftedHighDigits.shifted_value` proves in Lean that

```
CompactFixedBeta.betaNat + CompactSymbolicPorts.highNat
  = Nat.ofDigits (2^67) shiftedDigits
```

where `shiftedDigits = (3 :: highDigits.tail) ++ [1]`. The checked original
`highDigits` starts with 4 and has length 8,807. The theorem uses the generic
repunit-shift lemma with an **arbitrary base first**, then specializes it to
`2^67`; this avoids reducing the enormous fixed power. It adds beta exactly
once. Separate checked theorems establish that `shiftedDigits` has length
8,808 and all digits are less than `2^67`.

The external `python3 -I -B check_payload.py` separately transcribes the
pinned high-digit source, computes both beta-plus-high and the transformed
digit expression, and compares their minimal little-endian bytes to the
hash-pinned retained parent `MF_source.bin.gz`. It finds 73,759 bytes and
590,070 bits, with equality to the once-shifted recipe. The Python/Lean
transcription, file, gzip, and parent-to-95-row-supplement relation are
external provenance, not Lean theorems. The checker SHA-256 is
`6c95002c0daf6467c7d68b5d48829a2e3dcefdcdfecd3272cac6432f3ca62e39`;
the successful recorded output SHA-256 is
`040ce08f6a59355640f014f92f4b23f0a75657a7a96b7a239574150c29be0437`.

The bounded mixed-provider author run `observations/attempt03` exited 0 in
9.366 seconds without warnings or `sorryAx`; the direct dependency and
companion guards and the separately inventoried generic provider were
unchanged at the recorded points. Source SHA-256:
`25c60e91e8c5b214c1ffa622b53c88bdb5596a5772255422dc73321309a25d50`;
object SHA-256:
`be4f35d915c5e538aac51f2acd257188f15cb32609f16dc5d56bbd75b3b2beac`.
Named axiom reports are `[propext, Quot.sound]` for the length and
`[propext, Classical.choice, Quot.sound]` for the other results, as Lean
metatheory dependencies, not iPRA axioms.

Attempts 01 and 02 failed, and their sources and logs are retained. The
first had a singleton-membership simplification error; both attempts hit a
recursion limit and exponent warning while matching the huge concrete power.
Attempt03 avoids that whole-value matching by proving the transformation for
an arbitrary base before specialization. This is an exploratory author-side
build, not a paired replay or full symbolic/package/dynamic ancestry audit;
all guard checks are point-in-time. No MF byte-list decoding theorem, PDF
binding or compact iPRA endpoint follows yet.
