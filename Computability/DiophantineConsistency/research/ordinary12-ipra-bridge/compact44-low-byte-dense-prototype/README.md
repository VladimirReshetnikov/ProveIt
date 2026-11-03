# Periodic byte windows in the dense MC support region

`CompactLowByteDense.dense_byte` proves in Lean that, for every byte index
`17 ≤ j < 7890`, the symbolic low-mask window
`(lowNat / 2^(8*j)) % 256` equals `denseWindow ((8*j)%67)`, where

```
denseWindow r = 254              if r = 0
              = 255 − 2^(67−r) if 60 ≤ r < 67
              = 255              otherwise.
```

The proof establishes that both relevant base-`2^67` digits lie in the
checked dense support, so each is `2^67−2`, and verifies the 67 possible
window offsets by bounded arithmetic. It covers 7,873 indices with a
parameterized theorem; it does not expand the whole mask.

Separately, `python3 -I -B check_dense.py` compared a Python transcription
of this periodic rule against the hash-pinned retained parent `MC.bin.gz`
after decompression. It checked exactly `[17,7890)` and reported zero
mismatches among 7,873 bytes, with the full raw and compressed hashes pinned
and unchanged compressed bytes. This is external evidence, not a Lean
theorem about the file, gzip, or correspondence between the Python code and
the Lean function. The checker SHA-256 is
`685428e7ea45be577efc3aa7e9b62328c10ed4fe008d1bab83626b0d9910dd07`;
the recorded output SHA-256 is
`d163a64e6908c8dd318601bb11bf2add66002073576874ff88d8e2d8d539d661`.

The bounded mixed-provider author run `observations/attempt01` exited 0 in
3.772 seconds without warnings or `sorryAx`. Source SHA-256:
`b6e38377f8c7e361ef862ce7f1ea0660fcf45ee33c03433eb9479ee2255321d9`;
object SHA-256:
`6bd153c63fc059cccfd81cf569318105bc8b5725f39033acb6468f4350bd3cd0`.
Direct dependency/companion guards and the separately inventoried generic
byte-window provider were unchanged at the recorded points. Lean reports
`[propext, Classical.choice, Quot.sound]` as metatheory dependencies, not
iPRA axioms. This is an author-side check, not a paired replay or a complete
symbolic/package/dynamic ancestry audit; guard checks are point-in-time.

The separate checked prefix `[0,16)` and tail `[27613,73751)` are disjoint
from this interval, giving 54,027 distinct symbolic windows across the
three theorems. Those theorems have different right-hand sides and have not
been assembled into a single Lean equality to a 73,759-byte literal. The
remaining windows, file-to-literal link, supplement provenance, PDF and
iPRA result remain open.
