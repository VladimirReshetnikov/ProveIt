# Retained beta little-endian recipe

The bounded author-side Lean check establishes a byte-recipe equality for
the **first** of the four compact free-J ports. Define

```
betaBytes = List.replicate 73758 255 ++ [31]
```

as a little-endian list of base-256 natural digits. The checked theorem
`RetainedBetaBytes.decode_betaBytes` states

```
Nat.ofDigits 256 betaBytes = CompactFixedBeta.betaNat
```

where `CompactFixedBeta.betaNat = 2^(67*8807) - 1`. Separate Lean theorems
establish the recipe length is 73,759 and all its digits are below 256.
The reusable induction `decode_max_bytes_add_one` proves for arbitrary
`n` and `top` that decoding `n` bytes of 255 followed by `top`, plus one,
is `256^n * (top + 1)`. The fixed specialization remains symbolic; it
does not normalize the enormous power or enumerate the 73,758 low bytes.
The source SHA-256 is
`843341bb3fde311235b893a35245c3cbc7d7ae5c869fefd6aece51262b26757c`.

Separately, the external command `python3 -I -B check_payload.py` reads
the retained parent package's `BINDING.json` and `beta.bin.gz`, verifies the
binding hash pin, gzip and raw hashes, declared byte count and bit length,
and byte-for-byte compares the decompressed data with precisely the same
run-length recipe. Its actual output is `observations/payload-check.json`.
The raw hash is
`0664a868cbfef9869ea05c40a1c445563f685ff857092594c1c1223bc4b21f9d`;
the gzip hash is
`466796f146d60db9929fa0f0f62d70d5e6afbcea9940342764571f1ca6bea87c`.
The checker source SHA-256 is
`d9f45198470682bb4925bc458ad9fa3ec488a8dffc9d5e8ad9f6f912e08a492b`.
The checker and its correspondence to the Lean recipe, the filesystem and
gzip decompression are **external provenance**, not a Lean theorem about
file bytes, gzip, JSON, or a displayed PDF.

The actual bounded single-author Lean run `observations/attempt03` exited 0
without warnings or `sorryAx`; direct dependency and companion guards were
unchanged. Its output object SHA-256 is
`bd1611b2a0a3343d204c558628514b0e7132921a4263429c27b1f296ee03585b`.
The axiom reports for the generic induction and fixed decode theorem are
`[propext, Quot.sound]`, which are Lean metatheory axioms, not iPRA axioms.
Attempts 01 and 02 failed and produced no object: the first exceeded
recursion depth when simplifying the large list and the second tried to
evaluate a huge power. Their sources, diagnostics and guard receipts are
retained; neither failed run's error-recovery `sorryAx` is evidence.

This single-author result inherits its provider's transitive, package and
dynamic ancestry and has not had a paired replay or complete audit. It does
not identify the three remaining ports, prove the 95-row JSON/PDF binding,
or construct an iPRA derivation. The external checker only inspects the
retained parent package; correspondence to the reconstructed 95-row
supplement remains a separate provenance issue.
