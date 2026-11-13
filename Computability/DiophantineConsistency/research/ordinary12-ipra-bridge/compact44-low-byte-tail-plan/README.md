# A parameterized all-one run of symbolic MC byte windows

`CompactLowByteTail.interior_byte` proves in Lean that

```
∀ j, 27613 ≤ j → j < 73751 → (lowNat / 2^(8*j)) % 256 = 255.
```

The interval contains 46,138 byte indices. The proof first proves every
support index is at most 3,296, then shows both 67-bit digits touching each
window in this range are unmodified all-one digits. A bounded 67-case
arithmetic lemma handles all possible offsets of the 8-bit window within a
67-bit digit. This is one parameterized symbolic theorem, not a separate
computation of the full low mask or of 46,138 individual certificates.

A separate external `python3 -I -B check_tail.py` observation confirms that
the hash-pinned retained parent `MC.bin.gz` has a wider all-255 run at byte
indices `[27605,73758)`, and its last byte 73758 is 31. The Lean theorem
above covers only the strictly smaller interval `[27613,73751)`. The file,
gzip decompression and correspondence to any future Lean literal are
external; neither this observation nor the symbolic theorem proves those
file bytes in Lean. The other MC windows, a 73,759-byte literal binding,
supplement provenance, PDF and iPRA result remain open.

The bounded mixed-provider author run `observations/lean-attempt01` exited 0
in 3.702 seconds without warnings or `sorryAx`; its direct dependency and
companion guards and separately inventoried generic provider were unchanged
at the recorded checks. Source SHA-256:
`b7c501a6d08a1b73232e5097472f22adf5037babe424133883081d4179355f46`;
object SHA-256:
`8500c38698d2667a57f21231537807b5c872bb0d42b432416abd5c7a5b4e29f4`.
Lean reports `[propext, Classical.choice, Quot.sound]` as metatheory
dependencies, not iPRA axioms. The external checker SHA-256 is
`306457b7e813340319ea5349cebcc11a8e29f8f9346805bb995ab6b6f4e1bbb1` and
its output SHA-256 is
`3e49e18805dbc68ef018050e5ceb13fab8cecc62b9ad43c1630a71b8414cb0a7`.

The first Lean-runner invocation refused to overwrite the already-existing
external observation directory and stopped before invoking Lean; the failed
runner source and traceback are retained under `runner-attempt00`. The
successful run uses a separate observation directory. This is an author-side
check, not a paired replay or full symbolic/package/dynamic ancestry audit;
filesystem checks are point-in-time.
