# Current2011 MC byte recipe and the third Lean port

The [Lean theorem](CurrentMCBytes.lean) `decode_mc` proves that decoding the
big-endian base-256 recipe `bigBytes` yields `CurrentWindowCarry2011.ports 2`.
The recipe is the canonical `Nat.digits 256` conversion, reversed to big
endian, of an explicit six-run list of 2,011 little-endian radix-`2^47`
digits. The six run lengths are 951, 9, 26, 18, 1 and 1006; their digit values
alternate between `2^47-2` and `2^47-1`. The proof identifies this list with
the existing `ArithmeticMaskData.lowDigits`, uses `lowPort_ofDigits`, and
applies the generic `Nat.ofDigits_digits` identity. The byte decoding is
explicitly over ℕ before conversion to ℤ. The theorem concerns a symbolic
Lean recipe and the same fixed port used by the current-base equation clients;
it does not read files or interpret gzip in Lean.

The separate [byte check](check-bytes.py) hash-pins the two graph JSON files,
the Lean source and the compressed payloads. It reads the six run lengths and
digit offsets from the pinned source text, evaluates that radix recipe in
Python, converts it to minimal big-endian base 256, decompresses both the
67/106 MC file and the parent MC file referenced by 66/138, checks their
recorded compressed and raw hashes, and compares every byte. Both contain
11,815 bytes and encode a 94,517-bit integer. The
[observation](bytes-observation.json) and [exit](bytes-terminal.json) record
the result. This is an external evaluation and file comparison, not Lean
execution of the recipe or a theorem about file contents. It addresses
**only MC**, not K or MF, the whole graph, or the PDF.

[Attempt 05](attempt05/) compiled the theorem on the current14 fresh-base
client and exited 0 in observed outer session 8882. Its dependency query and
Lean compile exited 0; compile time was 2.081 seconds with no warning, error,
or `sorryAx`. The axiom report contains `propext`, `Classical.choice`, and
`Quot.sound`. The runner rechecked the successful 106 client, sixteen extension
outputs and direct guards, the source/base preflight before and after, and
120 direct companion/shadow slots. Both preflights matched the pinned result.
Lean used `-M2800`, one thread, nice 19, idle I/O and a 180-second foreground
timeout, without automatic group-RSS or host-memory stop. Existing base,
package-transitive, dynamic and between-observation ancestry remains
inherited.

The successful source SHA-256 is
`e30de9bd64cfbdd0c372a42805dd79c0a1629be7c6be6103cbf248332bbb2eb8`;
the state SHA-256 is
`6388d37739b7c82a09e66c497f6f88ee628b0487477ad309d0467b130d894b00`;
the temporary object `/tmp/current2011-mc-byte-binding-v5-20261105/CurrentMCBytes.olean`
has SHA-256 `392c502cfd8a6c10b695187e0b463affbadf0062b68f01f7657d449707c641c4`.
Attempts [01](attempt01/), [02](attempt02/), [03](attempt03/), and
[04](attempt04/) failed on rewriting, recursion depth, polymorphic decoding,
and a redundant tactic respectively; their actual exits and failed logs are
preserved and do not count as successful checks.
