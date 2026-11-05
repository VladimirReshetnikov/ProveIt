# Current2011 beta byte recipe and the first Lean port

The [Lean theorem](CurrentBetaBytes.lean) `decode_beta` proves that decoding
the explicit big-endian list `31 :: List.replicate 11814 255` yields
`CurrentWindowCarry2011.ports 0`. It reverses the list for `Nat.ofDigits 256`,
whose digit order is little-endian, and proves the identity symbolically from
`beta = (2^47)^2011 - 1`. This is a theorem about a Lean list and the same
fixed port used by the fresh-base 66/138 and 67/106 model clients. It does not
parse files or gzip within Lean.

The separate [byte check](check-bytes.py) hash-pins the two graph JSON files,
the Lean source and each compressed payload; it decompresses the beta file
retained with the 67/106 graph and the parent payload referenced by 66/138,
checks their recorded compressed and raw hashes, and compares every byte with
the explicit big-endian list. Each raw payload has 11,815 bytes and 94,517
bits. The [observation](bytes-observation.json) and
[exit](bytes-terminal.json) record the result. This file comparison is an
external finite check, not a Lean theorem about file contents; it addresses
**only beta**, not the K, MC or MF bytes, the whole graph or the PDF.

[Attempt 02](attempt02/) compiled the theorem on the current14 fresh-base
client and exited 0 in observed outer session 31226. The dependency query and
Lean compile exited 0; the compile took 2.268 seconds, with no warning, error,
or `sorryAx`. The general decoding lemma reports `propext` and `Quot.sound`;
the port theorem reports those plus `Classical.choice`. The runner rechecked
the successful 106 client, sixteen extension outputs and direct guards, the
source/base preflight before and after, and 80 direct companion/shadow slots.
Both preflights matched the pinned result. Lean used `-M2800`, one thread,
nice 19, idle I/O and a 180-second foreground timeout, without automatic
group-RSS or host-memory stop. Existing base, package-transitive, dynamic and
between-observation ancestry remains inherited.

The successful source SHA-256 is
`538444983d5a713194673f3e17377e234bbce33d27d0f3cffa37d4a1eff762c8`;
the state SHA-256 is
`499a0f11346df9d952e6bd67964c3bed3b4272701f97aa2a3a62bf4b6f32c0f2`;
the temporary object `/tmp/current2011-beta-byte-binding-v2-20261105/CurrentBetaBytes.olean`
has SHA-256 `b1601003102f4483dfcaba4238826e85b4a356ff99fcd28322f31c0f93862e27`.
[Attempt 01](attempt01/) exited 1 because an unnecessary tactic followed an
already closed goal; its failed `sorryAx`-bearing log is preserved and is not
evidence of the theorem.
