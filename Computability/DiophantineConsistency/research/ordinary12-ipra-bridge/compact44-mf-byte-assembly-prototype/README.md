# Once-shifted symbolic MF equals a closed Lean byte recipe

`CompactShiftedHighByteAssembly.decode_bytes` proves in Lean that

```
Nat.ofDigits 256 CompactShiftedHighByteWindow.bytes
  = CompactFixedBeta.betaNat + CompactSymbolicPorts.highNat.
```

`bytes` is the closed 73,759-entry list obtained by mapping a two-adjacent-
digit byte-window function over `List.range 73759`. The shifted radix digit
list is the original high list with its first digit changed from 4 to 3 and
one high digit appended; the previously checked `shifted_value` theorem
accounts for adding beta **exactly once**. The proof combines the checked
pointwise window theorem, the symbolic size bound and the generic
radix-window reconstruction theorem. No giant numeral is normalized.

Separately, `python3 -I -B check_recipe.py` evaluates a Python transcription
of the Lean high-digit list and local byte-window formula and matches all
73,759 bytes to the hash-pinned retained parent `MF_source.bin.gz` after
decompression. The binding JSON, high-source and Lean window-source hashes,
compressed/raw hashes and unchanged inputs are checked. The raw/recipe
SHA-256 is
`48333b0d30a4edeb8579f44286cb59806c5622cb42b367f5b5f9ee827711c737`;
the checker SHA-256 is
`24d6c2c9ea3d74a6f94d091d55290f8dbab4dc3fa5dcd24bffd9e8aea8f302d8`;
the recorded output SHA-256 is
`323ec89f75905eeee2a167f86f94b512549b1a47f57e154f147f6f24178edd39`.
The Python/Lean source transcription, filesystem and gzip decoding are
external provenance, not Lean theorems. The parent-to-95-row-supplement
connection, PDF and iPRA endpoint are also separate obligations.

The single-author mixed-provider `observations/attempt01` exited 0 in
1.873 seconds without warnings or `sorryAx`. Its selected 590-file union
rejected conflicting shared paths and suppressed no foreign companions;
the preparer inventory, selected files, recorded provider paths and direct
dependency/companion guards remained unchanged at the checked points. The
exact source, manifest, compiler log and terminal receipt are retained.
Source SHA-256:
`420ac9903e344d5952a22433003e7b5623514e52c042e017eb924e2f9f8390c2`;
object SHA-256:
`992dd20b27f39d9fda165349221ca1e93ed36789816d48d17555bea74efec77e`.
Lean reports `[propext, Classical.choice, Quot.sound]` as metatheory
dependencies, not object-theory axioms. This is not a paired replay or a
complete symbolic/project/package/dynamic ancestry audit; filesystem
checks are point-in-time.
