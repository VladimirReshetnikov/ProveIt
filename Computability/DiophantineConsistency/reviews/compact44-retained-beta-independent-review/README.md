# Independent source and payload review of the retained beta recipe

The reviewed [Lean source](../../research/ordinary12-ipra-bridge/compact44-retained-beta-byte-prototype/RetainedBetaBytes.lean)
has SHA-256 `843341bb3fde311235b893a35245c3cbc7d7ae5c869fefd6aece51262b26757c`.
Its induction states that decoding `n` little-endian base-256 digits of 255
followed by an arbitrary top digit, plus one, equals `256^n * (top+1)`.
The successor step follows from the `Nat.ofDigits` recurrence; the fixed
instance uses `n=73758`, `top=31`, and
`8*73758+5 = 590069 = 67*8807`. Its subtraction step follows from the
proved add-one equality. The recipe has 73,759 digits and the source checks
that each digit is below 256. I found no arithmetic, byte-order, off-by-one,
or top-digit mismatch in this argument.

The imported historical `CompactFixedBeta` source defines `betaNat` as
`2^(67*8807)-1`; its frozen source SHA-256 is
`9adc356351adfdeb2ccfcfe61cbf18fcd8a8458c911fabd91d07fe49ce85fcd5`.
The earlier fixed-graph receipt records that source and the imported author
object SHA-256 `a5d7c2f783e2c1bb527147e883f3433ae389079dd85562ab7aba047990f7cb02`.
I checked the beta author's recorded success, source/log and object hashes,
and direct-guard result against the live files. Its object SHA-256 is
`bd1611b2a0a3343d204c558628514b0e7132921a4263429c27b1f296ee03585b`.
I did not independently rerun Lean or authenticate the inherited provider,
package, transitive or dynamic ancestry. This review is not a paired replay.

My separate `python3 -I -S -B audit.py` observation in
`observations/attempt02` pins the Lean source, frozen beta source, build
receipt, log, live objects, retained parent binding and gzip payload, and the
95-row graph JSON. It decompresses the **parent package's** payload and
independently checks the integer value via little-endian `int.from_bytes`
against `(1 << 590069) - 1`. It also checks every byte, verifies that the
73,759-byte representation is minimal, and checks the binding's bit count,
byte count and both hashes. It exited 0 with unchanged pinned inputs. The
raw bytes are 73,758 copies of 255 followed by 31; the raw SHA-256 is
`0664a868cbfef9869ea05c40a1c445563f685ff857092594c1c1223bc4b21f9d`.
The audit source SHA-256 is
`6c5d7d80034ec5a4393bfe47422603452db5cc95feec1b2ff6f96a574943c6a5`;
its recorded output SHA-256 is
`b43149dd63d2d3ba624f2ae5d5555cbce89e36fe0f560f4595bd7d834c0f571a`.
The first audit attempt failed because it looked for a nonexistent `ports`
JSON key; its exact source and traceback are retained under `attempt01`.

The original external checker names one test
`minimal_length_and_bits_match_binding`, but that boolean tests the bit
length alone. Its separate exact recipe comparison nevertheless fixes both
the length and final nonzero byte; my independent observation explicitly
checks minimality. Neither external check makes gzip, the filesystem, or the
JSON-to-Lean relationship a Lean theorem. The 95-row JSON identifies beta as
the first fixed numeral but references a supplement `BINDING.json` that was
absent at this workspace snapshot. Thus this review does not by itself prove
that the parent payload is the 95-row supplement's intended coefficient,
and it establishes no result for the remaining ports, a PDF or iPRA.
