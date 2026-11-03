# Symbolic K equals a closed Lean byte recipe

`CompactKernelByteRecipe.decode_bytes` proves in Lean that

```
Nat.ofDigits 256 CompactKernelByteRecipe.bytes
  = CompactSymbolicKernelOpaque.paramKernel CompactSymbolicKernel.rho.
```

`bytes` is a closed 74,111-entry list obtained by mapping the checked
two-adjacent-radix-digit window formula over `List.range 74111`. Its
`kernelDigits` are the existing 8,850 coefficient-aggregated radix digits.
The proof uses the checked `kernel_byte` theorem, the symbolic top-digit
bound `K < 2^592884`, a byte-power comparison and the generic window
reconstruction theorem. It does not normalize the entire large integer.

The separate external `python3 -I -S -B check_recipe.py` check transcribes
the pinned symbolic coefficient aggregation, parsing 943 ordered rows and
41 copy slots from pinned sources. It computes all 74,111 Python local
byte windows and matches them to the decompressed hash-pinned retained
parent `K.bin.gz`; it verifies aggregate radix digits are below `2^67` and
the binding's length and 592,884-bit count. Checker SHA-256:
`300f474064afaf8451e8874da8a391acb3bc6222cd57956d036d5b5a054b5ba1`;
recorded output SHA-256:
`9970d24ff76cf239ca09940e1f152e422faa034b2ac1966431f988b0d55c25dd`.
Python/Lean source correspondence, gzip and filesystem bytes remain
external provenance, not Lean theorems. The separate older `kernelNat`,
parent-to-95-row-supplement link, PDF and iPRA endpoints are not identified
by this result.

The bounded mixed-provider author run `observations/attempt01` exited 0 in
1.748 seconds without warnings or `sorryAx`. Its selected 361-file union
rejected conflicting shared file hashes and suppressed no foreign
companions. Recorded direct dependency/companion guards, selected union
files and provider inventory paths were unchanged at the checked points.
Source SHA-256:
`eb9c2d879a9a8dcd304da80a402d52a4d92bdfcb18c247e54e887914c8528e4b`;
object SHA-256:
`8982509922de9594e9cca21a873efacb9944d0969a20f7d8e104c305c9f8ae19`.
Lean reports `[propext, Classical.choice, Quot.sound]` as metatheory
dependencies, not iPRA axioms. This is not a paired replay or complete
symbolic/project/package/dynamic ancestry audit; checks are point-in-time.
