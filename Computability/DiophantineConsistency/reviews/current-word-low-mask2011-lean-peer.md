# Constructed low mask: independent Lean review

Date: 2026-10-26. Reviewer: `circuit_reduction`. Author: root.
Verdict: PASS; no source change requested.

I read all110 main-source lines and all48 check-source lines before execution,
then confirmed the announced frozen hashes. I also read the complete
`CurrentSparseDigits2011` and `NativeRadixDigits` sources, the exact
`NativeCyclicConvolution.word_add`, `word_lt_pow` and `mask_word_iff` statements
and proofs, and the full previously peer-reviewed word-construction packet.
I authored the older `CurrentSparseDigits2011` prerequisite, but not this
reviewed encoder or its checks. No independence from my own prerequisite
work is claimed.

| Source | SHA-256 |
| --- | --- |
| `Lean/DiophantineConsistency/CurrentWordLowMask2011.lean` | `cc217428c511731eb99169a46d65ca2cf2f14cc7d17fa83f6fc68fc5497a70f4` |
| `Lean/DiophantineConsistency/CurrentWordLowMask2011Checks.lean` | `7c154017047e5ed5930d5de4b20a7745ebc0e8a665e2b68cde20984573714ae9` |
| Direct import `CurrentSparseDigits2011` | `5ce36d1cd28f0162e40d5e7ca712b0e77c7242a1ff9039016fc0765baf50b60d` |
| Direct import `CurrentWordConstruction2011` | `9455d6c2015906a8f76ff2be5275a95cae5340f0ca3e8dc16666ffc6bab2b5b8` |
| `NativeRadixDigits` | `61281eae24ab42852e08e86fc8dcd62a89d0e95f26b1eca5dda01da6639ca7de` |
| `NativeCyclicConvolution` | `9201387d63494a3ed80bc28f9fb5b1018a0ba7a326c6cded39ca9b838f468c52` |

Paths in this receipt are relative to `Computability/DiophantineConsistency/`
unless absolute. The two exact direct imports are unchanged. Prerequisite
objects were reused; this review does not claim a fresh dependency-closure
build.

## Mathematical scope

The generic encoder sets exactly the global origin digit to zero, preserving
all other digits. From `c 0 = 1`, it proves the actual ordinary equality
`word c = word z + 1`; hence natural subtraction gives `word c - 1 = word z`
without a borrow hypothesis. The masked digit capacity at the origin is zero,
and the supplied capacity at every other position remains intact. Both digit
and mask bounds needed by `mask_word_iff` are proved. This applies to mixed
capacities, not only Boolean words. It does not assume the desired mask or the
existence of an alternate representation.

For the current assembled word, `assembled_capacity` derives each allowed bit
from the exact periodic low support and the independent Boolean control maps.
The scalar theorem uses `CurrentSparseDigits2011.low_mask_word` verbatim, so its
mask is the complete `lowPort * repunit width N + 1`, including the source's
origin increment. Start at the origin is the only tile premise (`a 0 = 0`).
It does not ask for horizontal/temporal matching, a unique Start, a positive
transport word, a carry solution, a high mask, or native calibration.

The source lower bound comes from the actual origin summand, and the strict
upper bound from all actual digits being below the radix. Thus both bounds
refer to the same assembled scalar C as the mask theorem. They do not yet
assert the stronger combined native slack involving F or alpha. The N=1
specialization is valid, including independent all-one dummy and marker maps.

The focused checks cover the exact one-position origin subtraction and a
negative control showing that omission of that subtraction fails; mixed
capacities; the actual N=1 full low port with both controls one; and the complete
symbolic scalar conclusion with no carry/transport/matching premise.

## Fresh isolated replay

Using the pinned `lake env`, I compiled both frozen sources sequentially with
`lean -M6000 -j1`, with `Elab.async false` from the source. The temporary overlay
`/tmp/current-word-low-mask-peer-sz526vw8/` was first in `LEAN_PATH`; unchanged
prerequisite bundles were symlinked into it, while both reviewed objects were
freshly compiled there. The checks imported the freshly replayed main object.
No shared object or prerequisite bundle was overwritten.

Both commands exited zero, with no Lean warnings or errors. Main elapsed3.14s,
peak3264456KiB; checks elapsed2.70s, peak3248892KiB. The four printed axiom reports
contain only `propext`, `Classical.choice`, and `Quot.sound`. Neither reviewed
source contains `sorry`, `admit`, a new axiom, or `native_decide`. Source hashes
were unchanged across execution; both new objects match the author's shared
objects byte for byte.

| Replay artifact | SHA-256 |
| --- | --- |
| Main `.olean` | `9b3fa57f5d0d9f591c0fef854c378c00da6fb603741494febf074100889f5d13` |
| Checks `.olean` | `902ae1af54e2415ba26846a1c4cae39168b4757718ac2a961431a9e8e39c46f3` |
| Main log | `2d6d21d16fb031ae936eb28f81cdf34bfecadf11c5750d3a94f698ac28df8fa6` |
| Checks log | `1e866e813ea31c05cd07b7d852e5e8c689d3fd8245dd1923d42b87c8bc1718e4` |
| `REPLAY.json` | `72f0b5865bb2de9b13d5ac4bd3e413880a6c101e4d1a0f1882151480eb701163` |

Only this new peer receipt was written. No frozen source, shared document, or
git state was edited. The remaining constructed high-mask/carry/controller
obligations are outside this packet and this review.
