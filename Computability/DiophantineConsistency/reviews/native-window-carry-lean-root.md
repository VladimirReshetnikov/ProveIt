# Boolean temporal phases and the actual source carry word

Date: 2026-10-25. Author and full source/check reviewer: ROOT.
Independent whole-source review and fresh replay: controller_certificate,
recorded in the [peer receipt](native-window-carry-lean-peer.md).

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| NativeBooleanRotation.lean | d50110d8f2a959df7da69f23e80b4df09a1aad98ba2b66c67d2445203cf81f3e |
| NativeBooleanRotationChecks.lean | b58d43393f724c8ec583ca420a4f5d78c99d23b5112ed547b014e4256e6da0b9 |
| NativeWindowCarry.lean | df80356d4f26e30859b47aed5d39c913e4e3dfd7b876f82e816fdd4008edd589 |
| NativeWindowCarryAudit.lean | 47721e2ffe31bc0e552950deaadb4ddd7f004bd1f79bc94aab479eb8cb91b2fc |

All four direct fresh checks passed with `lake env lean -M6000 -j1`.
The five rotation and three source/carry axiom reports contain only
`propext`, `Classical.choice`, and `Quot.sound`. The independent reviewer
also freshly ran all four files successfully. These are module replays
against the checked dependency environment, not a complete ancestor or
umbrella rebuild.

For any positive radix width, a Boolean digit shifted by any fractional
phase stays below the radix. The quotient contribution is therefore zero,
including at the last phase. The exact rotation formula gives a half-radix
bound, even digits at every nonzero phase, the exact whole-cell permutation
at phase zero, and the location and scale of the fixed origin bit. Checks
include the last phase, cyclic wraparound, and a non-Boolean counterexample
that prevents silently dropping the Boolean hypothesis.

The source composition uses the literal source transport identity and
proved spatial power to derive the convolution congruence. Positivity of
the two summands beside F gives the strict bound F<q−1. An explicit mass
budget then supplies simultaneous bounded cyclic carries, their quotient
recurrence, the exact local decomposition, a digit word equal to F, and
every local high-mask test. Coefficient folding and collisions are allowed:
the coefficient word is required to be congruent to K, not identical to it.

The theorem exposes its finite Interface, positive actual31-row source
solution, Boolean C word, radix window, coefficient congruence, full mask
binding and mass budget. It assumes no temporal alignment, tile semantics,
machine run or consistency statement. Binding the actual current K recipe,
deriving phase alignment and recovering the native language remain required.
