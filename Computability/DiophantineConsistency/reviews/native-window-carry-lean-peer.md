# Independent Boolean rotation and source-window carry review

Result: PASS. ROOT authored the four modules below. `controller_certificate`
independently read all 199 source lines and the invoked transport, rotation,
normalization, and mask statements, and freshly compiled each module and its
focused check. No reviewed source was edited.

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| NativeBooleanRotation.lean | d50110d8f2a959df7da69f23e80b4df09a1aad98ba2b66c67d2445203cf81f3e |
| NativeBooleanRotationChecks.lean | b58d43393f724c8ec583ca420a4f5d78c99d23b5112ed547b014e4256e6da0b9 |
| NativeWindowCarry.lean | df80356d4f26e30859b47aed5d39c913e4e3dfd7b876f82e816fdd4008edd589 |
| NativeWindowCarryAudit.lean | 47721e2ffe31bc0e552950deaadb4ddd7f004bd1f79bc94aab479eb8cb91b2fc |

For Boolean digits, the scaled digit at phase `W % v` is strictly below
the radix for every positive v. Consequently the quotient contribution
in binary rotation vanishes even at phase v-1. The resulting exact formula
proves the half-radix bound, evenness at each nonzero phase, the whole-cell
shift at phase zero, and the shifted origin anchor. None of these arguments
assumes native tile decoding or temporal alignment. The negative control
with a non-Boolean digit correctly shows why the Boolean premise matters.

The source-window composition derives the strict bound F<q-1 using both
positive summands left beside F. Its temporal word uses the proved source
spatial power and the actual binary shift of the source gap. Combining
this with the genuine source transport identity gives the congruence
needed for simultaneous cyclic carry normalization. The explicit mass
budget bounds the carries; the source mask test then gives every local
digit-mask test from the exact normalized word. The proof handles folded
coefficient collisions and exponents beyond the cyclic window by accepting
congruence, rather than equality, for the coefficient word.

The hypotheses remain explicit and appropriately scoped: the finite
port Interface, a strictly positive solution of all 31-coordinate source
rows, a Boolean word representing the source gap, the radix-power window,
the coefficient congruence, the mask-word binding, and the numerical mass
budget. There is no hidden tile, refutation, alignment, or Con(ZFC)
premise. This supplies arithmetic normalization, not native calibration.

Independent replay used direct `lake env lean -M6000 -j1 -o ...` for each
source. All four exited 0. The two main-module logs were empty. The eight
axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
These were fresh module checks against the checked dependency environment,
not a full fresh rebuild of every transitive dependency. Final source
hashes were rechecked unchanged.

| Independent log | SHA-256 |
|---|---|
| /tmp/native-window-carry-peer/rotation.log | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| /tmp/native-window-carry-peer/rotation-checks.log | d4af403545d0ecedbbbcc8a7aaf6b1df1bee78f9bc9ea956def9b49098592e4c |
| /tmp/native-window-carry-peer-window.log | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| /tmp/native-window-carry-peer/window-audit.log | 0f23f1ad88be40506cf3dcbdb6caecae72381743dfe4bef2e5d50d67a4d74dde |
