# Constructing the full scalar low mask: author receipt

Date: 2026-10-26. ROOT authored and read all110 main lines and48 check
lines before replay. This is an author self-review; the independent
composition review is `current-word-low-mask2011-lean-peer.md`.

| Source | SHA-256 |
| --- | --- |
| `CurrentWordLowMask2011.lean` | `cc217428c511731eb99169a46d65ca2cf2f14cc7d17fa83f6fc68fc5497a70f4` |
| `CurrentWordLowMask2011Checks.lean` | `7c154017047e5ed5930d5de4b20a7745ebc0e8a665e2b68cde20984573714ae9` |

ROOT read the complete imported sparse-digit and word-construction
sources, the generic origin-capacity decoder, and the actual packed-word
mask, sum and bound proofs. The two direct imports remain unchanged.
Existing prerequisite objects were reused, not freshly rebuilt.

The generic encoder erases exactly the origin digit, proving the ordinary
word equality `C=word(z)+1` from `c 0=1`. It then establishes the complete
origin mask digit by digit, using the proved capacities and mask bounds.
For the actual assembled word, independent Boolean controls and Start at
the origin prove `(C-1) &&& (lowPort*repunit width N+1)=0` and `0<C<q`.
The literal final increment is retained. No transport, carry, high mask,
matching, unique Start or source zero is a premise.

Both final builds used `lake env lean -M6000 -j1`, declared
`Elab.async false` and pinned Lean4.32.0, sequentially writing the named
main/check objects. Both terminal results were exit0; main diagnostics
are empty and all four axiom reports use only the standard three axioms.
No `sorry`, `admit`, `native_decide` or new axiom occurs. The checks cover
one-position origin subtraction, failure when that subtraction is
omitted, mixed capacities, both controls one at N=1 and the full symbolic
scalar conclusion. An initial concrete check exceeded the default
elaboration heartbeat while inferring its radix exponent; specifying
`v:=1` fixed inference without raising limits or changing the example.

| Root evidence | SHA-256 |
| --- | --- |
| `/tmp/current-word-low-mask2011-root-main.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/tmp/current-word-low-mask2011-root-checks.log` | `4141ec1743638264132c8a69a395be0f0bcdd8068db60a22a71ad964be003482` |
| Main `.olean` | `9b3fa57f5d0d9f591c0fef854c378c00da6fb603741494febf074100889f5d13` |
| Checks `.olean` | `902ae1af54e2415ba26846a1c4cae39168b4757718ac2a961431a9e8e39c46f3` |

The independent peer read both complete sources and the prerequisites,
then rebuilt both targets in isolation with byte-identical objects.
The peer discloses authorship of the earlier sparse-digit dependency.
Stronger combined slack, whole high masks, rank controller, polynomial
converse and internal-ZFC derivation remain open. Equation artifacts,
their decimal numeral, fixed coefficients and unknown names are unchanged.
