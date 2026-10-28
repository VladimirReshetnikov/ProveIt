# Actual HA order irreflexivity — author receipt

Author: `circuit_reduction`; author review, not independent review. The full
new source, checks, build and freeze drivers were read before execution.
Only new owned files/private links were written; no frozen source, shared
object, vendor file, umbrella or Git state changed.

| Source | Lines | SHA256 |
|---|---:|---|
| `FoundationHAOrderIrreflexive.lean` | 73 | `f3db7b05cfad6de290e6f4d58136f47605ca433abecfbed9992cc55c14f00725` |
| `FoundationHAOrderIrreflexiveChecks.lean` | 63 | `7b33fe9ee2dc75d1bc00dec49682431fb1b348c78b80e51c44febd5241820cf9` |

Files are under `Lean/DiophantineConsistency/`. Both first fresh builds
passed with `-M6000 -j1 -DElab.async=false`, enforcing a 512 MiB reserve.
The main log is empty; all 14 final check reports use only `propext` and
`Quot.sound`, with no diagnostics, choice, custom axiom or `sorryAx`.
Private overlay: `/tmp/foundation-ha-order-irreflexive-alwjt7sm/lib`.
Fresh main object:
`b0a5b8bf9e0d183617d3cb25566bd49b315e1c2a824099ab26549eceb959dcfb`.
Fresh check object:
`e62db24a6cd3fc200158a2ceb04eb2d6d3072f0189822784ab60fd6b491db51e`.

The replay bundle `reviews/foundation-ha-order-irreflexive-author-replay/`
contains both invocations, complete source copies/logs and the read drivers.
Dependency manifest SHA256:
`08b2572bb095aebfa848f9c7afe5506def49546603a0b6a90fa0fcb53b46be66`.
Freeze snapshot: `13ecc8d1811d85a46023c286e69623721e13b37d`.

The exact source endpoint is
`FoundationHAOrderIrreflexive.ltIrrefl : HA.Proves
(sentence PeanoMinus.Axiom.ltIrreflᴺ)`.
The source contains a negative relation atom; its GG body is exactly
`not(ltFormula (var 0) (var 0))`, not its double negation. A literal `rfl`
check and a structural negative control bind this distinction.

The proof is genuine HA formula induction. For an arbitrary free-term
parameter `d`, `noReturnBody d` is
`not(var0 + S(renameSucc d) = var0)`.
The base uses actual HA `zero_add` and `succ_ne_zero`. In the successor
step, `succ_add` converts a supposed equality to an equality of successors;
`succ_inj` recovers the forbidden equality at the induction variable, and
the retained object-language induction hypothesis gives a contradiction.
The parameter is shifted under the induction slot and restored by the
checked zero/successor substitution identities. Neither Lean induction on a
standard natural nor a model-semantic inequality replaces formula induction.

`add_succ_ne_self s d` opens this actual universal theorem at arbitrary
terms. `lt_irrefl s` assumes an actual strict-order witness, eliminates its
existential with the entire context shifted, and applies the theorem to
`renameSucc s` and the fresh predecessor variable. Reclosing once gives the
literal named source image. No DNE, order decision, semantic positivity or
Foundation implication-conversion theorem is required.

Checks cover the exact parameter slot, the different zero and successor
substitutions, a negative control forbidding capture of a free variable zero,
nonlinear overlapping free parameters, and a contradiction under both a
hypothetical reflexive-order assumption and a separate open equality.
Every helper and the actual source endpoint has an axiom report.

The private overlay reuses the same 96 authenticated Witnesses prerequisites
used for the separate multiplication leaf, including 76 Foundation modules;
this leaf does not import the multiplication leaf. All selected source,
object/trace and inherited path pins, compiler/package identities and parent
manifest were rechecked before/after builds and at freeze. There were no
new Foundation imports or prerequisite builds. Only this main and checks
are freshly compiled; no broader closure replay is claimed.

The remaining source order image is `ltTri`. Full arithmetic proof transfer
and the final HA consistency/equation equivalence remain separate endpoints.
