# Exact decimal215 represented arithmetic machine — author receipt

All three new modules and their focused checks passed fresh private Lean
replays. They bind the literal `DecimalMachine215.machine`, whose complete
715-digit decoder and 430-action conjugacy remain unchanged. The packet
contains no free machine parameter at its public actual-machine endpoints.
This is an author review and validation receipt, not an independent review of
my own new proofs.

`ArithmeticMachineGraph215.literalRows` is the list of both typed transitions
for each of the 215 actual states. `lookup_ofFn` proves generic structural
lookup; `literal_lookup_actual` specializes it to every actual state and bit.
No repeated 430-action decimal evaluation or replacement table is needed.
Every typed action code lies in 1..864, so zero remains exclusively the absent
lookup code. The bounded arithmetic graph reuses the existing, read generic
lookup semantics over every IOpen model.

`ArithmeticMachineStep215` proves its bounded arithmetic step agrees with the
actual numeric machine step for every natural configuration code. Halted
state zero and invalid active codes above 215 are absorbing configurations.
A valid action entering halt still writes and moves. Focused checks evaluate
the actual decimal action125 (state62, bit1), which writes1, moves right and
returns `none`; its arithmetic action code is4. Separate left/erase and maximum
action-code controls cover the opposite direction and the upper bound.

`ArithmeticMachineRun215` constructs a Sigma1/Delta1 primitive-recursive run
graph that is total and unique at every index of every IΣ1 model. At every
ordinary natural time, `run_nat` agrees with the exact numeric run and
`run_represents` supplies the actual whole-tape zipper and absolute head.
`haltingSentence` is a closed, parameter-free Sigma1 sentence with standard
truth equivalent to actual blank halting. IΣ1 and PA prove the separate closed
run-totality sentence. These results do not prove an internal machine/validator
consistency calibration, an HA consistency equivalence, or an internal proof
of the equation theorem.

The first graph attempt failed before elaboration because the broad decoder
import brought mathlib's Matrix.map into the Foundation vector Matrix.map
environment. Root reviewed and authorized the single import-line replacement
recorded below. The remainder of the decoder, including every declaration and
proof body, is byte-identical. Its full main and existing checks were replayed
before using it in the new graph. No vendor or Foundation source was modified.

- Old DecimalMachine215 source:
  `da9e49c1a5f47a10d1f385810e1e89d2e3f4f25fc438dc85cf2184efdc3c719a`.
- New source:
  `00e46d6917bb18090027bece970a7ad1bc6eb691bd35c682d4be1a5332f82f80`.
- Import change: `Mathlib.Tactic` to
  `Mathlib.Algebra.BigOperators.Group.Finset.Basic`.

The final eight source/object pairs are:

| Module | Source SHA-256 | Object SHA-256 |
|---|---|---|
| `DecimalMachine215` | `00e46d6917bb18090027bece970a7ad1bc6eb691bd35c682d4be1a5332f82f80` | `d3a3e00a4cd47a0a147cf51f35f2dba60266a0790cc118a84b89a7519f2d1a06` |
| `DecimalMachine215Checks` | `8aa431e5c18b2aa3183838b6f0878561a454a59b2a9f161e7838313727388b9f` | `d423de0188c58d2107e258129b077449473356e57f124e3983b60e8c9d628c53` |
| `ArithmeticMachineGraph215` | `bd2bef54c8ba0c1b59dec84d1797edb68d122467e73fc743ef71e5c4ab2acaad` | `1ed8daa49345ccc097335d666cd9232215345e317d49bd330c86a5e795d48287` |
| `ArithmeticMachineGraph215Checks` | `f3a0a28ed32d170ebdd6406008fbea025e068bdbb870a2fbb6eb3145f2fcf11d` | `8bfc9b66d2d29ef1dddb9af19f95874b5af10bbaa4231f50f378bc6fa6d10bc8` |
| `ArithmeticMachineStep215` | `c04419c271a006d9e1526b75e86fb08de176be5589867abf6f7f2b1093ba7c37` | `e57d6436e5841a0dc7232c8583687845d8a4243114bbce94cef07b0c62c24e2e` |
| `ArithmeticMachineStep215Checks` | `b510f7c4c35f966c45f7691db7959aec4d9b84bb5487c6d76d509c733253502f` | `97bc5683397ccd3e76d6610080f86db63c97f039e35608a61a31879986b56974` |
| `ArithmeticMachineRun215` | `98f0c7004ac5796616bd3d7967a5bed443e7add149456813a0fd2d152a3751cd` | `bf73d9940d0f88a6ec391c02f6581e5e2d15667ba26f268168435cdfa3d29887` |
| `ArithmeticMachineRun215Checks` | `68ddcbfc29e20bbd6a0f0014a599b13e62160f15e41ec7f38ea2014b6ade5aa5` | `acc3cc0d1ba34ff34f36d0a418b4fb9d99de738a185dad796a652d5e68341f98` |

Private machine overlay: `/tmp/arithmetic215-actual-private/lib`. The commands
were recorded individually and used the exact Lean4.32 executable, `-M6000
-j1 -DElab.async=false`, and only the private overlay plus explicit external
package paths. Shared project objects were excluded and left unchanged. All
eight final commands returned0; all four main logs are empty. The new focused
checks have 22 axiom reports, and the existing decoder checks have two. Every
report uses only `propext`, `Classical.choice`, and/or `Quot.sound`. There is no
`native_decide`, new axiom or unfinished proof. Final machine replay time was
29.21 seconds in aggregate; maximum RSS was 2,075,828 KiB. No cap was raised.

Development failures are retained in the evidence archive: the initial Matrix
import collision, an explicit `literalRows` unfolding needed in the final
lookup proof, focused-check namespace ambiguity, and a concrete-state type
annotation before `decide`. All were terminal failures before correction; no
live proof process was restarted. The final run module additionally exposes
the whole-tape `run_represents` corollary and was freshly replayed afterward.

The cache boundary is explicit. There are 132 selected custom modules:
124 reused prerequisites and eight freshly replayed machine leaves. The
reused prerequisites comprise 95 Foundation modules authenticated against the
central source checkout `32e1a0956a8622fad067328ca1959729a7634428`, 12 arithmetic
BusyBeaver modules authenticated against the retained Rotation240 receipt,
and 17 unchanged modules authenticated by the prior native closure receipt.
For Foundation, all 95 source hashes and 380 output-companion Lake hashes were
independently recomputed and matched the actual Lean4.32 build traces: 475
checks, zero mismatches. This is cache provenance, not a fresh Foundation
proof replay. The 41 direct external imports are separately pinned as an
explicit precompiled package/toolchain boundary. No broad prerequisite
rebuild or shared cache mutation occurred.

Root also requested a separate regression of the existing native equivalence
endpoint after the decoder import repair. A new overlay,
`/tmp/current-positive-zero2011-decimal-import-regression`, links the retained
15-command refresh objects and substitutes only the fresh decoder object.
It freshly compiled CurrentPositiveZero2011 and its checks, both exit0,
with unchanged intermediate clients explicitly reused. The six endpoint
axiom reports are unchanged and standard-only. Both newly built endpoint
objects are byte-identical to the previous objects:

- Main `629d9b6e21a33c0ddaa9d61e067a3c47e0435cb146fb30f6bab259b4026b68c0`.
- Checks `c74a78cec6457027befbf2219859e18df01117875ba4dff0c11a8b5ed34524b3`.

The regression used 6.22 seconds and at most 3,359,272 KiB RSS. It is a two-leaf
regression, not a new full native dependency-closure validation. The original
09eaa closure and later five-source/15-command refresh stay unchanged as
historical, separately scoped receipts. The broad project umbrella is not
extended by this packet: unrelated wide mathlib imports may still conflict
with Foundation if combined there.

Durable evidence is in `arithmetic-machine215-replay/`: the current and initial
prerequisite inventories, all final source/object/log records, all development
logs, exact 95 Foundation build traces, independently computed Lake hashes,
the historical Rotation240 verification receipt, drivers and the separate
native regression state. No compiled objects or large package caches are
copied into the repository.

- Final machine receipt JSON SHA-256:
  `0c8b1f3057fea9887a9273a56d3234dd97b69a36305f4dd8541405cef5a7d27d`.
- Bundle manifest SHA-256:
  `6b75ab91c765b39aaa10c434f70bcb5b06cce2b453332d574fc5ee75e882b816`.
- Separate regression state SHA-256:
  `85a6f2f0a5c0ca5fffaaa0db7063269a8e71d2c53facde94453a7b5a4826d668`.
