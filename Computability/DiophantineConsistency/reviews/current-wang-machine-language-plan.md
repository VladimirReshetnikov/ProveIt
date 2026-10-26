# Actual942 Wang language: remaining Lean scope

This is a read-only scope audit and implementation plan. Proposed definitions
and theorem names below do **not** yet exist. No Lean source was edited or
executed, and no complete native/machine equivalence is claimed.

## What is already proved

Paths in this table are relative to `Computability/DiophantineConsistency`.

| Existing file and exact API | Proven fact; boundary |
| --- | --- |
| `Lean/DiophantineConsistency/DecimalMachine215.lean`: `action`, `machine`, `stateEquiv`, `action_conjugacy`, `commutes`, `blank_halts_iff_dense` | The actual715-digit reverse-discovery decoder gives all430 actions and is explicitly conjugate to the checked dense215 machine. It is not the same state numbering. In particular `stateEquiv_one` sends current1 to dense93. |
| `Lean/DiophantineConsistency/WangTiles942Data.lean`: `action_eq_decoder`, `targets_eq_decoded`, `rail_eq_decoded` | Every action, both complete direction-target sets and the exact printed rank-based rail colors are authenticated. No tiling semantics follow merely from those finite equalities. |
| `Lean/DiophantineConsistency/WangTiles942Core.lean`: `Tile`, `transitionRow`, `copyRows`, `signalRows`, `tailRows`, `indexedRows`, `orderedRows`, `tile` | The complete actual942-row table in `(west,north,east,south)` order. `transitionRow_eq_decoded` binds transitions to the literal decoder; `row_indices_exact`, `ordered_rows_perm`, `tile_bounded`, `start_zero`, `initializer_928`, and `actual_first_action` bind enumeration, colors and initialization. |
| `Lean/DiophantineConsistency/WangTiles942Permutation.lean`: `recovered_tile`, `tile_injective`, `physicalEquiv` | Actual table injectivity and the printed floor-rank permutation. These transport indices, not machine semantics. |
| `Lean/DiophantineConsistency/DecimalMachineZFC.lean`: `blank_halts_iff_zfc_refutation`, `blank_nonhalting_iff_conZFC` | The literal decimal machine's blank halt is equivalent to `BProv ZFCax_s [] Form.fBot`; its nonhalting is equivalent to the existing `DiophantineConsistency.ConZFC` (defined in `Bridge.lean`). These are closed machine endpoints, not fixed-port Diophantine calibration. |

The reusable machine definitions are in
`Computability/BusyBeaver/Lean/BusyBeaver/Core.lean`: `Tape.read/write`,
`Config`, `initial`, `Machine.step/run/runFrom`, `run_add_eq_runFrom`,
`runFrom_shift`, and `runFrom_of_halted`. `step` preserves the write and
movement of a transition entering halt; only subsequent steps are stationary.
`BusyBeaver/ZFC/KDenseBridge.lean` supplies the generic `Commutes`, `Rel`,
`rel_step`, `rel_halt`, and `blank_iff`. `KEndpoint215.lean` discharges the
specific machine/refutation side. Neither file supplies Wang row semantics.

Searches of the active Computability Lean sources found no existing marked
Wang tiling, signal-strip simulation, or independently cofinal canonical
rectangle theorem. The current arithmetic modules instead prove actual
mask/word/carry/count/phase facts. Their extraction of all-cell tile matching
and occupation is a separate composition still being assembled; it must
eventually produce the precise language interface below.

The compact54 modules cannot close this gap. `NativePackedMachine54` proves
its different seed equals the dense machine. `NativeModesData54.modeList`
has457 receiver modes; `NativeClauseModes54.local_clause_iff` decodes that
mode layout with extra receiver payloads. Their own documentation expressly
separates local arithmetic from interpreting labels as machine runs. They
are not the current942 table. `NativeZFC` is another closed proof-enumerator
equation, not a theorem identifying the current four ports.

## Retained ordinary contract and exact orientation

The direct ordinary language argument is
`con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/WANG943_COEFFICIENTS.md`,
sections2.1–2.4 (SHA256
`1d0f5a5b77a91070617bacdd63c87de312770e680612115ba2828a112969001d`).
The full388-line counterpart
`con-zfc-diophantine-forms/34-integer14/coefficients/sources/WANG943_LANGUAGE_AND_COMPILER.md`
was also read (SHA256
`4ec0981cc03121b972ff5b8640e46c598f45bae2384656069cb55166b750af3b`).
They describe an ordinary universal proof and finite checks, not a Lean
certificate. Their original machine is densely numbered: initializer
`(3,436,4,188)` has target93. The actual current initializer is
`(3,436,4,4)`, target1, and the current first action is `(true,true,1)`.

The retained transfer is explicit ordinary mathematics in
`INITIALIZATION_CORRECTION.md`, `research/indexed-tile-enumeration/PROOF.md`
§1, `research/admissible942-independent/PROOF.md` §1, and
`research/padding-staircase-independent/PROOF.md` §§1,8–9,11. It consists
of the complete state/typed-color conjugacy, reordered selectors, deletion
of Forbidden, the actual physical rank permutation, and complementation.
Checking transitions alone does not transfer initialization. A direct new
Lean language proof against `DecimalMachine215.machine` avoids formalizing
the old color-conjugacy chain; a transfer-based proof must formalize every
one of those maps, including initialization and seams.

The exact matching convention, independently clarified by
`reviews/padding-staircase2011-directional-terminology-amendment.md`
(SHA256 `978accdfd82602fbdaaa0fffc84919b8c0cd8dbc727ff755e76b366e78a8c7a8`), is

```text
East(i)  = West(i-1),
South(i) = North(i-s).
```

This applies to the original tile colors after inverse complementation.
The right/east neighbor has index `i-1`; forward computation time has
index `i-s`. No tile is reflected or its ports exchanged. The active
physical blocks are West978, North960, East969, South942. The ordinary
proof's two historical East/West naming errors are corrected by that
amendment, not adopted as definitions here.

The older133-line `BLANK_HELICAL_PROOF.md` in the same source directory
(SHA256 `b0595216f23b84b786660aa07e6b0550de68187604a18c14ac1d1a4667cd25e7`)
was read in full. It treats a439-symbol local relation and a huge3-by3
window alphabet, not942 Wang tiles. Its generic strip/helical strategy is
useful, but its local predicate, marker windows, cardinality and stronger
initial left-margin claim must not be silently substituted for the signal
table. The signal-table soundness permits zero left blank cells.

## Precise missing endpoints

Define a proposed `MarkedWord N s a` with `0<N`, `s : ZMod N`,
`a : ZMod N → Fin 942`, `a 0 = 0`, and exactly the two matching equalities
above using `WangTiles942.tile`. No uniqueness of Start, rectangular shape,
coprimality, `s∣N`, or machine-run premise belongs in this definition.
The first missing endpoint is

```text
MarkedWord N s a → KDenseBridge.BlankHalts DecimalMachine215.machine.
```

The pullback `T(x,t)=tile(a(-x-s*t))` has periods `(N,0)` and `(0,N)`
even when cyclic residues collide. The universal soundness proof must then
extract the marked strip: vertical437 boundaries persist; initialization
phase edges force boundaries on both sides of Start; the reset row extends
across the strip; deterministic signal updates simulate the actual machine;
heads cannot escape through a boundary; the first subsequent reset/finish
row forces the unique head to have halted. It must derive the strip's
unique head from initialization, not assume unique Start globally.

For completeness the useful missing endpoint is stronger than existence:

```text
BlankHalts DecimalMachine215.machine →
  ∃ w0 h0, ∀ w≥w0, ∀ h≥h0,
    ∃ a : ZMod (w*h) → Fin 942,
      MarkedWord (w*h) (w : ZMod (w*h)) a ∧
      (∀ i, a i = 0 ↔ i = 0).
```

Choose positive thresholds with `h0≥2`. The construction must retain the
action entering halt, provide two never-visited blank margin cells on each
side, and verify all nine time-shifted seams. Its helical plane is
`G(x mod w,(t+floor(x/w)) mod h)` with periods `(w,-1)` and `(0,h)`;
the cyclic index is `-(x-xStart)-w*(t-1)` modulo `w*h`. Width is enlarged
by blank margins and height independently by stationary halt rows.

This quantifier order is needed by the current2011 controller proof, which
chooses width and height independently as sufficiently large powers of
lambda120199. Merely cofinal total area, equal dimensions, or existence of
some period does not supply that contract. Dummy-bit freedom and actual
rank tuning are later arithmetic constructions; they are not tiling
assumptions or consequences of one bounded seam test.

## Smallest useful implementation decomposition

1. **`WangTiles942Language.lean`: exact family classification and rail decoding.**
   Derive `Allowed t ↔ ∃ i, tile i=t` from `orderedRows`, with constructors
   for the literal transition, stay, receiver, finish, initialization,
   reset and seam families. Prove `action_target_mem`, rail bounds and
   rail injectivity **on the actual direction target sets**, disjoint
   right/left rail ranges, and the structural boundary/control cases.
   Unrestricted rail injectivity is false: absent targets share ranks.
   This finite/structural module is the smallest useful next task and
   requires no assumption about runs or tiling existence.
2. **`WangPeriodicGeometry.lean`: exact word/plane geometry.** Define the
   proposed matching predicates and prove the cyclic pullback and helical
   index identities, including collisions and all boundary cases. These
   are reusable geometric results, without claiming semantic correctness.
3. **`WangSignalRun.lean`: ordinary strip rows simulate `Machine.step`.**
   Encode a finite interval of an actual `Config 215`; prove emitting and
   receiving the same rail implements precisely its direction and target,
   and unrelated tape cells are unchanged. Prove the current initialization
   gives `machine.run 1`, then use existing run/shift/stationary-halt lemmas.
4. **`WangMarkedSoundness.lean` and `WangCanonicalHelix.lean`:** extract the
   finite strip from arbitrary marked periodic data and separately build
   the independently padded one-Start witnesses from a finite halting run.
   These are substantial universal proofs; neither is supplied by the
   existing finite table certificates.
5. **Current arithmetic adapters:** after actual alignment, labels,
   occupation and both directed copy relations are proved, recover the
   unique abstract tile through `physicalEquiv` and feed `MarkedWord`.
   Conversely encode the canonical tiling afresh with complemented labels,
   the shifted Start marker and safe dummy subsets, then prove current
   carry/mask bounds, controller tuning and positive arithmetic witnesses.
   Those converse obligations remain distinct from the language theorem.

Finally the existing `DecimalMachineZFC` theorem composes with the proved
language endpoints. It must not be installed as a semantic-correctness
field supplied to the new theorem, and this plan does not claim an
object-language ZFC proof of the final polynomial biconditional.

Primary active source pins checked in this audit: Wang Data
`ac9047c705dddbab3bec84265beff2d72d498496bde12261cc76c46dc0c5a125`,
Core `7471a9ff93f06d0eb39c2f3791d5db28dd2927e6346213173f38c2b3ea150d85`,
Permutation `3351336105f22baf653dcefb3bd83273924dd539353eebf5f1232da855045cef`,
DecimalMachine215 `da9e49c1a5f47a10d1f385810e1e89d2e3f4f25fc438dc85cf2184efdc3c719a`,
DecimalMachineZFC `778af71680ec6aadd9858d30ace87c25012ac6b9dac02e2a483094401fc06107`.
The retained2011 ordinary proof is
`69ce844ef80894251f4bd9510d9f60468585b4a004f4a624d3b347ce3e144fb8`.
No incoming program was executed, no frozen artifact changed, and no commit
was made. This review records scope, not a newly checked Lean theorem.
