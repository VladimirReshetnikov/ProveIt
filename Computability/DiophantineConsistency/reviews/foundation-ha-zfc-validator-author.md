# Closed HA comparison of the fixed translated ZFC and validator sentences

Author: the `circuit_reduction` agent. This is the author receipt, not an
independent peer review. The agent authored the two new leaves and replay
driver, and previously authored parts of the reused HA syntax/arithmetic and
fixed-Nat interface. It did not author the existing closed PA consistency
theorem, the complete Foundation library, or the root's 73-module refresh.

## Exact result

`FoundationHAZFCValidator` proves four closed theorems in the existing
`DiophantineConsistency.HA.Proves` relation:

1. `translated_equivalence` is the existing GG image of the actual closed
   Foundation PA theorem `peano_proves_con_ZFC_iff_validator`, transferred by
   `FoundationHAPeano.peano_provable`.
2. `consistency_to_validator` proves the ordinary HA implication from the
   fixed `FoundationZFCConsistencyNat.ggConsistency` to `ggValidator`.
3. `validator_to_consistency` proves the reverse implication.
4. `equivalence` combines those two HA implications by conjunction.

Here `ggValidator` is definitionally
`FoundationPAHFSyntax.sentence validatorConsistencySentenceᴺ`, for the actual
`ValidatorConsistencyForward254` sentence. The other endpoint is the existing
fixed GG image of Foundation's **ZFC**, including choice, consistency sentence.
There is no supplied PA-proof, axiom-image, stability, model, or validator
comparison premise. The new proofs do not use the fixed-Nat semantic theorem.

The forward and backward proofs reuse the already checked
`FoundationHACurrentTransfer.sentence_imp_elim`; they do not duplicate the GG
recursion or invent an intuitionistic implication rule. The definition of
source equivalence becomes the two GG implication components by definitional
equality, and that existing bridge yields the displayed ordinary HA
implications. Although this dependency also imports the narrow current
equation data, no new theorem mentions the current equation.

## Frozen source and fresh replay

Sources are under `Lean/DiophantineConsistency/`:

| File | Lines | SHA-256 |
|---|---:|---|
| `FoundationHAZFCValidator.lean` | 55 | `d75384f68c3544e71d41aaff4c998016133bc2d8889b6418e2ae5e83ae889936` |
| `FoundationHAZFCValidatorChecks.lean` | 35 | `edbd3f0aeb47045113688dbb802bb361c1885204627b97c1ced3c209bd04d938` |

Both complete new sources and all 277 lines of the replay driver were read
before execution. The source definitions and exact proof chain were compared
with the complete fixed-Nat, CurrentTransfer, Peano, TheoryTransfer and actual
ValidatorConsistencyEquivalence source leaves. The final main and checks
passed on their first execution, with no intervening source changes or Lean
development failures. A preliminary read-only inventory script encountered a
manifest-field schema mismatch; it did not execute Lean or mutate a cache.

The private output directory is
`/tmp/foundation-ha-zfc-validator-574smz61/lib`. Both invocations used the full
actual source pathname, Lean 4.32.0, `-M6000 -j1 -DElab.async=false`, one compiler
process at a time, and a 512 MiB free-space reserve. Only the two new `.olean`
files were written. No symlink output, accepted object, dependency source,
vendor source, umbrella or maintained equation artifact was overwritten.

| Fresh object | Seconds | SHA-256 |
|---|---:|---|
| Main | 2.14 | `8caa54a3d059130cd2156f8d6fee6d0cd98d7712c306762aad7eb8de9f91b5a8` |
| Checks | 2.52 | `98247cc2803a04a993aea4f25566e5746b51634e2967f62c800b1fcadbebee54` |

The main log is empty. All eight checks reports contain exactly the standard
Lean metatheory axioms `propext`, `Classical.choice`, and `Quot.sound`; none
contains `sorryAx` or a new axiom. This metatheory choice dependency does not
add excluded middle to the object-language HA derivation rules. The checks
also bind both literal sentence definitions by `rfl` and expose an actual
closed HA proof at the literal validator target.

## Authenticated reuse and scope

The exact dependency traversal selects **448 cached current-source modules**,
including **139 Foundation modules**, with **57 explicit package/toolchain
boundary import names**. This is the union of the accepted fixed-Nat 410
prerequisites, its accepted main leaf, and 37 already accepted current-transfer
prerequisites/main. It has 865 cached artifact files. No Foundation or other
prerequisite was freshly built in this packet.

All selected current source bytes, source imports, and object/available
companion hashes were checked. Common modules have identical source hashes;
the 97 alternative record representations have identical actual object hash
sets. The accepted fixed-Nat provider takes precedence for common modules.
The driver separately verifies current compiler/toolchain/manifest identity,
reparses every selected import header, constructs dependency order, rejects a
reused module importing either new leaf, and rejects an unresolved custom
import. All 1,874 deduplicated pins match before and after each invocation.
The six package boundaries added by CurrentTransfer retain their prior
primary-object authentication and record their current source and all
available companion hashes explicitly. Package boundaries are reused, not a
claim of a fresh whole-Mathlib or whole-Foundation replay.

The direct summary is `foundation-ha-zfc-validator-replay.json`, SHA-256
`64412d89d65ba2d16cf5beaea8ebc0a2779bc09c7b58df3a75a956c3bd9dbb5a`.
The durable bundle is `foundation-ha-zfc-validator-replay/`, whose
`FILES.json` SHA-256 is
`8876106e7baa702300e734f122db02717aac4141080b2964b7c04d41e9d739be`.
It retains all 13 driver/parent-snapshot/source-snapshot/input/log/result files.
Its terminal result is
`attempt-1793061321466801718/RESULT.json`, SHA-256
`2f96f9a2b89b61c92871e23d2a760437923eff61aeef6dbfac83d6b71954683c`;
the complete input manifest SHA-256 is
`d33f747df8a5f95d1cb52f8eba9b81f7dc95a158dec4fd6f19dee95e39ff04a4`.
The driver SHA-256 is
`b90db1cfa249995f9f8f51c51cce46b583087f307d381e399d02ddb17c956cd8`.

## Boundaries of this checkpoint

This is a genuine closed HA proof-existence comparison of two fixed
**GG-translated** sentences. It does not identify either sentence inside HA
with an untranslated proof checker, assert an HA stability theorem for an
arbitrary arithmetic predicate, calibrate the current 215/222 runtime, or
prove the current equation equivalent to consistency in PA or HA. The
previous standard-Nat interpretation of the fixed sentence remains a
separate result. No current-equation or runtime source was changed.
