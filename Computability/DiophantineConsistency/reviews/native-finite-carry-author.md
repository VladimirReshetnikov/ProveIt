# Finite carry iteration: author receipt

Date: 2026-10-26. Author: `/root/controller_certificate`. This is author
validation, not independent peer review. The original `NativeCyclicCarry`
module was authored by `complemented47_review`; I have authored several
downstream literal-kernel and word-construction modules.

## Frozen packet

| Source | Lines | SHA-256 |
| --- | ---: | --- |
| `NativeFiniteCarry.lean` | 209 | `7c001a01899b691a3288586da781d3338307bd5fa8a8bb90e460e9399babd48a` |
| `NativeFiniteCarryChecks.lean` | 86 | `c4af30ec2a9f5c7407f083bb71e05302b8123f970cece36383d7184c775140d2` |

Both sources are under `Lean/DiophantineConsistency/`. Their complete source,
the original carry module, the finite-sum equality/order contract and the
directly reused digit/reset proofs were read before execution. Final main and
checks passed fresh serial direct builds under `-M6000 -j1`, with
`Elab.async false`. The final main log is empty; the focused log contains twelve
intended axiom reports. Eleven report exactly `propext`, `Classical.choice`,
`Quot.sound`; `iterate_le_prefixed` reports only `propext`. There are no new
axioms, `sorry`, native evaluation proofs, or rejected declarations in the
final packet.

The main's initial build exposed two elaboration problems: inference chose
`Fin (D+1)` instead of natural values for the sum comparison, and an unqualified
addition rewrite tried to rewrite the dependent `Fin` bound. Explicit natural
values and a definitional `change` repaired these without changing the
statements. Moving unused section parameters out then required putting two
doc comments after `omit ... in`. The third main build and first focused build
passed. No memory or heartbeat budget was increased after a failure.

## Explicit algorithm and bound

For a supplied `Fintype ι`, carry bound `D`, and any monotone endomap of
`ι → Fin (D+1)`, `iterate` is primitive recursion from the all-zero vector.
`potential` is the sum of the natural coordinate values. It is bounded by
`Fintype.card ι * D`. The iteration is monotone, equality of consecutive
potentials implies equality of the vectors, and each nonstationary step raises
the potential by at least one.

`iterate_stabilizes` proves the exact equality at indices
`card ι * D + 1` and `card ι * D`. `iterate_stable_after` proves persistence
after that bound. `iterate_le_prefixed` proves that all iterations lie below
any bounded prefixed vector. No inhabitedness assumption is needed, and `D=0`
and empty finite index types remain in scope. The usual bound
`card ι * (base−1)` follows by taking `D=base−1`; the current carry budget gives
the sharper `57 * card ι` bound.

`carries` uses exactly that many applications of the existing literal quotient
update `NativeCyclicCarry.carryStep`. `carries_recurrence` proves the actual
quotient recurrence. `normalization`, `reset` and `predecessor_reset` give the
same bounded-digit/decomposition/local-reset identities for these explicit
carries. The predecessor map need not be injective, acyclic or have a selected
initial field. In particular, the construction handles last-to-first carry.

`budget47` discharges the unchanged envelope
`raw i ≤ 56*2^47 + 2^46 + 1930942` into the budget `0..57`.
`radix47_stabilizes`, `radix47_normalization` and `radix47_reset` specialize
the actual quotient and digit formulas to radix `2^47`. The focused source
also checks the exact index `(N*2011)*57` for `Fin (N*2011)`.

The imported original module contains its previous complete-lattice proof,
but these new witnesses and stabilization proofs do not call `lfp`,
`map_lfp`, `exists_bounded_carries` or `exists_bounded_digits`. Only its
quotient update and generic digit/reset arithmetic are reused. The substantive
new result is a bounded algorithm; this packet does not claim to eliminate
classical Lean metatheory or to contain an internal HA proof.

## Focused controls

The checks cover empty indices, a zero carry budget, arbitrary `base−1`, radix
one, and current `2011*N` field counts. For the cyclic three-field raw vector
`[9,0,20]` at radix ten, the first iterations are `[0,0,0]`, `[0,0,2]`,
`[1,0,2]`; the explicit selected carries and digits are `[1,0,2]` and
`[1,1,0]`. Thus the origin receives the actual wraparound carry, and the middle
reset does not incorrectly force the next outgoing carry to zero.

A separate one-field raw-nine example preserves the ambiguity between
carry zero/digit nine and carry one/digit zero. The bounded algorithm selects
the least vector, but no uniqueness of all cyclic carry assignments is
asserted. No tile, source-solution, native-equivalence or consistency premise
is used in this packet.

## Private dependency and replay boundary

The only custom prerequisite object reused privately was
`DiophantineConsistency.NativeCyclicCarry`. Before copying it, both hashes were
checked against its entry in the existing
`reviews/object-current-equation2011-dependency-replay.json`:

- source SHA-256:
  `25c08e2b6b10e72fe9b3d4df81078e4e1e5ede8e3e94b9666dc5616dcfebc72e`;
- object SHA-256:
  `37e63fd379abc9eeaad12f152925eb0a71aec671b7eeceb19c03759a5671d41b`.

The private overlay is `/tmp/native-finite-carry-author-20261026`, with its
checked prerequisite metadata in `prerequisite.json`. Mathlib uses the existing
pinned Lean 4.32.0 environment; no entire dependency rebuild is claimed.
No new-target object was copied from a cache. The fresh commands were:

```bash
lake env bash -c 'export LEAN_PATH="/tmp/native-finite-carry-author-20261026:$LEAN_PATH"; exec lean -M6000 -j1 -o /tmp/native-finite-carry-author-20261026/DiophantineConsistency/NativeFiniteCarry.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativeFiniteCarry.lean'
lake env bash -c 'export LEAN_PATH="/tmp/native-finite-carry-author-20261026:$LEAN_PATH"; exec lean -M6000 -j1 -o /tmp/native-finite-carry-author-20261026/DiophantineConsistency/NativeFiniteCarryChecks.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativeFiniteCarryChecks.lean'
```

Final logs are `main-final.log` and `checks-final.log` in that overlay.
Fresh object hashes are respectively
`4f524a64546064ab875f084363f60e6114a9157704f3e316cfcd755197777222`
and `cddf87a6cec1d1e4bffc05d56186f286541562b28c604fdb9d8d974d3cabe500`.
Neither accepted dependency objects nor accepted sources, shared documentation,
equation artifacts or Git state were changed.
