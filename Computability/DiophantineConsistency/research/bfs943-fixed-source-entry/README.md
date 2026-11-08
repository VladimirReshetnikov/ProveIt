# A zero-free entry boundary for the direct-BFS943 word layer

The promoted trace75 closure reaches halting from a positive 75/402 zero
through the word layer `Trace75BFS*` (`Trace75BFSModelHalt.graph_halts`). The
word layer touches the algebra of the zero only through three entry lemmas,
`Trace75FixedSlots.graph_fixed_slots`, `Trace75FixedDigits.graph_fixed_digits`
and `Trace75FixedCongruence.graph_fixed_congruence`, and those need exactly
four facts about the coordinates `J = v 0`, `F = v 1`, `α = v 2`, `W = v 5`.
This record states those facts as an interface and re-enters the word layer
there, so that a circuit whose zeros cannot be mapped to a 75 zero (the
free charts of package 172) can still reach halting.

## The interface

`Lean/DiophantineConsistency/BFS943/FixedSourceInterface.lean`, namespace
`BFS943FixedSource`:

```lean
structure FixedSource (p : Fin 4 → ℕ) (v : Fin 10 → V) : Prop where
  power : X p v = Exp.exp (rankNat p v)
  mask : v 1 + v 2 < q p v
  transport : ∃ t : V, ((p 1:V) + v 5) * Cnat p v = v 1 + b p v * t
  population : ∃ ℓ : V, q p v = Exp.exp ℓ ∧ 3 * ℓ + 2 ≤ population (rankNat p v)
```

over a model `V` of `𝗜𝚺₁`, with the trace75 definitions
`h = b p v = β J`, `q = h + 1`, `X = W q`, `C = Cnat p v = q - F - α` and
`R = rankNat p v = [h (q - F) + α] (q² - 1) + (MC + q MF) J`. These are
functions of the ports and of `v 0`, `v 1`, `v 2`, `v 5` only; no other
coordinate of `v` enters. The statement is port-generic; the halting theorem
needs the direct-BFS943 ports, as the word layer does.

* **Halting**: `FixedSourceHalt.source_halts p v hp0 hp1 hp2 hp3 hv hz :
  ∃ t, first (ArithmeticMachineRun215.run t) = 0` for `hz : FixedSource p v`
  at `p = ![β, K0, MC, β + MF_native]` (the hypotheses of
  `Trace75BFSModelHalt.graph_halts`, with the 75 zero replaced by the source).
* **Sanity (75 factors through it)**:
  `FixedSourceOfTrace75.source_of_zero` (any ports with `31 ≤ β`, `MC < β`,
  `β + MF < 2β`, `β + 1 = 2^d`, `d ≥ 2`): a positive 75 zero is a
  `FixedSource`; `source_of_fixed_zero` at the BFS943 ports; and
  `trace75_halts_via_source` reproves `Trace75BFSModelHalt.graph_halts`
  through `FixedSourceHalt.source_halts`.

## Modules (all new, in `Lean/DiophantineConsistency/BFS943/`)

| Module | Content |
|---|---|
| `FixedSourceInterface` | `FixedSource`; radix alignment, repunit and population from `power` (copies of `Trace75RadixAlignment`, `Trace75Repunit`) |
| `FixedSourceSaturation` | `Trace75Saturation`/`Trace75FixedSaturation` from the source |
| `FixedSourceSlots` | the three entry lemmas from the source |
| `FixedSourceBFS*` (17 modules) | the `Trace75BFS*` modules that take the zero, copied with the zero hypothesis retyped to `FixedSource p v` |
| `FixedSourceHalt` | `source_halts` (copy of `Trace75BFSModelHalt`) |
| `FixedSourceOfTrace75` | the sanity factorization |

The 17 word-layer copies (`AlignedShift`, `AllBlocks`, `AllBlockWord`,
`Anchor`, `Carry`, `CellShift`, `CleanCarry`, `FieldMarkers`, `LocalWord`,
`Occupied`, `OriginalWord`, `SimpleParity`, `SpatialSuccessor`, `Support`,
`TileMatch`, `UniformDecoder`, `UniformReset`) are mechanical: each original
passes its zero hypothesis only to other word-layer modules and to the three
entry lemmas, so the copies differ from the originals only in module and
namespace names, the type of `hz`, and the redirected entry lemmas
(`FixedSourceSlots.graph_fixed_*`). `FixedSourceBFSLocalWord` keeps the
original definitions `Trace75BFSLocalWord.Word`/`field`, which
`Trace75BFSModelWordTransfer` (not copied, zero-free) consumes; the other
zero-free modules (`Trace75BFSFieldCastBridge`,
`Trace75BFSModelWordTransfer`, `Trace75FixedSlots.increment_digits`) are
reused unchanged. The promoted `Trace75*` modules are not edited.

Each module's `#print axioms` is `[propext, Classical.choice, Quot.sound]`.

## Client

`research/ten-positive-p172-82-endpoint` (package 172's 82/240 free-plain
circuit), whose zeros have no 75 counterpart with the same `A` and `k`.
