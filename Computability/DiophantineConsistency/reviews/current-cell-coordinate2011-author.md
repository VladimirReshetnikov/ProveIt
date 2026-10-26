# Exact cell-coordinate arithmetic: author receipt

This records the complete author read and fresh kernel builds of the new
coordinate extension and its focused checks. It is not an independent peer
review. No frozen dependency, existing documentation or umbrella file was
changed, and no git mutation command was run.

## Frozen files

Paths are relative to `Computability/DiophantineConsistency/`.

| File | Lines | SHA-256 |
| --- | ---: | --- |
| `Lean/DiophantineConsistency/CurrentCellCoordinate2011.lean` | 147 | `6e316a7a9a0107e8bc2bc41bf2bcd5868251b297f0b5cd7c79b64a52da1e9f48` |
| `Lean/DiophantineConsistency/CurrentCellCoordinate2011Checks.lean` | 92 | `4149684d1c8c344e8357ba3831c2627875cf55cdca1f37ec6566006dd73f30be` |

The main module imports only `CurrentCellCycle2011`, SHA-256
`874a68dc11255170f19dc1a5345e195f36379711f8af630b16dd6eb9fe77081d`.
The check module imports the new main module and `CurrentAdjacency2011`,
SHA-256 `160cef12e27cda2ece581ba0acfb2fcbbf194d918fe75d630705a7feb8e97133`,
to check the exact independently defined spatial and temporal base functions.

## Proved interfaces and mathematical scope

The ambient assumption is `[NeZero (N*2011)]`; positivity of N follows from
the frozen cycle module. No native `Facts`, occupation, tile, mask, or
target-equivalence assumption appears in the new results.

The canonical coordinate is identified with the cast of its physical
quotient index. It preserves zero, and its inverse sends a coordinate j
to the exact field base `cast(j.val*2011)` in `ZMod (N*2011)`.

The key cancellation lemma scales both representatives **and the modulus**:

```text
cast(a*2011) = cast(b*2011) in ZMod(N*2011)
  ↔ cast(a) = cast(b) in ZMod N.
```

It uses `Nat.ModEq.mul_right_cancel_iff'` and requires only that 2011 is
nonzero, not that it is coprime to N. Its nonzero specialization is exposed
as `scaled_cast_ne_zero_iff`, for transferring a nonzero physical temporal
shift to a nonzero cell stride. These two cancellation lemmas do not even
require the ambient nonzero-modulus instance.

`coordinate_add_of_physical` transfers any actual addition of `s*2011` in
the full physical word to addition of s in the cell coordinate. It gives:

- `coordinate_next`: the actual spatial successor becomes addition of 1.
- `coordinate_previous`: the actual predecessor becomes subtraction of 1.
- `coordinate_theta`: `theta (2011*s)` becomes subtraction of s for every
  natural s, with no bound relative to the word length.
- `coordinate_symm_sub`: the corresponding inverse-coordinate identity.

`subtractFullCell t ht` is the literal aligned subtype with underlying
value `b-cast(t)` when `ht : t%2011=0`. Its equality with the existing
`theta t` is proved, and `coordinate_subtract_of_physical` also accepts
any independently constructed aligned subtype with the same physical
value. Thus the proof term establishing alignment is not a binding
restriction. Its coordinate is `coordinate b-cast(t/2011)`.

`coordinate_temporal` specializes this to the actual shift `t=W/47` and
uses precisely the quotient `(W/47)/2011`. The focused checks construct
the subtype from `CurrentAdjacency2011.temporalCell W b` and its actual
alignment theorem and prove this exact formula. A separate check does the
same for `CurrentAdjacency2011.previousCell`. Neither check assumes any
native word or decoded label premise.

Further checks include inverse-coordinate formulas, adding arbitrarily
many complete periods to a stride, nonzero-stride transfer, and the
singleton cycle N=1. These results provide exact coordinate transport;
they do not assert a marked word, tiling or consistency equivalence.

## Reproduction and axiom audit

Both complete sources and every subsequent check-only correction were read
before execution. The main passed its first build. The final commands,
run sequentially from the repository root, both exited 0:

```sh
lake env lean -M 6000 -j 1 -o .lake/build/lib/lean/DiophantineConsistency/CurrentCellCoordinate2011.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentCellCoordinate2011.lean > /tmp/current-cell-coordinate-stage1.log 2>&1
lake env lean -M 6000 -j 1 -o .lake/build/lib/lean/DiophantineConsistency/CurrentCellCoordinate2011Checks.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentCellCoordinate2011Checks.lean > /tmp/current-cell-coordinate-checks-stage3.log 2>&1
```

Both files disable asynchronous elaboration. These commands rebuild the
two new modules against existing frozen dependency objects, not the whole
import closure. The main log is empty with SHA-256
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
The final checks log has SHA-256
`08cb5c425ebda9acaf6709a80ac1846d7c91f813bb4da51a5c852c45d3f5d2b8`.

The first check run needed explicit N and coercion annotations in its two
independently defined adjacency subtype expressions. The second needed
the positive, rather than nonzero, numerical hypothesis expected by
`Nat.div_self`. These were check elaboration corrections; the frozen main
source and mathematical scope were unchanged.

All 17 final axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`. No new axiom, `sorry`, `admit`, `native_decide`, or executable
certificate occurs in either new source.
