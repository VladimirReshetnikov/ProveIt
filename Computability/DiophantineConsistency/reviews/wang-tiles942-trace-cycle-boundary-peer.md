# Trace cycle and boundary: independent peer review

Date: 2026-10-26. Reviewer: `complemented47_review`.

Result: PASS. I read every statement and proof in both main modules
and both focused-check modules, and found no mathematical or binding
gap within their stated scope. All four isolated fresh replays passed.
No source correction is requested.

## Independence and exact sources

The reviewed modules were authored by `circuit_reduction`. I authored
some of their dependencies, including the literal table, actual
initialization, machine encoding, step-color, and action bridge.
I also authored the downstream CycleBand, which is explicitly not
being independently reviewed here. The complete StepConstruction,
FinishConstruction, and TraceBounds sources were read when checking
these dependencies. This is a review of the four listed files and
their mathematical use of the frozen dependencies, not a new replay
of the entire repository closure.

Paths are relative to
`Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.

| File | Lines | SHA-256 |
| --- | ---: | --- |
| `WangTiles942TraceCycle.lean` | 182 | `58ca5b2877426faf6704700f970043526c50873f429e9248552d8bb3019ca17e` |
| `WangTiles942TraceCycleChecks.lean` | 101 | `9934b7b6c05a83704474b842e2f425068ccadd05341b6c86dda0b453662d1081` |
| `WangTiles942CycleBoundary.lean` | 104 | `a2f992dbfd4c14d70b8daf423c0b598d714131c5605cf29c833bc7dc2b808f8f` |
| `WangTiles942CycleBoundaryChecks.lean` | 63 | `938cd83cf5a768a0c1a77f79cb6bb16b2f78b0caabe29f4ecca6ebf174c8aa65` |

## Mathematical review

`runTile t` uses the literal transition construction at a live actual
configuration and the halted pass tile otherwise. Its south colors
refer to actual time `t+1`, including write-before-move entry into
halt; halted configurations subsequently remain stationary. The
proof does not replace entry into halt by a pre-step halted state.

The finite cycle consists of initializer at zero, actual run/wait
rows, finish at `H-2`, and reset at `H-1`. The initializer's output
is actual run time1. Finish membership uses halt persistence and
`T+2≤H`; it is not inferred merely from matching colors. The separate
`3≤H` guard ensures initializer, finish, and reset do not overlap.
The successor is exactly `(k+1)%H`. I checked the initializer-to-next,
ordinary-run, finish-to-reset, and reset-to-initializer cases, at
every integer spatial coordinate. Extra height is filled with actual
halted pass rows, so height can grow independently of spatial margins.

For the boundary theorem, `halted_trace_box` is used at both `t` and
`t+1`. Consequently neither the old head nor the actual moved head
can occur at or beyond `±(T+1)`, and the tape there reads false.
Excluding only the old head would be insufficient; the focused
negative control checks the actual first receiver at position1.
This yields the full zero pass tuple in every run row, including
arbitrarily late waiting rows.

The margins `T+2≤L,R` put the first/last interior cells at least this
far out. Initializer left-west color is2. Its right-east color is4
both at the head position1 and farther right; the proof handles the
endpoint `R-1=1` explicitly. Reset gives1 on both sides; finish and
run rows give0. Thus the left code is `2/1/0` and the right code is
its square, exactly matching the actual seam constructor. No
boundary-cleanliness, no-finish, or additional run premise occurs.

The trace-cycle module alone does not choose walls or construct a
finite quotient. The boundary module proves only the actual boundary
facts. Neither claims an equation witness or the complete `Con(ZFC)`
equivalence.

## Isolated replay and checks

The replay used a fresh namespace overlay at:

```text
/tmp/wang-trace-cycle-boundary-peer-1_k40xqg/objects
```

All other existing DiophantineConsistency objects were symlinked
into that overlay; every artifact for the four reviewed modules was
excluded. The new main was built before its checks, and the fresh
TraceCycle object was used by the Boundary replay. Commands used
the `lake env` Lean binary and path, with the overlay prepended:

```text
lean -M 6000 -j 1 -o OVERLAY/DiophantineConsistency/MODULE.olean SOURCE
```

All four commands exited zero. The main logs are empty. The two
fresh main objects are byte-identical to the existing shared objects:

| Object | SHA-256 |
| --- | --- |
| TraceCycle | `e70c5747e8de28b4ab833c21eee2026f1995f6eea67623813b404156cebe246a` |
| CycleBoundary | `744423edc6903da467f6cdd978fa000365dc6c6405641fe95e6577854d54f8f1` |

There were no pre-existing shared check objects. Both focused checks
were additionally replayed with relative source paths; their objects
and logs are identical to the first isolated replays. All four source
hashes and both shared main objects remained unchanged. No shared
object, source, documentation, or git state was modified.

The 17 TraceCycle and 7 Boundary axiom reports use only subsets of
`propext`, `Classical.choice`, and `Quot.sound`; `edgeCode_le_two`
uses no axioms. Checks include missing-height and premature-finish
negative controls, the exact first output configuration, modulo
wrap, independent extra height/margins, squared seam codes, and
actual moved-head exclusion. No `sorry`, `admit`, `native_decide`,
new axiom, or incoming program execution was used.

The complete command/hash receipts are:

- `/tmp/wang-trace-cycle-boundary-peer-1_k40xqg/receipt.json`, SHA `80cd5ca724a2a9cc3a8368c85ec339d97feef00726ba8d75dd82d29baba63178`;
- `/tmp/wang-trace-cycle-boundary-peer-1_k40xqg/relative-checks-receipt.json`, SHA `217cdc2a9db8791a5185623d55602f0012db3b931c181c7c0690c5ce3ca624b0`.

The focused logs have SHA `3a480314632476e91c8afe212332e7e0c92a76d6461ea401e2c2769bdb398353`
(TraceCycle) and `7e138a58890b576b408a40c8529258beb3b472a87f26be559885f05357ae1245`
(Boundary).
