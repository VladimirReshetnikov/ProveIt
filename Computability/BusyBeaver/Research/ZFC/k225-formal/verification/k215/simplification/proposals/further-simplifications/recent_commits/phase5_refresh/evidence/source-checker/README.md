# Ordinary source simulation with an explicit decoder

The source proof now uses ordinary register-count bisimulation. Every one of the
2,240 K215 certificate offsets was zero, so the offset relation and its integer
arithmetic contribute nothing to this instance. The four-field certificate
retains both coded pointers and both successor indices.

`RMBisim.WithDecoder` shares one ordinary checker soundness proof for an arbitrary
`Nat → List Bool` decoder. Its relation means exactly the paths returned by that
function; no size or injectivity premise is needed. The legacy checker names
remain the 128-fuel specialization. K215 explicitly uses 512 fuel: its second
paths can have 176 bits, and the old decoder changes 622 entries. All five legacy
checker definitions are definitionally equal to retained literal old bodies;
all four old public soundness statements remain exact.

A separate `RMEquiv.fwd` refactor groups the car/cdr simulation cases and composes
runs through the existing `reaches_pre` lemma. Its body falls from 83 to 61 lines;
all other declarations and executable definitions remain exact.

The isolated checks compiled the two generic modules and typed old/generic/512
clients with zero warnings and only standard Lean axioms. An independent negative
control proves axiom-free that 128 fuel changes a concrete 129-bit pointer. The
first generic-checker attempt had only a documentation-comment parse error; its
exact source/log is retained.

The migration peer independently parsed all 2,240 original five-field and new
four-field entries, comparing the entire branch structure, cuts, successor
indices and sentinel codes. It verified all program/tree/WF declarations and
both public source-equivalence statements unchanged. It also read the complete
producer and partition delta. The parent phase5 check owns fresh evaluation of
all 16 certificate chunks and the final 215 endpoint; those are not claimed by
this feature packet. The proposed isolated Data/chunk pilot was cancelled before
invocation to avoid duplicating an 18 MiB object on a nearly full disk.

The decoder refactor follows the supplied `proof_refactor/ZERO_OFFSET_STAGE.md`
proposal in `Proof_Simplification_and_GC-ZC215_2026-10-21.zip` (arrival 05d063acef).
The generic Lean implementation, old-API controls and literal peer are by
`drop_contract`; root authored the four-field producer migration. The earlier
bisimulation and simulation proofs retain their source attribution.

`evidence.tar.gz` contains original/candidate source, complete diffs, producers,
API clients, actual commands/logs/results, immutable-provider bindings and the
literal comparison. It contains no compiled objects. Original commands and
scratch paths are historical evidence, not portable rebuild commands. The
standalone metadata reader checks the archive without running archived code:

```sh
python3 -B review_saved.py
```

`index.json` pins every member; `result.json` states the bounded scope. Full
current-source compilation and compatibility belong to the parent checkpoint.
