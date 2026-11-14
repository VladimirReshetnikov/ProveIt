# Register-file tape encoding

`PA194RegisterFile.lean` constructs explicit primitive-recursive function
codes for a register block and a finite register file. A register block for
value `v` prefixes the bit pattern `0 1^(v+1)` to an arbitrary numeric tape
suffix. For every fixed standard number `n` of registers, `fileCode n` takes
`n` register values and a suffix; `modelFileValue` proves its recursive
interpretation in every candidate classical PRA model. The values and suffix
may be nonstandard model elements. In particular, `fileCode 9` is an explicit
code for nine consecutive register blocks and an arbitrary suffix; it does not
yet apply the source-to-physical register permutation.

`PA194RegisterFileStandard.sourceFile` proves that, for every ordinary
finite list of natural-number register values and natural-number suffix,
interpreting the code agrees exactly with the binary encoding of the actual
`M6.Runtime.sepsR` list from the imported runtime. The encoding reads the
first list element as the low bit and places the numeric suffix beyond the
list. The checker pins the tracked imported `M6/Runtime.lean` source to SHA-256
`e66961d7acb60e0c84e9674ee2d91ca2049ac6d704ad0edf7d971ef933f3ce2e`.
That hash was also checked against the original PA194 archive member before
that archive was retired. Additional lemmas show that
trimming far-end blank cells leaves the number unchanged, and that reading
the first bit and moving past it match remainder and quotient by two.

The source-list comparison is a standard-natural-number theorem. The
all-model recurrence is separate: it does not interpret nonstandard lists or
establish nonstandard source-to-physical execution, complete source frames,
or either machine-consistency direction.

Replay with the documented dependency overlays:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-register-file.sh
```

The checker regenerates the pinned PA194 table, rebuilds the register-file
modules and their machine-code dependencies, checks selected source and
overlay object hashes, and rejects `sorryAx`. Other transitive prebuilt
overlay objects are assumed to correspond to their recorded sources; the
entire foundation and iPRA chain is not rebuilt by this replay.
