# Increment at any source register

`PA194IncrementSource.modelSourceIncrement` binds the existing physical
increment box to all nine logical source registers. Its input has the nine
permuted source-register blocks followed by a blank suffix, with the selected
register already marked. Its output has the selected logical register
incremented, the other eight unchanged, and an appended one-valued spare
block followed by a blank suffix. The theorem includes an explicit clock and
holds in every model of classical PRA, including nonstandard models. The
arbitrary starting model values supplied for the spare and suffix are ignored
and replaced by one and zero in the encoded output.

`PA194IncrementSourceSentence.nativeIPRA` derives the corresponding explicit
universally closed equation in the repository's native intuitionistic PRA for
each fixed logical register, using the all-model transfer. It does not prove
source dispatch, a complete source instruction, or either machine-specific
consistency implication.

Replay using the pinned overlays as for `check-decrement-source.sh`:

```sh
IPRA_LEAN_OVERLAY=/path/to/ipra/lib \
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/lib \
bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-increment-source.sh
```

The script rebuilds the physical boxes, source permutation and new modules in
a temporary directory, checks pinned input hashes and rejects any printed
dependency on `sorryAx`.
