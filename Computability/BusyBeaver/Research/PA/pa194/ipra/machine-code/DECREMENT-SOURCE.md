# Decrement at any source register

`PA194DecrementSource.modelSourceDecrement` binds the existing physical
zero/positive decrement box to all nine logical source registers.  The source
permutation determines the physical slot, and the proved file-split lemma
shows that the returned physical file is exactly the source encoding with
that logical register updated.  The theorem holds in every model of PRA,
including nonstandard models.  It starts at the physical decrement entry
control with the selected source register already marked.  The nonempty
following-file condition required by the zero branch is discharged from the
encoded remaining source registers and the spare register.

`PA194DecrementSourceSentence.nativeIPRA` derives the corresponding
universally closed equality in the repository's native intuitionistic PRA
for each fixed logical register.  Its terms explicitly encode the source
file, finite prefix, selector, predecessor, stepper and clock.  The proof
uses the all-model equality transfer, rather than standard-natural-number
reasoning.  This result does not prove source dispatch, a complete source
instruction, or either machine-specific consistency implication.

Replay using the pinned overlays as for `check-decrement-choice.sh`:

```sh
IPRA_LEAN_OVERLAY=/path/to/ipra/lib \
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/lib \
bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-decrement-source.sh
```

The script rebuilds the decrement boxes, source permutation and new modules
in a temporary directory, checks pinned input hashes and rejects any printed
dependency on `sorryAx`.
