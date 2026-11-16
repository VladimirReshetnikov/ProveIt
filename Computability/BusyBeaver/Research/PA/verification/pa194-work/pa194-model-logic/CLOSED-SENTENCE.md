# Packet independence for arbitrary internal PAeq sentences

In every model of IΣ₁, `sentenceTranslate_packets` proves that two valid source-arity-zero packets translate any internally valid PAeq formula `p` identically whenever `shift p = p`, including nonstandard `p`. The proof combines the independently replayed closed-environment theorem with the previously repository-replayed converse `formulaShift_freeBound_zero`. `sentence_root_packet` applies this to the root packet and any valid arity-zero packet, including any identity packet. Neither theorem assumes a packet-length bound.

This is an exact equality of translated formula codes. It does not prove that the source theory derives the translation, establish the guarded theory-axiom rule, or provide an induction-axiom supplier.

Reproduce from the repository root with a fresh empty output:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-closed-sentence.sh "$PWD" /dev/shm/pa194-closed-sentence-repo-NEW
```

The checker rebuilds this source and a two-report axiom audit. It retains the separately replayed closed-environment theorem, repository-replayed shift/free-bound results, and the remaining prebuilt paths enumerated in the checker; it does not rebuild the full dependency closure.
