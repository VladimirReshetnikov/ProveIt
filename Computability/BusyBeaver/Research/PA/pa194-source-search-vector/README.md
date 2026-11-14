# Foundation vector lookup for PA194 source search

`PA194SearchVector.lookup_nth` proves that the fixed candidate-PRA pair-stack
lookup code used in `pa194-source-search-model` equals Foundation's vector nth
operation on **every** vector value and index in each candidate-PRA model whose
arithmetic reduct satisfies IΣ₁. Both inputs may be nonstandard. The proof
uses the fixed code's Σ₁ graph and internal IΣ₁ induction; no external induction
on a model element is used.

`find_vector` composes that equality with the bounded-search theorem. Given an
internally valid source formula at every vector position below the bound and a
position whose shift is the target, it finds a position below that bound whose
Foundation source shift is the target. The validity hypothesis is explicit.
Foundation’s bootstrapped LK sequents use finite-set (bit-index) coding, whereas
the verified lookup operates on pair-encoded vectors. No theorem here converts
a nonstandard coded finite set to such a vector, proves preservation of
membership, or supplies the validity condition. In particular, standard list
preimage selection does not by itself establish any of these results for
nonstandard codes. The machine calibration and both reductions remain open.

The final module passed a fresh Lean 4.32 ordered-overlay check against the
fresh source-search and source-shift suffixes and audited project and Foundation
objects. `#print axioms` reported `[propext, Classical.choice, Quot.sound]` for
both main theorems, without `sorryAx`. The full standalone nested replay below
is pending. The source-search and source-shift prerequisites have passed
separate full standalone replays with the audited overlays.

From the repository root, with matching audited project and Foundation objects:

```sh
IPRA_LEAN_OVERLAY=/path/to/project/lib \
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
  Computability/BusyBeaver/Research/PA/pa194-source-search-vector/check.sh
```

The script uses `/dev/shm` by default for temporary objects; set `TMPDIR` for
another suitable temporary directory. It rebuilds the source-search dependency
chain and checks the final module's reported axioms.

An independent suffix replay recompiled this module using the independently
checked search and source-shift objects with the existing prerequisite overlays.
The main theorem axioms matched and did not include `sorryAx`; that replay did
not rebuild the full prerequisite chain.
