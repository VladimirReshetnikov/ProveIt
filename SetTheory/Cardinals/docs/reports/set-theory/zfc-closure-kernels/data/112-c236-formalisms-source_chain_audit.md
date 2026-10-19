# Independent audit of the inherited source and logical seed

This review concerns the inherited logical interface used by the team's new
236-state construction. It found no missing hypothesis at the source/seed
boundary. It is a source-level mathematical audit and static-data replay,
not a new build of the entire Lean ancestor library.

## The exact seed is explicitly covered

The packaged `LogicalSeed246.lean` defines

`seed = (np,tw,ws,ac,p1,p2,s1,s2,pl) = (3,0,0,0,3,0,0,0,0)`.

`L2.enc` sends these nine fields to logical registers 0 through 8 and sends
every later logical register to zero. The module's actual theorem
`halts_iff_native_refutation` applies
`DirtyProgram254.six_nonformula_path_iff 3 0 3 0 0 0` after the original
decoder/program bisimulation. It is therefore the exact displayed seed,
not merely the original public `nextproof=2` seed, that is calibrated.

The inspected definition of `DirtyProgram254.Safe` requires exactly
`C254(st.tw)`, `C254(st.p2)`, and `Enum254.Good(st.ws)`. In this family those
three fields are zero, and the proof supplies `C254.truth`, `C254.truth`,
and `Enum254.good_zero`. The six other fields are arbitrary natural numbers.
Thus the two nonzero 3 values impose no additional invariant obligation.

## Source theorem chain

Each of the first four comparisons below quantifies an arbitrary complete
register function and starts at the empty path:

| Comparison | Actual theorem |
|---|---|
| Rotation240 source to Rotation244 source | `SourceRotation240.program_halts_iff` |
| Rotation244 source to Routing245 source | `SourceRotation244.program_halts_iff` |
| Routing245 source to the public decoder program | `BisimRouting245.program_halts_iff` |
| Public decoder program to the 219-node structured program in path form | `Bisim254.prog254_halts_iff` |
| Exact safe seed to native-theory refutation | `LogicalSeed246.halts_iff_native_refutation` |
| Native-theory refutation to ZF refutation, in both directions | `WFTheory.native_refutation_iff_zf` |
| ZF refutation to ZFC refutation, in both directions | `ConstructibleChoice.zf_refutation_iff_zfc_refutation` |

The packaged `reference/pinned_CalibratedRotation240.lean` composes these
interfaces and states the exact source/seed endpoint as
`CalibratedRotation240.halts_iff_zfc_refutation`. The node-data files
`ProgramRouting245.lean` and `ProgramRotation244.lean` correctly avoid
claiming these whole-program theorems on their own; the comparison modules
supply them.

`WFTheory` uses the internally well-founded part of the native quotient and
first-order soundness/completeness. `ConstructibleChoice` uses the
constructible substructure of a set-coded ZF model, then the same finite-proof
soundness/completeness comparison. These are the inherited ordinary
mathematical arguments supporting formalizability in ZFC. This audit does
not replace them with a reflection claim that arbitrary Lean proofs are
automatically theorems internal to ZFC.

## Exact static-data replay

The inherited extractor was replayed on the files actually present in the
new package. Its default paths refer to folders not included in that trimmed
copy, so the retained explicit inputs must be supplied:

```sh
python3 -B upstream/zfc237/source_interface/check_source_interface.py \
  --sites upstream/zfc237/source_certificate/baseline_sites.json \
  --blank-prefix upstream/zfc237/inputs/boundary239_blank_prefix.json \
  --output evidence/source_interface_replay.json
```

The replay passed all 6,455 ordered leaf occurrences, the 8,386 guarded
descriptors, all 203 literal lookup indices, the rotation row overrides, and
the exact seed encoding. Its receipt from this independent audit is
`generated/logical_source_interface_audit.json`.

The physical seed is `(0,0,0,3,0,0,3,0,0)` followed by 167 spare registers of
value 1. The inherited literal frame has empty source path, head -5 and
header distance 181. This static check identifies that frame and its seed;
the new candidate's finite blank startup is verified separately by the
team's complete-tape startup proof. The inherited extractor's 409,691-step
field belongs to the original rotation240 startup, not to the new candidate.

The original logical source byte hash is
`74b1e7f73cc3ffe7761e36ab2d57a26e0ba34d3ac624f2472799e6ac41d5a51d`.
The inherited 25-rotation certificate maps it to
`7fd152d1f5371d2a561d4ad1870d241683b010ce7b7a27399b95363a4537cfb6`.
The new closed-block rotation maps that source to
`1ebe9691507b2d3236951a31d6b9a7ef548a2cdf90525cd57051992f8ac2626f`.
Each source comparison preserves the ordered register actions and all
actual guarded successors, with the corresponding change of leaf paths.

The packaged `LogicalSeed246`, `SourceRotation240`, `ProgramRotation244`,
`ProgramRouting245`, `WFTheory`, `ConstructibleChoice`, and pinned
`CalibratedRotation240` files were also compared byte-for-byte with the
read-only ProveIt checkout and all matched.

## Limits of this audit

The new finite-table and source certificates are ordinary proofs about
concrete effective objects. Combining them with the inherited source/logic
calibration supports the requested ordinary ZFC-provable equivalence. The
audit does not claim a newly compiled Lean theorem for the 236-state table,
a serialized proof inside PA or ZFC, or a fresh verification of every
dependency in the model-theory library.
