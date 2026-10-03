# Complete streamed Grill arithmetic packet

This is a fixed numerical source and complete arithmetic composition, with a source-parametric proof conditional on pinned U15/native theorems. It preserves the independently reviewed literal/semantic packets in their earlier directories. No upstream Python was executed and no public repository changed.

## Result

- Fixed Grill program:397,488 phases,24,300 positive runs; full `grill_program.u32`
- Complete DAG:3,600,546 binary arithmetic gates =803,517 multiplications +2,797,029 additions/subtractions
- Positive existential coordinates:797,135
- External positive coordinates: ordinary x and five program parameters fixed for the represented c.e. set
- Comparisons:86 nonunit comparisons plus the unit condition, all in `U*(1+sum r²)-1`
- Formal degree upper bound:71,731,007; no exact-degree claim
- Every emitted gate and every supplied coordinate is live

The universal language statement is only for x>0 and the explicitly constructed valid program slices. See `FULL_COMPOSITION_PROOF.md`; arbitrary positive parameter tuples are not claimed to encode valid programs. This is a new source, not the old205 or16,291/16,289 examples.

## Main artifacts

- `grill_program.u32`, `grill_program.json`: exact little-endian32-bit run table and metadata
- `universal.dag`, `universal.json`: full paid arithmetic stream, constant recipes, coordinate families, comparisons, finalizer and ledger
- `FULL_COMPOSITION_PROOF.md`: valid five-parameter slices, soundness, full positive converse, exact width, halting boundary and cost attribution
- `native_history_proof.md`, `input_PROOF.md`: component-level source identities and complete recoder interface proofs
- `emit_grill_program.py`, `compact_dag.py`, `native_history.py`, `input_loaders.py`, `compose_universal.py`: own reproducible generators
- Frozen native kernel and receipt JSON: all data, not executed upstream programs
- `review_grill_program.*`: independent exact run-table/block/phase/cleanup audit
- `review_complete_*`: independent whole arithmetic stream audit, when frozen
- Root's separate whole-circuit audit: `source://circuit-audit`

The full program SHA-256 is `fa658fcdfe1dae2be3a8e2bf97bd613db59558949ea23ca03f549b77201dad01`.
The full DAG SHA-256 is `a07c1ba41e3a18fafd05c19b8ac39211b0475e30ed8a08ddf43c45a9f5f440f2`.

## Stream format

`universal.dag` begins with eight bytes `CDAGv1\0\0`. Each following17-byte row uses little-endian struct `<Bqq`: opcode0 addition,1 subtraction,2 multiplication; two signed64-bit operand handles. Gate IDs are implicit0-based row indices. A negative handle refers to constant recipe `-handle-1`; a handle at least2^50 refers to positive supplied coordinate `handle-2^50`; any other nonnegative handle refers to an earlier gate.

The JSON manifest explicitly lists compact input families and separates external parameters from positive existential witnesses. It defines every exact fixed numeral using integer strings, fixed powers of2, fixed geometric sums `(4^n-1)/3`, or constant-only +,-,* recipes. A constant recipe can never reference an input or a gate. Runtime powers and repunits emit and charge ordinary gates. This representation avoids enormous repeated decimal literals without hiding a variable exponentiation operation.

## Reproduction and limits

Current generators use the frozen literal table in the sibling research packet, with an explicit SHA guard. The current directory plus that preserved input packet is required until the later portable bundle is prepared.

    python3 emit_grill_program.py
    python3 compose_universal.py --size 397488

The default limits are6,000,000 gates,200,000 constants,600 seconds and1,800 MiB peak RSS. Full emission plus liveness checks took5.47 seconds and107.5 MB peak RSS in the recorded run, producing61,209,290 source bytes. Truncated prototypes are labelled resource fixtures, not universal instances. Manifest execution-time fields may change on replay; source DAG bytes and mathematical metadata are deterministic.

For component and independent checks, use the corresponding `native_check.py`, `native_backend_check.py`, `input_verify.py`, `review_grill_program.py`, and `review_complete_*` entry points. They execute only this packet's own code and read pinned upstream receipts as data. They do not construct astronomical complete positive Pell witnesses.

Do not execute the historical large in-memory builder unchanged. It duplicates huge coefficients and retains quadratic phase-prefix polynomial caches. The new emitter uses exact numeral interning, streamed numeric rows, iterative structural/degree/liveness checks and a linear prefix-sum identity proof.
