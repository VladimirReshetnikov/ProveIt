# Concrete review of deleting scanner state 50

The proposed change deletes native state 50 from the accepted K217 table and changes the zero transition of native state 34 from `(0,L,50)` to `(0,L,75)`. This leaves 216 working states. It fails the inherited primitive simulation on a frame attained by the accepted source execution. The failure is not an artifact of allowing arbitrary independent registers in the universal runtime checker.

From the accepted initial source frame with registers `[3,0,0,0,3,0,0,0,0]`, gap 80, 130 one-valued spare blocks, and head −5, literal source execution reaches ordinal 40 after 1,474 primitives. The instruction is `CD 1`, at path `11101001001000000`, with a zero guard. Its frame has registers `[7,0,0,0,4,0,0,0,0]`, gap 495, 546 one-valued spare blocks, and absolute head −9. The checker reconstructs every intervening register operation, control transfer, gap increment, and spare append.

Both machines are then run literally, using a set of one-cells, from this exact frame. The tape coordinates in the receipt are relative to its head.

| Table | Microsteps to clean redispatch | Next source ordinal | Tape difference from required result |
|---|---:|---:|---|
| Accepted K217 |4,546|43|None|
| Shortened scanner |4,622|66|Cells 13 and 15|

Both outputs retain the input register values, gap, spare count, and relative head 0. The discrepancy is the source pointer. During the zero-decrement return, cells 11 through 17 form a run of seven zeros, with a one at cell 10. The accepted scanner reaches state 50 on that one and resumes scanning left. The shortened scanner reaches state 75 there and falsely treats that internal one as the left boundary, dispatching inside the source pointer. The compact receipt includes the exact local trace fragment and hashes of both complete traces.

This is a counterexample to the intended primitive refinement, including a source-reachability witness under the accepted implementation. It does **not** show that the altered machine reaches this same frame from blank, and it does **not** prove that its blank-tape halting predicate fails to be equivalent to inconsistency. Any such use would require a different proof.

## Reproduction

Python 3.10+; standard library only; assertions must be enabled. The checker imports no repository code. It verifies the SHA-256 of the accepted table and source files before executing them as data.

```sh
python3 -B review_short_scanner.py \
  --baseline /path/to/ProveIt/Computability/BusyBeaver/Research/ZFC/candidate-k217 \
  --output short-scanner-counterexample.json
```

Alternatively supply `--table /path/to/k217.native.tm --sites /path/to/sites217.json`. Add `--full-trace` to retain every microstep; the default receipt contains complete sparse input/output tapes, decoded output frames, trace hashes, and the short scan fragment. The finite search caps bound the computation of this explicit witness; there is no unbounded correctness claim for the shortened table.
