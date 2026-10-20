# Rejected compilation of a proved source specialization

**`rejected_reuse_e.native.tm` is not a valid new construction. Do not promote it into the machine catalogue.** It is included solely to reproduce a concrete compiler failure that arises despite an exact source proof and passing decoder binding.

The source replaces the known-one contradiction comparison by a predecrement and comparison with a proved-zero register. Its all-natural source argument and independently checked invariant are in `../audit/halt_specialization.md`. The full source still has 206 DAG nodes, but the raw incremental compiler changes native row `(38,0)` from `0 R 13` to `0 R 303`. That row is also an arithmetic-helper entry used outside the changed source region.

The ordinary CI5 primitive at source address `111010010010011110` reaches `(38,0)` with a small zero-background frame and is corrupted. The exact baseline blank-start endpoint also fails. Thus this raw 219-state table is rejected before it can support any consistency-equivalence claim. `decoder_binding_only.json` records a necessary but insufficient check, and `rejection.json` states the decisive failure.

`patch38.cpp` tests every write, direction, and existing target for row `(38,0)` while keeping the other raw rows fixed. It accepts relaxed auxiliary tape details but requires the correct logical counters and source continuation at every tested primitive. All 876 attempted repairs fail; the best passes 98 of 6,168 finite cases. This is a narrow synthesis failure, not an impossibility theorem for context-sensitive repairs.

Build with a C++17 compiler. The command-line inputs are the raw `.tm` file, a source file with one `path opcode integer` row per line (convert null CH arguments to `-1`), and a chosen output file for hits. The recorded search uses the supplied source JSON. The `blank_start_rejection.log` is the recorded assertion failure when comparing the raw table against the baseline startup endpoint; it is not an assertion that no different valid startup could exist.
