`mira_backend.py` is a usable assembler for a fresh binary Turing machine built
around Mira-Cult's published single-marker register engine. It accepts the
finite register-program DAG recovered by `recover_wade_dag.py`, or a modified
binary Wade builder. It reads pinned vendored data, emits complete numeric
tables into an outside-repository scratch directory, and charges its own
initializer. It supplies executable compiler evidence; it does not supply a
Lean simulation theorem or calibrate a new machine to consistency of ZFC.

The original 219-node DAG compiles to **408 working states** from nine zero
registers, or **410** when `nextproof` starts at 2. These are larger than the
281-state public Wade-backend baseline. The clean assembler provides an
editable interface for experiments, and does not reconstruct the decoder
rotations, contextual state folds, or compressed boot of the 254-state table.

| Component | Zero-register start | `nextproof = 2` start |
|---|---:|---:|
| Decoder nodes | 219 | 219 |
| Literal engine rows retained | 44 | 44 |
| Arithmetic/control leaf states | 19 | 19 |
| Break scans | 1 | 1 |
| Continue scans | 3 | 3 |
| Fresh initializer | 122 | 124 |
| **Working states** | **408** | **410** |
| Binary transition rows | 816 | 820 |

The public DAG unfolds to 6,460 instruction sites and has maximum path depth
96. Its longest zero run is seven. The compiler chooses a gap of `depth + 6`,
which is 102 here, and the original nine-zero dispatcher. The large direct
initializer is therefore a measured cost. The optimized published decoder
has depth 34; its shape cannot simply be substituted for a modified theory.

Reproduce offline from the repository root:

```sh
python3 Computability/BusyBeaver/Research/ZFC/mira_backend.py \
  --scratch /tmp/zfc-mira-backend \
  --output-evidence /tmp/mira-backend-results.json
```

The two output tables are `dag219-zero.tm` and `dag219-nextproof2.tm` in that
scratch directory. Start state is 0; the only terminal target is the working
state count, with no transition rows of its own. Every working state has both
binary rows. The checked measurements, hashes and provenance are recorded in
[`mira-backend-results.json`](mira-backend-results.json).

The callable interface is:

```python
from mira_backend import compile_dag, compile_builder

machine = compile_dag(nodes, names)  # nodes[0] is the root
# Or: machine = compile_builder(builder) after builder.reduce_to_cons().
machine.check_sites()
machine.save("/tmp/my-candidate.tm")
print(machine.evidence)
```

`nodes[q]` contains two strings of the form `ENode n`, `EInc r`, `EDecnz r`,
`EBreak k`, `EContinue k`, or `EHalt`. Register indices use the nine logical
registers declared in `recover_wade_dag.REGISTERS`. Names are optional
metadata. Unreachable nodes are discarded; cycles, unsupported edges,
register indices outside 0–8, and control levels that escape the root are
rejected. The builder adapter reads binary sequences without changing the
builder and does not call the upstream generator.

The result has `.table`, `.evidence`, `.save(path)` and `.check_sites()`.
The table maps `(state, read_bit)` to `(write_bit, "L" or "R", next_state)`.
Optional keyword arguments are `initial_registers` (nine naturals, default
all zero), `gap`, `dispatcher_threshold`, and `generic_decrement` (default
true). Explicit gap and dispatcher choices must meet the conservative checks
below. Saving inside the repository is rejected, including through symlinks.

The engine's dispatch configuration is

```text
blank  1 | PC 0^(D − |PC|) 1 | concat(0 1^(value+1))  blank
       marker              header
```

The head starts immediately after the marker, at the new root decoder. The
logical registers have physical indices `[6,7,0,2,1,8,4,3,5]`; equivalently,
the physical file contains logical registers `[2,4,3,7,6,8,0,1,5]`.
Every decoder node preserves the bit it reads and moves right into its child.
Arithmetic leaves use two cells after their path to distinguish prepare,
select and execute phases. On 0 a leaf moves right into state 57 for increment
or 30 for decrement; on 1 it writes 0 and moves right into its register's skip
state. State 57 routes `00` to preparation state 42 and `01` to increment
seek 73; state 30 similarly routes to preparation or decrement seek 43.

The skip states for physical registers 0–8 are
`[60,44,31,56,38,40,28,64,69]`. They erase the first 1 of the selected block
and return on the header in state 2 for register 0, otherwise state 6.
Increment returns in 48. Decrement returns in 3 when zero, or 63 for a positive
physical register 0 and 48 otherwise. Positive decrement appends a spare zero
block. The copied engine rows and generated routing are explicit in the
assembler. The relevant published specifications are `coq/tm/Box.v:233–286`
and `coq/tm/Check254.v:12–13` in the pinned snapshot.

Break leaves move left into a scan that erases the suffix through the kth
zero, then enters increment-PC state 7. Continue leaves erase the suffix
through the kth one, then enter cleanup state 10. These implement the same
`inc_path`, `brk` and `cont` path arithmetic used by the recovered register
program. Level zero is supported. Explicit source well-formedness is checked
at every unfolded path rather than inferred from shared-node names.

Two details require fresh routing. The published zero-decrement return reaches
state 5 on the last path bit. Its read-0 action is the desired strip-and-carry
operation, but its read-1 action enters the old bootstrap. Every published
decrement path ends in 0. With `generic_decrement=True`, the assembler changes
read 1 to erase that bit and continue left through the shared break-one scan.
This supports well-formed decrements on right edges too. With the option
false, the unused read-1 row halts and paths ending in 1 are rejected.

The dispatcher counts consecutive zeros while returning left across the PC.
A selection phase adds a zero next to the path, so the compiler requires the
threshold to be at least `max(9, maximum_path_zero_run + 2)`. Longer runs cause
the assembler to extend the counter. The gap is conservatively required to
be at least `maximum_path_depth + 6`. These are implementation conditions
checked by this assembler and its per-site execution, not a proved minimum
gap theorem.

The old blank-tape bootstrap is unusable after replacing its decoder. Literal
simulation reaches state 96 first at step 35, with a gap of only three cells
and no complete register file. There are 1,412 visits to 96 before the
published checked boot endpoint at step 264,982. The new initializer instead
writes the reversed physical register file while moving left, then the header,
the chosen zero gap, and the marker. Its last transition moves right directly
into the new root. Both binary rows are supplied and every initializer state
is counted. The resulting register file has exactly nine blocks and no spare
tail; the engine supports a growing spare tail thereafter.

The source pins are upstream commit
`297ab8df7e5de329605c3875b4934643b371a5e3`, the `Dag254.v` hash already enforced
by `recover_wade_dag.py`, and literal table SHA-256
`d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb`.
No vendored file is edited or executed. The assembler reads the finite Coq
declaration only as data through the existing parser. Its generated evidence
also records the assembler hash and each complete output table hash.

Each baseline variant passes all **8,391 symbolic instruction cases**, including
both branches of all 1,931 decrement sites, with at most 797 abstract executor
steps and four dispatch visits. The checker keeps the excess gap symbolic and
uses an opaque arbitrary register file with the four published box contracts.
It checks the complete successor configuration, including PC, marker position,
gap and register effect, rather than stopping at the first dispatch visit.

Concrete checks separately exercise 864 register-box excursions and 88 whole
instruction traces, including extra gap values 0, 1 and 2. Both initializers
are executed from blank and their complete resulting tapes are compared with
the declared configuration. Output tables are independently reparsed and
compared row for row. The offline regressions include four small machines
executed to halting from blank, four builder-adapter roundtrips, eleven invalid
input rejections, a long-zero path requiring an extended dispatcher, a
right-edge decrement requiring the state-5 patch, and the restricted native
zero-return option.

These checks leave material proof work. The Python executor has no proved
soundness theorem; sampled box and concrete tests do not quantify over all
register values. The published Coq specifications guide the implementation,
but no Coq theorem is imported for the changed table. A Lean proof must connect
the emitted table to the RM semantics, prove the initializer and box contracts,
and connect each edited theory program to its intended calculus and ZFC
metatheory. State minimization must then measure actual emitted tables,
including initialization, rather than infer savings from formula length.

## Batch 150 initializer controls

Source 21's reviewed initializer has, for nine nonnegative register values
of sum S and positive n,m, gap `n(m+2)+2`, `S+28+2n+m` states and exactly
`S+28+6n+(m+2)n(n+2)` steps. The frontier/counter invariant accounts for all
nonzero cells and the blank exterior. For required gap 102, minimal cost
`2n+m=27` occurs at (6,15), (7,13), (8,11); (6,15) is fastest. Integrating
it preserves all 572 runtime rows and changes the old clean assembler from
408 to 341 states, or 343 with next-proof value 2. Both tables and all finite
frame/affine checks reproduce. This saving compares two clean-assembler
initializers and cannot be subtracted from the optimized public 253 table.

Source 20 separately transfers the attributed public 253 initializer idea
into source 09's decoder 256, obtaining a 255-state table. Its 606,702-step
blank run reaches the recorded whole frame; independent simulation checks
all 283 nonzero cells and the blank exterior. Its 8,391 affine checks and
57,150 bounded fold attempts pass, with no surviving fold. Those contracts
and finite runs do not prove arbitrary runtime or a new consistency endpoint.
The source's separate EPSC 271 control also reproduces; its 276 comparison
has only a table and historical data, without the generating search.

See the host's `intake-150-source-20.md` and `intake-150-source-21.md` for the
exact scope, provenance, ordinary initializer proof and reproducible commands.
