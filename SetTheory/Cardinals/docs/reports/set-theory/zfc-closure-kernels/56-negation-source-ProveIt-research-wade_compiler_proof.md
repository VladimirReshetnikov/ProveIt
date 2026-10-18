`WadeMachine.lean` begins a compiler proof for the **public Wade engine in the
frozen 252-state research table**. It does not use the separate 408-state Mira
assembler. Register values are actual unary runs of `value + 1` one-cells; a
movable double-zero selector identifies the next register. The public engine
and these invariants are read from pinned `ZF/generator/TMBuilder.py` and the
frozen canonical `raw-candidate-252.tm`.

The first claim executes the increment scan, rather than merely translating
between two data encodings. Canonical states 15 and 16 are public `1.inc.c`
and `1.inc.d`; state 23 is `2.ret1`. The scan starts in state 16 with an
arbitrary list of preceding unary blocks and a selected register after the
first following double zero. It crosses all preceding blocks, fills only the
selector's second zero, and reaches state 23 on its first zero. The selected
register now contains one more unary cell. This statement quantifies over
arbitrary register values, arbitrary preceding registers and an arbitrary
finite-support tape outside the specified cells.

`Span`, `RegisterPrefix`, `SelectedRegister` and `UnaryRegister` define the
local tape invariants directly using `Core.Tape.read`. `Reaches` is existential
finite execution by the existing `Machine.runFrom`, with no new TM semantics.
A generic scan lemma executes a literal bit-preserving right self-loop while
preserving the entire tape. The increment proof uses the checked Table252 rows
for states 15 and 16 and that scan lemma. Its frame conclusion preserves every
cell except the one filled selector zero.

The initial scan layer passed its authorized scoped Lean check in
`/tmp/zfc-lean-check-68s1rnfy`: `scan_right`, `inc_prefix_execution` and
`inc_prefix_register_effect` print only `propext` and `Quot.sound`. The next
source layer, `increment_execution`, additionally starts at actual state 13,
writes the temporary marker, crosses the arbitrary zero gap in state 14, and
reaches state 23 with the selected register incremented. It preserves every
tape cell except the temporary marker and filled selector zero. Its authorized
scoped Lean check also passes and prints only `propext` and `Quot.sound`.
Both layers stop at the first
return state; they are not yet the complete source-level INC instruction.

The next source extension supplies `return_one_execution` for the actual
state-23/24/25 return across arbitrary preceding registers and a zero gap of
length at least two. It erases the temporary marker and reaches `6.break.0`
(state 55) with the head on the last PC bit. `increment_return_execution`
composes both excursions: the register increases by one and every other tape
cell has its original bit. The PC carry and redispatch are still separate.
This return extension passed its authorized scoped Lean check in the same
scratch cache. Both return theorems print only `propext` and `Quot.sound`.

The analogous zero and positive decrement exits,
selector relocation, bounded-zero-run PC dispatcher, boot configuration and
per-decoder-site simulation must follow. They must connect the actual logical
register order and selector position of the public backend, rather than import
Mira's different physical register representation. Only after the register
program is connected to its proof enumerator and the edited theory is
calibrated can the 252-state table receive a consistency interpretation.
