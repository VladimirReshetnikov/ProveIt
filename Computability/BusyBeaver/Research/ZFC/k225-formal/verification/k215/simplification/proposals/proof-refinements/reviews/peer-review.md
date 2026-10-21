# Independent mathematical and interface review

Reviewer: machine-reduction subagent, 21 October 2026. This is an independent
review within this research collaboration, not an external human endorsement.
The reviewed source hashes and finite exact-data bindings are in review.json.
No redundant kernel compilation was performed by this reviewer.

## Early-halting selection: pass

`EarlyHaltSelection.select_with_zero` and `NativeSelection.native_select_nth`
have the correct early-halting disjunction. In particular, NIP tests the *old
cache before popping*. The proof never silently treats NIP as an unconditional
pop. An alarm in a skipped row or in the selected row is allowed to terminate
the macro; this is sufficient for the production compiler's `blk` contract,
which already accepts early halting.

For n rows and zero-based selected index j, the first j+1 NIPs pop through the
selected row. DROP pushes the original top g. There are then exactly n+1-j
explicit cells left: g, the remaining rows, and zero. The final drain reads
those cells and stops with the old opaque tail intact and cache zero. It never
pops the tail. The proof handles the boundary cases j=0 and j=n-1; the
`nth_error` premise prevents arithmetic underflow in the remaining count.

The pairing assumption is precisely `unP (P x w) = (x,w)`. No positive-code,
nonempty-code, or anti-alias premise is used. In particular P(0,0)=0 is harmless.
The numeric adapter preserves the counter d exactly. Its two commands match
`K215F.L1_CompPerm.xstep` literally, including DROP retaining the old cache.

The production AX stack is nine rows (rho1 through rho8, then GEN) followed by
the saved prior top. After the existing reset sets that saved top to zero,
the theorem selects all nine entries. Zero-based j=0..7 matches the current
one-based leaf1..8 macros; GEN has j=8 and uses NIP^9;DROP;NIP^2. The current
GEN preparation also reaches AX with saved top zero.

**Integration boundary:** the numeric adapter currently defines its own
command type and executor. A mapping to the actual production command type,
the pairing instantiation, and replacement of production compiler clients
remain to be supplied. This standalone result does not establish that the
entire endpoint has been rebuilt. The existing eight leaf proofs already fit
one line each via `leaf_tac`, so there is no demonstrated total source-line
reduction for those clients. The improvement is a more general contract that
removes repeated nonfalsity side conditions and handles arbitrary row lists.

## Decoder context propagation: pass

`DecoderContext.internal_context_sound` uses two distinct coverage conditions:
the current suffix and read bit provide the local execution window, and they
also provide the next role's preceding suffix after a head shift of one.
`blockCheck` certifies positive time, exact target state/head, and restoration
of the complete arbitrary tape. Consequently the unchanged tape can support
the suffix invariant at the next edge. The coordinate shift in
`matches_shift_at` has the correct orientation.

`route_sound` composes these blocks by induction with no intermediate tape
window witnesses from the caller. `follow_route` constructs the indexed route
from executable lookup data. `source_path_follow` adds a separate syntactic
link from every internal source-DAG path to a decoder route. Thus
`K215Context.every_internal_source_path` genuinely removes the per-edge window
premises: only the initial predecessor marker and actual pointer bits remain.
Nonempty paths have positive total runtime. Empty paths correctly allow zero
runtime and leave the configuration unchanged.

The source checker deliberately ignores leaf branches. This is sound because
`nodeFollow` succeeds only when every traversed node, including its endpoint,
is internal. It must not be cited as a primitive-entry or primitive-return
execution theorem. Rejecting a primitive node used as a source parent is a
useful explicit negative control.

An independent parser compared every one of the generated native table's
430 transition rows with published K215. A separate recursive expansion of
the 202-node generated source DAG reproduced all 4,751 ordered source sites
exactly. Their published SHA-256 values match review.json. This is an external
exact-data audit, not an in-kernel identity theorem with maintained endpoint
constants.

**Integration boundary:** primitive final edges and their register contracts,
re-entry to the decoder from arithmetic primitives, blank startup, and the
connection to maintained `KSites215`/`KMachine215` definitions are outside the
new theorem. The theorem is already meaningful for the supplied literal table
and source data; closing those bindings is necessary before replacing the
existing complete endpoint proof. No new state count or global proof-time
speedup follows from these lemmas alone.

## Addendum: production selector adapter verified

The production adapter is now compiled and recursively rechecked, upgrading the
previous standalone-command boundary. `K215SelectorAdapter.v` imports the actual
`L1_CompPerm.cmd`, `xstep`, and `exec`. Its step equality is definitional, and its
execution equality follows by induction over the command list. `select_actual`
instantiates the generic numeric theorem with the production `P`, `unP`, and
`unP_P`; `select_AX_row` uses a reflexive equality with the exact production
`ax_stack` and the nine AX rows in their maintained order.

The reviewer independently checked all 11 source hashes recorded in
`production-verification-final/receipt.json`, that the three delivered new
sources equal their compiled copies, and that the five captured production
files differ only by the recorded `Stdlib` to `Coq` import-prefix changes in
three files. The actual `EnumPerm.v` and `L1_CompPerm.v` files are byte-identical.
The receipt records all compilation exits zero and recursive `coqchk` exit zero;
this reviewer inspected the receipt rather than duplicating that build.

Final adapter SHA256:
`80923e68cc13a43a3487d660fad67ca12c41103a1e140a49541ad69eb3af4905`.

**Result: PASS.** This is a checked production-command adapter. Replacing the
existing `blk_r1` through `blk_r8` and `blk_gen` proof clients, measuring any
resulting proof-size or time change, and rebuilding the binary/ZFC endpoint
remain outside the completed result.
