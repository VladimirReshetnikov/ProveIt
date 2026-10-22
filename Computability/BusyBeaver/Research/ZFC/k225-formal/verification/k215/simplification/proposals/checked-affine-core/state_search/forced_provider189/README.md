# Coordinated reuse of the K215 append/restoration helper

This additional fixed-family experiment explores deleting dense state 189
while reusing another state for either or both of its branches. **No correct
214-state consistency machine is established.** All 109 short-screen survivors
have independently replayed first-clean-redispatch counterexamples.

This directory can be placed inside `state_search/`; it uses the parent
component's exact K215 table, literal source and independent audit helpers.
The upstream table/source bindings and license notices are those already
included in that component at commit
`56e487ce8fa4cf63ad169ffe0cd2944e9fc62dd3`. No inherited source file is modified
here. New scripts and records are supplied under the repository's MIT No
Attribution terms. The parent component remains independently reproducible.

## The fixed family

For each provider `p` in `0..214`, excluding 66 and 189:

1. Replace `66/0: 1 R189` with `1 R p`.
2. Copy the old 189 read-zero branch (`1 L40`), its read-one branch (`1 L111`),
   or both branches into the corresponding row(s) of `p`.
3. Delete both rows of 189.

Excluding 66 keeps the redirect row distinct from the copied provider rows.
This gives exactly **213 providers × 3 modes = 639 tables**. It is a specific
coordinated rewrite family, not an exhaustive synthesis search. The retained
working labels are inherited K215 dense labels with a hole at 189; halt remains
215. The separately supplied example tables each have 214 listed and
graph-reachable working states, and 428 rows.

## Results and their proof boundaries

The first screen uses the same 69 short primitive samples as the parent
component: three register/spare/gap choices for each of 23 opcode/register
classes. Each sample is bounded at 20,000 transitions and stops at the first
clean redispatch. The screen performs 11,891 sample runs and leaves 109
survivors. All parent controls pass.

Full-source refinement tests those 109 survivors in source order, with all
registers initially zero and both zero/positive variants of each CD command.
It performs 170,182 sample runs before rejecting every survivor with an
explicit wrong first-redispatch output. These are finite input tests; no
universal correctness is inferred from a long prefix of passing cases.

An independent byte-array audit replays all 639 parent controls and classifies
the complete family as follows:

| Final classification | Tables | Interpretation |
|---|---:|---|
| Wrong first-redispatch output | 338 | Explicit counterexample to that primitive contract |
| Outward blank ray | 223 | Self-loop moves indefinitely into an all-zero exterior |
| Literal configuration cycle | 5 | Complete state, head and tape repeat exactly |
| Unexpected halt | 2 | A nonhalting source command halts prematurely |
| Unresolved bounded run | 71 | No negative theorem is claimed beyond the 20,000-step bound |

Thus 568 tables have explicit obstructions to the specified reusable primitive
contract, while 71 remain bounded failures. A wrong first-redispatch output
does not exclude a different simulation allowing later redispatches. None of
these classifications decides a table's blank-run consistency calibration.

Hashes are used only to locate possible cycles. The audit reconstructs the
entire byte array at both proposed endpoints and compares it literally, with
checked head bounds and the infinite all-zero exterior. Ray witnesses verify
a read-zero self-loop whose head lies beyond every nonzero cell in its move
direction. Determinism and the blank exterior then justify indefinite motion,
including when the loop writes ones behind its moving head.

## Exact startup matches and late primitive failures

Blank-prefix comparisons use a separate 100,000-transition cap. The parent
first satisfies this experiment's clean-frame decoder at step 79,633. This is
the first decoded frame under this specific format, not an assertion that no
earlier machine control visits the dispatcher. Across all 639 tables, 95
first frames match the parent's logical registers and continuation, 46 do not,
24 tables halt, and 474 remain bounded without such a frame.

Three late-failing providers have been checked more closely by the independent
simulator. For each, the complete tape and head at its first decoded frame
match the parent's frame exactly, with only the indicated step-count change:

| Provider, both branches | Passing guarded source cases before first failure | First decoded blank frame | Failing zero-based source index | Command |
|---|---:|---:|---:|---|
| 95 | 5,944 | 79,633 steps | 4,578 | CD5 |
| 188 | 5,936 | 79,633 steps | 4,572 | CD7 |
| 213 | 5,918 | 79,639 steps | 4,560 | CD5 |

That common startup frame has head position −7, continuation one-bit positions
`[0,1,3,6]` relative to the head, logical registers
`[4,0,0,0,0,0,0,0,0]`, forty unit spares and gap zero. The full tape cells are
saved in `near_survivors_checked.json`.

For provider 95, the failed source address is `110100100111100000`. Its
counterexample uses nine zero registers, spare list `[0]` and gap zero. The
parent correctly redispatches after 612 steps; the changed table redispatches
after 64 steps with the wrong continuation. The changed prefix reads only
positions −10 through 14 relative to its initial head. Providers 188 and 213
have analogous fixed prefixes reading only −10..15 and −10..21.

In every valid input frame, all cells that depend on the registers, spare
suffix or gap are at positions at least 64. Hence these failing prefixes are
unchanged for **every** natural register assignment, every nonnegative gap,
and every nonempty finite natural spare suffix at the given source address.
There is no intermediate dispatcher control, and the output counter differs
from both the zero and positive CD branch continuations. This is an ordinary
finite-trace extension argument, not a proof-assistant kernel theorem.
A source-invariant rescue would therefore have to exclude the entire source
address, not merely the displayed all-zero register assignment. Complete
blank-run calibration remains a separate question.

### Why a simple source-unreachability rescue also fails here

The separate source analysis identifies all three sites in the mandatory final
AX validation gate, `dagPerm` node 457. The first comparison is an
`ifeq_clear` comparing `c` and `B`; loop 211 then restores `c` from scratch
register 7 to register 6; loop 197 restores the other compared value, and the
second `ifeq_clear` compares `c` and `A`. The literal node decomposition is
`457=(192,458)`, `458=(131,459)`, `459=(211,460)`,
`460=(197,131)`. The first node-131 instance contains source site 4560,
node 211 contains site 4572, and the second node-131 instance contains 4578.

The maintained source evidence is in
`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/L2AxiomsPerm.lean`
(`AXAtom.run`, `axWordRun`, `axWord_checked`, `l457`, `l236`),
`L2Perm.lean` (`loop192`, `ifeq_clear`, `loop211`, `loop197`),
`L2Lib222.lean` (`AS`, `enc`), and `L2Macros222.lean` (`Clean`). A separately replayed direct graph
prefix takes 180 checkpoint transitions from source vertex 25 with register
file `[4,0,0,0,0,0,0,0,0]` to AX entry 26 with
`[7,0,0,0,0,0,0,0,0]`; its scratch registers satisfy `Clean`.

The existing total macro-run theorems and the displayed sequential gate
structure give an ordinary eventual-visitation argument for all three sites
in the parent source execution. A long finite source probe that has not yet
reached them does not establish unreachability; it is still executing earlier
arithmetic. This argument uses inherited checked totality and finite literal
mapping/prefix evidence. It is not a newly checked kernel reachability theorem,
and it does not prove the altered binary tables' blank-run calibration.
The exact mapping, prefix replay and ordinary eventual-visitation argument
are supplied in the sibling [source-reachability component](../source_reachability/README.md).

The three literal tables are named `rejected_provider95_214.dense.tm`,
`rejected_provider188_214.dense.tm`, and `rejected_provider213_214.dense.tm`
to prevent their being mistaken for accepted consistency candidates.

## Original provider roles and a bounded source-layout follow-up

All three late-failing providers are **source-address decoder controls**. They
are not the generic append/restoration routine that state 189 implements.
The inherited `decoder_map` traversal of the exact parent table gives:

| Dense / native state | Original source prefixes | Zero-based leaf intervals | Operational role |
|---|---|---|---|
| 95 / 96 | `1101001001111` | 4578–4590 | Final AX comparison and cleanup, including its terminal control leaf |
| 188 / 197 | `110100100111011` | 4572–4577 | Branch between the closed transfers R7→R6 and R4→R5 |
| 213 / 301 | `11010010011101011000`, `11010010011110000`, `1101001011000`, `11110000` | 4560–4563, 4578–4581, 4661–4664, 4726–4729 | Shared four-leaf comparison/clear fragment |
| 189 / 198 | No decoder prefix | None | Append/restoration helper reached from dense row 66/0 |

`layout188_results.json` records the literal original rows, incoming rows,
subtree leaves, closure bounds and all these prefixes. The late failures occur
at the first tested source locations that use the overwritten decoder role.
The number of earlier passing cases is therefore not evidence of almost
complete runtime correctness.

At prefix `11010010011101`, the source has shape `(A,(B,C))`, where `A` has
4,253 leaves and the two closed three-leaf factors are
`B=(CD7,(CI6,CC2))` and `C=(CD4,(CI5,CC2))`. Each factor has closure bound
`(0,0,false)`. The transfers B and C commute because they modify disjoint pairs
of registers and terminate for every natural register file. This permits a
source-level swap without assuming that A commutes with either factor.

A final bounded follow-up examined exactly three layouts: `(A,(C,B))`,
`((A,B),C)`, and `((A,C),B)`. For each it also constructed the direct two-node
physical rewire and computed the coarsest deterministic Mealy partition of
that listed table, preserving both write and move labels and keeping halt
distinct. The observed counts are:

| Source layout | Distinct source DAG nodes | Physical decoder controls visited | Listed working states / Mealy classes | Maximum depth / zero run |
|---|---:|---:|---:|---:|
| Parent `(A,(B,C))` | 202 | 165 | 215 / 215 | 47 / 6 |
| `(A,(C,B))` | 202 | 165 | 215 / 215 | 47 / 6 |
| `((A,B),C)` | 202 | 165 | 215 / 215 | 48 / 7 |
| `((A,C),B)` | 202 | 165 | 215 / 215 | 48 / 7 |

The order-preserving reassociation also preserves the full guarded ordinal
CFG, checked by two independent resolvers. The other two layouts have the
ordinary source equivalence supplied by the disjoint transfers. **Source
safety and the table counts do not certify the binary rewires.** The inherited
decoder traversal checks motion across known prefixes; it does not by itself
check every literal command entry. Indeed, swapping B and C changes one
context-sensitive intermediate decoder control from native 47 to 46, recorded
in the receipt. No full primitive runtime or blank calibration was checked
for these rewires. The finite partition result excludes only a plain
output-labelled state quotient of each particular listed table, not a
reduction with a tape invariant or a different implementation.

This small family saves no state even at the source-DAG or direct-rewire
level. A useful next synthesis target is the joint implementation of the two
closed transfer loops and their address decoder around provider 188, while
preserving the append/restoration helper's contract. A different source layout
could still free a decoder state, but these three changes do not. Providers
95 and 213 are less isolated: their displayed fragments have nonzero external
control bounds, and 213 already serves four source contexts. Blindly moving
those fragments would require additional control-depth and decoder proofs.

The portable command `python3 inspect_layouts.py` reproduces the role mapping,
three source layouts and finite table partitions in about one second. It uses
only the standard library and the two verbatim inherited helper modules in
`reference/`. Their original repository paths are
`Computability/BusyBeaver/Research/ZFC/candidate-k215/code/source_language.py`
and `Computability/BusyBeaver/Research/ZFC/candidate-k215/code/build221.py`.
Although retrieved from checkout `53269bcab1efc0f82d3022645bd7cf0c22d84959`,
both files' Git blob IDs match current pin
`56e487ce8fa4cf63ad169ffe0cd2944e9fc62dd3`, as recorded in
`layout_reference_bindings.json` and checked again by the script. Their
original headers are preserved, and the parent component's
`reference/k215/NOTICE.md` and `reference/k215/licenses/` supply the inherited
attribution and terms. No inherited file is relicensed.

## Reproduction

The independent finite audit and detailed three-provider checks take a few
seconds and do not rerun the synthesis screen:

```sh
python3 audit_forced_provider.py
python3 check_near_survivors.py
```

To reproduce the bounded screening and source-wide refinement, run:

```sh
python3 forced_provider_screen.py
python3 refine_forced_provider.py
```

The scripts write their local receipts; preserve an untouched copy when
checking the delivered manifest. Original observed runtimes were approximately
30 seconds for the initial screen and 70 seconds for refinement. The
`near_survivor_prefix_scope.json` file records the initial exploratory summary;
`near_survivors_checked.json` is the independently checked, fully bound record.
