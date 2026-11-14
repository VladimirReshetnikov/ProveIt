# MP196: immediate contradiction detection at modus ponens

This is a concrete **196-state protocol prototype**. It does not meet the
requested target of fewer than 194 states. It makes a different halting
location and proof-search protocol fully reviewable. No new end-to-end
Lean or Rocq theorem is claimed.

The literal machine is `machine/machine.tm`: 196 working states numbered
0 through 195, initial state 0, separate halt label 196, 392 rows, binary
alphabet, blank two-way tape. Every transition writes one symbol and moves
left or right. `machine/machine.native.tm` retains the inherited labels
and adds 400 and 401; its initial label is 74 and halt label is 254.

## Exact command behavior

For a command store `(t,w,d,h)` and MP parameter `x`, let `b=d+x` and
`I(t,b)=4*((t+b)*(t+b+1)/2+b)`. The command compares `I(t,b)` with `h`.
On mismatch it returns `(0,w,b,0)`. On a match with `b=1` it halts
immediately. On every other match it returns `(b,w,0,0)`, including `b=0`.
The successful command clears the offset and leaves the formula stack
unchanged. The AX command is unchanged.

The original Shift remains unchanged: it halts if `t+h=1`, and otherwise
returns `(h,tl(w),d,hd(w))`. After the checked initialization, at every completed nonhalting command
boundary, every stored formula differs from 1: initial formulas are zero;
AX never generates 1; a successful MP with conclusion 1 halts without
returning to a completed command boundary; other MP outputs and ordinary
Shift preserve this invariant. Thus the original Shift halt is unreachable in this
protocol, without assuming PA consistency. Retaining its rows allows
**every** primitive source contract to be checked, without omitting any
branch or changing the machine outside its intended reachable stores.

The exact source block and invariant are proved in `source_proof.tex`.
The main report supplies the command proof compiler and explains the
inherited numerical-calculus calibration to PA. The unshifted variant
uses command parameter `b` when compiling an MP conclusion `b`.

## State budget

| Component | Working controls |
| --- | ---: |
| Inherited primary PA194 table | 194 |
| Reader for `node51 ; (incH ; node7)` | 1 |
| Reader for `incH ; node7` | 1 |
| **Total** | **196** |

Only one inherited row changes: `(164,1)` now writes 1, moves right, and
enters new control 400. The two new controls are

| Native control | Read 0 | Read 1 |
| --- | --- | --- |
| 400 | `0 R 130` | `1 R 401` |
| 401 | `0 R 63` | `1 R 68` |

The 23 states used by the inherited symbolic arithmetic-block oracle are
unchanged byte for byte. All 196 controls are reachable in the transition
graph; no claim is made that each is visited by the blank execution.

## Reproduction

From this directory, with Python 3 and assertions enabled:

```
python3 -B build.py --output generated
```

No repository checkout, network, third-party Python module, or proof
assistant is required. The builder checks the pinned input hash, resolves
all 3,663 source sites, checks the new command endpoints, verifies all
4,768 primitive source outcomes with inherited symbolic arithmetic
contracts, simulates the complete startup tape, and performs 478 bounded
command cross-checks. The symbolic run uses 1,476,043 operations and at
most 497 for any one primitive contract. The bounded checks are not a
universal source proof; that argument is in `source_proof.tex`.

The complete blank startup reaches source site 25 after exactly 58,154
transitions: native state 84, head -2, gap 48, physical primary registers
`[0,0,0,0,0,0,2,0,0]`, and 26 one-valued spare registers. Thus logical
candidate K is 2 and all other logical registers are zero. The receipt
checks the entire finite support of the tape (66 one-cells), not only
the register projection. No halt occurs during these steps.

Dense table SHA-256:
`c14cc614c8f33a67697b4fbc3b502ee5c8c6b3764ef721cd1e0c09f3810a97f3`

Native table SHA-256:
`7689bf1cf5843f3f2c27ac3e3f7da2a84b28a8bce1d9f6458209579012ef6271`

## Proof boundary

The new source controller has an ordinary mathematical proof and an
explicit literal transition table. The runtime argument inherits the
four generic arithmetic-block lemmas unchanged. The PA consistency
calibration inherits the existing numerical-calculus argument and the
new command compiler in the main report. No new independent literal
arithmetic-block audit, end-to-end Lean/Rocq theorem, or iPRA
internalization has been produced. This is not a state-count improvement.
