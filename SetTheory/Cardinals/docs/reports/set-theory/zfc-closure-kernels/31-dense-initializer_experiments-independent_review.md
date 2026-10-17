# Independent review of the BB5-assisted blank initializer

**Outcome: the literal 315-state control and its 29-state initializer pass
an independent full Python replay.** The first arrival at the frozen runtime
is after exactly 47,189,196 transitions, at state5/head-44. Every integer
tape cell is specified by the resulting eleven-element set of one-cells.
The ordinary adapter proof and its general r-register count are sound.
No arbitrary-runtime theorem or new Con(ZFC) machine record follows.

## Finite preprocessor fact and attribution

The five-state preprocessor is the published Marxen--Buntrock machine in
the orientation used by the author's primary simulation page:
https://www.turbotm.de/~heiner/BB/simmbL5_1-m.html . It is not a newly
invented busy-beaver machine. Its ordinary halt action is redirected into
the initializer adapter without changing its write or move.

The independent replay checks that after 47,176,870 transitions its state
is the adapter's `aux`, its head is12242, and its complete set of one-cells
is

`{-45, 12243} union {-44+3k : 0 <= k <= 4095}`.

This is an exact finite execution result. It does not require the global
optimality theorem for BB(5), nor does the report establish such optimality.

## General adapter proof for r >= 1

Write L=-45 and H=12243, so G=H-L-1=12287.

1. The two setup states write an auxiliary1 at H-1 and retain/write the
   header1 at H. They leave the head at H+1.
2. Exactly2r dedicated printer states write `(01)^r` at positions
   H+1,...,H+2r. The last printer moves left, entering `back` at H+2r-1.
3. The two preserving return states move left across the alternating
   register block. They recognize the **first adjacent pair encountered
   from the right**, at H,H-1, retain the header at H, erase the auxiliary
   at H-1, and enter `erase` at H-2. This takes2r+1 transitions.
4. The two eraser states move left across the periodic work pattern.
   Every one is erased except the leftmost marker L. Successive periodic
   ones are separated by two zeros; the sole adjacent pair in the remaining
   work region is L,L+1. On reaching it, the state that remembers an erased
   right-hand1 retains the1 at L and moves right into the runtime at L+1.
   This last phase takes exactlyG transitions.

The word **first** in step3 is essential. Before cleanup the source pattern
contains the left pair L,L+1, and the last periodic1 at H-2 together with
the auxiliary and header makes a triple111. The algorithm does not require
the auxiliary/header pair to be globally unique; it is first along the
return path from the newly printed registers.

The resulting one-cells are exactly

`{L,H} union {H+2j : 1 <= j <= r}`,

and the head is L+1. All G cells between the left marker and the header are
zero. The r physical register blocks are all `01`, representing r zeros.
Everything outside this specified finite support remains blank.

The working-state count, excluding the external handoff/terminal, is

`5 + 2 + 2r + 2 + 2 = 2r+11`.

The exact number of transitions is

`47,176,870 + 2 + 2r + (2r+1) + 12,287 = 47,189,160+4r`.

For r=9 this is29 initializer states and47,189,196 transitions. The generic
r statement concerns the initializer component; the frozen project runtime
specifically expects nine registers.

## Independent execution and origin checks

`independent_python_audit.py` does not import the generator or either C++
simulator. It parses the actual total630-row numeric table, checks every
target bound, determines the unique initializer-to-runtime exit from those
literal rows, and executes with an independent set of arbitrary integer
one-cell positions. The target is the first runtime entry, not an arbitrary
late checkpoint. It checks the full preprocessor profile en route.

Observed final values:

* steps47,189,196; state5; head-44;
* visited head interval[-45,12261];
* ones at -45,12243,12245,12247,12249,12251,12253,12255,12257,12259,12261;
* gap12287, exceeding the frozen runtime's minimum102;
* all572 frozen runtime rows retained under the explicit renumbering.

This replay took approximately7.04 seconds in the audit environment, which
is an observed implementation measurement rather than a portable bound.

An additional independent origin check recompiled the current pinned
`mira_backend.py` from the attributed pinned Dag254/literal254 input bytes.
It reproduced the old408-state clean control with122 initializer states
and matched all572 extracted named runtime rows to `runtime_286.json`.
Hence the preservation check does not rely solely on that file's metadata.

Evidence is in `output/independent_python_replay.json` and
`output/independent_runtime_rebuild.json`. The literal315 table hash is
`cf68ed84e9e51f1776d32666f9e3a843cd522621a1cd011a36ce0ef9ed30a097`.

## What the reduction establishes

The same286-state editable runtime can now be initialized from blank tape
with29 states, so its complete control shrinks from408 to315. The earlier
newly arrived compact-initializer control was341; this improves that control
by26 states while retaining its runtime exactly. It remains larger than
the attributed public253 construction.

The initializer computes zero registers only; arbitrary nonzero startup
data require a separately charged extension. The frozen runtime's complete
enumerator/compiler/consistency proof remains open. Exact finite startup
and all-row preservation do not silently supply that theorem.
