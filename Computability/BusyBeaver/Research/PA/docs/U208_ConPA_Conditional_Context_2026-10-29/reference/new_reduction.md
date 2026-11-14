# Two-history-bit fold: U209 to U208

## Exact artifacts and transformation

The parent is the native Joint/Compatible_Folds U209 table, SHA-256
`d0a155d3c683789f3bf5327c0cfb2a0cfd78076af8f1654d4ca426ccbb604d16`.
Its initial state is 0 and its separate halt label is 254. Delete native state
172, redirect its sole incoming row `116 0 0 R 172` to `116 0 0 R 211`, and
change `211 0 0 R 157` to `211 0 0 L 217`. All other retained rows are unchanged.
No source address, source instruction, origin detector, or startup row changes.

The result has 208 working states and 416 binary transition rows. The supplied
builder renumbers working states in increasing native-label order to 0..207,
and renumbers halt to 208.

* Native table SHA-256:
  `b348a466a2c316511e0037ea3824de29d4c6ad37338404fbc98a3968fdb25135`
* Dense table SHA-256:
  `a2fee9e41311c0d43aaac871ea411be24eada17e6b3633c55f40b437101144e1`

## Parent reachability invariants

Write tape coordinates relative to the current head. For every computation of
the parent starting in state 0, on an arbitrary initial binary tape:

1. At state 172, `T(-2)=1` and `T(-1)=0`.
2. At state 211, if `T(0)=0`, then `T(-1)=1`.

These follow from complete physical incoming-edge censuses, not from a blank
run sample. The relevant censuses are:

| Target | Every incoming row |
| --- | --- |
| 172 | `116/0: 0 R 172` |
| 116 | `215/1: 1 R 116` |
| 211 | `163/0: 0 L 211`; `163/1: 1 R 211` |
| 163 | `132/1: 1 R 163`; `199/1: 1 R 163`; `217/0: 0 R 163` |
| 217 | `216/1: 1 R 217` |

None of these states is initial. The first invariant follows from the last two
steps into 172. For the second invariant, an entry from 163/1 directly writes
one to the cell immediately left of the new head. An entry from 163/0 moves
left onto the predecessor bit. If that bit is zero, the previous entry to 163
must have been 217/0, because the other entries write one. The entry to 217
was 216/1 and wrote the required one one cell farther left. These are all
possible cases. The implication is deliberately conditional on the currently
scanned zero; state 211 does NOT have an unconditional left-one invariant.

## Four exact local simulation contracts

Define the state quotient f by f(172)=211 and f(q)=q otherwise. At simulation
boundaries the head and entire tape are identical. Only old states 172 and
211 need more than the ordinary one-step quotient check.

| Old state | Read | Required parent tape | New steps | Final native state/head |
| --- | --- | --- | --- | --- |
| 172 | 0 | `T(-2)=1,T(-1)=0,T(0)=0` | 7 | 67, -1 |
| 172 | 1 | `T(-2)=1,T(-1)=0,T(0)=1` | 1 | 184, +1 |
| 211 | 0 | `T(-1)=1,T(0)=0` | 3 | 157, +1 |
| 211 | 1 | `T(0)=1` | 1 | 184, +1 |

All four contracts preserve the entire tape, read only the cells explicitly
specified in the table, and have strictly positive length. In particular,
unread tape exteriors are arbitrary.

The seven-step zero case for old state 172 is:

```
(211,  0) --0/0,L--> (217, -1)
(217, -1) --0/0,R--> (163,  0)
(163,  0) --0/0,L--> (211, -1)
(211, -1) --0/0,L--> (217, -2)
(217, -2) --1/1,R--> (215, -1)
(215, -1) --0/0,R--> (157,  0)
(157,  0) --0/0,L--> ( 67, -1)
```

Every write preserves the scanned bit. The three-step case for old state 211
is `(211,0) -> (217,-1) -> (215,0) -> (157,+1)`, reading 0,1,0.
Both read-one cases use the unchanged row `211/1: 1 R 184`.
The old rows of 172 are `0 L 67` and `1 R 184`; the old rows of 211 are
`0 R 157` and `1 R 184`. Thus the endpoints are exactly the old one-step
endpoints after applying f. The other 414 old rows are checked directly.

The new seven-step path re-enters state 211. This is safe: its whole path is
an explicit finite identity, not an appeal to an assumed recursive simulation
contract or an invariant of arbitrary new-machine configurations.

## Global theorem and arithmetic strength

For each old computation step, choose the applicable positive block above or
the ordinary one-step block. Let tau(0)=0 and let tau(n+1)-tau(n) be that block's
length. Induction yields equality of heads and tapes and the state quotient
at every matched boundary. In particular, `n <= tau(n) <= 7n`. No internal
state of any longer block is a halt state. This proves halting equivalence
for the two machines from state 0 on every common initial tape; the requested
blank tape is a special case.

For coded blank computations, the finite guard/case proof and its induction
are formalizable in PA. A parent halt by step n gives a child halt by step 7n.
A child halt by step n gives a parent halt by step n. This reduction has no
consistency assumption and inherits precisely the parent's higher-level
Con(PA) calibration. It does not supply a new kernel-checked end-to-end
certificate for that calibration.

## Independent construction checks

`build_u208.py` uses only Python's standard library. It checks the frozen
parent hash, the full incoming censuses, and all three-step histories from
arbitrary state/tape, adding all shorter prefixes from initial state 0.
It then checks each of the four local traces without allowing a read of an
unspecified cell. It checks all 414 ordinary quotient rows, dense renumbering,
table completeness, binary symbols, L/R moves, a separate halt, and graph
reachability of every working state. The output JSON contains complete traces.

The discovery scripts and their negative screens are separate from this
small construction checker. The certified result does not depend on the
discovery search bound, pseudorandom seed, or sampled screens.

## Compatibility-family variant

On the distinct Compatibility U209 machine, the same reduction removes 172
into 211 but uses helper 214 instead of 217. Its seven-step path is
`211 -> 214 -> 216 -> 211 -> 214 -> 163 -> 157 -> 67`.
The corresponding one-step history invariant and conditional guard have
the same form. The two directions of aliasing (remove 172 into 211, or remove
211 into 172) merely choose different native representatives.

## Discovery results

All direct state aliases with seven-step history contexts and replacement
blocks of at most 27 steps failed in the two U209 isomorphism classes. Allowing
positive blocks on both sides also found no certificate at tested limits 21
and 25. A broader one-row-fold search over 358 ordered shared-row interfaces,
all replacement write bits/directions/helper states, and seven-step history
contexts discovered the fold above in both classes. Its exact proof only
needs three-step history and blocks of length at most seven.
