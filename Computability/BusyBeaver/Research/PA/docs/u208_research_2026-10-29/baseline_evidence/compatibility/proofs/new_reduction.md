# A 209-state candidate by contextual reassociation across a shared helper

## Frozen machine and source

The new literal machine has 209 working states and one separate halt label. Its
native-label table is `u209.native.tm`, SHA-256
`4564c4876f9b18725bfb3505ec1f50d1ebce572502f2c6381ad673ecfdc3c3e1`.
The dense table is `u209.tm`, SHA-256
`bda91bd40880f96edef104246d22797fe281355cf03610ab7e93e7923be8aa16`.
The source map is `sites.json`, SHA-256
`912724f29b0de28b3326c710fdf1f3863ebd07058c6db1a9b4bbaffb3ae5e3f3`.

The construction starts with the new Research+Rotated U210 composition. U209
changes 15 retained transition rows and removes native state 180. It retains
3,909 source primitives and their complete ordinal control graph. The source
has maximum depth 41, maximum consecutive-zero run 6, and 197 distinct syntactic
subtrees. Exactly 847 leaf addresses change from U210 to U209.

## Why the previously published constructions do not simply stack

The Research U211 fold uses state 129 as a backward helper for state 220. A
simple rotation whose outer node is 129 would normally be forbidden because
129 has two entries: `215/1 -> R129` from source decoding and `220/0 -> L129`
from the tagged selector. Treating 129 as an ordinary single-purpose decoder
can corrupt the selector. The new construction changes a larger closed
source block while preserving exactly the helper rows that the backward entry
can execute. It therefore crosses a sharing boundary that the published
rotation-only recipes avoid.

## The eight-factor source identity

In U210, native 174 is reached at source prefix
`0011001110101011111111`; its source interval is `[3016,3736)` in zero-based
primitive ordinals. Decompose that 720-primitive source subtree into eight
closed factors, in this unchanged order:

| Factor | Physical entry | Primitive length | Old suffix | New suffix |
| --- | --- | ---: | --- | --- |
| A | 98 | 26 | 00 | 00 |
| B | 158 | 134 | 010 | 010 |
| C | 147 | 52 | 0110 | 0110 |
| D | 146 | 108 | 01110 | 0111 |
| E | 220, with predecessor bit 0 | 136 | 011110 | 10 |
| F | 90 | 27 | 011111 | 1100 |
| G | 211 | 103 | 10 | 1101 |
| H | 163 | 134 | 11 | 111 |

All eight actual source subtrees have closure signature `(0,0,False)`: neither
kind of ancestor-relative branch escapes their root, and none contains halt.
The rewrite is

```
((A,(B,(C,(D,(E,F))))),(G,H))
             ->
((A,(B,(C,D))),(E,((F,G),H))).
```

Because each factor is closed, both source trees execute the same ordered
primitive effects and have the same resolved ordinal successors, including
both outcomes of conditional decrement. Branches outside this block are
unchanged because its interval and leaf order are unchanged. Both independent
ordinal CFG resolvers confirm equality for all 3,909 primitives. This is a
universal statement about the source program; it is not a finite register test.

State 220 is already contextual: its zero-predecessor meaning is E, while its
one-predecessor occurrence elsewhere has a different source subtree. The
reassociation preserves E's predecessor zero by moving its incoming edge from
`216/0` to `217/0`. Its one-predecessor entry `185/1` is unchanged. Hence the
rewrite preserves which of state 220's two meanings appears at each source
occurrence.

The seven edited decoder rows are

```
204/1 : 1 R214 -> 1 R146
214/0 : 0 R146 -> 0 R216
214/1 : 1 R216 -> 1 R163
216/0 : 0 R220 -> 0 R90
216/1 : 1 R90  -> 1 R211
217/0 : 0 R211 -> 0 R220
217/1 : 1 R163 -> 1 R214.
```

All are bit-preserving right moves. They implement the new association using
the same seven internal labels. No state is added here. In particular state
216 now has children `(90,211)`, preparing the later fold.

## The 129 helper remains correct

The complete incoming inventory for 129 remains

```
215/1 : 1 R129
220/0 : 0 L129.
```

The backward entry occurs only after 220 reads and preserves a zero. Put the
old 220 head at h, with current bit zero and predecessor bit t. The helper
executes

```
220@h -> 129@(h-1) -> (158 if t=0 else 204)@h
      -> (157 if t=0 else 147)@(h+1).
```

It reads only h-1 and h and leaves both unchanged. The only rows of 129, 158,
and 204 used by this block are 129/0, 129/1, 158/0, and 204/0. All four are
literally unchanged. Although 204/1 is changed, this row cannot occur inside
that backward-entry block: 220 just wrote zero at h. The common `220/1 -> R176`
row is also unchanged.

The full incoming inventories exclude any additional entry to 158 or 204:
158 is reached only from 129/0, and 204 only from 129/1. States 214, 216, and
217 have only the displayed pure-decoder predecessors before reassociation.
The remaining source entry to 129 is the explicit source occurrence inside
174. Thus the larger source rewrite and the local helper proof cover the
known entry modes without declaring the runtime entry to be a source entry.
The complete universal primitive-runtime replay is a separate gate that checks
the final table directly, including other inherited contextual folds.

## Make every entry to 180 carry predecessor one

Apply the three right rotations inherited from the Contextual proposal:

```
(206,199,1), (205,206,1), (7,205,1).
```

Their source prefixes are, respectively,

```
00110011101010110111
0011001110101011011
001100111010101101.
```

Each rotated triple consists of closed factors, each inner decoder has exactly
one incoming edge, and all source primitive effects and successors remain
unchanged. State 7 has a separate backward entry from 171/0, so repair that
entry from `0 L7` to `0 L205`. The complete incoming list for 7 before the
change is `171/0 -> L7` and `207/1 -> R7`; this repair therefore accounts for
its unique non-decoder entry.

The repair is a whole-tape identity on every 171/read-zero configuration. If
the predecessor bit is 0, old and new paths both take two steps and finish at
86 with the original head. If the predecessor is 1, old and new paths both
take three steps and finish at 164 one cell to the right:

```
left=0: old 171@0 -> 7@-1   -> 86@0
        new 171@0 -> 205@-1 -> 86@0
left=1: old 171@0 -> 7@-1   -> 205@0 -> 164@1
        new 171@0 -> 205@-1 -> 206@0 -> 164@1.
```

The two cells read have arbitrary stated bits, all writes preserve those bits,
and no outside cell is read. The state after repair and before final folding
is the frozen table `prefold210.native.tm`.

## The final 180-to-216 fold

In the prefold table R, both states are ordinary decoders:

```
216/0 = 0 R90      216/1 = 1 R211
180/0 = 0 R152     180/1 = 1 R211.
```

Their *complete* incoming inventories are

```
In(216) = {214/0 : 0 R216}
In(180) = {132/1 : 1 R180, 199/1 : 1 R180}.
```

Neither is the initial state. Therefore every visit to 216 in a run from
state 0 has a zero immediately left of the head; every visit to 180 has a one.
This follows from the written bit of the preceding transition on any initial
tape, not from an experimental blank-tape invariant.

Define rho(180)=216 and rho(q)=q otherwise. Redirect the two targets of 180 to
216, delete both rows of 180, and replace `216/0` by `0 L211`. Its one row stays
`1 R211`. This produces C, the 209-state table.

For the four possible old state/read-bit cases, put the old head at zero:

| Old state | Predecessor | Read | C path | C steps |
| --- | ---: | ---: | --- | ---: |
| 216 | 0 | 0 | 216@0,211@-1,157@0,67@-1,151@0,90@1 | 5 |
| 180 | 1 | 0 | 216@0,211@-1,184@0,152@1 | 3 |
| 216 | 0 | 1 | 216@0,211@1 | 1 |
| 180 | 1 | 1 | 216@0,211@1 | 1 |

Each old R block has one step. Each C block preserves the entire tape and
finishes with the same head and rho-projected control; it reads only cells
-1 and 0 and has no internal halt. The five-step case is essential: the
Rotated saving has already replaced 218 by 157, so the new fold must compose
with that three-step two-cell detour rather than pretending 211/0 still goes
to an ordinary one-step decoder.

For every other old row the new row has the same write and direction and the
rho-projected target. Induction on old steps gives a positive, bounded block
simulation from every common initial tape in state 0. If an old run halts,
its projected run halts. If a new run halts after T steps, simulate T old
steps or stop at an old halt. Every block has at least one step and no internal
halt, so the new halt cannot be missed: the old machine must already have
halted. This is a finite induction argument and is formalizable in PA for
arithmetically encoded finite-support tapes, including the blank tape.

If n0 is the number of old read-zero visits to 216 and n1 the number of old
read-zero visits to 180 in a halting run, the exact clock relation is

```
T_C = T_R + 4 n0 + 2 n1;    T_R <= T_C <= 5 T_R.
```

These bounds apply to R→C alone. The source reassociation before R changes
addresses, so the same bound is not asserted for U210→C.

## Startup and evidence boundary

Fresh complete blank startup replay is identical for U210 and U209 through
48,140 transitions. It ends at native state 84, head -2, source ordinal 136,
address `001100110101010`, header distance 56, zero extra gap, logical registers
`[1,0,13,0,0,1,0,0,1]`, and 43 spare registers equal to 1. The entire tape,
including its zero exterior, matches the canonical frame. No changed row is
visited during startup. The trace SHA-256 is
`8d9cef508b7a08195a64502866197cc05748e48e17142006512d8616f15481ef`.

The construction and source identities do not themselves prove the entire
machine implements Theory U. That connection also uses universal primitive
runtime contracts and the inherited numerical enumerator, proof-calculus, and
U/PA consistency calibration. Preserve the original calibration status;
this candidate is not a new kernel-checked PA endpoint certificate.

## Fresh final-table universal replay

The native-label symbolic checker completed successfully for U209. It freshly
derived all 5,084 guarded primitive contracts for all 3,909 source sites, using
1,248,748 symbolic execution steps. The cases and list-block lemmas cover all
418 literal transition rows. Every duration is an affine expression with
nonnegative coefficients and positive constant term; the smallest constant is
5. Inputs range over arbitrary natural values of all nine primary registers,
an arbitrary extra gap, and an arbitrary nonempty finite spare-register list.
Whole-tape endpoints, including the zero exterior, are checked.

These are symbolic induction arguments in the inherited Python engine, not
5,084 finite numerical samples. The checker is not a proof-assistant kernel.

There is a necessary distinction between source identities and machine
admissibility during construction. The source zero-run bounds by stage are
6,6,7,7,6 (input, eight-factor reassociation, first right rotation, second right
rotation, third right rotation). The two intermediate seven-zero trees can
trigger the inherited origin detector and are not claimed to implement the
source. All primitive effects and ordinal CFGs remain identical at those
stages, but only the final tree satisfies the scanner condition and passes
the entire runtime replay. The final prefix auditor also verifies all 3,908
internal source prefixes against the final literal table.
