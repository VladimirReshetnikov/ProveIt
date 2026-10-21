# Independent review of the depth-41 K215 alternative

**Result: PASS.** The frozen depth-41 candidate is a materially different 215-state encoding of the accepted K215 program. Its ten-step simplified construction recipe, source, native table, dense table, complete blank startup, and saved complete symbolic-runtime records passed the portable independent review. This review does not establish a 214-state construction.

## Exact identities

| Artifact | SHA-256 |
|---|---|
| Native table | `8cfb95be77f8f8819ac7dc5c92297cf32b5104cbdf22aea925ab38de9c4443b9` |
| Dense table | `27a2a4f452f9fcb1e84ba6f78d0f952ea438eca00d415cc6b0ef4298d35086a4` |
| Source | `46ab3fdabc6ade3c6e4b5f08a0a59af66eb96f3992124ab6b71b8c3f1a05bf35` |

There are 215 working states and 430 transition rows. The native halt is 254; the dense working labels are exactly 0 through 214, with separate halt 215. The independent canonical graph calculation verifies that the dense and native tables differ only by state names, including preservation of the initial state and halt.

## Material difference from existing K215 machines

The new machine changes 19 literal transition rows and 4,120 of the 4,751 source-leaf addresses. Its maximum address depth falls from 47 to 41. The sum of all address lengths falls from 160,305 to 149,265 bits, a reduction of 11,040. The source retains 202 distinct subtrees, 4,751 primitive occurrences, and maximum zero run six.

Canonical breadth-first state labeling, with transitions ordered by read symbol and their write/move actions retained, shows that the candidate's rooted deterministic transition graph is not isomorphic to any of the three accepted 215-state graphs: primary, commands120, and composed. The candidate's canonical graph digest is `9ff31fa59bb5ea2d8dcb29ee384dbaee251c5169768f534e1e087af99568f18c`. Since source164 is an exact renaming of composed, it is also covered by this nonisomorphism conclusion. This comparison proves that the new machine is not merely another labeling of an accepted graph.

## Independent source and table reconstruction

The portable script reads the pinned primary table/source and the ten-step recipe as data. It implements its own source-tree reconstruction, closure calculation, table rotation, prefix replay, two CFG resolvers, and canonical graph comparison. It does not import the synthesis program.

At each rotation, the reviewer checks that each involved state has exactly one source-subtree role; the internal child belongs only to the parent occurrence; both states' decoder rows preserve the scanned symbol and move right; and all three reassociated factors are closed. Closure means that no decrement, break, or continue escapes the factor and no halt occurs within it. The literal ordered opcode/operand word and both complete CFG reconstructions remain identical after every rotation. Every internal decoder prefix is replayed from the actual dispatcher with the known tape prefix restored exactly.

The final source checks cover 4,750 internal prefixes, 4,751 ordered primitives, 6,175 guarded successor edges, and one halt site. The reconstructed table and source equal the delivered bytes. All state counts include the initialization mechanism.

The initial research recipe contained fourteen rotations. Removing the four redundant operations gives the ten-step recipe checked here; both recipes reproduce exactly the same frozen table and source. The final review records ten verified rotations, not the earlier fourteen-step draft.

## Complete blank startup

The independent review starts with an explicitly empty set of one-cells and replays every one of the 95,714 saved transitions against the frozen native table. It verifies each read symbol, write, move, and next state, then compares the whole final tape against the saved result. The final zero exterior follows directly from the explicit finite support maintained from the all-zero initial tape.

The endpoint is native dispatcher 84 at head -8, with header coordinate 57 and gap one. The logical registers are `[4,0,0,0,0,0,0,0,0]`; there are forty spare blocks, all of value one, and exactly 95 one-cells. This is the same calibrated seed used by the accepted primary K215, including the enumeration counter's finite cutoff four.

## Actual unbounded primitive-runtime evidence

The separate source-search task executed the unchanged inherited symbolic checker on the frozen candidate. It completed all 6,176 cases, using 1,640,317 symbolic rules, with minimum positive affine duration constant six. The checker covers independent arbitrary natural register values, both decrement guards, arbitrary natural gap, a nonempty arbitrary finite spare list, and the complete zero exterior. Unary and finite-list induction supply its unbounded contracts.

The independent reviewer checks the actual saved case order against every source ordinal and decrement guard. It verifies the positive affine-duration forms, four one-block traces against the exact table, complete coverage of all 430 literal rows, the table/source hashes, and pinned identities of the checker, helper, wrapper, and native-to-legacy mapping. Thus the receipt is tied to these exact delivered inputs.

This is an audit of the actual saved quantified-runtime records and unchanged checker source, not a second derivation of all symbolic cases or a proof-assistant kernel check. The separately executed checker is the source of the quantified primitive contracts. This distinction is explicit in the JSON review.

## Precise duration tradeoff

Shallower source addresses do not imply uniform runtime improvement. Matching corresponding source ordinals and guards, all nonconstant coefficients in the affine primitive-duration formulas remain unchanged. The constant part decreases in 1,427 cases, increases in 3,827 cases, and stays equal in 922 cases. Individual changes range from -12 to +12; their unweighted sum is +15,528. These figures do not apply any execution-frequency weighting.

The source-depth changes, over its 4,751 leaf occurrences, are:

| New depth minus old depth | Number of leaves |
|---:|---:|
| -6 | 919 |
| -4 | 123 |
| -3 | 1,028 |
| -2 | 708 |
| -1 | 956 |
| 0 | 698 |
| +1 | 216 |
| +2 | 103 |

The result should therefore be described as a shallower, materially different encoding with the same state count. Neither the lower address sum nor the lower symbolic-rule count should be presented as a demonstrated overall execution-time speedup.

## Mathematical conclusion and limits

The accepted K215 numerical-calculus calibration, full ordinal source bisimulation, separately executed unbounded primitive contracts, their positive durations, and the exact calibrated blank startup compose into an ordinary mathematical proof formalizable in ZFC that

`Halt(K215R, blank) iff not Con(ZFC)`.

Equivalently, ZFC proves `not Halt(K215R, blank) iff Con(ZFC)`. The proof inherits the established compact-theory consistency reductions; this candidate does not introduce a different axiom system. No unconditional nonhalting, state-count minimum, new proof-assistant endpoint, internal-PA proof certificate, or 214-state result is claimed.

## Reproduction and attribution

From the packet root, run:

```bash
python3 code/review_depth41.py --packet . --output verification/independent_review-fresh.json
```

The script requires assertions enabled, reads compressed receipts transparently, and performs only finite source/table/startup and saved-runtime-record checks. A fresh complete symbolic runtime run remains a separate operation documented by the packet.

The parallel source-search task authored the rebalanced construction. The root task simplified and packaged its recipe. The encoding task independently reviewed the resulting frozen files and saved evidence. The inherited ProveIt machine, compact calculus, compiler, proof calibration, and runtime checker retain their original attribution and licensing.
