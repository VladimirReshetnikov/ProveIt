# Mathematical scope of the contextual alternative

This is an intake exposition of Source147's construction, not a new logical calibration. The original submitted report and proof inputs remain recoverable through intake190. The inherited K219 calibration and all attribution remain unchanged.

## Source and allocation

Both the accepted K218 and this alternative have4,744 primitive occurrences and205 distinct source subtrees. Their source addresses differ at4,724 ordinals, but the operation and argument at every ordinal and all6,166 nonhalting guarded successor edges agree with K219. Relating corresponding ordinal configurations by identical nine-register stores therefore gives a strong source bisimulation for every natural store. Decrement's zero/positive split exhausts all naturals; no reachability assumption is used.

The submitted construction first reparses and reallocates the original K219 table, preserving the first37 source addresses. It temporarily adds79, then removes190 after making188 a direct decoder. Two rotations reuse existing helpers12 and150. Finally, state96 is folded into85. The successive physical counts are219,219,220,219,219,219,218. The final table has79 added and96/190 removed relative to K219, with57 retained rows changed. These intermediate allocations are construction data; final arithmetic correctness requires the complete final-table runtime proof.

## The contextual saving

Immediately before the final fold, states85 and96 both have zero action `0 R 98`; their one actions enter12 and150 respectively. Nine admitted source prefixes for the85 role end in0, and four prefixes for the96 role end in1. The final table redirects `177/1` to85, deletes96, and gives85 the one action `1 L 221`.

For scanned1 and predecessor0, the path is85→221→188→12, with heads0,−1,0,+1. For predecessor1, it is85→221→189→156→176→150, with heads0,−1,0,−1,0,+1. Every row writes the bit already present. Both paths restore the entire tape, touch only those two cells, and return to the required child after3 or5 positive steps. Scanned0 uses the shared direct row. The predecessor premise is essential; this alone is not a theorem for arbitrary entries to85.

The alternative's source-prefix audit checks all4,743 interior prefixes using132,281 literal transitions, reading no unknown exterior and preserving every supplied bit. Complete primitive runtime proofs are still needed to include arithmetic uses of shared states and the return to the dispatcher.

## Whole computation

The complete initializer is required to reach state84, head−5, sentinel−6, header139, gap80, logical registers `[3,0,0,0,3,0,0,0,0]`, and130 one-valued spares, with exactly277 one cells and every other cell zero. Source147 specifies312,701 steps. The initialized source is then simulated by positive finite machine blocks, with no interior halt in a nonhalting primitive.

The6,167 primitive interfaces quantify over nine arbitrary natural registers, arbitrary extra gap and first spare value, and an arbitrary finite remaining spare list. Literal transitions, exact unary-loop induction and finite-list induction justify the symbolic derivations; the proof-search bound does not bound those semantic parameters. Full-tape endpoint equality and positive duration permit concatenation. Machine halting is equivalent to source halting, which transfers through the source bisimulation to the pinned K219 refutation search. Thus the stated ordinary mathematical argument gives the ZFC-provable nonhalting/Con(ZFC) equivalence. It does not prove Con(ZFC), unconditional nonhalting or minimality, and is not a new exact-byte Lean/Rocq endpoint.

## Why this saving does not add to the accepted K218 saving

The independently calculated [role comparison](comparison/comparison.json) identifies exactly the same two source-subtree types at final85, with identical9+4 multiplicities, in both218 constructions. Accepted K218 implements the same marker routes through190 and removes212; this alternative routes through221 and removes96. The retained212 in the alternative has rows `0 R 92` and `1 R 79`, not the shared-zero-child role needed by accepted K218's fold. There are65 differing common rows, so the two allocations cannot be united as disjoint patches.

This excludes counting the same contextual fold twice. It does not rule out another saving in the different allocation. The separately checked [row157 variant](variant-row157/README.md) composes by an all-initial-tape positive-block equivalence and remains218 states.
