# Independent audit of the source-level commutations

Audited 18 October 2026: `semantic_work/commutations.py`,
`semantic_work/affine_commutations.py`, the pinned `rmpath.py`, and the
actual `ast_dag` / fine-atom data. This is an ordinary semantic audit,
not a new proof-assistant theorem or an independent binary-TM bridge.

## Result

The two commutation criteria are sound for the actual atoms inspected.
The actual input has 226 well-formed acyclic AST nodes and 30 fine atoms,
all closed. The affine recognizer accepts 22 atoms: five increments and
17 draining loops. It adds 44 commuting pairs to disjoint-support
independence. All accepted atoms are free of `halt`, and all 17 zero
branches reach the wrapper sentinel at consumed path `[True]`.

A generic recognition issue was found and corrected during this audit:
testing only that the zero endpoint's opcode was `halt` could confuse an
internal halt with the wrapper's normal-completion sentinel. The current
script additionally checks the exact consumed path `[True]` and absence
of internal halt. None of the actual 22 accepted atoms was affected.

## Closed-block semantics

The AST leaf syntax is `inc r`, `dec r`, `brk k`, `cont k`, or `halt`.
Registers are numbered 0 through 8. The actual source nodes have integer
registers in that range, nonnegative integer jump levels, and node edges
to strictly earlier nodes. There is consequently no malformed operation,
out-of-range register, or cyclic AST hidden in this dataset.

For a block T, the two closure bounds are the required external break and
continue levels. An increment or halt requires (0,0), a decrement (1,0),
break k requires (k,0), and continue k requires (0,k). For N(A,B), the
bounds are

    (max(break(A)-1, break(B), 0),
     max(continue(A), continue(B)-1, 0)).

This agrees with `rmpath`'s consumed-path arithmetic: entering a left
child supplies a false frame for break; entering a right child supplies
a true frame for continue. Increment performs binary succession on the
consumed path, break strips the specified number of false frames before
succession, and continue strips true frames. The zero branch of a
decrement is break1. Structural induction gives the closed-block
interface: execution begun at the block's entry either remains inside,
encounters a halt, or returns at the ordinary successor of the block.
A closed block cannot jump into an arbitrary outer continuation.

In the no-halt case it therefore denotes a partial function on natural
register files. The undefined case means divergence. Residual pointer
bits beyond a leaf do not alter this interface, because every operation
uses the consumed path returned by `site`, not the unused suffix.
Associating a sequence of closed blocks in different binary trees
preserves composition of these partial functions.

## Disjoint support

The support used by `commutations.py` includes every register occurring
in either an increment or a decrement; it counts both reads and writes.
All control operations other than decrement are independent of the
register values. For a closed no-halt block, two initial states agreeing
on its support have identical control behavior and identical supported
register effects, while unsupported registers remain unchanged. This is
an induction on finite execution prefixes, followed by the deterministic
divergence case.

Let closed no-halt blocks A and B have disjoint supports. A cannot change
B's termination condition, and B cannot change A's. If both terminate,
their supported updates commute and both orders produce the same full
register file. If either diverges, both orders diverge. Thus their
partial functions commute, including their domains. This is stronger
than a sampled run check and does not require totality of the atoms.

The certificate changes a source word by adjacent swaps satisfying this
criterion. The multiset check, step-by-step crossing check, and exact
target reconstruction are sufficient to certify that word permutation.
The source-word generator's support-based dependency DAG is only a
search aid; its outputs are checked by this independent swap criterion.

## Exact affine maps

The second criterion is deliberately stronger and needs total atoms.
An increment has the expected affine map. A recognized draining loop has
these finite control properties:

1. No increments precede its first decrement test, on register r.
2. Taking the positive branch follows a finite segment of increments,
   break and continue instructions, returning to exactly the same
   consumed test path. There is no intervening decrement or halt.
3. Register r is not among the segment's increments.
4. Taking the zero branch follows a finite segment with no increments
   and reaches the wrapper sentinel at exactly `[True]`.

The finite segment runner stops at the first decrement or halt, so these
checks account for every possible conditional exit. In particular,
testing that the returned decrement opcode merely equals the initial
opcode would be insufficient; the script also checks the consumed path.

If the positive segment increments register j exactly n_j times,
induction on the initial value of r proves total termination and the map

    r := 0;  j := j + n_j * old(r)  for every j != r.

There is no invariant restricting other registers. A register file is
represented by a 10-coordinate column, its nine natural values followed
by constant1. The script constructs the corresponding exact integer
matrix; its final coordinate remains1. Equality AB=BA therefore proves
equality of total register transformations for all natural register
files. It justifies all 44 additional pairs without asserting that their
decrement traces are bisimilar.

The 17 loop tokens are
`b d g i j k l n o q r s u w x y A`.
The five increment tokens are `a c f m t`.

## Contextual replacement and the proof boundary

For every adjacent swap, both blocks return through the same ordinary
entry/exit interface and have equal partial register transformations.
Replacing them inside a closed sequence, then inside a larger structured
tree context, preserves behavior under every initial register file.
If a surrounding loop visits the replaced region repeatedly, induction
on the visits preserves the same boundary register state; if either
version diverges within the region, the other does as well. Surrounding
halt sites therefore occur in one version exactly when they occur in
the other. The same argument justifies substituting equivalent closed
sequence words for grammar definitions.

The dependence relation used by the affine trace canonicalizer is
symmetric and irreflexive. Connecting each letter occurrence to the
latest occurrence of each dependent letter preserves the order of every
dependent pair by transitive closure, because equal-letter occurrences
are dependent. Topologically sorting this DAG gives a linear extension;
two such extensions differ by adjacent swaps of incomparable positions,
whose letters are independent. Canonical equality therefore witnesses
a word equivalence under the established swaps.

This semantic replacement is a source-program theorem. The old strict
`rmpath` decrement-trace bisimulation may correctly reject a changed
source order, because it insists on the same next decrement register.
One must replace that source-equivalence boundary with the partial-
function theorem, then separately establish the candidate grammar / DAG
and binary compiler bridge. Once those independent bridges are proved,
the ordinary ZFC argument transports the established consistency
equivalence. Neither a passing source commutation check nor matrix
equality alone certifies a complete binary machine or a state count.
