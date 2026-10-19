# Uniform proof of the transferred K230 copy-loop identity

The replacement is

`((CD 6, (CI 5, CC 2)), CI 5)`  →  `(CI 5, (CD 6, CC 2))`.

Let the source machine's register file be arbitrary, with R6=n and R5=m. Here n,m are arbitrary natural numbers. The two registers are distinct. Every other register remains untouched.

## Source control

In the old tree, the leaves have local paths `00`, `010`, `011`, `1`. At `00`, a zero decrement skips its containing left subtree and reaches the increment at `1`. A positive decrement reaches `010`, then the continue at `011`. Removing the last two right turns from `011` returns control to local subtree `0`, whose first leaf is `00`. Thus the left subtree repeats a successful decrement and increment until R6 reaches zero; the final increment at `1` then executes once.

In the new tree, the leaves have local paths `0`, `10`, `11`. After the increment at `0`, the decrement at `10` tests R6. A zero test exits the complete replacement subtree. A positive test reaches the continue at `11`, which removes the last two right turns and returns to the beginning of the whole subtree, first leaf `0`.

In both trees, every externally entered execution starts at the first leaf. Both subtrees have boundary `(0,0,false)`: neither exports a break, a continue, or a halt. This permits replacement in every enclosing source context, since the finite source syntax admits external jumps only to complete ancestor entries or exits, never to an arbitrary proper interior leaf of the replaced closed subtree.

## Arbitrary-input induction

For the old tree, after k successful decrements, where 0<=k<=n, control is about to test R6 and the pair of register values is

`(R6,R5) = (n-k,m+k)`.

At k<n the next positive decrement, increment, and continue establish the same assertion at k+1. At k=n the zero test reaches the final increment, giving `(0,m+n+1)` and normal return.

For the new tree, after k successful decrements, where 0<=k<=n, control is at its initial increment and the same pair is `(n-k,m+k)`. The increment first changes this to `(n-k,m+k+1)`. If k<n, the successful decrement and continue restore the loop assertion at k+1. If k=n, the zero test returns normally with `(0,m+n+1)`.

Each loop performs exactly n successful decrements, n continues, n+1 increments, and one final zero test. Each therefore takes exactly `3n+2` primitive source instructions. Their intermediate register files differ; their complete entry-to-exit functions and total primitive-step counts agree for every natural n,m. This is an induction on an arbitrary natural, not an inference from finite simulation.

## Exact K230 occurrence binding

The pinned `machine/sites230.json` has SHA-256

`400fad2b1c5f99ed8490f6346ff63088ba94fc39ada376962cee2f68c092e487`.

The old tree occurs exactly four times, at:

- `111010010010111111000011`;
- `11101001001011111110011`;
- `1110100101100011`;
- `111110011`.

The standalone source builder confirms these are the same literal structural subtree and replaces all four by the same new tree. The instruction census decreases by four, from 5,125 to 5,121. Both sources have 212 distinct DAG nodes, maximum depth 40, and maximum zero run 6. Equal DAG counts do not preclude a binary state fold, but no state saving follows merely from the source census.

The changed `sites_logical.json` is an input to a new binary runtime verification. The original Rocq theorem certifies the frozen K230 table and source; changing the source requires a new source-to-table theorem or a proof that a proposed table executes this changed source. The loop theorem supplies the source-semantic part of that composition.
