# A verified specialization from 3,909 to 3,904 source primitives

## Result and limits

The supplied class-A U208 source can be specialized to a source with **3,904 primitive occurrences and 5,076 ordinal control edges**, preserving halting from its established canonical initial state

\[
(pc,r_0,\ldots,r_8)=(136,1,0,13,0,0,1,0,0,1).
\]

The original source has 3,909 primitives and 5,083 edges. The two substitutions below remove five primitive occurrences. This is a source-program theorem. **It is not a 207-state Turing machine.** The number of distinct hash-consed source subtrees increases from 197 to 200; address depth stays 42 and maximum consecutive-zero length stays six. A correct physical allocation of the changed source is a separate research problem.

The exact original source is `original_sites.json`, SHA-256
`cddbed7f20e7a8b085b7ca0e76811d07b021522375643b5d1134eec0d2d23164`.
It is the source in the supplied class-A Three-cell U208 packet. The transformed source is `generated/optimized_sites.json`, SHA-256
`5c2ba0b336ea1e32921154a050c0231b5d1c45d440a7dd348ae39a57ef364f5d`.

## Source semantics

`CI i` increments register i and advances to the next primitive. `CD i` tests register i: on zero it follows its zero successor without changing the register, and on a positive value it decrements the register and follows its positive successor. `CB k` and `CC k` are register-preserving source jumps. `CH` halts. The input gives each primitive a binary address in a full binary source tree; the address determines the jump successors.

The checker reconstructs the complete tree and independently resolves the ordinal graph in two ways:

1. Intervals of source subtrees and outward ancestor walking.
2. Binary address increment, deletion of the requested zero/one ancestor, and zero-padded prefix decoding.

The second resolver checks the absence of a stray one beyond the decoded successor leaf. Both resolvers agree on every old and every new primitive.

## First substitution: a zero-input transfer loop

The original subtree rooted at address `0011011100` has these three leaves:

| Old ordinal | Address suffix | Primitive | Successors |
|---:|---|---|---|
| 3847 | `0` | `CD 1` | zero:3850; positive:3848 |
| 3848 | `10` | `CI 6` | 3849 |
| 3849 | `11` | `CC 2` | 3847 |

This is a loop transferring register 1 into register 6. At every reachable entry to ordinal3847, register1 is zero. Therefore the loop immediately exits to3850, leaving every register unchanged. Its body ordinals3848 and3849 are unreachable.

The parent subtree at `001101110` has the form `(loop,remainder)`, where both children are closed, nonhalting source factors. Replace that parent by its right child, originally at `0011011101`. This removes all three primitive occurrences.

### A local proof and a small inductive certificate

The sole external entry into the comparison region at3837 is the zero exit of `CD 1` at3834. That exit establishes register1=0. The source instructions3837 through3846 inspect and change only registers5 and6; their jump instructions preserve every register. Their exits either leave this region or enter3847. Thus every initial entry to3847 has register1=0. Its positive successor3848 is then impossible, so the hypothetical back edge3849→3847 is vacuous. The canonical initial ordinal136 lies outside this region. The complete incoming inventory verifies this state-conditional invariant by induction on source steps.

A compact independently reproducible finite certificate tracks **only register1**, with categories zero and positive. Every conditional decrement of any other register is treated nondeterministically. The abstract rules are:

- `CI 1` establishes positive; other increments preserve the category.
- `CD 1` at zero follows its zero edge and stays zero.
- `CD 1` at positive follows its positive edge and may become zero or stay positive.
- Either edge of any other decrement is permitted; jumps preserve the category.

These rules overapproximate every concrete source transition. The checker computes the least reachable family and then separately verifies initial membership and closure under every abstract transition. It contains **6,430 `(ordinal,category)` pairs**, assigns only category zero to3847, and assigns the empty set to3848 and3849. Its complete finite family is `generated/register1_zero_positive_invariant.json`.

Induction on a coded concrete run proves membership in the checked family. Therefore the transfer-loop premise follows without a consistency assumption. The proof and finite certificate are formalizable in PA.

For comparison with the discovery calculation, the checker also regenerates the nine-register joint zero/positive family with278,384 pairs. At3847 that stronger family is

\[
 \{1,5,17,21,257,261,273,277\},
\]

where bitj represents `registerj>0`; all eight masks have bit1 clear. It is saved as a512-bit little-endian integer for each old ordinal in `generated/zero_positive_invariant.bin`, SHA-256
`f454cf5c9403613e81d27213aebfab472853ae6f2e3e6fbd3e3ee3753cff5d96`.
This larger auxiliary certificate is not needed for the smaller proof.

## Second substitution: a redundant decrement in the target test

The original subtree at `1110011` is

\[
 ((\mathrm{CD}\ 6,\mathrm{CC}\ 2),\mathrm{CB}\ 1).
\]

Its leaves are old ordinals3891,3892,3893. At every reachable entry to3891, register6 is zero. Thus it executes the zero branch directly to3893, and3892 is unreachable. Replacing the entire subtree by a single `CB 1` at address `1110011` removes two primitive occurrences. In both versions, that `CB 1` exits to the first source leaf under prefix `1111`, old ordinal3895.

### A small invariant for the premise

Write \(X=r_6\) and \(H=r_5\). The relevant control edges are:

| Old ordinal | Instruction | Zero/positive or unconditional successors |
|---:|---|---|
| 3880 | `CD X` |3883 /3881|
| 3881 | `CI H` |3882|
| 3882 | `CC 2` |3880|
| 3883 | `CI X` |3884|
| 3884 | `CD H` |3888 /3885|
| 3885 | `CD X` |3887 /3886|
| 3886 | `CC 2` |3884|
| 3887 | `CB 1` |3889|
| 3888 | `CD X` |3894 /3889|
| 3889 | `CD H` |3891 /3890|
| 3890 | `CC 1` |3889|
| 3891 | `CD X` |3893 /3892|
| 3892 | `CC 2` |3889|
| 3893 | `CB 1` |3895|
| 3894 | `CH` |halt|

The complete source graph contains no additional incoming edges into ordinals3883 through3894 beyond this inventory. Entry to3883 comes from the zero branch of3880, so \(X=0\), and `CI X` establishes \(X=1\). Through the comparison loop at3884,3885,3888, the invariant is \(X\le1\). The positive decrement at3885 or3888 therefore leaves \(X=0\). The zero exit from3885 also has \(X=0\). Consequently every entry to3889 has \(X=0\). Its loop changes onlyH, so3891 has \(X=0\), and its positive branch3892 is impossible.

For a compact independently reproducible finite check, it suffices to track **only register6**, with categories0,1,at least2. All conditional decrements of other registers are treated nondeterministically, so no unproved correlation with another register is used. The checker derives9,651 reachable `(ordinal,category)` pairs and verifies inductive closure. It obtains categories`{0}` at3891 and the empty set at3892. This is much smaller than a joint nine-register three-category analysis.

## Exact source projection and halting equivalence

Let \(D=\{3847,3848,3849,3891,3892\}\). The new source retains the old primitive order after deletingD. On retained old ordinals, let\(f\) be the increasing bijection onto\(0,\ldots,3903\). For targets entering the two deleted identity tests, extend the projection by

\[
 f(3847)=f(3850),\qquad f(3891)=f(3893).
\]

The three other deleted ordinals are unreachable by the proved invariants. The checker verifies the following literal finite facts:

- Every retained old primitive has exactly the same opcode and operand after renaming.
- Every edge out of a retained old primitive has the projected target given by the new ordinal graph.
- The deleted3847 zero branch goes to3850 with no register change.
- The deleted3891 zero branch goes to3893 with no register change.
- The initial ordinal136, its address, and its instruction are unchanged.
- The unique halting primitive is retained.

At matched retained control locations, the two programs have identical register vectors. A new source step corresponds to one old source step, followed by at most one deleted identity test. Conversely, the old computation can only spend one step at either deleted test, if reached, before returning to a retained location; it cannot remain in a cycle of deleted instructions. The invariants rule out every deleted nonidentity instruction. Induction therefore gives a positive-block simulation with block lengths at most two, identical registers at boundaries, and matching halting. This proves the stated source-program halting equivalence from the canonical seed.

Both components are finite PA-verifiable syntax/counter calculations together with induction on a coded finite execution. No claim of a new Lean, Rocq, MM0, or exported PA certificate is made.

## Reproduction and next allocation problem

Run:

```bash
python3 verify_source_optimization.py
python3 -O verify_source_optimization.py --output optimized_python_result
```

The latter reproduces exactly the same files. Every required check uses explicit exceptions, so Python optimization does not disable them. The default run takes less than a second in the preparation environment.

The verified optimization establishes that this inherited source still contains removable behavior. It does not by itself shrink the physical table: the optimized source has200 distinct subtrees instead of197, because the old transfer and comparison subtrees were shared at other source occurrences. The next concrete problem is to allocate these specialized occurrences using existing guarded decoder behaviors, or to reassociate the surrounding factors so that specialization enables a net state deletion. Any such allocator must preserve the literal machine's shared arithmetic entries and must reverify startup and interpreter contracts.
