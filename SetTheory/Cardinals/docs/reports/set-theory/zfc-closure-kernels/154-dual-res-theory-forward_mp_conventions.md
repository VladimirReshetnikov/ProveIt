# Complete proof enumeration with three simpler MP returns

This note calibrates changes to the successful MP *return convention*, leaving
the formula calculus and proof-command encoding unchanged. It is conditional
only on the source block implementing the stated register contract; it makes
no transition-table or state-count claim.

Write a command state as `(t,w,d,h)`: current theorem, theorem stack, additive
parameter counter, and cached theorem. The common command reader changes the
counter to `D=d+x`. The current forward MP test is

\[
 I(t,D)=h.
\]

The following successful return conventions are each sufficient:

| Name | Successful return | Failed return |
| --- | --- | --- |
| `no_push_copy` | `(D,w,D,0)` | `(0,w,D,0)` |
| `no_push_move` | `(D,w,0,0)` | `(0,w,D,0)` |
| `no_push_cache` | `(0,w,0,D)` | `(0,w,D,0)` |

All three preserve the existing stack. The source contract also clears both
scratch registers, leaves selector register 3 zero, and preserves next-proof
and proof-list registers. In the cache convention, cache `D` is a theorem on
success by MP; in the other conventions, current `D` is a theorem. Every
other changed field that denotes a formula is zero, the native truth code.
Thus the original theorem invariant and soundness proof transfer directly.

## One-command DISCARD for all three conventions

Starting from `(T,w,0,0)`, execute `CMP(0)`. Its comparison is `I(T,0)=0`.
Native pairing implies that this equality holds exactly when `T=0`. If it
holds, `D=0` makes all three successful returns `(0,w,0,0)`; otherwise the
failed return is also `(0,w,0,0)`. Therefore

\[
 \mathrm{DISCARD}_{new}=[\mathrm{CMP}(0)]
\]

has the exact old DISCARD contract for every `T,w`. This calculation includes
the exceptional formula identity `I(0,0)=0`; it does not force a failed match.

## Standard block contract

For any code `X`, a block `L_X` has the contract that, from every `(T,w,0,0)`,
it either halts or returns `(X,w,0,0)`. The unchanged axiom-leaf, gated-bundle,
and GEN templates from `L1_Comp222.v` retain this contract after replacing
their use of DISCARD by the single command above. Their remaining stack
calculations do not depend on the MP return convention.

For MP, suppose blocks `L_A` and `L_I` respectively build `A` and `I(A,B)`.
Use the common prefix

\[
 L_A;\ \mathrm{DROP};\ L_I;\ \mathrm{NIP};\ \mathrm{DROP};\
 \mathrm{NIP};\ \mathrm{CMP}(B).
\]

Before the last command the state is `(A,w,0,I(A,B))`, unless an earlier valid
halt occurred. In particular, if `A=1`, the second NIP already halts, which is
an acceptable outcome of the block contract. The last comparison succeeds.

### `no_push_copy`

The common prefix returns `(B,w,B,0)`. Append

\[
 \mathrm{CAX}(B,0,0,0);\ \mathrm{NIP}^{10};\
 \mathrm{DROP};\ \mathrm{NIP}.
\]

The AX command sets its input label and private code both to `B`, so its gate
returns zero, and it resets counter and cache. It pushes ten entries: the old
current `B`, its GEN entry, and the eight axiom rows. Ten NIPs leave current
zero, stack `w`, counter zero, and cache `B`. All nine preceding popped entries
have non-membership tags, so none is the native contradiction 1. DROP sets
current to `B` and pushes zero. The final NIP either halts when `B=1`, or pops
that zero and returns `(B,w,0,0)`. Compared with the old MP proof block, the
final extra NIP is removed because no MP dummy zero was pushed.

### `no_push_move`

The common prefix already returns `(B,w,0,0)`. It needs no suffix.

### `no_push_cache`

The common prefix returns `(0,w,0,B)`. Append only

\[
 \mathrm{DROP};\ \mathrm{NIP}.
\]

DROP returns `(B,P(0,w),0,B)`. NIP halts if `B=1`; otherwise it pops zero and
returns `(B,w,0,0)`. This gives the entire MP block

\[
 L_A;\mathrm{DROP};L_I;\mathrm{NIP};\mathrm{DROP};\mathrm{NIP};
 \mathrm{CMP}(B);\mathrm{DROP};\mathrm{NIP}.
\]

## Completeness from the existing bootstrap seed

The preceding contracts compile every ordinary native proof by induction.
To compile a contradiction proof, use the old fixed START command
`CAX(0,1,1,0)` to reset counter and cache from arbitrary retained state, run the
new block for code 1, then use the old suffix `DROP,NIP,NIP`. The resulting
command list halts from every retained state.

The command fields and Cantor-pair tail coding are unchanged. The proof-list
tail decreases between candidate boundaries, and the next-proof counter is
incremented at a boundary. Consequently every later candidate number is
reached unless the machine halts earlier, exactly as in `reach`, `drain`, and
`reach_from` in `L1_Comp222.v` and `Seed222.v`. The encoded START selector is at
least 3, so the contradiction program is available from the original seed
`(pl=0,np=3,tw=0,ws=0,d=3,h=0)` as well as the all-zero abstract seed.

Each variant therefore enumerates the same inconsistency condition as the
original forward-MP program. In combination with the baseline native theory
calibration, its halting is equivalent in ZFC to inconsistency of ZFC, provided
the concrete source and machine implement the stated command contract.

## Application to the newer K219 equality macro

The upstream K219 source changes the internal tree of its four equality
comparators, while preserving the following all-natural contract. With
registers 5 and 6 initially `a,b`, the macro clears both registers and
returns normally exactly when `a=b`; otherwise it returns one level of
structured break. All other registers are preserved. In particular, the
MP call still tests exactly `I(t,D)=h`. The new open, ten-leaf comparator
therefore changes none of the command or proof-block calculations above.

For the K219 `no_push_copy` and `no_push_cache` candidates, the comparison
prefix is retained and only its successful return suffix is changed.
Consequently the same proof applies to their respective contracts in the
table, with the same axiom blocks, START command, command encoding, and
candidate-reachability argument. There is no need to transfer a proof
through the older comparator's internal source tree. The remaining
concrete obligations are that the complete revised source has that command
contract and that its compiled transition table simulates the revised
source. Those obligations are separate from this enumerator calibration;
a source-leaf count or finite runtime test alone does not discharge them.

## Broader NIP halt predicates

The same proof permits NIP to halt on **any cached membership atom**,
`h mod 4 = 1`, instead of only code 1. Under the theorem invariant, a halted
cache would be a globally valid membership atom in every model of ZFC.
Assigning the same object to its two variable labels contradicts
irreflexivity. Conversely, code 1 is among the newly accepted halt codes, so
the compiled contradiction program still halts. Extra earlier halts are
acceptable outcomes of every block contract.

For this predicate, the nonhalting NIP branch must still clear the old cache
and then pop the next stack entry. The nine axiom/GEN entries used in the
copy-return cleanup have implication or quantifier tags, and its gated top
has implication tag or is zero, so that calculation remains valid.

There is further optional freedom: globally valid equality atoms must have
equal variable labels. Their codes are

\[
 E(a,a)=8a(a+1)+3\equiv3\pmod{16}.
\]

Thus NIP may also halt on equality-tag codes that are not 3 modulo 16. In
particular residue 7 modulo 8 is safe to add to a membership halt predicate.
These are additional permitted false-theorem detectors, not required changes
to any of the three MP conventions.
