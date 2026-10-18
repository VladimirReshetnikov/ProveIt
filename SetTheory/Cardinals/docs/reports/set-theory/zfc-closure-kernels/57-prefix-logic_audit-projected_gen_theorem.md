# A fully calibrated GEN prefix using a Cantor projection

This is a source-level proof for the optimized prefix discussed during this
investigation. It retains the literal eight logical rows and gated native
bundle. It is not a claim of a sub-252 binary machine or a checked Lean
theorem. Binary compilation and startup are independent obligations.

## The algebraic observation

For Cantor pairing

```
P(x,y) = (x+y)(x+y+1)/2 + y,
Imp(A,B) = 4P(A,B),
All(i,A) = 4P(i,A)+2,
```

one has the exact identity

```
Imp(i,0) = 4P(i,0) = 2i(i+1) = P(i,i).
```

Hence both Cantor projections of the theorem code `Imp(i,0)` equal `i`.
Moreover `Imp(i,0)` has a purely propositional proof for every natural `i`:
truth0 and K give `0 -> (i -> 0)` and then `i -> 0`. K is obtained from the
original rho8 implicational basis without any use of GEN. This supplies
arbitrary numerical labels by decoding actual theorem codes.

## Exact optimized register prefix

Use original logical register names `T,S,d,h,X,Y`. The current theorem is
`T`, the theorem stack is `S`, the additive numerical parameter is `d`, the
cached theorem is `h`, and the clean scratch condition is `X=Y=0`.

Let `oldT=U`, `oldh=H`, and `unP(U)=(i,j)`. Replace only the first GEN prefix
of AX by this word:

```
unpair_T ; 122 ; 211 ; 162 ; 117 ; 159
```

Here `unpair_T` is one new decrement-T loop around the original unpair walk
body154. The numbered suffix consists entirely of original macros:

| Point | T | X | Y | h | S |
|---|---:|---:|---:|---:|---|
| entry | U | 0 | 0 | H | S |
| after unpair_T | 0 | i | j | H | S |
| after loop200 inside122 | H | H+i | j | 0 | S |
| after loop207 inside122 | H | 0 | j | H+i | S |
| after211 | H | j | 0 | H+i | S |
| after162 | 0 | 0 | P(j,H) | H+i | S |
| after117;159 | All(j,H) | 0 | 0 | H+i | S |

Node122 is the original par2 **tail**, not the full par2 macro121. Its
copy/restore pair is allowed here to start with nonzero scratch1. The
resulting change `h := H+i` is intentional. No entry in the theorem stack
is changed, and the old current theorem is consumed.

The original first GEN prefix used the full parameter push, full cached
theorem push, and All constructor. The new prefix replaces only that first
occurrence, not every parameter push in the program. In particular it does
not perform the unsound global MP modification described by prior work.

## Exact AX command contract

Let the command fields be `(c,x,y,u)` and the input working state be
`(U,S,d,H)`. Define

```
(i,j) = unP(U),
a = d+x,
b = H+i+y.
```

The new AX returns current formula equal to the original gated bundle at
`(a,b,c)` and stack

```
[rho1(a,b), rho2(a,b,c), rho3(a,b,c), rho4(a,b,c),
 rho5(a,b,c), rho6(a,b), rho7(a,b,c), rho8(a,b,c,u),
 All(j,H)] ++ S,
```

where `++ S` denotes successive Cantor pushes above the old stack. The
gate is the unchanged test `c != a` and `c != b`; otherwise the current
formula is truth0. Both `d` and `h` finish zero, and both scratch registers
finish zero. The original current theorem `U` is not saved below the rows.

The new `b` is essential. It is not correct to claim that this edit preserves
the original command's output formula parameters for arbitrary dirty `U`.
The existing AX code reads the second parameter after the GEN prefix, so it
uses `H+i+y`, exactly as the table above requires.

## Soundness

At command boundaries, retain the original invariant: the current formula,
the cached formula, and every theorem-stack entry are C254 theorems. Both
numeric parameters and the candidate-enumeration registers are unrestricted.

For the new AX, the GEN row is `All(j,H)`. It is an original C254 theorem
because `H` is a theorem and the original calculus allows GEN at every
natural `j`. Each of the other eight emitted rows is an original logical
axiom at its actual numerical parameters. The current bundle passes exactly
the original gate at those parameters. Thus every output theorem satisfies
the invariant.

The temporary register value `H+i` need not be a theorem code. After the
first GEN row, the original AX body uses that register as an axiom parameter
and finally clears it. No intermediate command boundary or second use of
the cache as a theorem is inserted. Imposing the command-boundary invariant
on this intermediate numerical value would unnecessarily forbid a sound
optimization.

Unchanged DROP and NIP preserve the invariant. The known successful-MP
dummy-zero deletion also preserves it, as does the optional consuming-DROP
variant of the companion theorem. Halting at the NIP falsity comparison
therefore still implies `C254 1`.

## Completeness of proof blocks

A block for formula `A` maps every `(T,S,0,0)` to `(A,S,0,0)`, or halts
already. No theorem assumption on the arbitrary underlying `T,S` is needed
for this algebraic contract.

Use the destructive-AX normalization and extraction blocks in
`destructive_axiom_theorem.md`. In normalization, each logical-axiom
extraction, each bundle extraction, and MP cleanup, the AX input current
formula is zero. Its Cantor projections are therefore zero. The offset `i`
vanishes, and all selected logical rows and bundles have exactly the
parameters specified by those block proofs. The GEN row may differ from
the companion rewrite's unused GEN row, but it still has tag2 and is never
falsity code1. Their row counts and stack-clearing arguments are unchanged.

In particular, the truth/axiom/MP fragment has proof blocks without any use
of a GEN block. For each `j`, let `q_j` be the block for `Imp(j,0)` obtained
from the fixed propositional K derivation and truth. Its construction is
independent of the generalization case below.

Suppose `p` is already a block for `H`. Write `D=DROP0`, `N=NIP0`. The new
block for `All(j,H)` is

```
p ; D ; q_j ; N ; AX(c=0,x=0,y=0,u=0) ; N^9 ; D ; N.
```

If no earlier instruction halts, its key states are:

1. `p` returns `(H,S,0,0)`.
2. `D` saves `H` above `S`, with current/cache zero.
3. `q_j` returns `(Imp(j,0), P(H,S), 0,0)`.
4. `N` exposes cached `H` and restores the underlying stack `S`.
5. The prefix decodes `Imp(j,0)=P(j,j)`, so AX emits `All(j,H)`. The bundle
   gate is zero because `c=a=0`, irrespective of the shifted parameter
   `b=H+j`.
6. Nine NIPs expose the GEN row. DROP makes it current and saves the old
   zero current formula. The final NIP removes that zero and clears cache.

The result is exactly `(All(j,H),S,0,0)`. This proof works with either
successful-MP stack convention and either preserving or consuming DROP.
All NIPs in the fixed selection suffix test zero or an emitted tag0/tag2
row, never1; any earlier halt from a recursive block is already sufficient.

Structural induction on an arbitrary C254 derivation now gives a block for
every theorem. There is no appeal to restricted-GEN completeness,
alpha-renaming outside a reservoir, or a change to the native theory.

## Exhaustive search and the ZFC comparison

The scheduler and command encoding are unchanged. The first AX of the
usual reset-prefix construction still sets `d=h=0` on every input working
state. A block for1 followed by `DROP;NIP;NIP` therefore supplies a halting
candidate word from every persistent working state. Padding the first
AX's parameter `c` places this candidate beyond any finite initial
candidate counter exactly as in the companion theorem.

The new arithmetic prefix terminates for every finite register value:
unpair_T strictly consumes T, and all remaining constituent loops have the
original terminating contracts. Thus the standard scheduler argument still
reaches every candidate, or halts earlier. From a sound initial frame,

```
new command enumerator halts  iff  C254 1.
```

The original native-theory/ZF/ZFC refutability comparison is reused without
changing its logical input. Consequently a binary table that correctly
implements this new source program and reaches its sound initial frame has
the same consistency equivalence. Those finite binary and startup claims
must be established for the actual emitted table; this source argument does
not infer them from a reported state count.

## Attribution and verification boundary

The macro meanings and original logical calibration are taken from pinned
ProveIt sources `L2Lib254.lean`, `L2Macros254.lean`, `L2Control254.lean`,
`Code254.lean`, and the existing native/ZF/ZFC comparison. The successful-MP
dummy push deletion is documented prior work in
`mp_dummy_push_partial_cost.md`.

The projection identity, exact dirty-cache prefix, and block argument here
are ordinary mathematical proofs. `verify_projected_gen.py` independently
checks the proposed prefix by exact decrement/increment arithmetic and
checks its source block interfaces on bounded integers. Those checks are
evidence about the displayed equations; they are not a compiler proof or a
new serialized object-ZFC proof.
