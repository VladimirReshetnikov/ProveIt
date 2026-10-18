# Destructive axiom emission with a shifted generalization binder

## Status and provenance

This is a source-level correctness argument for concrete changes to
the full original proof enumerator. It does **not** delete equality, weaken the
native set theory, or assume that a changed binary table simulates the old
instruction stream. Binary compilation, startup, and state counts must be
established separately. The source interface is the exact `Enum254.lean` at
ProveIt commit `43026ff42f0939f09b9e95495248cfadcad38e38`.

The MP dummy-push elimination is **prior work in the pinned repository**, not
a new idea of this report. `mp_dummy_push_partial_cost.md` already records
the source edge 166-to-167 change, the direct optimized-table patch, all 8,366
guard cases, a 2,998-pair source relation, and the one-NIP proof-compiler repair.
Its changed blank startup remained unresolved there. The argument below
supplies explicit combined proof blocks and independent exact tests; novelty
must be assessed separately for the shifted-binder AX change, cache-consuming
DROP, and any new initializer actually certified in this investigation.

The register compiler agent independently confirmed the relevant source
expansion: the first AX macro `166` is `171;167`, where `171` pushes the old
current theorem and clears its register and `167` adds a preserved copy of
the parameter register to that register. The following operations form the
generalization of the cached theorem. Replacing this *occurrence* of `166`
with `167` therefore has exactly the effect below. It does not mean globally
changing every occurrence of macro 166.

## Definitions

Retain the original natural-number pairing P and formula constructors. Write
I(A,B)=4P(A,B), U(i,A)=4P(i,A)+2, true=0, and false=1. The derivability predicate
is the unchanged twelve-constructor `C254` relation. In particular it is closed
under modus ponens, arbitrary generalization, the eight original logical
rows, and the original gated set-theoretic bundle.

A working state is `(T,S,d,h)`, where T is the current theorem, S is the Cantor
encoded theorem stack, d is an additive parameter, and h is the cached theorem.
Write `push(L,S)` for pushing the finite list L, first element uppermost. Write
`N^k` for k copies of `NIP 0`, and D for `DROP 0`.

For parameters a,h,b,c,u and an old current theorem t, let

    L(a,h,b,c,u;t) =
      [rho1(a,b), rho2(a,b,c), rho3(a,b,c), rho4(a,b,c),
       rho5(a,b,c), rho6(a,b), rho7(a,b,c), rho8(a,b,c,u),
       U(a+t,h)].

Thus L has length m=9. Every element is different from 1: the first eight
are implication codes, and the last is a universal-quantifier code. The
original `rho1` is an encoded existential and hence also has outer implication
tag. These congruence facts do not depend on consistency.

Keep DROP and NIP unchanged:

    DROP x: (T,S,d,h) -> (h,P(T,S),d+x,h).
    NIP  x: halt if h=1; otherwise
            (T,S,d,h) -> (T,second(S),d+x,first(S)).

For delta in {0,1}, use

    MP_delta x:
      if I(T,d+x)=h, output (d+x,Z_delta(S),d+x,0);
      otherwise output (0,S,d+x,0),

where Z_0(S)=S and Z_1(S)=P(0,S). Delta=1 is the original MP stack effect;
delta=0 omits its disposable pushed truth.

The new AX command is

    AX'(c,x,y,u):
      a := d+x; b := h+y;
      (T,S,d,h) -> (gate(a,b,c), push(L(a,h,b,c,u;T),S), 0, 0).

Here gate(a,b,c) is exactly the old bundle when c differs from both a and b,
and 0 otherwise. There are two changes to AX: the old T is not saved, and
the generated universal formula binds label a+T instead of a. No logical
axiom or inference rule is removed.

## Theorem

For either delta=0 or delta=1, the candidate enumerator retaining the old
command packing, fetch rule, increasing candidate counter, and modified
commands above halts from its zero working state if and only if `C254 1`.
Consequently, once a literal binary implementation and its blank initializer
are verified, its halting is equivalent to a ZFC refutation by the unchanged
theory calibration.

### Soundness

Use the invariant that T, h, and every entry of the decoded stack S are C254
theorems. It holds at the all-zero start. DROP and NIP preserve it. A successful
MP is an actual modus ponens; its optional extra stack entry is the theorem 0.
A failed MP returns 0 and preserves the existing stack.

For AX', all eight logical rows are original C254 theorems. Since h is a
theorem, `U(a+T,h)` is a theorem by generalization at the natural-number label
a+T. This uses no interpretation of T as a variable or any bound on its size.
The old gated bundle is a theorem, including its zero case. Thus every output
of AX' satisfies the invariant. The sole halting condition is h=1, which then
gives a derivation of 1.

This proof also shows why simply deleting the initial push is safe despite
leaving the old current theorem in an arithmetic operand: it changes only an
unrestricted generalization label. Leaving old data in an arbitrary repeated
logical parameter would not have the same justification.

### A precise block convention

Call a finite command list p a block for X if, for every T and S, it either
halts, or maps `(T,S,0,0)` to `(X,S,0,0)`. An early halt is acceptable: the
global soundness theorem already identifies every actually reachable halt
with a proof of 1. The block contract itself allows arbitrary numerical
T and S and does not presume that the stack is good.

All equalities below are exact command semantics. None assumes that the
enumerator resets its whole working state between candidate programs.

### Normalization

Define

    discard' = MP_delta 1; D; AX'(1,0,0,0); N^10.

From `(T,S,0,0)`, the first MP fails because `I(T,1)>0`, producing
`(0,S,1,0)`. DROP pushes a zero sentinel. AX' uses a=1,b=0,c=1 and old T=0;
its gate is zero, and it pushes nine non-1 rows above the sentinel. Ten NIPs
pop these nine rows and the sentinel, giving exactly `(0,S,0,0)`.

In particular normalization is total and does not inspect any entry of the
underlying S. Delta is immaterial because this MP takes its failure branch.

### The eight logical rows

Normalize, execute D to push a zero sentinel, and execute `AX'(c,a,b,u)`.
The resulting stack is `L(a,0,b,c,u;0) ++ [0]` above S. To select row j,
where 1 <= j <= 8, execute

    N^j; D; N^(11-j).

The first NIPs place the selected row in h. DROP makes it current and pushes
the gate. The remaining NIPs discard the gate, the lower rows, and the zero
sentinel. The output is the selected row with S unchanged and d=h=0. Every
discarded intermediate cache has a code different from 1. This gives blocks
for all original logical axiom instances, with no change to their parameters.

### The gated bundle

Normalize, push a zero sentinel with D, execute `AX'(c,a,b,0)`, and execute
N^10. The output is `(gate(a,b,c),S,0,0)`. Under the original two freshness
conditions, it is exactly the bundle. The gate's interpretation and both
conditions are unchanged.

### Generalization

Given a block p for H, append

    D; N; AX'(i,i,0,0); N^9; D; N.

After p succeeds, D and N produce `(0,S,0,H)`. Hence AX' has a=i, old T=0,
and h=H. Its gate is zero because c=a, and its last pushed row is exactly
U(i,H), with no shifted label. Nine NIPs expose this row in h. DROP puts it
in T and pushes the zero gate. One final NIP restores h=0 and the original S.
If an earlier NIP sees H=1, it halts; that is permitted by the block contract.

The actual sequence D;N before AX does not halt on H=1, since N's incoming
cache is 0. It first moves H into the cache; AX is then still executable.
The early-halt alternative is included uniformly, but is not needed in this
particular preparation step.

### Modus ponens

Given blocks p_A and p_I for A and I(A,B), form

    p_A; D; p_I; N; D; N; MP_delta B;
    D; AX'(B,0,0,0); N^10; D; N^(1+delta).

The first D saves A while p_I runs on the larger stack. The subsequent N,D,N
put A in T, I(A,B) in h, and restore S. If A=1, the last of these NIPs halts
before MP; otherwise MP succeeds exactly. Its output is

    (B,Z_delta(S),B,0).

The next D explicitly saves B and changes T to 0. AX' uses a=c=B and has zero
gate; it clears d and h and puts its nine non-1 rows above the saved B. Ten
NIPs put B into h and leave Z_delta(S). DROP puts B into T and pushes one zero.
If B=1, the next NIP halts. Otherwise, 1+delta NIPs remove this zero and the
optional MP zero, giving exactly `(B,S,0,0)`.

Therefore structural induction on a C254 derivation constructs a block for
every theorem code. Normalization supplies the truth base case; the preceding
sections supply all other constructors.

### Exhaustive enumeration without a reset assumption

The old command packing is untouched. A nonzero remaining pointer strictly
decreases on each command, so each candidate terminates or the machine halts.
The next-candidate counter increases by one at a new candidate. Thus every
finite command list encoded by the original `encL` is eventually reached,
unless the machine has already halted.

Suppose C254 derives 1 and let p be its block. The finite list

    AX'(0,1,1,0); p; D; N; N

halts from *every* working state: the first AX' clears d and h, regardless of
the old T and stack; p then either halts or returns current theorem 1 with
d=h=0; D,N,N halt. Therefore its candidate number suffices even though earlier
candidate computations leave their working registers in place. Soundness
and completeness now yield the claimed equivalence.

The same argument handles an arbitrary finite initial candidate counter N.
Replace the first AX' tag parameter 0 by c>=N; the command still resets d,h,
and the corresponding candidate code is at least c+3 by the pairing component
bounds. Thus a suitable universal halting candidate occurs above every N.

## Independent corollary: unchanged AX and MP without the pushed truth

One may instead change only MP, using delta=0 while retaining the entire old
AX effect, including its saved old T and the exact binder a. This variant is
also complete for the full original C254 calculus.

Soundness is the same invariant. Every old truth, axiom, bundle and GEN block
is unchanged: all their uses of MP except the modus-ponens combination are
known-failure normalization calls. The old normalization is

    discard = MP_0 1; AX(1,0,0,0); N^10.

The old axiom-selection and bundle blocks append the original AX and NIP
sequences to discard. The GEN block, after p_H, is

    D; N; AX(i,i,0,0); N^9; D; N; N.

For modus ponens replace the old combination block by

    p_A; D; p_I; N; D; N; MP_0 B;
    AX(B,0,0,0); N^10; D; N.

After the successful MP the state is `(B,S,B,0)`. The unchanged AX saves B
under its nine rows, sets the gate to zero because c=a=B, and clears d,h.
Ten NIPs put B in h and restore S. DROP puts B in T and pushes the zero gate.
One final NIP halts if B=1 or yields `(B,S,0,0)` otherwise. Relative to the
original MP block this removes exactly the last of its two cleanup NIPs;
the removed stack entry was exactly the MP-success truth.

The original derivation induction and candidate fairness argument therefore
apply with this new MP block. No source-AX change is needed for this corollary.
It is the applicable logical theorem when a compiled table changes only the
MP-success occurrence of macro 166 to 167.

## Further independent corollary: DROP may consume its cache

In any of the four AX/MP combinations above, DROP may be replaced by

    DROP_consume x: (T,S,d,h) -> (h,P(T,S),d+x,0).

It keeps the saved old T and new current theorem h, but sets the cache to the
truth code instead of retaining a duplicate h. Soundness follows from the
same invariant.

The written normalization, row, bundle, GEN and MP blocks remain valid with
this replacement. After every DROP used inside these blocks, a subsequent
NIP reloads the cache from a known stack entry; the old duplicate h is never
needed as an inference premise. During MP preparation and cleanup, removing
that duplicate can prevent an early halt when A=1 or B=1. In those cases the
block simply continues to its exact claimed output instead, which is
permitted by the block contract. Every other claimed output is unchanged.

The final falsity detector `D;N;N` also still works: from `(1,S,0,0)`, D saves
1 while leaving cache 0; the first NIP loads 1, and the second halts. Therefore
the derivation induction and global refutation equivalence are unchanged.

This rewrite is useful only if a literal implementation can replace the
cache copy/restore routine by a smaller destructive transfer while restoring
its scratch registers. Leaving an unaccounted scratch value does not follow
from this source corollary. No binary state saving is inferred here.

## Recovery from a useful initializer frame

An initializer need not establish the theorem-stack invariant at its first
structural root if a separately checked finite continuation establishes it.
For example, consider the exact logical register vector

    (N,T,W,A,D,H,X,Y,L) = (0,0,0,0,1,1,0,0,0).

The cache H=1 means this frame is **not** invariant-safe and it must not be
accepted merely by inspecting its tape shape. Nevertheless, at the abstract
command level its next candidate is 0. Since P(0,0)=0, the two command fields
decode as MP and additive increment 0. The comparison is

    I(0,1) = 4 P(0,1) = 8 != 1.

Thus MP takes its failure branch in all four AX/MP variants, producing

    (N,T,W,A,D,H,X,Y,L) = (1,0,0,0,1,0,0,0,0)

at the next complete command boundary, provided the implementation's ordinary
read and MP macros have their stated effects from zero scratch registers.
This latter frame is safe: T, H and every stack entry are 0, while the free
additive parameter D may be 1. Starting the candidate counter at 1 does not
lose completeness, by the arbitrary-counter argument above.

For a new binary initializer the obligation is therefore to verify the whole
finite continuation to this safe command boundary, including the complete
tape and scratch fields. A structural first root with H=1 alone is not a
certificate. The physical spare suffix remains governed by the binary runtime
contracts and is not a logical theorem-stack suffix.

## What the theorem does and does not certify

It certifies two exact source rewrites: AX loses the initial push and its GEN
binder becomes a+oldT; MP may lose the pushed zero on success. It provides
the unchanged consistency calibration by complete derivability equivalence.

The full binary compiler's stack arithmetic, dispatch, state table, universal
runtime simulation, and blank startup are separate obligations. A lower
number of macro calls does not itself imply a lower number of binary states.
Neither finite literal runs nor the proof of this source theorem proves the
remaining binary statements.

## Exact primary sources

- [Enum254.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/43026ff42f0939f09b9e95495248cfadcad38e38/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Enum254.lean)
- [Code254.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/43026ff42f0939f09b9e95495248cfadcad38e38/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean)
- [Prior MP dummy-push elimination](https://github.com/VladimirReshetnikov/ProveIt/blob/43026ff42f0939f09b9e95495248cfadcad38e38/Computability/BusyBeaver/Research/ZFC/mp_dummy_push_partial_cost.md)
- [Original compiler snapshot](https://github.com/jeff87654/busy-beaver/tree/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254)
