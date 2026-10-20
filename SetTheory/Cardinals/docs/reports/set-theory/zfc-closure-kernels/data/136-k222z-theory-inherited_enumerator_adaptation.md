# The changed bundle, finite proof compilation, and a nonzero cutoff

> **GC222 adaptation note (20 October 2026).** The historical text below
> describes the K224 bundle adaptation. The present conditional-G222 source
> additionally replaces logical row 7 by G. The argument still applies:
> G occupies the same row position, is an axiom instance of the new numerical
> calculus, and has an implication at its root, so its code is not 1.
> The other command, stack, reset, and block interfaces are unchanged. The
> current packet's exact emitter and uniform G certificates bind these facts
> to the actual GC222 source. References below to a change only in the bundle
> describe the inherited K224 step, not the full GC222 source change.

## Scope and pinned interfaces

This note is an ordinary proof adaptation of the frozen interfaces in
`coq/logic/Enum230.v` and `coq/logic/L1_Comp230.v` at K230 commit
`3142e4dd980f0be12f4abb636c4ae2528afc17eb`.

The main K224 source keeps the eight logical rows and their order, all
proof commands, parameter decoding, and reset effects. Only the gated
bundle expression changes. The exact emitter contract identifies that
expression, and the mathematical equality/fusion calibration identifies
its theory. No new Rocq endpoint for this adaptation is claimed.

The optional row permutations in the final section are valid further
source-layout choices, not edits made in the main machine.

## 1. Command semantics and the only changed premise

Use the persistent command tuple `(t,w,d,h)`: current formula, encoded
stack, additive parameter counter, and cached formula. An AX command
`AX(c,x,y,u)` sets

    a = d+x,  b = h+y,
    t' = gate(a,b,c),  d'=h'=0,

and pushes, in bottom-to-top order,

    old t, All_a(old h), rho8(a,b,c,u), ..., rho1(a,b).

The main gate is 0 if c=a or c=b; otherwise it is the independently
identified new fused bundle. Its enabled output has an implication
constructor at its root, so its code is a multiple of 4 and is not 1.
The disabled output is 0, also not 1. Every logical row and universal
formula pushed above the old current formula likewise has code other
than 1.

The proof-state soundness invariant says that current formula, cache,
and all entries in the stack are numerical theorems. The truth seed 0
starts the invariant. AX supplies theorem instances; its generalization
of the old cache is theorem GEN. MP, DROP, and NIP retain their exact old
effects. A halting NIP has cache 1, hence gives a refutation. Arbitrary
initial parameter counters do not enter this logical invariant.

## 2. The finite block compiler still applies

The original block contract for a formula X is:

    for every T,w, running block L from (T,w,0,0)
    either halts, or finishes at (X,w,0,0).

In particular the contract quantifies over *all* initial current-formula
and stack codes, not just over stacks whose formulas are theorems.

The original `DISCARD` block is

    [MP(1), AX(1,0,0,0)] ++ NIP^10.

It establishes a clean current truth seed and retains the underlying
stack when entered with d=h=0. The proof uses only the retained command
semantics, the old gate `gate(a,b,a)=0`, and the non-1 status of skipped
logical rows. Neither the K matrix nor the equality helper is inspected.

For the unchanged top-first logical-row index j in {1,...,8}, the leaf
block is

    DISCARD ++ [AX(c,a,b,u)] ++ NIP^j ++ [DROP] ++ NIP^(11-j).

It returns the indicated rho_j instance. The bundle leaf is

    DISCARD ++ [AX(c,a,b,0)] ++ NIP^10.

For c distinct from a,b this returns the new bundle. The formula code
used by the corresponding theorem constructor is changed to this exact
bundle code. Its non-1 property is the only additional computational
fact needed in the original block calculation.

The old GEN and MP block proofs therefore apply unchanged. Their
induction on finite numerical derivations supplies a block Build_F for
every derivation of the relative falsity code F=1.

## 3. An explicit cofinal family of resetting proof prefixes

For any natural U define

    START_U = AX(0,1,1,U),
    SUFFIX  = [DROP,NIP,NIP].

START_U always resets d and h to zero, whatever the retained input tuple.
It may change both the current formula and the stack. The U parameter
occurs in the pushed rho8 row, so it is not literally unused by AX.
It is ignored by the *following block contract*, which holds for every
new current-formula and stack code.

Consequently, if Build_F has the block contract for F, then

    START_U ++ Build_F ++ SUFFIX

halts from every retained input tuple and for every U. If Build_F has
not already halted, it returns `(1,w,0,0)` for some w. DROP pushes 1 and
sets current to 0. The first NIP moves the pushed 1 into the cache; the
second NIP halts.

The native command fields are

    fields(START_U) = [3,1,1,U].

Write `enc_fields(fs,r)` for right-folding the native pair constructor P
over the field list fs with final tail r. The code of an ordinary
subsequent command receives the inherited extra successor; the initial
candidate number does not. If R is the encoded fixed tail
`Build_F ++ SUFFIX`, the complete candidate number is exactly

    N_U = P(3, P(1, P(1, P(U,R)))).

Since P(v,w) is at least both v and w, N_U >= U. This exhibits halting
candidate numbers above every fixed cutoff. No appeal to an informal
claim that the same finite word has arbitrarily large encodings is used.

The enumerator's retained `step_pl` and `drain` arguments show that every
candidate N at or above the initial next-proof value is eventually
started unless a previous computation halts. Within a candidate, a
positive proof-list value strictly decreases; at a candidate boundary
the next-proof counter increases by one. The main initializer starts
the next-proof counter at 3, so choosing U>=3 suffices. The reset prefix
handles the initializer's nonzero additive counter and any state
retained after earlier candidates. Thus the actual seeded enumerator
halts if and only if the new numerical calculus derives F.

## 4. Optional row orders and parameter bijections

The eight logical rows may be pushed in any permutation while retaining
the generalized cache and old current formula below them. If a desired
row is at new top-first position j, use the same leaf formula above with
that j. The bundle leaf still skips ten entries; the GEN row remains in
position nine. The original MP/GEN cleanup blocks and the START_U proof
remain valid, because every skipped row is a theorem and is not code 1.

Independently for each row, a bijective permutation of its complete AX
parameter tuple `(a,b,c,u)` preserves the supplied row family. At the
beginning of a leaf, DISCARD gives d=h=0, so the subsequent AX fields can
choose arbitrary natural a,b,c,u. To retrieve a particular desired row
instance, fill unused arguments with 0 and choose the inverse-permuted
tuple as the AX fields. The simultaneous alteration of other row values
does not matter: the block skips them. This observation permits source
sharing experiments without changing the logical strength.

These are finite changes to leaf selection and the theoremhood proof.
They do not by themselves establish a source simulation, a changed
transition table, or any state-count improvement.
