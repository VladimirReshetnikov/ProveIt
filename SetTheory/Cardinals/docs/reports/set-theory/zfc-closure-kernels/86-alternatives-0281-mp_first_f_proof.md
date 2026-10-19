# Moving contradiction detection to successful modus ponens

## Result and scope

Two precisely specified changes to the native C254 enumerator preserve its
halting equivalence to derivability of code 1. The stronger change also clears
the additive parameter after successful MP and omits the dummy truth push.
It has a particularly short complete derivation compiler, given below.
Consequently the established ordinary calibration of native C254 to
inconsistency of ZFC transfers to either changed abstract enumerator.

This is an ordinary mathematical proof, not a Lean-checked theorem, a proof of
an emitted binary table, or a claim of fewer than 246 states. The actual binary
compiler, bootstrap and source/table simulation remain separate obligations.
The source definitions used here are the pinned ProveIt snapshot
`7ba1598461c6e485c5aeb8f673c0b1d571f8012b`, specifically
`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/{Code254,Enum254,EnumSafeStart254}.lean`.
The executable source already contains `wim_ne_one`, `wal_ne_one`,
`gate_ne_one` and `axList_ne_one`, exactly the arithmetic facts needed below.

## 1. Definitions, including the exceptional truth code

Write P for the bijective Cantor pairing, head/tail for its two inverse
components, and

- I(A,B) = 4 P(A,B),
- U(i,A) = 4 P(i,A)+2,
- F = 1.

Code 0 is an explicitly admitted theorem, called truth. It satisfies
I(0,0)=0, and is not the code of a finite syntactic formula. We do **not**
reason by structural induction on a decoded formula when proving the machine
invariant; C254 is the native inductively generated numerical derivability
predicate and explicitly has the constructor `C254.truth`.

The theorem stream S is the infinite stream obtained by repeatedly unpairing.
The numerical stream 0 has every entry 0. Define Good(S) by requiring C254 of
every stream entry. A working state is (T,S,D,H). Its soundness invariant is

  C254(T) and Good(S) and C254(H).

D is a numerical parameter, not a purported theorem. It may freely equal 1.
This distinction is important for the 246-state startup, whose D is 3.

AX has exactly the published action, for a=D+x and b=H+y:

  T := gate(a,b,c)
  S := [rho1(a,b), ..., rho8(a,b,c,u), U(a,H), old T] ++ old S
  D := 0; H := 0.

Here gate is either 0 or the published conjunction bundle. Each rho_i has
outer implication, including rho1, because existential quantification is the
relative-negation abbreviation I(U(i,I(A,1)),1). The bundle also has outer
implication. Thus none of these nine new AX entries and neither alternative
for gate can numerically equal 1. This argument applies to **all numerical
parameters**, including c=0, c=1, malformed/non-formula codes and arbitrary H.
The embedded relative falsity constant 1 is not itself a new stream entry.

## 2. First occurrence in the original enumerator

Call a working state F-free if T!=1, H!=1, and no entry of S equals 1.
The zero-formula starting states (T,S,H)=(0,0,0), with arbitrary D and arbitrary
scheduler registers, are F-free.

For any original nonhalting command from an F-free state:

1. DROP pushes T and copies H into T. It preserves F-freeness.
2. NIP cannot halt because incoming H!=1; its new H is a stream entry and its
   new S a tail. It preserves F-freeness.
3. AX pushes only the nine new entries described above and old T. Its new
   T is gate and its new H is 0. It preserves F-freeness.
4. Failed MP writes T=H=0 and keeps S. It preserves F-freeness.
5. Successful MP with B=D+x writes (T,S,D,H)=(B,P(0,S),B,0). It preserves
   F-freeness exactly when B!=1. If B=1, this is the first occurrence of F.

Therefore the earliest occurrence of code 1 in any original run from an
F-free start must be the output of a successful MP whose target B is 1.
In particular an original halting NIP is preceded by such an MP. This is a
finite earliest-index argument and does not assume consistency.

Caution: an individual successful MP producing 1 need not cause the original
*same candidate* to halt; that result could be discarded. The global converse
uses complete enumeration, rather than claiming an invalid per-candidate
bisimulation after F has appeared.

## 3. Variant A: detection relocation only

Change NIP to unconditional pop, and halt immediately on successful MP with
B=1. Otherwise keep all original command actions, including the successful-MP
dummy push and D=B. Before the first such MP, original and changed executions
are identical, and F-freeness is preserved.

If the old run halts from an F-free state, the first-occurrence theorem gives
an earlier common successful MP producing 1, so the changed run halts.
If the changed run halts from a sound state, invariant preservation up to its
halt gives C254(T) and C254(I(T,1)); MP gives C254(1). The published completeness
and safe-start theorem then imply that the old enumerator halts from every
sound start. Consequently the halting equivalence is exact for F-free sound
starts, including the initialized 246-state logical interface.

## 4. Variant B: reset success and omit dummy push

The compiler experiment's stronger variant has these precise command actions:

- MP x: B:=D+x. If I(T,B)!=H, return (0,S,B,0). If I(T,B)=H and B=1,
  halt. Otherwise return (B,S,0,0).
- DROP x: return (H,P(T,S),D+x,H).
- POP x (old NIP opcode): return (T,tail(S),D+x,head(S)), unconditionally.
- AX c x y u: exactly the original AX action.

This is not claimed to be a stepwise simulation of the old machine, since D
and S change on success. The following independent soundness and completeness
proof supplies the necessary replacement.

### Soundness

Each nonhalting command preserves the soundness invariant:

- DROP and POP only copy/move existing theorems.
- AX rows, gate and generalization have exactly the native C254 constructors;
  the pushed old T is already a theorem.
- Failed MP writes the explicitly derivable truth code 0.
- Successful MP uses C254(T) and C254(I(T,B)) to derive C254(B), retains the
  already-good stream, and writes derivable truth to H.

The value assigned to D is irrelevant to this invariant. A halt can happen
only at a successful MP with B=1 and hence produces a derivation of C254(1).
This argument works from every sound initial state; F-freeness is unnecessary.

### Complete command blocks

Let POP^k denote k repetitions of POP 0. Define a strong contract for a block
p and a theorem code X:

  for every numerical T,S, running p from (T,S,0,0) either halts,
  or ends at (X,S,0,0); if X=1, it always halts.

T and S are unrestricted in this contract; they need not be sound. The block
is built by induction on a native C254 derivation. No numerical theorem
codes are evaluated by the proof of this contract.

**Truth/discard block**

  discard = MP 1; AX 1 0 0 0; POP^10.

For initial H=D=0 the MP necessarily fails: I(T,1)>0, so cannot equal H=0.
It produces (0,S,1,0). AX then has a=c=1, so gate=0, resets D,H and pushes
its nine rows followed by old T=0. Ten pops leave (0,S,0,0).

**Logical axiom leaf**

For row j in 1..8 (top-first numbering rho1,...,rho8), use

  discard; AX c a b u; POP^j; DROP 0; POP^(11-j).

After discard, AX has exactly the requested parameters a,b,c,u and H=0.
The first pops select row j into H. DROP selects it into T while pushing the
gate value. The remaining pops remove that gate and all remaining AX entries,
ending with H=the pushed old truth 0 and restoring S. Each rho_j!=1, so the
strong contract's last clause is vacuous. Unconditional POP removes all
side conditions previously needed for the old NIP instruction.

**Bundle leaf**

When c!=a and c!=b, use

  discard; AX c a b 0; POP^10.

This leaves (bundle(a,b,c),S,0,0). The bundle is an implication code, not 1.

**Generalization**

Given a block p satisfying the strong contract for X, use

  p; DROP 0; POP 0; AX i i 0 0; POP^9; DROP 0; POP^2.

If p halts, so does this block. Otherwise the first DROP/POP loads X into H
and leaves T=0, the old S unchanged. AX has a=c=i, b=X, hence gate=0; its
ninth row is U(i,X), and the old T below it is 0. Nine pops select that row,
DROP makes it current, and two pops remove the two zeros. The result is
(U(i,X),S,0,0). U(i,X)!=1, proving the required contract.

**Modus ponens**

Given blocks pa for A and pab for I(A,B), use the much shorter block

  pa; DROP 0; pab; POP 0; DROP 0; POP 0; MP B.

If either subblock halts, so does the composite. Otherwise its states are:

  after pa:          (A, S, 0, 0)
  after DROP:       (0, [A]++S, 0, 0)
  after pab:        (I(A,B), [A]++S, 0, 0)
  after POP:        (I(A,B), S, 0, A)
  after DROP:       (A, [I(A,B)]++S, 0, A)
  after POP:        (A, S, 0, I(A,B)).

MP B succeeds. If B=1 it halts; otherwise the new success rule returns exactly
(B,S,0,0). This proves both clauses of the strong contract. In particular no
cleanup AX, dummy truth stack cell, or final contradiction-checking NIP is
needed in this proof compiler.

These cases exhaust the constructors of C254. Hence a derivation of code 1
has a finite command block p that halts from every (T,S,0,0).

### Fair enumeration and arbitrary safe starts

Keep the native command packing and scheduler unchanged. Their arguments do
not depend on the values of T,S,D,H after a nonhalting command:

- decoding an internal candidate command strictly decreases its nonzero list
  pointer, because the input is first decremented and Cantor components do
  not exceed their parent;
- at a candidate boundary, the next-candidate counter increases by one;
- therefore every candidate number greater than or equal to the current
  counter is eventually reached unless an earlier command halts.

For a contradiction block p, prepend AX 0 1 1 u. From arbitrary working
registers this AX produces some T',S' and resets D=H=0, so p then halts.
Its encoded candidate N is at least u, by the Cantor component inequalities.
Choose u at least the current next-candidate counter. Thus that candidate is
in the enumerated tail, and the enumerator must halt. This proves completeness
from **every** six-register initial state, including states not satisfying the
soundness invariant. Combined with soundness:

  For every sound initial state s,
  Variant-B-HaltsFrom(s) iff C254(1).

The zero-formula start (pl,np,T,S,D,H)=(0,3,0,0,3,0) used by candidate-prefix246
is sound. Any newly emitted binary table must independently be shown to reach
a corresponding legal interface; a working startup for the old table is not
a proof of startup for a modified one.

## 5. Formal status and cost handoff

The argument uses only finitary numerical induction, primitive recursive
pairing, and induction on a finite C254 derivation; it can be formalized in PA
and hence in ZFC. This document does not assert that such a formalization has
been checked. The original Lean proof provides the old scheduler lemmas and
most unchanged block contracts, but the new MP and POP definitions require
fresh theorem statements.

The initial source-DAG proposal from the compiler worker was:

- NIP node 147 right edge goes to 170, removing old test nodes 152,153;
- MP success at node 130 right goes to new node 219=(198,220);
- new node 220=(increment H,132);
- node 198 copies D into X,TW while consuming D; existing node 132 compares
  X,H and halts on equality, so the new H=1 realizes target B=1.

**This initial literal proposal fails:** independent executable contracts
found that redirecting 147 directly to 170 leaves incoming H added to the
popped stack head. The old equality test cleared H as a side effect. Thus an
explicit clear-H path is required to implement the abstract unconditional POP.
See `../machine_encoding/mp_first_contract_tests.json` for the detected defect
(48 goal-copy cases, 490 complete-MP cases, 936 NIP cases before reporting).
The abstract Variant-B proof above remains valid; this failed direct edit is
not an implementation of it. Revised helper entry conditions, scratch
cleanup, literal table and bootstrap must be checked by the compiler
workstream. Context-sensitive state savings, if any, are still unestablished.
