# AX9: externalizing the saved top

## Status and pin

This is a new source-level construction and compiler argument, not a 214-state binary machine. It is based on ProveIt commit `b07002a86bcc96e76a31b57dce23d3b8c2b76fa6`, `Computability/BusyBeaver/Research/ZFC/candidate-k215/sites215.json` (SHA-256 `17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba`). The parent command equations are in `candidate-k216/alternatives/permuted/proof.md`. The parent numerical-calculus/ZFC calibration is inherited. The source-level contracts below do not supply a new binary runtime or blank-start proof.

`AX9Factor.v` is an original standalone Coq 8.18 formalization. It was compiled and recursively checked by `coqchk`. Its named theorem assumption reports are closed. These are universally quantified conditional theorems: pairing projections, theorem-preserving axiom rows and gate, and numerical modus ponens are explicit arguments. The reports do not turn those interfaces into an exact K215 endpoint.

## 1. An exact macro identity

Write the arithmetic state `(t,w,d,h)` for top, paired stack, additive parameter and cache. Let `R(d,h;c,x,y)` be the list of eight implication-coded generated logical rows, and `G(d,h;c,x,y)` the gated set-theoretic bundle. The established AX10 command is

    (t,w,d,h) |-> (G, [R; Q_d(h); t; w], 0, 0).

Here `[R; a; w]` means the right-nested Cantor stack, and `R` has eight entries. The list notation does not assume the raw tail `w` is an encoded finite list.

Define the clear-top nine-head emitter by

    AX9(c;x,y)(t,w,d,h) = (G, [R; Q_d(h); w], 0, 0).

The established DROP command is `(t,w,d,h) |-> (h,[t;w],d,h)`. Since AX9 ignores the incoming top,

    DROP ; AX9(c;x,y) = AX10(c;x,y)

on every natural tuple. This is an equality of complete returned arithmetic states. It is independent of formula decoding, theoremhood, zero aliases and stack well-formedness. It immediately translates every old finite command program by replacing AX10 by DROP;AX9, and therefore transports the strong proof compiler. Its proof is `ax10_factor` in the Rocq file.

This is a useful source-minimization principle: move an emitter's saved-data operation into a command that the enumerated proof language already supplies. The extra DROP increases witness-word length, not interpreter state count.

## 2. The cheaper source realizes a top-biased binder

In the primary K215 source, the closed 19-leaf subtree at path

    11010010010000

consists of original ordinals `[26,45)`. Its arithmetic contract, on zero scratch registers, is

    (T,W,X,Y) = (t,w,0,0) |-> (0,P(t,w),0,0).

The next seven-leaf block at path `11010010010001` adds D into T while restoring D. The original next 62 leaves build `Q_D(H)` in T and restore the underlying stack. Replacing the 19-leaf block by `(CD1,CC1)` gives clear-top AX9 and removes 17 occurrences. Before any reassociation it has 205 distinct source subtrees, versus 202 for the parent.

Deleting the 19-leaf block entirely is cheaper. Replace its 26-leaf parent `1101001001000` by that parent's right child. Then D is added to the incoming top, and the nine-head interface becomes

    AX9+(c;x,y)(t,w,d,h) = (G, [R; Q_(t+d)(h); w], 0, 0).

The `+` here denotes a top-biased binder, not an extra axiom. All eight logical rows, the full bundle, parameter resets and cache reset remain the parent ones. At the end of the modified first AX prefix, T is `Q_(t+d)(h)`, W is `w`, D and H are unchanged, and both arithmetic scratches are zero. The remainder of AX treats this as the generalized head and continues unchanged.

The exact emitted source has 4,732 leaves, 204 distinct subtrees, maximum depth 47 and maximum zero run 6, before reassociation. Both complete successor resolvers agree. Removing leaves does not establish a reduction in physical states, and these raw DAG counts are worse than the parent's 202; allocation and reassociation remain necessary.

For this no-clear version, the unrestricted factorization is false: DROP changes top to h, so it would produce `Q_(h+d)(h)`. The correct restricted identity is

    DROP ; AX9+ = AX10       when the incoming cache h is zero.

A second exact identity is

    AX9+(0,[0;w],d,h) = AX10(0,w,d,h).

These are `ax10_factor_zero_cache` and `ax10_factor_zero_top` in the kernel-checked file. The cache-zero restriction is essential, and is not silently assumed at generalization calls.

## 3. Strong compiler for AX9+

A strong block for a native theorem X maps every `(t,w,0,0)` to `(X,w,0,0)`, or halts earlier. The raw tail w and initial t are arbitrary. As in the parent, early halt is allowed and successful returns preserve the exact raw tail.

Let D, N, M(x) and A(c;x,y) denote DROP, NIP, MP and AX9+. A repeated NIP tests the old cache for 1 before popping. Every displayed returning calculation is therefore understood as exact normal return or an earlier halt; none assumes arbitrary initial heads are theorems.

Set

    CLEAR = M(1); D; A(1;0,0); N^10.
    J(0) = empty,   J(i) = M(i) for i>0.

From `(t,w,0,0)`, M(1) fails because `I(t,1)>0`, giving `(0,w,1,0)`. D installs a zero sentinel. A emits its nine generated heads above that sentinel, has zero gate because C=A=1, and resets counter/cache. Ten NIPs return `(0,w,0,0)`. On a cleared state, J(i) sets only the counter to i; the zero exception avoids a successful aliased M(0).

For every existing row-selection, dominated-row, gated-bundle or MP compiler block, replace each AX10 by D;A. Every such AX call has zero cache. The exact restricted factorization proves the original block's contract unchanged. This includes the MP cleanup after a successful MP, whose cache is zero even when its returned top is a nonzero or falsity code. Truth uses CLEAR.

Generalization is the only case requiring a new block. Given a strong B_X, use

    CLEAR; D; B_X; D; J(i); N; A(i;0,0); N^9; D; N^2.

Its returning checkpoints are:

| Prefix | Returned tuple |
|---|---|
| CLEAR;D | `(0,[0;w],0,0)` |
| then B_X | `(X,[0;w],0,0)` |
| then D;J(i) | `(0,[X;0;w],i,0)` |
| then N | `(0,[0;w],i,X)` |
| then A(i;0,0) | `(0,[R;Q_i(X);0;w],0,0)` |
| then N^9 | `(0,[0;w],0,Q_i(X))` |
| then D;N^2 | `(Q_i(X),w,0,0)` |

The AX gate is zero because its A and C parameters both equal i. The sentinel is part of the entire raw stack [0;w] preserved by B_X; it lies above the original tail w and below any temporary heads created by B_X. At AX entry the top is zero, so the top-biased binder is exactly i. If any NIP halts sooner, the strong contract is already satisfied.

Induction on the inherited finite native derivation now gives a strong AX9+ block for every old native theorem. If 1 is derivable, append D;N;N to its strong block: the final NIP tests cache 1. Prefix a resetting AX9+ call with a free padding field, exactly as in the parent's cofinal-encoding argument. AX9+ resets counter/cache from every incoming tuple, regardless of the new binder. The usual raw Cantor encoding enumerates that finite successful command word beyond every finite cutoff. Thus completeness survives the changed emitter.

The all-theorem-stack invariant supplies soundness from the original clean zero-stack source seed. For the ZC215 exhaustive scheduler and arbitrary tail, the theorem in the next section supplies the stronger protected-tail version. These are source-level consistency calibrations conditional on the inherited native-calculus theorem and on the source arithmetic contracts; they are not binary runtime theorems.

## 4. Separating enumeration credit from semantic soundness

Existing ZC215 codec proofs show that every prefix of its exhaustive command schedule has at least as many DROPs as NIPs. `AX9Factor.v` proves the remaining generic semantic bridge.

Fix an arbitrary raw natural J. A protected state is witnessed by a finite list `xs` such that top, cache and every explicit head in xs satisfy a predicate Good, and the raw stack equals `prepend xs J`. No assertion is made about J, including whether it contains falsity or a decodable formula.

Assume Good(0), theorem-only generalization Good(h) implies Good(Q_i(h)) for every i, and the theorem-preserving row, gate, and MP hypotheses stated in AX9Factor.v.

Use only the budget DROP=+1, NIP=-1, MP=AX=0. `prefix_counts_credit` converts the all-prefix count inequality into an inductive budget trace. `credit_run_sound` simultaneously proves:

- a successful executed prefix retains a protected list at least as long as the remaining budget;
- a returning NIP has an explicit protected head available, so it never reads the opaque tail;
- MP and AX may add heads, but the proof does not need their positive contribution;
- a halt implies Good(1).

`zero_credit_semantic_soundness` starts with no protected heads at all. It applies to every initial tail J and all natural initial counters, with theorem-valued initial top/cache. It quantifies arbitrary generated row lists and does not use the length-eight hypothesis. Thus it remains valid after safe changes to the number of AX outputs, as long as each emitted row and gate is a theorem. Completeness is a separate obligation; resource safety alone does not authorize deleting axioms.

The pairing part of the proof uses only the two projection equations `hd(cons a w)=a` and `tl(cons a w)=w`. These hold even at Cantor's zero alias `P(0,0)=0`. Protected lists are logical witnesses, and need not be unique numerical decodings. No well-founded-list assumption is imposed on the raw tail.

## 5. Finite ghost zeros remove all credit conditions for a clean zero stack

The original clean zero stack admits an even shorter soundness route. Cantor pairing has `P(0,0)=0`. Consequently `prepend [0,...,0] 0=0` for every finite number of zeros. For a finite executed command word of length n, choose a ghost witness of n initial theorem zeros above tail 0. This changes no raw register or tape cell.

Every prefix contains at most n NIPs, so initial budget n is enough regardless of command order, candidate cutoff, skipped candidates, or the number of AX outputs. Apply the generic resource theorem to this ghost spine. If the finite execution halts, its tested cache is a theorem, hence 1 is derivable. Each finite trace may choose its own witness length; no uniform finite physical reserve is claimed or needed.

`zero_stack_semantic_soundness` and `zero_stack_halt_refutes` formalize this argument. They eliminate every enumeration-credit premise from clean-zero-stack soundness and avoid quantifying an infinite decoded sequence of stack heads. They still require theorem-preserving command contracts, and say nothing about completeness or whether a physical initialization reaches the clean zero stack. A dirty arbitrary tail has no corresponding zero fixed-point equation and still requires the ZC tag-lowering resource theorem.

This supplies a useful division of proof responsibilities: the same finite protected-list invariant proves soundness for both kinds of initialization. Clean zero uses a finite ghost reserve chosen from trace length; arbitrary opaque tails use actual prefix credit. The scheduler is used for completeness in both cases, but it enters soundness only in the opaque-tail case.

## 6. Alternatives and proof effort

The shortest route to an additional formally certified 215-state alternative is still a small marker transport from the primary K215. Among reviewed choices, M124 is particularly simple: four changed rows, the two unconditional entry-marker assertions for old states 124 and 127, and two three-step blocks. It has no conditional 176/156 exception. M160 has an equally simple four-row structure. CM215 has six changed rows and a three-clause invariant. Standalone transport proposals for these families already exist; this packet does not claim that route is new or that its entire transitive proof closure is smaller than K215's.

ZC215 is the best source-level target for removing protected-stack reserve bookkeeping: its exhaustive tag-lowering theorem plus the generic semantic bridge avoids AX=+10 arithmetic, dirty-tail decoding and a machine-specific initial reserve. This does not make its complete exact-table formalization shorter automatically; its source scheduler and initialization still need adapters. AX9+ strengthens that direction by making the saved top an operation performed by the compiled witness instead of by every emitter invocation.

## References

All paths below are relative to ProveIt at the stated pin:

- `candidate-k216/alternatives/permuted/proof.md`: exact four-command equations and original strong compiler.
- `candidate-k215/sites215.json`: exact source edited here.
- `candidate-k215/alternatives/zero-credit/proofs/tag_lowering_credit.md`: the existing all-prefix zero-credit theorem.
- `k225-formal/verification/k215/simplification/proposals/certificate-refinements/zero_credit/CantorCredit.v`: existing concrete kernel codec/count proof.
- `candidate-k215/alternatives/dr215/markers/MARKER_PROOF.md`: existing M124/M160 local transport proofs.
- `k225-formal/verification/k215/simplification/proposals/README.md`: already delivered simplifications and their statuses.
