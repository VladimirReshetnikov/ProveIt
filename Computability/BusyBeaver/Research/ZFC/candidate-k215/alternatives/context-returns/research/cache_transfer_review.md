# Independent review of transfer-pop plus cache-return MP

## Verdict and scope

**PASS at the ordinary mathematical source level.** The three-command compiler in `research_audit/cache_transfer_proof.md` is correct for all natural register values, including the raw zero alias and arbitrary numerical stack codes. Its direct-transfer sources have 201 distinct source subtrees, 4709 primitive occurrences, maximum depth 44, and maximum zero run 6. These are source metrics, not a binary state count. Allocation, full-tape binary simulation, and blank startup remain separate certificates.

This review independently checked the literal construction, the selector arithmetic, the strong proof-block invariant, and the composition of the two existing command redesigns. `verify_cache_transfer.py` reconstructs all eight supplied source variants and checks both independent CFG resolvers. It also verifies that all 4565 primitive effects and internal successors of the AX body are unchanged, with its one external edge still reaching the appropriate common `CB1` continuation.

## Exact source binding and three-command selector

Let `p` be the pinned accepted K215 source, SHA256 `17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba`. The construction is exactly:

1. Replace `11010010111` by `(CD4,(CI5,CC2))`, a destructive transfer of the successful MP target from D to the known-zero H.
2. Replace `11010` by its current descendant `11010010`, deleting the DROP selector layer.
3. Replace `111` by the chosen closed transfer body.

The dispatcher skeleton before the change is

    (READ, ((CD3, (((CD3, (((CD3,AX),MP),CB1)),DROP),CB1)),NIP)).

Afterward it is

    (READ, ((CD3, (((CD3,AX),MPcache),CB1)),S)).

Here READ is the unchanged command-field reader. The first decrement dispatches zero to S. On a positive field it leaves one less; the second decrement dispatches zero to MPcache, and otherwise leaves the original field minus two for AX. Therefore the fields are exactly

    S = [0],  MP(x) = [1,x],  AX(c;x,y) = [c+2,y,x].

The two common branch continuations skip the unused branches as in the accepted source. The AX body itself has one outward break demand and is not claimed to be independently closed; the retained enclosing selector supplies that continuation. The machine check verifies its unique exterior successor is `CB1` in both sources, rather than silently assuming AX closure.

Four further `swap01` variants exchange the two closed small-command bodies at `110101` and `111`. Their fields are S=[1], MP(x)=[0,x], and AX(c;x,y)=[c+2,y,x]. The AX body and branch wrappers remain identical; only which closed body the first two decrement cases select changes. Command-name proof blocks are unchanged, and the padding first command remains selector2.

For direct S, clear-T is closed and leaves T zero. The old DROP cache-copy tail is closed and copies old H into T while preserving H and clearing scratch. Old NIP is closed; it halts iff the old H is one, otherwise clears H and pops the old stack. Both parenthesizations consequently implement

    S(t,w,d,h) = (h, tail(w), d, head(w))  if h != 1,

and halt if h=1. No incoming-top test is present in the direct variant. For the DNN variants the body is old DROP followed by two old NIPs. Its nonhalting map is identical, and its guard is h=1 or t=1. The latter is an early-halting refinement on all raw stores.

## All-natural compiler review

Write `[x;w]=P(x,w)`, `I(a,b)=4P(a,b)`, and `Q_i(a)=4P(i,a)+2`. AX still pushes nine generated nonfalsity entries followed by the old top; its generated quantified entry is nonzero with residue two. Its gate is truth zero or an implication code and is never one. These exact tag facts suffice for every forced-failure and auxiliary assertion below.

The strong contract is: for each native theorem code X, the finite word B_X, started from **every** `(t,w,0,0)`, either halts or returns exactly `(X,w,0,0)`. The arbitrary t and w need not be theorem-valued. Soundness is a separate invariant restricted to actual safe executions; conflating these two claims would invalidate arbitrary-stack completeness, but the supplied proof does not conflate them.

The inherited transfer auxiliaries remain valid because their MP calls are forced failures:

* `H = AX(0;0,0); S^11` tests the incoming top, then preserves that top and pops one old stack entry while clearing d. The first ten shifts traverse only generated nonfalsity codes before old top becomes the cache tested by the eleventh shift.
* `PUSH = AX(0;0,0); S^9; MP(0)` leaves `(0,[t;w],0,0)`. Its final comparison is between an implication code of residue zero and the generated quantified cache of residue two.
* `DISCARD = MP(1); AX(1;0,0); S^10; MP(0)` leaves `(0,w,0,0)`. The first MP fails because `I(t,1)>0`; the second fails because `I(Q_1(0),0)>0`. Both caches are zero.
* The setter J(u) is empty at u=0 and MP(u) for positive u. The positive case necessarily fails from top/cache zero. The zero exception is essential because `I(0,0)=0` would otherwise succeed.

The row, dominated-row, full-bundle, and GEN blocks therefore retain their exact equations. Their successful MP branch is never used inside any auxiliary. The dominated-row block uses the permitted nonnegative operand `a-u`; all other parameter values are raw naturals. GEN includes i=0 and X=1: the S immediately before AX reads an incoming cache zero and only then loads X, so it does not prematurely test X.

The new inductive MP block reserves one zero **before** compiling either premise:

    DISCARD; PUSH; B_(I(A,Y)); PUSH; B_A; PUSH;
    S; S; MP(Y); S.

After the first two commands the stack is `[0;w]`. Because each premise block preserves its entire incoming stack, after both saved premises it is `[A,I(A,Y),0;w]`. The two shifts give `(A,[0;w],0,I(A,Y))` unless the antecedent-one guard halts first. Cache-return MP succeeds and gives `(0,[0;w],0,Y)`. The final shift either halts at Y=1 or returns `(Y,w,0,0)`. This is exactly the strong contract and removes the old cleanup AX. The reserved zero is necessary: without it the final transfer would pop an arbitrary original stack head.

The trace is valid when A=Y=0 and when w=0. In particular `P(0,0)=0` does not invalidate any step, since its two inverse projections are still zero. One need not treat a paired stack as a free list datatype or assume that a leading zero gives a distinct numerical representation.

The DNN extra-top guard transfers the strong contract by the elementary early-halting refinement lemma. Exact never-halt auxiliary statements also survive, because every intermediate tested gate or generated code is nonfalsity; arbitrary old top remains untested in PUSH, and H's old-top test is its intended final test.

## Soundness, cofinality, and logical conclusion

For safe actual executions, current, cache, and all decoded stack heads remain native theorem codes. On successful MP, the existing current and implication cache derive Y, which becomes the new cache; current becomes truth zero. S moves theorem codes and halts only on a theorem equal to one. The DNN extra guard has the same justification for current. Thus every actual halt yields a native refutation, including arbitrary malformed or nondecodable field choices; no proof-word validity check is assumed.

For completeness, append H after a compiled B_1 if necessary. Let R be the successor-delimited encoding of that word. The candidate

    N_z = P(2, P(z, P(1,R)))

first executes AX(0;1,z), resetting d and h to zero regardless of retained work data. The universal strong block then succeeds. Since `N_z >= z`, these candidates are cofinal beyond any fixed finite initial cutoff. Continuation pointers decrease strictly after the scheduler's predecessor operation and one or more Cantor projections, so each nonhalting candidate is exhausted and sequential enumeration reaches a successful one. This is a genuine all-natural cofinality argument, not a finite simulation.

The numerical calculus and its original axioms, including all support-bearing bundle material and the dominated rho8 calibration, are unchanged. The result is therefore ordinary source halting iff native refutability iff syntactic ZFC inconsistency, by the inherited calibration. All arguments are finite arithmetic and syntactic proof transformations formalizable in ZFC. The new contribution is the compatible composition of cache-return MP with transfer-pop, specifically the disposable-zero MP compiler; neither historical ingredient alone is claimed to be new.

## Remaining boundary

This review does not identify a 214-state binary table. It certifies a 201-subtree source candidate and its complete ordinary command-level reduction. Any state-count claim must cite the separate exact allocation, all-natural full-tape runtime proof, and blank initializer for the actual emitted binary table. Existing proof-assistant artifacts for the baseline do not automatically certify these changed source commands.
