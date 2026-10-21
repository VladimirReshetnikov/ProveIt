# Composite transfer command: independent compiler audit addendum

Date: 2026-10-21.

## Verdict

PASS. Replacing each transfer command S by the closed composition S'=oldDROP;oldNIP;oldNIP preserves the complete strong-block compiler and all-natural safe-run soundness. The compiler needs no changed command word, field encoding, or padding formula.

The new primitive equation must say “halt iff incoming h=1 or incoming t=1.” The exact old nonhalting map is unchanged. Physical allocation, whole-tape runtime, and blank initialization are not certified here.

## Exact composite equation

Let unpair(w)=(x,v). Starting at (t,w,d,h), old DROP returns

    (h,[t;w],d,h).

If h=1, the first old NIP halts. Otherwise that NIP returns

    (h,w,d,t).

If t=1, the second old NIP halts. Otherwise it returns

    (h,v,d,x).

This is the proposed S map with one additional guard t=1. The calculation includes arbitrary numerical w and [0;0]=0, by the exact pairing/unpairing identities. All three old command bodies are closed; their normal-exit composition is the only source-level identification needed for this equation, apart from inherited arithmetic macro contracts.

## General early-halt refinement lemma

Consider any finite word over S, MP, and AX, and replace S by S'. The two executions have identical stores until the new execution halts. At a non-S command their next stores agree. At S, if the old execution halts because h=1, the new execution also halts; if h!=1 and t=1, only the new execution halts; otherwise their next stores agree.

Consequently every old block satisfying “halts or returns exactly f(input)” satisfies precisely the same alternative after replacement. This applies to all raw inputs, without a theoremhood assumption. In particular, it transfers every strong B_X contract, arbitrary underlying-stack preservation, major-first MP, GEN, refutation suffix, and cofinal candidate packing immediately. Termination of the finite composite command follows from termination of its constituent old macros.

The early-halt refinement is enough for completeness even if one weakens auxiliary exact-return/never-halt assertions. For the actual retained numerical calculus, those auxiliary assertions can be preserved too, as follows.

## The extra fact needed for exact auxiliary claims

Every AX gate is not1. A failed gate is truth0. An enabled gate is the full original bundle

    Bundle(a,b,c)=N(I(V(a,b,c),J(a,b,c)))
                =I(I(V(a,b,c),J(a,b,c)),1),

so it is an implication code, hence 0 modulo4 and not1. This is an established property of the unchanged literal bundle, not a new restriction or removed conjunct.

The earlier proof said the gate was irrelevant because the first S overwrote it, and used only nonfalsity of the ten new entries. For S', the gate is tested at the first shift. Add the gate-nonfalsity fact to that bookkeeping paragraph if retaining the exact “never halts” claims. Alternatively, qualify those claims with “or halts early”; the general strong-block proof remains valid without this extra bookkeeping fact.

## PUSH still never halts on arbitrary incoming t,d,h

After D=AX(0;0,0), top is a non1 gate, cache is0, and stack heads are

    [r1,...,r7,L,Q_d h,t;w].

The first S' tests gate and0; both are non1. For shifts2 through9, the top/cache values tested are among0, the eight implication rows, and the quantifier head. They are all non1. Saved incoming top t is still on the stack after shift9 and has not been tested. Incoming cache h has already been absorbed into Q_d h and reset.

Thus after nine S' commands, including when original t=1 or h=1, the state is exactly

    (L,[t;w],0,Q_d h).

The final MP(0) necessarily fails by tags0 versus2 and returns

    (0,[t;w],0,0).

Therefore the original PUSH “never halts” assertion remains true for every natural t,w,d,h, not merely as an early-halt alternative.

## H and DISCARD retain their exact contracts

For H=D;(S')^11, the first ten shifts test only gate,0,the eight implication rows,and Q_d h. They cannot halt. After ten shifts the tuple is (Q_d h,w,0,t). The eleventh S' has non1 top Q_d h, and halts exactly when t=1; otherwise it returns the same top-preserving pop state as before. Incoming h=1 is still harmless because AX resets it before a shift.

DISCARD's AX gate is specifically0. Its ten shifts test only non1 generated heads, and the final MP(0) fails as before. Hence DISCARD still never halts and returns exactly (0,w,0,0) for every starting (t,w,0,0).

## GEN with X=1 remains exact

After a nonhalting B_X and PUSH, the tuple is (0,[X;w],0,0). J(i) leaves top/cache0. The next S' tests top0 and cache0, so it does not halt even when X=1; it returns (0,w,i,X). AX(i;0,0) then resets cache before any further S', and its gate is0. Ten S' shifts recover exactly (Q_i X,w,0,0).

Thus no relaxation is needed for the stated GEN suffix with X=1, nor for i=0, where J(0) is still empty. The test is on the precommand cache/top, not on the newly popped X.

## Other blocks and zero aliases

Axiom retrieval uses only non1 selected row/bundle tops and the H contract above. Full-bundle retrieval preserves the original bundle without changing any support-bearing material.

The major-first MP suffix begins its first two S' commands with top0. The second still halts iff antecedent A=1, exactly as the previous S proof did. If it returns, MP succeeds by the same literal equality. The cleanup AX gate is0; its final shift has top Q_B 0 and cache B, so it still halts iff B=1. The A=B=0 alias and its deliberate pushed-zero cleanup remain unchanged.

Accordingly none of the specific compiled block calculations requires a changed command count or an added zero-alias case. The general refinement lemma already proves their weaker strong contracts independently of this detailed observation.

## Actual-run soundness and enumeration

The safe invariant makes both top and cache native theorems. The extra halt t=1 therefore certifies a refutation just as h=1 does. A nonhalting S' has the old transfer map and preserves the same invariant. Equivalently, each of its three constituent old commands is safe-run sound.

Fields remain S'=[0], MP(x)=[1,x], AX(c;x,y)=[c+2,y,x]. Neither composition nor the new guard consumes another encoded field. The predecessor-tail draining argument is unchanged. With R=tail(B_1;H), candidate N_Y=P(2,P(Y,P(1,R))) still starts with AX(0;1,Y), resetting d=h=0 from every retained tuple, and then succeeds by the transferred strong block. N_Y>=Y still gives cofinal successful candidates past every finite cutoff.

## Required textual changes

1. State the primitive halt condition as h=1 OR t=1.
2. Add that AX's gate is0 or the unchanged implication-coded full bundle, hence is not1. Remove the claim that the gate is irrelevant to the first S' test.
3. State soundness of the additional top test explicitly.
4. Include the early-halt refinement lemma, or repeat the direct calculations above.

No correction to the compiler words, PUSH's actual never-halt contract, GEN(X=1), zero-alias split, or cofinal packing is necessary.
