# Transfer-pop plus cache-return modus ponens

## Contribution and exact interface

This composes two existing, independently meaningful command redesigns: Source54's cache-return MP and Source166's three-command transfer-pop enumerator. The new composition retains MP's numerical operand. It is distinct from the incoming file named MP0_Transfer_215, whose contents were not inspected here; no global novelty claim is made. The four emitted source trees have 201 distinct subtrees. Physical state counts and correctness must be supplied separately.

Use P(a,b)=(a+b)(a+b+1)/2+b, I(a,b)=4P(a,b), Q_i(a)=4P(i,a)+2. At boundaries the retained work state is (t,w,d,h), and [x;w]=P(x,w).

The new commands are:

* S: halt if h=1; otherwise, if unpair(w)=(x,v), return (h,v,d,x).
* MP(x): put Y=d+x. If I(t,Y)=h, return (0,w,0,Y). Otherwise return (0,w,Y,0).
* AX(c;x,y): unchanged dominated-rho8 axiom command. Put U=d, A=d+x, B=h+y, C=c. Return (gate(A,B,c), [r1,...,r7,L(A,B,c,U),Q_U(h),t;w], 0,0).

Wire fields are S=[0], MP(x)=[1,x], AX(c;x,y)=[c+2,y,x]. The retained eight logical rows and gated bundle have their original code meanings. Every rj and L is an implication code, hence not 1. Every Q-code has residue 2, hence is nonzero and not 1. The gated bundle is also an implication code when enabled, and truth0 otherwise.

## Literal source construction

From the accepted K215 tree, replace successful-MP subtree 11010010111 by the existing transfer (CD4,(CI5,CC2)). This removes the old dummy push and copies the conclusion destructively into cache.

Delete the DROP selector layer by replacing subtree 11010 by its descendant 11010010. The remaining selector0 is S, selector1 is MP, and selector c+2 is AX with residual c. All AX internals, field-reader order, gates, scheduler and numerical formula constructors remain literal.

The direct S body is a sequential composition of clear-T, the old DROP's cache-copy tail, and old NIP:

    clear-T = (CD1,CC1)
    copy-H  = old subtree 1101011
    old-NIP = old subtree 111.

Clear-T terminates with T=0. The copy tail makes T=H_old while restoring H_old and zero scratch. Old NIP tests H_old=1 and otherwise clears it and pops the stack into H. Thus the complete direct body has exactly the S equation above. The two parenthesizations ((clear-T,copy-H),old-NIP) and (clear-T,(copy-H,old-NIP)) have identical command effects because all three components are closed.

Two further source trees use old-DROP;old-NIP;old-NIP instead. This composition has the same nonhalting map and halts when incoming h=1 OR incoming t=1. Its extra test is sound for safe executions, and it is an early-halting refinement of S. The strong compiler below therefore transfers unchanged to those composite variants. Both parenthesizations are supplied separately for physical allocation.

## Soundness

The invariant is that t, h and every decoded stack head are theorems of the calibrated dominated calculus. AX preserves it by its original proof. Failed MP produces truth. Successful MP derives Y from t and I(t,Y), places Y in cache and truth0 in current, and preserves the theorem stack. S only moves theorem codes; either permitted guard tests a theorem equal to falsity1. Numeric d need not be a theorem and may be cleared.

Thus any halt from a safe seed implies a native refutation. This covers all raw command fields and arbitrary raw formula codes, rather than only compiled proof words.

## Three auxiliary blocks, valid with cache-return MP

Let D0 denote AX(0;0,0). Define:

    H       = D0; S^11
    PUSH    = D0; S^9; MP(0)
    DISCARD = MP(1); AX(1;0,0); S^10; MP(0).

H, from (t,[x;w],d,h), halts if t=1 and otherwise returns (t,w,0,x). To see this, the first ten shifts traverse the ten generated AX entries, returning (Q_d(h),[x;w],0,t); the eleventh shift performs the stated test and pop. The cache tests in those ten preliminary shifts concern only 0 and the nine nonfalsity generated entries. H does not test the incoming h before AX resets it.

PUSH, from any (t,w,d,h), never halts and returns (0,[t;w],0,0). After nine shifts it has current L, cache Q_d(h), and stack [t;w]. MP(0) is forced to fail: its compared implication has residue0 and the cache residue2. Cache-return MP changes only success, so this existing auxiliary proof remains valid.

DISCARD, from any (t,w,0,0), never halts and returns (0,w,0,0). Its first MP(1) fails because I(t,1)>0 whereas the cache is0. AX then has U=A=c=1 and a zero gate. Ten shifts leave (Q_1(0),w,0,0), after which MP(0) fails because Q_1(0)>0. Both MP uses are forced failures.

The parameter setter J(u), used only from current/cache/counter zero, is empty when u=0 and MP(u) when u>0. Its positive call is a forced failure, returning (0,w,u,0). Omitting MP(0) avoids the zero-alias success; this exception is retained.

For the composite DNN transfer, the extra top test cannot disrupt these exact auxiliary statements: every tested AX gate and newly generated row is not1. The only old-top test in H is its intended final one. PUSH's old top remains untested on the stack.

## Strong theorem-block compiler

For each derivable X construct B_X, from every (t,w,0,0), that halts or returns exactly (X,w,0,0). The arbitrary starting t and stack w need not be safe for this completeness contract. Actual-run soundness is established separately.

Truth uses DISCARD. For row j, 1<=j<=7, use

    DISCARD; AX(c;a,b); S^(j+1); H^(9-j).

For dominated row L(a,b,c,u), where u<=a, use

    DISCARD; J(u); AX(c;a-u,b); S^9; H.

For an enabled full theory bundle use

    DISCARD; AX(c;a,b); H^10.

These are the accepted transfer compiler's exact selection blocks. They invoke MP only inside the forced-failure DISCARD/J auxiliaries, so their proofs are unchanged. The H repetitions remove precisely the residual generated entries and the saved zero, retaining the selected current formula and restoring the original stack.

For generalization use

    B_(Q_i X) = B_X; PUSH; J(i); S; AX(i;0,0); S^10.

After PUSH/J/S the state is (0,w,i,X). AX has U=A=c=i and zero gate; its ninth generated entry is Q_i(X), followed by saved0. Ten shifts give (Q_i(X),w,0,0), or an earlier permitted halt. This argument includes i=0 and the raw truth alias.

### The new MP block: reserve a zero before computing premises

For premises A and I(A,Y), use

    DISCARD; PUSH; B_(I(A,Y)); PUSH; B_A; PUSH;
    S; S; MP(Y); S.

The initial DISCARD;PUSH places a disposable zero beneath the premise-building work. If no earlier halt occurs, the exact trace is:

    initial                         (t,w,0,0)
    DISCARD;PUSH                     (0,[0;w],0,0)
    B_(I(A,Y));PUSH                  (0,[I(A,Y),0;w],0,0)
    B_A;PUSH                        (0,[A,I(A,Y),0;w],0,0)
    first S                         (0,[I(A,Y),0;w],0,A)
    second S                        (A,[0;w],0,I(A,Y))
    successful MP(Y)                (0,[0;w],0,Y)
    final S, if Y != 1              (Y,w,0,0).

The second S may halt if A=1. The final S halts if Y=1. Otherwise each is the stated exact nonhalting map. The cache-return MP requires no additional reset AX because it clears d on success. The deliberately reserved zero compensates for the one stack pop used to transfer its cached result to current. Cantor's pairing/unpairing identities validate the trace even when A=Y=0 and [0;0]=0.

Induction on finite native derivations gives the strong block contract. If B_1 returns rather than halting, append H: its top-one guard halts. Therefore B_1;H is a successful finite word from every (t,w,0,0).

## Cofinal candidate encoding

For right-folded pairing F(fields,r), set

    tail([])=0,
    tail(k::L)=1+F(fields(k),tail(L)).

A fresh candidate is decoded without the outer successor; a continuation first decrements its positive pointer. Let R=tail(B_1;H). For each padding value z choose candidate

    N_z = P(2, P(z, P(1,R))).

It starts with AX(0;1,z), which resets d=h=0 from every retained tuple, then executes B_1;H. Its new current and stack may be arbitrary, as allowed by the strong contract. Pairing domination gives N_z>=z, so successful candidates are cofinal beyond every fixed startup cutoff.

Every nonhalting candidate drains: after decrementing its positive pointer, each one-, two-, or three-field reader returns a Cantor right projection no larger than that predecessor. All macros terminate on natural counters. Thus sequential candidate enumeration reaches a successful N_z unless it has already halted.

Together with soundness, this proves ordinary source equivalence of halting and native refutability, hence syntactic ZFC inconsistency by the inherited calibration. The argument is formalizable in ZFC. A concrete binary table additionally requires an exact source binding, quantified full-tape primitive runtime proof, and a complete blank startup reaching a safe frame.

## Source references

All repository references are to commit 75716498437bfc7291d5900cab2983a11fd54bac of VladimirReshetnikov/ProveIt.

* candidate-k215/proof.md and its provenance/permuted-commands/sections/source_calibration.tex: current dominated source and command semantics.
* SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/54-cachemp-proofs-cache_mp_proof.md: original cache-return interface (252-state stage).
* The later candidate-k217/research/cache-return rebase retains separate 217-state status.
* SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/166-transfer-proofs-transfer_compiler.md: transfer-pop compiler and H/PUSH/DISCARD.
* The adjacent composite_transfer_review.md: extra-top-guard refinement and zero-alias details.
