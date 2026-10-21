# Independent review of the three-command NIP-transfer compiler

Date: 2026-10-21.

## Verdict

PASS for the all-natural command-level soundness and explicit completeness compiler, conditional on the displayed command equations and unchanged scheduler/macro contracts. No missing proof case was found in the new compiler. This is a fresh review of the three-command construction, not an application of the old DROP-based compiler.

One terminological correction is required: H is not operationally equivalent to the old NIP. Its exact contract is a top-preserving pop with a top-falsity guard. Old NIP tests incoming cache h; H tests incoming top t after first discarding the incoming cache. This does not affect any use of H in the new proof.

This verdict does not certify either provisional 214-state table. Literal source identification, physical allocation, all-tape primitive simulation, and complete blank initialization are separate obligations. In particular, the stated helper collision is not repaired by a valid compiler. The numerical-calculus-to-ZFC comparison is an identified inherited premise, not independently re-proved here.

## Inputs and method

Read as text/data, without executing received programs:

- `research214_theory/NIP_TRANSFER_COMPILER.md`, SHA-256 `3727ca41d74bf6fed85ab10872959b8b042d07f7413f20c9b7e67bf7be40d42e`.
- `research214_commands/price_nip_transfer.py`, SHA-256 `aee53c1a1795897f9b3d0a2f26d707cb8b0ccb77c6044e28bd0ffb5a7ba60203`.
- `research214_theory/check_nip_transfer.py` and its receipt, as corroboration only.
- `research215_calibration/SOURCE_COMPILER_REVIEW.md`, SHA-256 `6cc6a9ba0d3f89bdcc2089851a137bf46f0704767a0e7f85d3cc835480b10483`.
- `research215_report/package/provenance/inherited_source_calibration.tex`, SHA-256 `53aa8956201ed70d9aa2bb1a254b121cf742542382a1d690aea69a23c1c65669`.
- Relevant logical definitions and inherited-premise statement in `research215_report/report_body.tex`.

The audit is an ordinary mathematical proof review. The existing symbolic test's generic variables and finite parameter cases are not treated as a universal verifier. In particular, generic variables can denote 0 or 1; the branch cases below are handled explicitly.

## Exact interface needed

Let P(a,b)=(a+b)(a+b+1)/2+b, I(a,b)=4P(a,b), and Q_i a=4P(i,a)+2. Thus I(a,b)=0 iff a=b=0; every implication is 0 modulo 4; every Q-code is positive and 2 modulo 4. Pairing is bijective on all natural pairs, including P(0,0)=0.

At a command boundary write (t,w,d,h). The reviewed S tests h=1 and halts in that case; otherwise, if unpair(w)=(x,v), it returns (h,v,d,x). MP and AX have exactly the equations stated in the proposed compiler. AX pushes, in order, eight implication codes, Q_d h, and saved top t, then sets d=h=0. Its first eight generated heads cannot be 1; the ninth cannot be 0 or 1. Its gate is the unchanged permitted full bundle, or truth 0. The full bundle itself is also an implication after expanding N, but the completeness argument would permit an early halt even without using that extra fact.

The strong block contract is universal in natural t,w, not just theorem-valued inputs. It promises either an early halt or the exact tuple (X,w,0,0). It does not assert that a halt from an arbitrary unsafe input certifies a refutation. Actual-run soundness is a separate safe-seed invariant.

## Structural macros

Put D=AX(0;0,0). Write its eight implication heads as a1,...,a8, its ninth head as q=Q_d h, and its saved tenth head as t. After D the tuple is (gate,[a1,...,a8,q,t;w],0,0).

For 1<=k<=10 successive S commands, the old-cache test inspects 0,a1,...,a8,q. None is 1. After k shifts, the cache is the kth generated head, the top is the preceding head (or 0 for k=1), and exactly k generated heads have been removed. This elementary shift-counting lemma proves the following two calculations for all raw inputs:

- H=D;S^11: after ten shifts the tuple is (q,[x;v],0,t), where the original w=[x;v]. The eleventh shift halts exactly when t=1; otherwise it returns (t,v,0,x). No earlier halt is possible, even when incoming h=1. H therefore has the claimed useful state-transform contract, but not the old NIP's halting behavior.
- PUSH=D;S^9;MP(0): after nine shifts the tuple is (a8,[t;w],0,q). MP(0) cannot succeed because I(a8,0) has tag 0 and q has tag 2. Its exact result is (0,[t;w],0,0). It never halts, including incoming t=1 or h=1.

These equations are valid for numerical stacks, not only free lists. The identity P(0,0)=0 can collapse the notation for a zero head over zero, but unpair(P(x,v))=(x,v) still holds. All claimed finite sequences of pops therefore remain valid.

## Truth/reset and all axiom leaves

DISCARD starts from (t,w,0,0). MP(1) fails since I(t,1)>0, giving (0,w,1,0). AX(1;0,0) gates to 0 because A=c=1, and saves top 0 as its tenth head. Ten shifts give (Q_1 0,w,0,0). The final MP(0) fails since Q_1 0>0, yielding exactly (0,w,0,0). No unsafe suffix head is read and no halt is possible.

J(u) is correctly defined only at top/counter/cache zero: it is empty for u=0 and MP(u) for u>0. In the latter case I(0,u)>0, so MP fails, sets d=u, and leaves the stack unchanged. The empty u=0 case is essential; MP(0) would succeed by I(0,0)=0 and push a zero.

After DISCARD;AX(c;a,b), S^(j+1) places retained row j on top and the next generated head in the cache. Exactly 9-j generated heads remain above the original w. Each H preserves the selected row (which is not 1) and removes one of those heads. H^(9-j) ends with cache equal to the final saved zero and the exact original stack w. This verifies all j=1,...,7, including both endpoints.

For L(a,b,c,u), J(u) followed by AX(c;a-u,b) supplies U=u,A=a,B=b because u<=a. S^9 selects L, and one H removes saved zero. This includes u=0 without an alias failure.

For a permitted full bundle, DISCARD;AX(c;a,b);H^10 preserves the exact gate and removes exactly the ten generated heads. It ends with cache zero and stack w. The proof never replaces the original bundle, removes a conjunct, weakens its gate, or assumes atom substitution.

## Generalization

Assuming B_X has returned, PUSH gives (0,[X;w],0,0). J(i) gives counter i. The next S tests incoming cache 0, not X, and returns (0,w,i,X). AX(i;0,0) has U=A=c=i and zero gate; its ninth generated head is Q_i X and its tenth is saved zero. Ten shifts therefore return exactly (Q_i X,w,0,0).

This remains valid for X=1, because X is first loaded into cache immediately before AX resets the cache. It also remains valid for i=0, because J(0) is empty. No underlying head of w is inspected.

## Major-first modus ponens

Let M=I(A,B). Compile M first and PUSH it, obtaining (0,[M;w],0,0). The inductive contract for B_A is universal in its stack, so it applies above [M;w]. Its PUSH gives (0,[A,M;w],0,0).

The first S returns (0,[M;w],0,A). The second halts if A=1; otherwise it returns (A,w,0,M). MP(B) then succeeds by literal numerical equality, producing (B,[0;w],B,0).

AX(B;0,0) gates to zero because A=c=B, resets counter/cache, and saves B as its tenth head above the successful-MP zero. Ten S commands yield (Q_B 0,[0;w],0,B). The eleventh halts if B=1; otherwise it returns exactly (B,w,0,0).

The special A=B=0 case is valid. Its major M is raw zero, MP(0) succeeds intentionally, and the final shift removes exactly the deliberately pushed zero. Numerical collapse when w=0 changes no equality. If A=1, halting before MP is allowed by the strong contract; if B=1, halting in cleanup is likewise allowed.

The major-first order introduces no proof-theoretic circularity. Both premises have finite subderivations. A finite DAG can be expanded to a finite proof tree and recursively compiled in this order. Together with the leaf and GEN constructions, this proves the strong contract by induction on every finite native derivation.

## Soundness on all candidate numbers

For actual runs, assume top, cache, and every successive decoded stack head are native theorems. This holds at the zero seed: zero is truth, and unpair(0)=(0,0).

- S either halts with theorem-valued cache 1 or moves theorem-valued cache/head into top/cache.
- Failed MP supplies truth. Successful MP applies numerical MP to theorem-valued t and h=I(t,d+x).
- AX inserts retained axiom instances, a dominated row with d<=d+x, a theorem generalization Q_d h, saved theorem t, and either the permitted bundle or truth.

Thus every command, including commands arising from malformed or unintended raw candidate encodings, preserves safety when it returns. Every halt proves native 1. This argument does not require successful decoding of natural codes as conventional formulas. The inherited calibration is expressly about the numerical calculus on all naturals.

## Refutation packing, draining, and cutoff

If B_1 returns, it returns (1,w,0,0), and H halts at its eleventh shift. Thus the fixed finite suffix B_1;H succeeds from every (t,w,0,0), regardless of arbitrary incoming t or underlying w.

For the new fields S=[0], MP(x)=[1,x], AX(c;x,y)=[c+2,y,x], right-folded pairing F and the recursive tail encoding tail(k::L)=1+F(fields(k),tail(L)) have the claimed decoding behavior. Subsequent commands are decoded after decrementing a positive proof-list value; the first command of a freshly fetched candidate is decoded without that decrement.

Consequently N_Y=P(2,P(Y,P(1,R))), with R=tail(B_1;H), encodes first command AX(0;1,Y) and leaves the fixed suffix R. The initial AX resets d=h=0 from any retained tuple. Its particular top and stack are irrelevant because the strong suffix contract is universal in both.

For every natural a,b, P(a,b)>=a,b. Therefore N_Y>=Y, which yields a successful candidate beyond every fixed startup cutoff. Each later command leaves a proof-list residual at most pred(p)<p, since every field tail is a right projection. This covers S with selector 0 and zero residuals, as well as MP and AX. Termination of all arithmetic macros and exact fetch/increment contracts are the stated source dependencies. Under them every earlier nonhalting candidate drains finitely and the scheduler reaches a chosen successful candidate unless it has already halted.

## Literal source and remaining limits

The pricing script deletes the middle DROP selector branch and prepends clear-top plus the old cache-copy suffix to old NIP. The cache copy preserves H; the following old NIP tests H and pops the stack. On normal return this is exactly the proposed S. Performing the clear/copy before the halt test is harmless for this command-level abstraction: the halted branch promises no final store.

However, the script's allocation receipt expressly establishes only raw decoder allocation. It does not prove all-natural scratch restoration, exact new selector fields and exits, the still-live arithmetic-helper rows, a whole-tape simulation, or blank startup. The source helper-collision repair being investigated must preserve the complete new command equations, not merely the same subtree count.

Recommended wording replacement in the compiler: replace “implements old NIP with the counter reset to zero” with “returns the top-preserving pop state (t,v,0,x) when t is not 1, and otherwise halts.” No mathematical block changes are needed.
