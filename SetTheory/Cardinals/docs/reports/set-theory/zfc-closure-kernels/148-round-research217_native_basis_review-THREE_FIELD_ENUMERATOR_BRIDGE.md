# Three-field AX and two-row H/PW: exact finite-command completeness bridge

Date: 2026-10-20. Ordinary symbolic proof for the original zero-test/draining scheduler. This is not a source-runtime certificate and does not apply to the rejected additive-feedback scheduler.

## Scope and exact AX contract

Keep the original MP, DROP, NIP, gate, and candidate-loading behavior from `latest219_baseline/k225-formal/rocq224/src/Enum222.v`. Change AX to read exactly three Cantor fields `[3+c,x,y]`, with no fourth `u` field. On a retained tuple `(t,w,d,h)`, it computes `a=d+x`, `b=h+y`, then returns

    (gate(a,b,c), push([r1,r2,r3,r4,r5,r6,G,PW',H',Q_a h,t], w), 0, 0).

Here push([v1,...,vk],w)=P(v1,P(v2,...P(vk,w)...)); `PW'` and `H'` are the selected independently permuted universal schema instances. This is emission order H then PW, so PW is stack position 8 and H is position 9. Reversing emission swaps only those two positions. The unchanged rows occupy positions 1 through 7, GEN is position 10, and saved previous top is position 11.

All nine logical rows are implication-headed and hence differ from target 1. GEN has tag 2. The gate is 0 or the full negative bundle, never 1, and gate(a,b,a)=0. Those facts suffice for the following exact compiler. Absolute source row order and literal AX source realization remain obligations for the source worker; the bridge states precisely the contract to verify.

Notation: `MP(x)` adds x to d, compares I(t,d+x) with h, and follows the original success/failure clauses. DROP and NIP have x=0. `AX(c,x,y)` means selector 3+c followed by x,y. `NIP^k` means exactly k consecutive NIPs.

## 1. Universal block contract

For a code X, a finite block B_X satisfies, for every natural T and w,

    exec(B_X,(T,w,0,0)) either halts or returns (X,w,0,0).

No theoremhood of T or of arbitrary older stack w is needed for completeness. Early halt is success. Soundness is proved separately only for theorem-valued inputs.

### Discard

Set

    DISCARD = MP(1); AX(1,0,0); NIP^11.

With d=h=0, I(T,1)>0 prevents the MP comparison with h=0, so the first command gives `(0,w,1,0)`. AX then has a=1,b=0,c=1, disables the gate, and pushes its nine non-1 rows, Q_1 0, and saved top 0. Eleven NIPs consume exactly those entries and end with cache 0. Hence DISCARD returns `(0,w,0,0)` without halting.

### Logical-row leaf at position j, 1<=j<=9

For requested AX parameters a,b,c, use

    DISCARD; AX(c,a,b); NIP^j; DROP; NIP^(12-j).

After DISCARD, AX has exactly those parameters, because d=h=0. The first j NIPs put row j in the cache. DROP makes it the top while pushing the old gate. The remaining stack prefix consists of that gate, rows j+1 through 9, Q_a 0, and saved zero: exactly `1+(9-j)+2=12-j` entries. All skipped codes differ from 1, and the final entry is zero. The block therefore returns precisely the selected row, original w, and d=h=0.

Each H or PW instance is selectable because each row's parameter permutation is bijective on N^3. Requesting one row does not require controlling the other beyond its guaranteed non-1 property. No syntactic atom substitution is involved.

### Full-bundle leaf

For c!=a,b, use

    DISCARD; AX(c,a,b); NIP^11.

The gate is the requested full bundle. All eleven stack entries are consumed, restoring w and cache 0. No helper or support-bearing part is omitted.

## 2. Generalization block

Given B_X, define

    B_(Q_i X) = B_X; DROP; NIP; AX(i,i,0);
                  NIP^10; DROP; NIP; NIP.

After B_X returns, DROP;NIP changes `(X,w,0,0)` to `(0,w,0,X)`. There is no intervening NIP with cache X: AX is next, so X=1 causes no hidden exception. AX sets a=i,b=X,c=i, disables the gate, and resets d=h=0. Its stack is nine logical rows followed by Q_i X and saved zero. Ten NIPs retrieve Q_i X. DROP makes that the top and pushes gate zero, leaving two zeros over w. Two final NIPs restore w and cache zero. All intervening tested cache values are 0, logical rows, or Q-codes, never 1.

## 3. Modus-ponens block

Given B_A and B_(I(A,B)), define

    B_B = B_A; DROP; B_(I(A,B));
          NIP; DROP; NIP; MP(B); AX(B,0,0);
          NIP^11; DROP; NIP; NIP.

Ignoring already-successful early halts inside the two supplied blocks, the states are:

1. After B_A;DROP: `(0,P(A,w),0,0)`.
2. After B_(I(A,B)): `(I(A,B),P(A,w),0,0)`.
3. After NIP;DROP: `(A,P(I(A,B),w),0,A)`.
4. If A=1 the next NIP halts. Otherwise it gives `(A,w,0,I(A,B))`.
5. MP(B) succeeds exactly, giving `(B,P(0,w),B,0)`.
6. AX(B,0,0) disables the gate because a=c=B, resets d=h=0, and pushes nine rows, Q_B 0, and the saved top B over the older stack P(0,w).
7. Eleven NIPs retrieve B and leave that older P(0,w); none tests cache B before retrieval has finished.
8. DROP gives top B with two zeros over w. If B=1 the next NIP halts. Otherwise the two NIPs remove those zeros and return `(B,w,0,0)`.

Thus the required universal block contract holds in all cases. This is the original finite compiler with each AX-depth-dependent count increased by one. The change is justified by the displayed states, not by assuming the old fixed-source theorem applies unchanged.

## 4. Finite-proof compilation

Induct on an H/PW-calculus derivation: use DISCARD for raw truth 0; the nine row-leaf blocks or full-bundle block for axioms; the preceding GEN and MP blocks for inference. This yields B_X for every theorem X. Combined with `NATIVE_CALIBRATION.md`, a finite old-calculus refutation yields a finite new-calculus refutation, then a finite command block B_1.

The proof works at arbitrary raw natural codes, including zero aliases. Every stack equation uses only unP(P(v,w))=(v,w); collapse of an all-zero stack prefix does not invalidate it.

## 5. Exact three-field recoding

Define the fields of commands by

    fields(MP(x))=[0,x], fields(DROP)=[1,0], fields(NIP)=[2,0],
    fields(AX(c,x,y))=[3+c,x,y].

Let F(fs,r)=fold_right P r fs. Define tail([])=0 and

    tail(k::L)=1+F(fields(k),tail(L)).

At a positive proof-list p, the original scheduler first subtracts one, then unpairs the command's exact number of fields. Consequently p=tail(k::L) executes k and leaves proof-list tail(L). At a candidate boundary p=0, the candidate number itself is decoded without the leading successor. Therefore the exact initial candidate for k::L is

    F(fields(k),tail(L)).

This proves the new read-one-command lemma by exactly two or three uses of unP_P. It does not use a fourth-field parser or reuse old command numbers.

## 6. Cofinal successful candidates without u

Let R=tail(B_1 ++ [DROP,NIP,NIP]). For every U, take first command

    START_U=AX(0,U,1),
    N_U=P(3,P(U,P(1,R))).

From arbitrary retained `(t,w,d,h)`, START_U computes a=d+U,b=h+1,c=0, changes top/stack in an unrestricted way, and resets d=h=0. The universal block B_1 works from the resulting top/stack. If it returns rather than already halting, the suffix DROP;NIP;NIP pushes top 1, loads it into the cache, and halts. Thus this same tail succeeds after every START_U, independent of U and all retained data.

Pairing domination gives N_U>=U. Hence successful candidate numbers occur above every fixed initial cutoff, including 3. There is no need for a fourth unused or used field to supply padding.

For any positive proof-list, the next list is a right projection after two or three unpairings of pred(p), hence is at most pred(p)<p. Every nonhalting candidate therefore drains in finitely many steps. At each empty boundary the next-proof counter increments by one. Finite induction reaches any chosen N_U above the current cutoff unless an earlier halt occurs. This proves completeness for the original zero-test/draining scheduler with three-field AX.

The same domination/inverse argument works for a separately verified alternative raw stack/list pairing. It is not a statement that the formula-code isomorphism commutes with untagged pairing or additive counters.

## 7. Soundness and remaining machine obligations

The original theorem-valued invariant covers top, cache, and all decoded stack entries. AX emits valid native axioms and GEN of the cached theorem, then resets cache to truth0. MP validates an exact implication; DROP/NIP only move existing values. Zero is a theorem. Thus a halting NIP from a theorem-valued initial boundary implies theorem1. The standard seed with top=cache=stack=0 is valid even when next-proof and additive counter are 3.

This proves the abstract equivalence: three-field H/PW enumerator halts iff the H/PW native calculus proves 1, hence iff the calibrated original native calculus proves 1. It does not prove that any particular edited source has the stated AX contract, that a source compiles to a specified binary table, that startup reaches the standard boundary, or that the physical state count is <=217. Those remain independent obligations.
