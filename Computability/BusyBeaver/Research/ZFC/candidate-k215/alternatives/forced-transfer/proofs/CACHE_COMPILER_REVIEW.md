# Independent review of the cache-return compiler and exact ST-layout binding

The new source is literally the calibrated ST215 source with its successful-MP subtree at 00110111 replaced by `(CD4,(CI5,CC2))`. The independent standard-library checker `audit_cache_stlayout.py` verifies this exact equality. The old subtree has 26 leaves; the replacement has three. All AX, scheduler, selector, failed-MP and direct-transfer source trees are unchanged. This is stronger than a comparison of command names or leaf counts.

The inherited successful comparison enters with T=H=X=Y=0 and D equal to the proposed conclusion y. Induction on natural D proves that the new closed loop terminates with H=y and D=0, leaving every other register unchanged. It neither pushes nor pops the numerical stack. Hence MP success is exactly `(0,w,0,y)`, and failure remains `(0,w,d+x,0)`. Truth-zero aliases are included.

The upstream cache-transfer proof supplies a complete strong compiler. I independently checked its interface calculations:

* H=AX(0;0,0);S^11 removes exactly one head while preserving arbitrary incoming top, resets D, and returns the removed head in cache, or halts when that incoming top is 1.
* PUSH=AX(0;0,0);S^9;MP(0) is always a failed MP: the cache is Q_d(h), residue 2 modulo 4, while the proposed implication has residue 0. AX has already reset D, so the operand is exactly zero. PUSH returns `(0,[t;w],0,0)` and does not inspect saved t.
* DISCARD=MP(1);AX(1;0,0);S^10;MP(0) has two forced failures. The first has incoming D=H=0 and strictly positive proposed implication. The last has positive top Q_1(0), cache zero, and D zero. No successful-MP behavior is silently reused here.
* J(u) is MP(u) only for u>0, from T=D=H=0. The zero case is the empty word, avoiding intentional success at I(0,0)=0.
* Row selection, bundle selection and generalization invoke MP only through these forced-failure auxiliaries. Their prior exact calculations consequently remain valid. In the GEN block the binder and cache are set to `(d,h)=(i,X)` before AX, and its gate is zero because A=c=i, including i=0.
* The new inference block starts DISCARD;PUSH to reserve a zero below all later work. The two premise blocks and their PUSH calls, followed by S;S, give `(A,[0;w],0,I(A,Y))`, unless an already permitted halt occurred. MP(Y) gives `(0,[0;w],0,Y)`. One final S either halts when Y=1 or gives exactly `(Y,w,0,0)`. Thus no assumption that a successful MP preserves or pushes a zero remains.

These equations establish the universal strong contract from every numerical `(t,w,0,0)`, not merely safe stacks. A final H after the compiled theorem 1 guarantees a halt. The safety invariant is separate: logical top/cache and protected heads are theorems; successful MP merely moves its theorem consequence into cache; failed MP supplies truth. AX still supplies ten heads, S consumes one, and MP has zero conservative stack effect. The transfer-first scheduler debt bound of two and the old cofinal padding therefore apply unchanged to the same field encoding.

This review does not assert a new proof-assistant endpoint. Binary runtime and blank-start calibration must be established for the actual new table. Raw215 context-donor allocations failed concrete runtime; the ST-layout table has 216 states before any further physical reduction.
