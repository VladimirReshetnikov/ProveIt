# Independent review of zero-spare MP-first transfer215

Date: 2026-10-21. Reviewed candidate SHA-256: `0f201336eda34691f2892c217431bdd2524e813d805645cb0b4a23e58168f7d9`.

## Verdict and scope

The proposed source/blank calibration is sound, conditional on the fresh full append-zero physical runtime theorem for these exact rows. The finite independent replay has passed. This review supplies no new proof-assistant endpoint and does not claim that a finite execution establishes unbounded primitive correctness.

The source is byte-identical to the public MP-first composite-transfer source (SHA-256 `8ddb942f0f1d8e2e3b12ab7217c7232eb553cd288fca38dbf9b0eded73893dd5`). The only transition change relative to its public native table is 198/read0 from write1,left,40 to write0,left,40. The designated blank start changes from 0 to 74. The source is not a new calculus or compiler; the new contribution is this physical composition and its independently checked unsafe-tail initializer with changed credit application.

## Exact finite bridge

`check_startup.py` imports no upstream programs. It reads the source and transition tables as data, executes all 73,172 blank transitions in native and dense labels, checks the state bijection in lockstep, and independently reconstructs the entire tape support. The endpoint is dispatcher 84, head -2, header 62, gap 0, source ordinal 119, address `11010011000110110110`, registers `(N,T,W,A,D,H,X,Y,L)=(0,6,0,0,1,1,10,1,0)`, with65 spares `[0,0,1,0,...,0]` and107 one-cells. Every nonlisted tape cell is zero.

A separately implemented source interval resolver proves that the exact source starts the same AX at ordinal 25 with registers `(0,0,0,0,1,1,0,0,0)` and reaches ordinal 119 after177 source primitives. This logical bridge need not reproduce the hypothetical earlier gap/spare history: the complete actual physical frame is independently matched and the unbounded runtime domain must include its actual spares.

## Initial AX: eight, not ten, safe heads

The all-natural AX arithmetic contract applies without theoremhood hypotheses. Its fields are c=x=y=0, with U=D=1, A=D+x=1 and B=H+y=1. Its top is enabled Bundle(1,1,0), a native axiom since0 differs from both1-valued parameters. Its first eight stack heads are the seven retained logical rows and the dominated classical row L(1,1,0,1). Their restrictions hold, in particular U<=A is1<=1. The new counter/cache are0, N remains0 and the residual proof pointer is0.

The ninth head is Q_1(1)=18, generated from raw incoming cache 1. It must not be declared a theorem. The saved old top 0 and old stack 0 give the suffix P(18,P(0,0))=171 beneath the eight safe heads. Regard171 as a fixed arbitrary numerical tail. The theoremhood invariant begins only after this AX completes; the physical startup cache 1 is never treated as a proof of falsity.

## MP-first credit is d(0)=1

The correct fields are MP(x)=[0,x], S=[1], AX(c;x,y)=[c+2,y,x]. The public diagonal proof explicitly gives W(0)=[MP], W(1)=[S], W(2)=[MP], so their minimum conservative balance is-1 under weights0,-1,+10. All subsequent complete Cantor diagonals are prefix-safe relative to their starts. Consequently every prefix of the schedule starting at cutoff 0 has balance at least-1. This is an all-natural theorem, not an extrapolation from the finite500,000-case corroboration.

Thus the special AX's eight safe heads leave at least seven safe heads above171 at every later command boundary. It is not appropriate to reuse the old S-first d(0)=3 as if the command tags were unchanged, nor to silently substitute the public MP-first blank root at cutoff 1. Here the explicit d(0)=1 clause is the applicable statement.

## Internal transfer guards remain safe

The actual composite S is DROP;NIP;NIP. Its exact halt test is old top1 OR old cache 1. Internally it pushes the safe old top, pops that temporary head, and pops one head from the safe wrapper; the two tested values and the final loaded head are theorem-valued. The strict seven-head margin is more than enough. Successful MP adds theorem 0; failed MP pops nothing. Every subsequent AX receives theorem-valued top/cache and adds all ten theorem heads, unlike the special initial AX.

Therefore every later semantic halt exhibits native theorem 1, and no value from 171 can become a tested top/cache. Exact Cantor unpairing validates explicit zero wrappers even when P(0,0)=0 numerically collapses them; wrapper length is an auxiliary representation witness, not uniquely recoverable from the natural stack code.

## Completeness

The strong transfer compiler is unchanged apart from the already public MP-first wire tags. It supplies a fixed successful command block from arbitrary top/underlying stack after an initial resetting AX, so the protected unsafe suffix does not obstruct compilation. The public cofinal shell AX(0;1,Y) has code P(2,P(Y,P(1,R)))>=Y. Candidate enumeration from N=0 visits every successive natural, and each nonhalting candidate drains finitely. If the inherited native calculus derives1, a successful candidate is eventually tried unless an earlier sound halt occurred. The inherited native-calculus/ZFC comparison gives the claimed source equivalence.

## Necessary final acceptance boundary

The exact-table append-zero primitive checker must pass all 6,209 guarded cases over arbitrary natural primary values, arbitrary gap, arbitrary nonempty finite spare lists and the whole zero exterior. Its row hash must equal the reviewed candidate hash above. With this independent physical premise, the reviewed finite startup, AX contract, safe-tail invariant and strong compiler compose to the ordinary mathematical ZFC equivalence. This review does not establish214 states or universal novelty.

## Sources

- Public MP-first archive: ProveIt commit 75716498437, `docs/incoming/T215_Transfer_2026-10-20.zip`; extracted here under `t215_transfer/T215_Transfer_2026-10-20/`.
- All-natural MP-first credit: `proofs/permuted_credit.md`, Sections 1-6; its d(0) follows explicitly from the initial three words and the full-diagonal theorem. Alternate exact statement: extracted MP0 archive `proofs/mp0_s1_credit_proof.md`, Section 4.
- Dirty zero-spare AX analysis: extracted `Zero_Spare_Transfer_215_and_Alternatives_2026-10-21/primary/proofs/zero_spare_startup.md` and its independent review. The present source's finite bridge was freshly checked, not assumed from that earlier source.
- New finite receipt: `startup_review.json`.
