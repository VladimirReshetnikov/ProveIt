# Order201 zero-spare repair: source calibration and finite bootstrap

## Scope

This is a new composition of the formerly uncalibrated order201 allocation with the zero-valued spare allocator and initial state74. It is not a214-state result. The native table has215 working states and430 rows. The fresh inherited mathematical runtime checker passes all6176 guarded cases, with1697188 symbolic rule applications and full430-row coverage. The frozen report is runtime/runtime.json.

The exact change to research/command_family/201/candidate.native.tm is198/0: `1 L 40` becomes `0 L 40`; the designated initial state changes from0 to74. No other transition changes. Its source retains command order NIP,MP,DROP (tags0,1,2), with AX tags c+3 unchanged. The source hash is0b7e1e035796b954b96a358b8e634b921abb36118ce84baf02b4e61c29b95c80.

## The actual finite prefix

The first genuine root occurs at118411 transitions with registers(N,T,W,A,D,H,X,Y,L)=(2,0,2,0,0,0,0,0,0). This is NOT a safe theorem-stack seed, and we make no such claim. W=2=P(0,1) contains one truth above an unsafe tail1.

Execute the literal finite prefix rather than assuming an invariant there. Candidate2=P(0,1) runs NIP,NIP. The first leaves W=1,H=0 and positive continuation1; the second leaves W=0,H=1. The NIP halting test precedes the pop, so neither halts. Candidate3=P(2,0) is DROP; it leaves topT=1,H=1. Candidate4=P(1,1) is MP(1). Its implication test fails (I(1,1)=16 differs from cached1), clearing the top/cache and leaving D=1. Thus after435 source primitives the exact root is(5,0,0,0,1,0,0,0,0). No CH occurs in this finite execution. audit_source201.py uses two independent inherited graph readers, checks agreement, selector routes, field arities and normal returns, and saves the complete primitive trace.

More importantly, no dependence on the source simulation is needed for this initialization claim: audit201.py independently replays the entire binary blank prefix in native and dense labels. At570263 transitions it reaches state84, head−9, gap131, header186,176 natural spare words, and the exact tuple above. It reconstructs the full one-cell set from all primary and spare values. The minimum one is−10; the next one is186=−9+64+131. Therefore all64 PC bits really are zero; this is not an interior-frame false positive. The complete exterior is zero. No halt occurs during the replay.

## Arbitrary-counter calibration for order201

At a source root assume N=n,D=d arbitrary naturals, A=X=Y=L=0, and T,H plus all stack heads of W are numerical theorems. The source halts iff numerical inconsistency.

For soundness, the unchanged command bodies preserve theoremhood for every natural d. In AX the old counter U=d and new parameter A=d+x satisfy U≤A. All other axiom rows, theorem-only generalization, and gated literal bundle retain their inherited soundness. MP applies numerical detachment on equality and returns truth on failure; DROP and NIP move theorem entries. The sole CH tests cached falsity H=1. Command renumbering does not change any of these facts. The all-zero theorem tuple and zero stack at the actual terminal root satisfy these assumptions; d=1 is permitted.

For completeness, translate the inherited strong compiled refutation block command by command to order201, using NIPtag0,MPtag1,DROPtag2 and preserving fields/AX encoding. The resulting block works from every retained top/stack once D=H=0; it either halts or returns(1,w,0,0). Append DROP,NIP,NIP to load/test falsity. For y≥1 prefix AX(0;1,y), which resets D=H=0 regardless of incoming d,h: its parameters U=d,A=d+1,B=h+y,C=0 satisfy the two gates. The top/stack need not be prescribed, because the strong compiler quantifies over arbitrary retained data.

Let R=enc201(compiled refutation;DROP;NIP;NIP). Its prefixed first-candidate integer is n_y=P(3,P(y,P(1,R)))≥y, with no outer successor on a first candidate and the inherited successor convention for positive continuations. Choosing y≥max(1,n) supplies a successful candidate beyond every finite cutoff. Every earlier nonhalting candidate drains: arithmetic macros terminate and each positive continuation strictly decreases before its tail projections. Commands do not change N; the scheduler advances it and restores selector/scratches. Hence the successful candidate is eventually reached unless a halt has already occurred.

This proves calibration for the exact order201 source, not by reusing an order210 debt bound. The finite unsafe prefix is discharged before applying the theorem. The proof inherits the numerical-calculus equivalence to Con(ZFC), command-local strong compiler, and arithmetic macro theorems; it is an ordinary mathematical argument formalizable in ZFC, not a newly kernel-checked theorem.

## Binary realization obligation

verify201.py adapts only the public zero-spare wrapper's table/source pins and expected finite initial frame. It uses the same unchanged symbolic checker with append=0 and checks every source site and guard over arbitrary natural registers, gaps and arbitrary nonempty finite natural spare lists. All6176 cases pass with positive affine durations and full430-row coverage. This universal simulation combines with the literal safe bootstrap and above source theorem to establish blank halting iff notCon(ZFC).

## Novelty and exclusions

The native source is a command permutation different from210,120 and partialcb120; zero-spare bootstrapping calibrates a table previously only retained as unverified research. audit201.py checks complete rooted labelled transition-graph nonisomorphism (also after global tape reflection) against the public Z215 machine, all seven retained command_family tables and its pinned comparison machines. A different start alone is not the substantive claim: both command encoding and spare-allocation backend differ from the prior calibrated order201-free constructions.

For the same zero-spare mutation with start74, orders012,021,102 halt before any genuine root at4680,14184,4680 transitions respectively. Their original start0 escapes at78 transitions. These are concrete rejected variants, not lower-bound evidence.
