# Adjacent-pair completeness for the abstract feedback scheduler

STATUS: CONDITIONAL SCHEDULER THEOREM ONLY. Independent source audit found that the actual scratch-biased CC3 at address100111 targets ordinal23, not scheduler0. The proposed command-boundary semantics below are therefore NOT established for the archived215 table. No calibration of that table follows from this note. The adjacent-pair theorem remains valid for the explicitly defined abstract scheduler. This is not a new Lean/Rocq exact-table certificate.

## 1. Proposed abstract scheduler and intended source target

The inert upstream scratch-biased source has SHA-256
`2407f815551b4aba335c9bf041e15e8ce3cfb9ad830d89539f3bcf123462371a`;
the native table has SHA-256
`f08bed9e62b9f43237b65c465d2f1bfc17474637b4b02785ca7f1813827bb0ce`.
The source has 4,733 primitive occurrences, 201 distinct source DAG nodes and 6,152 guarded primitive cases. The table has 215 working states.

Write P(a,b)=(a+b)(a+b+1)/2+b and f(n) for its right inverse projection. In the abstract scheduler considered here, the scratch bias b is zero after short transfer S and one after MP or AX. The other parser scratch registers vanish. The fields are S=[0], MP(x)=[1,x], and AX(c;x,y)=[c+2,y,x].

If the residual L is positive, this abstract scheduler first decrements L, and its biased first read therefore unpairs L-1+b. That read clears the bias; subsequent command-field reads are ordinary unpairings. If L=0, refill copies the old candidate counter n into L and increases the counter by 1+b, while clearing the bias. The first command of the new candidate is decoded directly from n, with no predecessor operation.

The increment is made when a candidate is **entered**, using the bias left by the preceding candidate. A claim that the next candidate gap is determined by the candidate currently being entered would be an indexing error. All that the proof below needs is that consecutive candidate numbers differ by either one or two.

## 2. Finite draining

For every positive n, f(n)<n. Indeed, if n=P(a,y)>0, then P(a,y)>y: this is immediate for a>=1, and for a=0 follows from P(0,y)=y(y+3)/2>y when y>0; y=0 would give n=0.

At a positive residual L, the next residual is obtained by one, two or three right projections of L-1+b. If b=0 it is at most L-1. If b=1 it is at most f(L)<L. Extra projections cannot increase a natural number. Consequently every nonhalting candidate finishes after finitely many commands. The separately proved command and primitive contracts give finite time for each such command. Hence, unless the machine halts, it enters infinitely many candidates with unbounded, strictly increasing numbers and gaps in {1,2}.

## 3. Encoding a fixed command word under feedback bias

Let W=(C_0,...,C_{m-1}) be a nonempty finite command word and choose an unused positive residual r>=1. Define R_m=r, and, backwards for i=m-1,...,1, put

    R_i = 1 - b(C_{i-1}) + F(fields(C_i), R_{i+1}),

where b(S)=0, b(MP)=b(AX)=1 and F is right-nested Cantor pairing of the listed fields over its last argument. Put

    K = F(fields(C_0), R_1).

For m=1 this means K=F(fields(C_0),r). All R_i and K are positive, since P(a,z)>=z and r>=1. If the next first-field read is K, the machine executes exactly W unless it halts earlier. At every internal command boundary, subtracting 1 and adding the prior bias cancels the added 1-b in R_i. The unused terminal residual r is never reached when W is universally halting.

Positivity is essential. Encoding a trailing S after bias one with terminal residual zero could yield cursor zero, causing refill rather than executing that S. The construction explicitly excludes that error.

## 4. Universal refutation word

The inherited short-transfer compiler is proved directly in `research214_theory/NIP_TRANSFER_COMPILER.md`, independently reviewed in `research214_calibration_review/INDEPENDENT_NIP_TRANSFER_REVIEW.md`. Its S command tests only the incoming cache h=1 and otherwise maps

    (t,[x;w],d,h) -> (h,w,d,x).

This is precisely the short command here, not an inference backwards from the composite command with an additional top guard.

For every numerical-calculus theorem X, the compiler supplies a finite block B_X that from every natural store (t,w,0,0) either halts or returns exactly (X,w,0,0). Its macro H=AX(0;0,0);S^11 halts when the incoming top is 1. Thus B_1;H halts from every store (t,w,0,0) if a refutation exists.

Define

    W = AX(0;0,0); B_1; H.

The first AX resets d=h=0 regardless of the incoming natural top, stack, counter and cache. Its new top and stack may be arbitrary, but the strong contract quantifies over all of them. Therefore W halts from every natural work store. An earlier halt during any prefix is also success. Feedback bias affects only encoding, not these work-tuple command equations.

Fix a positive-residual encoding K of this W as in Section 3.

## 5. Consecutive universally halting candidates

For every x>=0, let

    z = 1+K,
    n_x = P(1, P(x, P(0,z))).

Candidate n_x decodes MP(x), leaving residual P(0,z) and bias one. Its next first-field read is exactly P(0,z), so it executes S and leaves residual z with bias zero. The following first-field read is z-1=K. It therefore executes W and halts, unless MP(x) or S caused an earlier halt.

The Cantor identity P(a,b)-1=P(a+1,b-1) holds for b>0. Applying it three times gives

    n_x - 1 = P(2, P(x+1, P(1,K))).

Here all required right arguments are positive. Candidate n_x-1 therefore decodes

    AX(0; x'=1, y'=x+1),

leaving residual K and bias one. Its next first-field read is K-1+1=K. It executes precisely the same W and halts. The stores at the two entries to W need not coincide; universality of W handles both.

Thus {n_x-1,n_x} is an adjacent pair of universally halting candidates for every x. The pair is cofinal because P(x,P(0,z)) and hence n_x grow unboundedly with x.

Any unbounded increasing sequence of integers with gaps at most two intersects every sufficiently late adjacent pair: at the first selected value at least n_x-1, the preceding value is at most n_x-2, so the selected value is at most n_x. Apply this to the candidate sequence of the defined abstract scheduler from Section 2. A numerical-calculus refutation therefore forces the defined abstract scheduler to halt. No arithmetic-progression assumption, equidistribution assertion, or unproved feedback fairness is used.

## 6. The startup work store is entirely safe

The exact startup evidence identifies a partial AX execution from logical registers

    (N,T,W,A,D,H,X,Y,L)=(1,0,3,0,0,0,0,0,0).

The number 3 is not an arbitrary unsafe tail: P(2,0)=3, and 2=Q_0(0) is a theorem by generalizing the theorem 0. Repeatedly unpairing tail zero produces theorem zero forever. Therefore every decoded head of stack 3 is a theorem. The initial top and cache are both theorem zero, and all AX outputs preserve theoremhood.

More formally, call a numerical stack safe when every member of its infinite iterated head-projection sequence is a theorem. Stack zero is safe because its heads are all zero. Pairing a theorem onto a safe stack preserves safety. Stack 3 is safe by the explicit identity above. This avoids pretending that finite list length is uniquely recoverable from the pairing code, since P(0,0)=0.

Under the stated abstract command contracts, top, cache and stack heads remain theorems at ordinary boundaries under S, MP and AX. The numerical parameter d is unrestricted. S can halt only when the cache is the theorem 1. Thus every halt of the defined abstract scheduler from this safe seed yields a numerical-calculus refutation. This proof needs no protected-tail credit estimate, because the actual startup tail is already wholly theorem-valued.

If the abstract scheduler and command equations are implemented by a blank-start machine with the safe startup just described, Sections 2–6 and the inherited calibration prove its equivalence to Con(ZFC). The archived215 table has a newly discovered source-binding obstacle and is NOT claimed to implement these equations.
