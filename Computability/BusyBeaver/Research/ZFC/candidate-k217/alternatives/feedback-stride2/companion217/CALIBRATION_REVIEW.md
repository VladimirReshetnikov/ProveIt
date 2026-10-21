# Independent calibration review of the corrected common-footer companion

Verdict: PASS mathematically, conditional on the final all-natural runtime certificate for the exact 217-state table below. This companion does not meet the requested 214/215-state threshold. The historical proof filename mentions216, but the reviewed physical repair has217 working states.

Source SHA-256: `ab25e03f724b45011660aeecb120a27b896a5f5dca0cb3848dbfde49bccd42d8`.

Native table SHA-256: `aebbe0246969c49d8d4dc6f0ab690d791291d5dc187fa024f084cf46f1aec945`.

Start state74; halting label254. These labels are not state counts.

## Source interface and the corrected return

Reviewed `GLOBAL_BIAS_SOURCE_PROOF.md`, `GLOBAL_BIAS_SOURCE_AUDIT.json`, the exact source data and the owned source-audit code. The new common footer is at ordinals4732–4733: CI6 followed by CC3 at address111. Its CC3 genuinely reaches the root because111 has exactly three right edges. The two old command-return edges are redirected to4732; the MP/AX return at4696 and the short-transfer finishing CD6 zero branch at4729 are the only changed old edges. Other old CFG edges and work-register effects are unchanged.

This is crucially different from inserting CI6 immediately before the former CC3 at10011, which moved that CC3 to100111 and changed its target incorrectly. The reviewed source routes every nonhalting command through one common increment, after its scratch cleanup.

The all-natural command contracts therefore give X=1 after every command, including short S, while A=Y=0. Schedule/Read with this bias decodes a positive cursor L as unpair(L): Schedule subtracts1, and Read starts with P(1,0)=1 and adds back1. Refill from exhausted L instead clears X and copies the old N without a predecessor, advancing N by2. The source-loop argument and exact CFG identity establish these facts; finite probes alone would not suffice.

## Actual first candidate and safety

Independently reran both sparse and dense binary simulations for69744 transitions on the exact table, and reran the172-step source prefix from AX entry25. The two binary implementations agree on every transition and the complete final finite tape support, including zero exterior. The full frame equals ordinal64 with registers

    (1,4,0,0,0,0,3,10,0).

The source seed is

    (N,T,W,A,D,H,X,Y,L)=(1,0,3,0,0,0,0,0,0).

Receipt: `GLOBAL217_INDEPENDENT_STARTUP.json`; owned checker: `check_global217_startup.py`.

The inherited AX body does not change N, consumes only the zero proof cursor for its remaining zero parameters, and returns with L=0 and clean parser scratch. The common footer then makes X=1. Thus the first refill decodes candidate1 and sets N=3. Subsequent normal refills decode3,5,7,... . Any earlier halt is already covered by soundness; the exact odd sequence is conditional on continuing execution.

The seed stack is wholly safe, not merely protected by a finite credit budget: 3=P(2,0), 2=Q_0(0) is a theorem, and the zero tail decodes into theorem-zero heads forever. Top/cache are also theorem zero. AX, MP and short S preserve theorem-valued top/cache/stack, while the footer changes no work register. A short-S halt therefore proves raw theorem1. No optional density-credit result is needed here.

## Draining and positive-tail encoding

For every L>0 the right Cantor projection f(L)<L. Each command consumes at least one projection, so every nonhalting candidate finishes in finitely many commands. The arithmetic command contracts supply finite duration for each command.

A refutation gives the directly proved short-S universal word W=AX(0;0,0);B_1;H. The leading AX resets d=h=0 for every incoming work tuple, and B_1;H halts for every resulting top/stack. Concatenating all command fields and nesting P over a positive unused tail r encodes W exactly. No successor wrappers are required because the constant bias cancels every internal predecessor. Positivity prevents premature refill at an intended later command.

## Dyadic residue argument

The stated inverse-residue lemma is correct. For F(z)=z(2z+1),

    F(z)−F(w)=(z−w)(2z+2w+1),

and the second factor is odd. Hence F is injective and therefore bijective modulo every2^k. For fixed a, use

    P(a,b)=T_(a+b+1)−a−1.

Choose z with F(z)=c+a+1 modulo2^k, then choose b=2z−a−1 modulo2^(k+1). Congruent arguments modulo2^(k+1) have triangular numbers congruent modulo2^k: their difference factors as d(2n+d+1)/2, with d divisible by2^(k+1). Thus this one-step inverse lifts any desired output residue to a right-argument residue using one extra bit of modulus.

Iterating over a finite field list produces a tail residue class modulo2^(k+m). Taking positive representatives makes every intermediate cursor positive. Since the resulting nested code is at least r, that class gives arbitrarily large successful codes. With k=1,c=1, successful odd codes are cofinal. The exact odd scheduler reaches one unless it has halted earlier.

This is the inherited dyadic-prefix lemma correctly applied to the new constant-bias implementation, not a new proof of the general lemma.

## Conclusion and remaining condition

The source, startup, soundness, universal command compiler, finite draining and cofinal odd encoding together establish the desired numerical-calculus calibration. The inherited numerical-calculus comparison then gives Con(ZFC) equivalence, provided the ongoing universal primitive proof passes for the exact table hash above. No new Lean/Rocq endpoint is claimed. No 214/215-state result follows from this217-state companion.
