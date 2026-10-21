# Independent review of the conditional adjacent-pair theorem

Verdict: PASS as a theorem about the explicitly defined abstract scheduler. It does not calibrate the currently archived scratch-biased binary table, whose return-target defect is proved separately.

Reviewed Sections 2–6 of `research215_round3_scheduler/COFINAL_ADJACENT_PAIR_PROOF.md`.

## Preconditions

The command work-store equations must be the original short transfer S, inherited MP and inherited AX. On normal return, a command sets a parser flag b=0 for S and b=1 for MP/AX. Positive residual L is read as L−1+b; an empty residual fetches an unbiased candidate and advances the candidate counter by either one or two. All commands terminate or halt.

These are explicit assumptions, not facts proved for the rejected literal table.

## Word compiler

The original short-S arbitrary-store compiler is directly available in `research214_theory/NIP_TRANSFER_COMPILER.md`, with its independent review. It is not necessary or valid to reverse the later early-halt-refinement argument for composite DNN.

The prefix AX(0;0,0) resets d and h from arbitrary work stores. Consequently W=AX(0;0,0);B_1;H universally halts when a numerical-calculus refutation exists. Each macro has its actual short-S semantics, including the h-only guard. An arbitrary initial stack is allowed in this completeness claim; soundness is handled separately.

A positive unused terminal residual r≥1 ensures every internal biased wire cursor remains positive. The backwards equation R_i=1−b(C_{i−1})+F(fields(C_i),R_{i+1}) then exactly cancels the parser adjustment. This positivity check is essential because a final S after bias one could otherwise disappear into cursor zero and cause refill.

## Adjacent candidate construction

For a fixed positive first-read encoding K of W and every x≥0, put

    n=P(1,P(x,P(0,1+K))).

The first candidate executes MP(x);S;W. The predecessor identity follows in three valid steps, all with strictly positive subtracted right arguments:

    n−1 = P(2, P(x,P(0,1+K))−1)
        = P(2, P(x+1,P(0,1+K)−1))
        = P(2, P(x+1,P(1,K))).

That predecessor executes AX(0;1,x+1);W. The two work stores need not coincide, since W is universally halting. Their first reads into W are identical: after S the residual is 1+K and b=0, whereas after AX the residual is K and b=1. Both adjust to K.

The x=0 endpoint is valid. Varying x alone makes the pairs cofinal; no separate equidistribution or variation of terminal r is needed.

## Draining and coverage

For every positive n, the Cantor right projection f(n) is strictly less than n. Therefore every subsequent residual strictly decreases, whether the incoming bias is zero or one. A nonhalting run thus enters infinitely many candidates with unbounded increasing numbers and gaps at most two.

Every sufficiently late adjacent pair is hit: the first selected value at least n−1 is at most n because its predecessor is at most n−2 and its jump is at most two. This gives completeness without assuming a fixed parity or arithmetic progression.

## Soundness for the stated seed

The proposed seed stack 3 is safe because 3=P(2,0), 2=Q_0(0), and truth zero and its generalization are theorems. The zero tail unfolds into theorem zeros. Define stack safety by all iterated decoded heads, not by a uniquely recoverable finite list length. The original short-S, MP and AX equations preserve this safety and theorem-valued top/cache; a short-S halt therefore certifies theorem 1.

Thus no protected-credit theorem is needed for this specific safe seed. This observation remains mathematically valid even though the existing faulty source destroys the intended command equations and injects 1 into H from scratch.

## Conclusion

The feedback-scheduler/cofinality obstacle has a complete abstract solution. A repaired binary implementation still needs exact source binding, universal primitive runtime and whole-tape blank initialization. The archived source must not be promoted using this conditional theorem.
