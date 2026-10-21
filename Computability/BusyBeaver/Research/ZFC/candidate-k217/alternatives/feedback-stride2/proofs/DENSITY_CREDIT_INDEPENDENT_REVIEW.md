# Independent review of the optional density-credit theorem

Verdict: PASS for the defined abstract biased scheduler, including every increasing candidate sequence starting at 1 with gaps in {1,2}. This is not a source-binding certificate for the rejected binary experiment.

Reviewed `research215_round3_scheduler/OPTIONAL_DENSITY_CREDIT_LEMMA.md` and its owned finite dynamic-program certificate. The review below supplies the index checks that matter in the infinite argument.

## Candidate recursion

For n=P(a,y), the exact candidate grammar is:

- a=0: one S followed by W(y−1) if y>0;
- a=1: one MP followed by W(f(y)) if f(y)>0;
- a≥2: one AX followed by W(f²(y)) if f²(y)>0.

These follow because S sets bias zero, while MP/AX set bias one. Empty residuals stop the current candidate rather than reading W(0). Hence g(0)=0 is necessary, whereas s(0)=1. The document handles this distinction correctly.

## Strong-induction argument

Let A(N)=sum_{n<N}s(n). For positive L below the induction target,

    sum_{j<L}g(j)=A(L)−s(0)≤L−1.

The f-sequence splits into consecutive nonempty prefixes of (0,1,...,k). Each such block loses at least one relative to its length. Therefore pullback prefix sums satisfy H(L)≤L−r(L), where r(L) is the number of nonempty diagonal blocks, the least r such that T_r≥L. Since H(L)≤L−1 for L>0 and the pulled-back function also vanishes at zero, the same argument applies a second time, giving H2(L)≤L−r(L).

At T_q, q≥2, decomposition by root command gives exactly

    A(T_q)=q+A(q−1)+H(q−1)+sum_{l=1}^{q−2}H2(l).

The first q counts all S roots, the second term their suffixes, H counts MP-root suffixes, and the final sum counts AX-root suffixes with their correct multiplicities. Substitution yields

    A(T_q)≤T_q−[sum_{l=1}^{q−1}r(l)−(q−1)].

The bracket is nonnegative because r(l)≥1. Every induction invocation has a smaller argument than the current target; q=0 and q=1 are separate direct small cases.

For N=T_q+k, 0≤k≤q, a partial diagonal starts with AX roots. For k≤q−1 its cost is H2(k). For k=q its additional MP suffix costs g(f(q−1)). The bounds g(m)≤m and f(q−1)≤r(q−1) give total extra cost at most q−1. The g bound follows by taking one term in A(m+1)−s(0), and its induction argument is again smaller than the current target. Thus A(N)≤N for all N.

## Uniform prefix-credit estimate

For a selected candidate n, the number of earlier candidates is at least floor((n−1)/2). This is a deliberately weaker version of the available ceiling bound, so parity is harmless. Among all indices through n there are at most 2q+1 non-AX roots, where q is the current Cantor diagonal index. Subtracting even this overcount from the earlier selected candidates gives a valid lower bound on already completed root AX commands.

Only AX commands in earlier completed candidates are credited. No credit is borrowed from the current candidate before it executes. All S commands executed through any point of current candidate n are bounded above by A(n+1)≤n+1. Therefore the claimed lower bound

    10 floor((n−1)/2)−20q−10−(n+1)
    ≥4n−20 sqrt(2n)−21

is valid for every internal prefix. At n=64 the right side is greater than 8, and its derivative is positive thereafter. Candidates 1 through 63 are the entire remaining domain.

## Finite certificate audit

The original owned checker was rerun. Independently, this review reconstructed W(n) recursively from the three displayed grammar clauses using an elementary triangular-search unpair algorithm, rather than the worker's iterative parser/isqrt implementation. A separate min-plus dynamic program reproduced all 63 certificate entries exactly, including every word and entry/internal/exit balance.

The minimum is −3, attained on the permitted prefix schedule 1,2,4,5. The receipt is `DENSITY_CREDIT_REVIEW_CHECK.json`; the reviewed finite certificate SHA-256 is `d330aaa4019d6585a0fc072a89eb556ede62ca8dfdb708b3a05964c34bd04283`.

The finite domain is justified by the analytic bound, not by the separate 200,000-candidate corroboration. Starting at 1 and gaps at most two are explicit hypotheses. The theorem must not be silently applied to an arbitrary later starting counter or a larger-gap sequence.

## Stack interpretation

Three initial safe wrapper heads suffice: every S consumes one head, and the cumulative lower bound prevents consuming a fourth unprotected head. At a return that leaves wrapper length zero, the just-loaded cache is still the final safe head. MP's possible extra zero push is conservatively ignored; AX contributes ten safe heads. This argument uses an explicit finite wrapper over an opaque tail, not a uniquely encoded numerical stack length.

The actual hypothetical seed W=3 needs no credit theorem because all of its decoded heads are already theorems. The optional theorem nevertheless supplies a sound, stronger resource result for other safe wrappers, conditional on the specified command/scheduler equations.
