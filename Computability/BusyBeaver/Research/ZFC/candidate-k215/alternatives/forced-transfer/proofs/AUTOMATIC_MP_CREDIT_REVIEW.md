# Independent review of automatic-M stack credit

Verdict: PASS for the abstract ordinary consecutive scheduler and displayed automatic-M command equations. This is not a source/physical calibration or a new state-count result.

Reviewed `research215_round4_auto_mp/CREDIT_THEOREM.md`, its owned checker and receipt, and the relevant command interfaces in `research215_round4_calculus/AUTOMATIC_MP_COMPILER.md`.

## Correct counting recurrence

Let k(n) count S and M commands, each charged−1. The ordinary positive continuation cursor is decremented before its next first-field read. Consequently g(0)=0 and g(r)=k(r−1) for positive r are the correct suffix counts. The three root recurrences

    1+g(y),  1+g(f(y)),  g(f²(y))

for selectors0,1,≥2 follow directly. In particular M has both its own negative cost1 and its suffix term; that extra1 must not be omitted at partial diagonals.

## Infinite induction

For every positive relevant L, the g-prefix sum is B(L−1), not B(L) or B(L)−1. Strong induction therefore gives at most2(L−1). Splitting the right-Cantor projection sequence into nonempty diagonal prefixes loses at least2 per block, so H(L)≤2(L−r(L)). Its pulled-back function still vanishes at zero and satisfies the required prefix hypothesis, so the same inequality holds for H2.

At a complete triangular boundary, the exact root decomposition is

    B(T_q)=q+B(q−1)+(q−1)+H(q−1)+sum_{l=1}^{q−2}H2(l).

The constants q and q−1 count the S and M roots. Substitution gives exactly

    q²+3q−3−2 sum_{l=1}^{q−1}r(l)
    ≤q²+q−1 <2T_q.

The algebra is correct. For q≥2 every invoked induction argument is smaller than T_q; q=1 is a direct small case.

A partial diagonal with j≤q−1 contains only AX roots, costing H2(j)≤2j. At j=q its MP root adds1+g(f(q−1)). For m>0, g(m)=k(m−1)≤B(m)≤2m; g(0)=0 handles the endpoint. Using f(q−1)≤r(q−1) gives total additional cost at most2q−1, as claimed. The pointwise induction argument m is strictly below the current target. Thus B(N)≤2N holds for every natural N.

## Prefix-credit estimate

The candidate schedule is explicitly1,2,3,..., not either earlier biased schedule. Before candidate n, exactly n−1 candidates have completed. At most2q+1 of all indices through n have non-AX roots. Subtracting this overcount gives a valid lower bound n−2q−2 on already completed root AX commands; when negative it remains a valid lower bound.

All negative commands executed through any internal point of n are at most B(n+1), including an extra harmless count for candidate zero. No credit from an unexecuted current AX is used. Therefore

    10(n−2q−2)−2(n+1) ≥8n−20sqrt(2n)−22

is valid. At n=32 the right side is74>0, and it increases thereafter. Thus the finite domain1,...,31 genuinely suffices.

## Independent finite verification

The review used an iterative predecessor-cursor parser with elementary triangular-search unpairing, rather than the original recursive cached word function and integer square root. It reproduced all63 archived records, including each word, entry/exit balance and internal prefix minimum. On the required first31 candidates the minimum is−3 and exit balance178. Candidate1 is M, and candidate2 is S;S, attaining−3.

Owned checker: `check_auto_mp_credit.py`.
Receipt: `AUTOMATIC_MP_CREDIT_BASE_REVIEW.json`.
Reviewed original receipt SHA-256:
`f196736c35e46c709b95b2361ab1b085ba52c7af842546977af7ee38e7649b90`.

The longer finite counting sanity check is not used to justify the infinite bound.

## Wrapper soundness

The automatic M first performs cache-return MP without a successful zero push, then short S. On successful MP the new cached consequent is a theorem by numerical modus ponens; on failure its cache is theorem zero. The MP portion leaves the old stack untouched. The final short S either halts soundly on cached theorem1 or consumes exactly one safe stack head and leaves theorem-valued top/cache. Thus−1 is the correct conservative stack balance for either nonhalting M branch, and its lowest stack depth is its final depth.

Explicit S has the same one-head consumption; AX adds ten theorem heads. Starting with ten safe wrapper heads, the global minimum−3 leaves at least seven above the opaque tail at every nonhalting command boundary and throughout these stack-changing command interiors. The numerical parameter may be arbitrary; it is not assumed to be a theorem. As in the other credit arguments, wrapper length is an explicit invariant, not a uniquely decoded numerical list length.

## Limits

The theorem assumes the stated command equations and enumeration starting at candidate1. A different startup cutoff or altered scheduler needs another argument. No physical table currently realizes the whole proposed interpreter within the target, so this proof must remain labeled mathematical research rather than a calibrated candidate.
