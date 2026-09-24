# Proof and claim audit

## Universal synchronization theorem

**Claim:** For every integer k >= 1, the specified A_k has the reset word
R_k = p (e c^(r-1))^(r-2) e, where r=k+4, c=ab, p=c^r,
e=a p b p c^(r-1). Every state ends at q_2.

**Proof chain in the article:**
1. The c-functional graph has the r-cycle (0,1,3,...,2k+3,2).
2. All other states enter that cycle within r-2 steps. The junction enters
   at state 2 in exactly r-2 steps, by traversing every tail state once.
3. Hence p=c^r retracts the entire state set onto that cycle and fixes it.
4. On cycle indices, ap is j -> -j except r-2 -> 1; bp is j -> 1-j.
5. Composing ap, bp and the backward cycle rotation gives the elementary
   transformation r-2 -> r-1, fixing all other indices.
6. Combining this elementary merger with backward rotation gives a directed
   path with one fixed endpoint. Its powers lose one image state each time.
7. A final elementary merger collapses the final pair to index r-1, state 2.

Every step is an all-parameter argument. No BFS table, finite test, conjecture,
unproved pair-distance formula, external Lean theorem or purported global
inverse of c is a premise.

**Length:** literal concatenation gives 8r^2-10r+4 = 8k^2+54k+92.
This is an upper bound on reset threshold, not an equality for that minimum.

**Novelty:** The consulted 2026 survey and September 2026 online note leave
all-k synchronization open. This supports the problem selection but is not
an exhaustive priority search. The credited 2018 thesis was not examined.
The draft has not received independent human peer review.

## Shortened-tail theorem

**Claim:** The one-state-shorter family, with the endpoint loop moved to the
new last state, is strongly connected but not synchronizing.

**Proof:** A surjective explicit coloring onto Z/rZ intertwines a and b with
x -> -x and x -> 1-x. Every word is therefore a permutation on the quotient;
its original image has at least r states. The proof separately checks both
endpoint parities and the one-state tail k=1.

**Relation to A_k:** For the actual family the same coloring has exactly one
failure, at the endpoint self-loop. The retract converts the discrepancy
into an elementary merger. This is a structural explanation, not a claim
that all near-permutation automata synchronize.

## Known short merging word

**Claim:** (ba)^(k+2)(ab)^(k+2) merges q_0 with q_2 to q_2, length 4k+8.

**Status:** Prior result in the Machina Mathematica/Korea Superintelligence
Labs note, reproved here using the c-trajectory. Not claimed new.

**Correction:** The source's displayed (ab)^(k+2) a (ab)^(k+2) is a times
that word and has length 4k+9. It merges q_0 with q_1. The correction too is
prior work. It does not refute the numerical conjecture tau(q_0)=4k+8.

## Finite pair-distance claims

**Claim:** For each k=1..200, the table is the complete exact pair-distance
function. The threshold is 4k+8; d(0,1)=4k+9; the optimal partner set is
{2,2k+5}; the stated parity-dependent diameter formula holds.

**Evidence:** 200 gzip JSON certificates containing 12,486,300 pair entries;
an independent verifier checks zero diagonal, positive off-diagonal, and
d(P)=1+min(d(Pa),d(Pb)) for every off-diagonal pair. The article proves that
these local conditions imply both lower and upper distance bounds. Completed
logs are included, together with the source and full CSV.

**Not established:** Any of these exact formulas for k>200; uniqueness of an
optimal word; an asymptotic theorem inferred from the diameter formula;
the shortest reset threshold. The proof of universal synchronization is
separate and does not rely on extrapolating the finite tables.

## Source-model fidelity

The printed map in the survey is incomplete at b(0) and one endpoint arrow.
The article uses b(0)=1 and an endpoint return to the predecessor, matching
Figure 3 and the prior note. The theorem is specifically for this complete
model, not every possible filling of omitted arrows.

A wrong completion can change the numerical question immediately: assigning
b(0)=0 makes b merge states 0 and 1 in one step.

## Implementation checks and trust boundary

The two automaton constructors use different descriptions (cases versus
transpositions), and their outputs were compared over the structural test
range. Word orientation was compared to a state-by-state evaluator. Expanded
reset words were checked for k=1..10. Three damaged certificates were rejected.

The code uses explicit exceptions, not assertions disabled by optimization.
Nevertheless it is ordinary Python, not kernel-checked mathematics. The two
programs were developed in the same research session. Software independence
does not constitute independent authorship, peer review or source validation.

## Remaining lower-bound task

A universal function L_k on pairs with L_k(diagonal)=0,
L_k(P)<=1+L_k(Pa), L_k(P)<=1+L_k(Pb), and
L_k({q_0,q_j})>=4k+8 for all j>0 would complete the numerical conjecture.
No such all-parameter formula is claimed or supplied. The finite exact tables
are examples only for their individually certified parameters.
