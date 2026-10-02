# Independent audit: higher-arity DFA renewal comparison

Audit date: 2026-10-02. Scope: the renewal comparison in `/workspace/shared/larger-alphabet-automata-research/proof.md`, not an independent reproof of the relaxed-tree Airy theorem. No claim of universal novelty or amplitude equivalence.

## Verdict

**The comparison proof passes, with its explicit boundary convention retained.** For every fixed integer k >= 3 and n >= 1,

P(k,n) 2^(n-1) R_n <= B_n <= 2^(n-1) R_n,

P(k,n) = product over j=2,...,n of [1 - 1/(2 j^(k-1))].

The proof actually gives the displayed finite inequality for k=2 as well. The positive uniform lower constant is specific to k>=3. Independent exact recurrence and positive-renewal computations agree on every supported entry for k=2,...,8 and n<=30. Independent direct graph enumeration agrees in the smaller ranges described below.

## 1. Boundary and counting conventions

Write q=k-1. The combinatorial count B_n is the number of accessible minimal complete DFAs, up to state isomorphism, recognizing finite languages over a fixed ordered k-letter alphabet, with n transient states and one rejecting sink. Equivalently it counts languages of complete state complexity n+1. Alphabet permutations are not quotiented out. B_0=1 represents the empty language. At n=1, the only language is {epsilon}, so B_1=1.

Use r(x,0)=b(x,0)=1 for x>=0, triangular support x>=qm, and **b(-1,0)=1**. All other out-of-domain terms vanish. Alternatively bypass the auxiliary entry by specifying directly

b(x,1)=2^(x-k+2)-1 for x>=k-1.

This matters: applying the printed interior recurrence with every negative-index term zero yields b(k-1,1)=2, which contradicts both the elementary DFA count and the published numerical table. The special b(-1,0) value supplies exactly the missing subtraction. It is not a counted negative-size object; it is an auxiliary recurrence convention. The proof under review states this clearly and therefore passes.

R_0=R_1=1. At size 2, R_2=2^k-1 and B_2=2(2^k-1), providing another immediate sanity check. The finite comparison must be stated for n>=1; the factor 2^(n-1) makes its naive n=0 extension false.

## 2. Positive completed-run renewal

The proof defines A(x,1)=a(x,1)=1 for x>=q and zero below the triangular boundary. At each level m>=1 it uses

V_m(l)=(m+1)^l,
W_m(l)=2(m+1)^l - 1_{l>=k}(m+1)^(l-k+1).

For x>=q(m+1), the next A row is the convolution of W_m with the preceding A row, over 0<=l<=x-qm; a uses V_m instead. Thus every completed-run history visits each height m exactly once. The history is specified by its nonnegative run lengths and the same triangular admissibility constraints in both models.

The generating function identity

sum_l W_m(l)t^l = [2-(m+1)t^k]/[1-(m+1)t]

is exact as a formal power series. Following with the horizontal-run convolution establishes

b(x,m)=sum_l (m+1)^l A(x-l,m),
r(x,m)=sum_l (m+1)^l a(x-l,m).

Consequently A(x,m+1)=2b(x,m)-(m+1)b(x-k,m). Incorporating the final horizontal run recovers exactly the signed b recurrence. All sums respect the triangular zero conventions. In particular, at the diagonal x=qm only l=0 survives in the trailing-run sum, so B_m=A(qm,m) and R_m=a(qm,m).

This derivation avoids a dangerous invalid shortcut: the signed recurrence cannot itself support an ordinary termwise comparison by dropping its negative term and then comparing inductively. The regrouped W coefficients are positive, so the comparison is valid there.

## 3. Multiplication of losses and positivity

For all l>=0,

W_m(l)/(2V_m(l)) = 1 if l<k,
W_m(l)/(2V_m(l)) = 1 - 1/[2(m+1)^(k-1)] if l>=k.

These identities show strict positivity for k>=2, m>=1. The lower factor is independent of the run length. Each path has precisely one possible loss at each level m=1,...,n-1, not one loss per horizontal step. Therefore its weight ratio to the colored relaxed path is a product of a subset of the factors indexed by j=2,...,n. Because all factors lie in (0,1), this ratio is bounded below by the product of ALL factors. Summing pathwise preserves both bounds.

Equivalently, induction on positive convolutions gives the full-array bound

2^(m-1)P(k,m)a(x,m) <= A(x,m) <= 2^(m-1)a(x,m),

and the same for b and r after the nonnegative trailing-run convolution. The initial factor is 2^0, because the first transient state must accept; only later transient states have two unconstrained color choices in the relaxed comparison model.

## 4. Infinite product and uniformity

For k>=3, the sum of deficits 1/[2j^(k-1)] converges and each deficit is <=1/8. Thus the logarithm of the product converges to a finite number and P(k,infinity)>0. Factorwise monotonicity in k gives

P(k,infinity) >= P(3,infinity)
= (2 sqrt(2)/pi) sin(pi/sqrt(2))
= 0.7163755720264882... .

The equality follows by removing the j=1 factor, 1/2, from Euler's sine product at z=1/sqrt(2). The resulting comparison constant is uniform simultaneously in n>=1 and integer k>=3. The asymptotic Theta constants inherited from the relaxed theorem are only asserted for each fixed k; the product's uniformity does not establish uniformity of the entire Airy theorem as k varies.

For k=2, P(2,n) is of order n^(-1/2), so this proof does not establish the binary polynomial exponent.

## 5. Asymptotic transfer and indexing warning

Set lambda_k=2k^k/(k-1)^(k-1), alpha_k=(2k-1)/3, and c_k=3 a_1 [k(k-1)/2]^(1/3), with a_1 the largest negative Airy zero. Combining the comparison with the published relaxed theorem gives

B_n = Theta((n!)^(k-1) lambda_k^n exp(c_k n^(1/3)) n^alpha_k)

for each fixed k>=3. For k=3 the base is 27/2 and alpha=5/3. The constant 1/2 between 2^(n-1) and 2^n is absorbed in Theta.

**If the variable denotes TOTAL states N, the polynomial exponent changes.** Since the count is B_(N-1), writing the formula with (N!)^(k-1) and lambda_k^N gives

B_(N-1) = Theta((N!)^(k-1) lambda_k^N exp(c_k N^(1/3)) N^((2-k)/3)).

The factorial shift contributes N^(-(k-1)); the Airy shift is asymptotically negligible. In particular, the ternary total-state exponent is -1/3. Keeping (N-1)! and N-1 throughout is an equally valid way to avoid confusion.

Neither a fixed positive comparison nor the numerical ratios establishes a limiting amplitude. The proof correctly leaves this open.

## 6. Finite-defect truncation

Retain W_m only for m<M and replace it by 2V_m thereafter. The lower comparison ratio is then the product over j=M+1,...,n. The claimed uniform error bound

0 <= 1-B_n/B_n^[M] <= 1/[2(k-2)M^(k-2)]

is valid for k>=3. It follows from the product inequality 1-product(1-u_j)<=sum u_j and the integral test. For n<=M the ratio is exactly one.

The convergence reduction is also valid. Normalize by 2^(n-1)R_n; every normalized truncated value is <=1, so this relative error is also an absolute normalized error. If each fixed-M normalized truncation converges as n grows, its limit sequence is Cauchy by uniform approximation, and the original normalized sequence converges. Those fixed-M limits have NOT been proved by this argument.

## 7. Independent exact tests

Reproducible script: `exact_checks.py`; saved output: `exact_checks.json`.

1. Signed recurrence implemented independently from positive renewal, using exact Python integers.
2. For k=2,...,8 and N=30, all supported entries x<=qN, 1<=m<=N were checked for both reconstruction identities and the product inequalities. Products use exact rational arithmetic.
3. A separate brute-force enumeration generated transition tuples for every postorder-labeled DAG, rejected graphs whose deterministic left-to-right DFS postorder did not match the labels, and enumerated accepting/rejecting colors. Requiring distinct color/transition signatures is sufficient and necessary for acyclic DFA minimality by bottom-up induction. The sink was rejecting, the first transient state accepting, and reachability was enforced by DFS. No division by guessed automorphism factors was used.
4. Brute-force ranges: k=2 through n=5; k=3 through n=4; k=4 and k=5 through n=3. Every result matched both arrays. For example k=3,n=4 gives R=5711 and B=42644.

## 8. Primary-source and version check

Verified against Dastidar–Wallner, *Asymptotics of Relaxed k-Ary Trees*, AofA 2024, DOI https://doi.org/10.4230/LIPIcs.AofA.2024.15 (published 2024-07-18). Its Theorem 1 gives the relaxed estimate, Proposition 8 the relaxed recurrence, and Proposition 12 the DFA recurrence and total-state indexing. Its conclusion reserves the other asymptotic generalizations for a longer version.

The arXiv record https://arxiv.org/abs/2404.08415 lists only v1 dated 2024-04-12 as checked on 2026-10-02. The author's current publication page https://manosijghoshdastidar.wordpress.com/2026/06/30/109/ also lists the AofA paper. Targeted title searches did not identify a later version. This is a bounded literature check, not proof that no later theorem exists.

## Final scope of certification

Certified: the boundary-repaired positive renewal construction; finite and uniform-product comparisons; transfer of the published relaxed Theta estimate; total-state reindexing; finite-defect error reduction; exact checks.

Not certified here: the source paper's full computer-assisted Airy proof, an amplitude equivalent, finite-defect endpoint-ratio limits, or priority/novelty of the comparison result.
