# Exact compaction for bounded-multiplicity ascent sequences

Proved 1 October 2026. This note concerns the exact counting operator, independently of any analytic growth-constant conjecture.

## 1. Raw states and the last boundary

Fix an integer b >= 2. An ascent sequence is a word a_1 ... a_n with a_1=0 and

    0 <= a_t <= 1 + asc(a_1 ... a_{t-1})   (t >= 2).

Each label may occur at most b times. After a nonempty prefix, call all labels in {0,...,1+asc(prefix)} that have not exhausted their multiplicity budgets *active*. Keep these labels in numerical order. Their positive remaining budgets form a tuple beta=(beta_0,...,beta_{m-1}), with each beta_i in {1,...,b}. Let

    k = number of active labels <= the actual last label.

This is a boundary, not necessarily the rank of an active label: if the actual last label has just exhausted its budget and been removed, k is the resulting virtual gap. A choice at active rank i is an ascent exactly when i >= k.

The raw suffix-counting process therefore has this exact transition, with alpha=1_{i>=k}:

- Decrease beta_i by one
- If it becomes zero, remove this entry and set k'=i
- Otherwise keep the entry and set k'=i+1
- If alpha=1, append one new top label with budget b

Appending the new top label is correct because the ascent count and hence the upper admissible label each increase by exactly one. No other new label becomes available. Deleting exhausted labels and relabeling the surviving order does not affect any ascent comparisons; k stores the comparison with a possibly deleted last label.

In every reachable nonempty-prefix state, the top admissible label is unused and lies strictly above the last label. Consequently at least one budget-b label remains active, and 0 <= k < m. For the actual prefix 0, the raw state is ((b-1,b),1).

## 2. Adjacent-budget interchange lemma

**Lemma.** Let x<y be two labels adjacent among the initially active labels, and suppose y is at or below the actual last label. Equivalently, if their active ranks are r,r+1, assume r+1<k. Give x and y arbitrary positive remaining budgets c,d; leave every other budget unchanged. For every suffix length N, the number of legal suffixes is unchanged if c,d are interchanged while the last boundary stays fixed.

The lemma applies to arbitrary raw states, including states with a virtual last boundary. It does not require the two budgets to differ by one or be equal to any prescribed b-dependent values.

**Proof by an explicit involution.** Given a suffix word, divide it into maximal contiguous blocks consisting only of x and y. In each such block:

1. Reverse the order of its letters
2. Interchange x and y

Leave all other letters in their original positions. Denote this map by Phi.

The set of positions occupied by x or y does not change, so the maximal blocks do not change, and applying Phi twice returns the original suffix. Within every block the counts of x and y are interchanged. Hence total suffix usages of x and y are exchanged, with all other label usages fixed. The original quota constraints c,d therefore imply the transformed quota constraints d,c. Since multiplicity constraints are upper bounds and every prefix usage is at most total usage, this also verifies quotas at every intermediate time.

Internal ascents of a binary block are preserved in number. Indeed an old adjacent pair p,q becomes the pair complement(q),complement(p), and

    p < q  iff  complement(q) < complement(p).

Thus the ascent indicators are reversed in order, with their sum unchanged. Outside labels cannot lie strictly between x and y: none was initially active there, exhausted labels never return, and every subsequently introduced label is above the initial active set. Consequently a boundary comparison between a block letter and an outside label has the same result after Phi. If the suffix begins with an x,y-block, entry into that block is nonascending both before and after Phi, because the original last label is >= y. This is exactly the role of r+1<k; it includes the case in which the last label itself equals y.

It follows that the cumulative ascent count agrees at the end of every transformed block, and before every unchanged outside letter. The precise timing of ascents inside a block can change, but both x and y were already available at the start of the suffix. Therefore they remain below the nondecreasing admissible upper bound at every position of the transformed block. All unchanged outside letters see the same admissible upper bound as before. Thus Phi preserves ascent-sequence legality.

Phi is consequently a bijection from length-N legal suffixes with budgets (c,d) to those with budgets (d,c). In fact it preserves the total number of suffix ascents as well. QED.

**Scope caution.** The lemma allows arbitrary permutations of the first k budgets by adjacent swaps. It does not assert that arbitrary budgets *above* the last boundary can be sorted without changing the count. The global grouped-state reduction below uses only legal swaps below the newly chosen last boundary.

## 3. Canonical grouping and exact child rank

Use canonical states in which the active budgets are weakly increasing: remaining budget 1 at the bottom, then 2, ..., then b at the top. Equivalently labels are grouped from most-used to least-used, with unused labels at the top. Let s_j count labels used exactly j times, for 1 <= j < b, and let u count unused labels. The group order is

    j=b-1, b-2, ..., 1, 0,

where group 0 has size u and remaining budget b. Put m=u+sum_j s_j. Retain the last boundary k, with 0<=k<m.

Suppose a label of rank i and remaining budget r is selected. If r=1, its exhausted entry is removed and the surviving tuple is already sorted. The new last boundary is k'=i. If r>1, the entry decreases from r to r-1. The sole resulting disorder is that this entry may now follow other entries of budget r. Bubble it left to the beginning of its former budget-r group. Every swap exchanges adjacent entries with right endpoint at most i. Both swapped entries therefore lie among the first i+1 positions, below the new boundary k'=i+1. The lemma applies to each swap. The boundary is held fixed during each application, so sorting leaves k'=i+1 unchanged.

Any newly born label has budget b and is appended at the top, preserving sortedness. Thus every child raw state has exactly the same suffix counts as the canonical grouped child described here, for every suffix length.

This explains an initially counterintuitive point: the budget of the label just selected can move left during compaction, but the last boundary does not follow that budget. The interchange lemma changes budget assignments and transforms entire future suffixes while holding the current numerical last boundary fixed.

## 4. Exact positive operator

Write N_0=u and N_j=s_j for 1<=j<b. The groups in increasing rank order are N_{b-1},...,N_1,N_0. For every integer i in [0,m-1], let j be its group and put alpha=1_{i>=k}. The child population is

    N' = N - e_j + 1_{j+1<b} e_{j+1} + alpha e_0,

and its boundary is

    k' = i       if j=b-1,
    k' = i+1     if 0<=j<b-1.

Here e_j is the jth population unit vector. In expanded terms:

- Used label j<b-1: s_j decreases by one, s_{j+1} increases by one, and u increases by alpha
- Saturating label j=b-1: s_{b-1} decreases by one and u increases by alpha
- Unused label j=0: s_1 increases by one and u changes by alpha-1

Define (T_b f)(N,k) as the sum of f over these m child states, counting each choice separately. With initial state

    x_0: s_1=1, all other s_j=0, u=1, k=1,

we have exactly

    T_b^n 1(x_0) = A_{n+1}^{(b)}.

This follows either by induction on remaining suffix length using the lemma at each child, or by composing the explicit suffix bijections. No asymptotic approximation or conjecture is involved.

The state conditions u>=1 and 0<=k<m are invariant. In particular, a nonascending unused-label choice cannot consume the final unused label: the last rank m-1 is unused and lies at or above k, hence would be an ascent. If a nonsaturating choice is at the top rank, it is ascending and creates a new top label, ensuring k'<m'. A saturating label cannot be the unused top label, so deletion also preserves k'<m'.

## 5. Exact weighted rank formulas

These identities are useful for analytic barriers. Assign any weights rho_0=1 and rho_j to group j, with rho_b=0 as a convenient notation for an exhausted label. No monotonicity assumption on these weights is needed for the following algebra. Let

    D = sum_{j=0}^{b-1} rho_j N_j,
    h(i) = sum of weights of the old labels with ranks strictly below i.

For selection of a group-j label at rank i, the exact canonical child satisfies

    D' = D - rho_j + rho_{j+1} + alpha,
    h_child(k') = h(i) + rho_{j+1}.

Indeed, before compaction the prefix ending at the new last boundary consists of all old labels strictly below i plus the selected label with its new weight, or just the old lower labels if it exhausted its budget. The appended top label is strictly above the boundary. Every compaction swap stays entirely inside that prefix, so it preserves its total weight. The denominator identity follows directly from the population update.

Consequently the exact child weighted rank fraction is

    r_child = [h(i)+rho_{j+1}] / [D-rho_j+rho_{j+1}+alpha],

whenever the denominator is positive. This includes saturation, with k'=i and rho_b=0; unused choices, with rho_0=1; and a virtual last boundary.

## 6. Independent finite verification

The companion executable `compaction-verify.py` implements three separate calculations:

1. Direct generation of numerical ascent-sequence words using their actual ascents and usage counts
2. The unsorted raw-budget recursion, with exhaustion/removal and new-label birth but no compaction
3. The grouped recursion in Section 4

All three agree for b=3 and b=4 through length 9:

    b=3: 1,1,2,5,14,47,180,773,3701,19488
    b=4: 1,1,2,5,15,52,210,964,4960,28272

Separately, all unequal adjacent-budget swaps below k were checked for every budget tuple of length 2 through 4 and suffix length 1 through 5, allowing k=m as an additional generalized-state stress test. There were 1,920 comparisons for b=3 and 6,540 for b=4; all passed.

All canonical sorted budget tuples of lengths 1 through 5, all boundaries k=0,...,m, and suffix lengths 0 through 5 were also compared between raw and grouped recursion. There were 1,590 comparisons for b=3 and 3,774 for b=4; all passed.

These checks support the implementation but are not the proof; Sections 1-5 establish exactness for every b and every length. Machine-readable results are in `compaction-validation.json`.

A fourth, word-level check directly applies the proposed involution to every legal length-5 suffix for all initial budget tuples of lengths 2 and 3, all eligible boundaries and all unequal eligible adjacent-budget pairs. For each individual suffix it verifies that Phi squared is the identity, its total ascent count is preserved, and it is legal under the exchanged quotas. All 16,218 b=3 cases and 53,282 b=4 cases pass. This separately tests the actual map rather than merely equal aggregate counts. Code and results are in `compaction-bijection-check.py` and `compaction-bijection-validation.json`.
