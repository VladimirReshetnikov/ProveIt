> Closing credit: a late packet already supplies the dense quadratic delta update. The additional positive-support sparsity, absent-label minimization and tested implementation are the surviving refinement. The cubic reference below is historical; final comparisons also include the stronger dense-delta method.

# Sparse delta conditional expectations

This is a component improvement to the asymmetric-packing derandomizer, not
a new complete SAT implementation. The reference follows the incoming
asymmetric report's conditional-expectation formula, but our baseline and
accelerated programs are independently authored from that formula. No
incoming script was executed.

After deterministic row grouping, write w[a,j] for the number of edges from
row group a to column j. Let Q be the number of labels, q=1+1/(h C)>1,
where C is the maximum column degree (use C=1 for an empty graph).
The current cell loads are l[a,b]. Before assigning column j, remove its
future factor, giving F'[a]. The exact candidate potential is

  E_b = sum_a F'[a] sum_c q^(l[a,c] + [c=b] w[a,j]).

All prior labels and future products are fixed. Set U_a=F'[a](q^w[a,j]-1).
Separate the b-independent part to obtain

  E_b = B + sum_a U_a + delta_b,
  delta_b = sum_a U_a (q^l[a,b]-1).

Since the average candidate potential is the current conditional potential P,

  E_b = P + delta_b - (sum_c delta_c)/Q.

Only rows with positive w[a,j] and cells with positive l[a,b] contribute.
Every contribution is strictly positive on this support. Consequently labels
not present in the sparse delta dictionary have score zero and are exact
minimizers; select the least absent label if any, otherwise the least label
among the dictionary's minima. This implements precisely the same
lexicographic tie-breaking as the full candidate formula. Update the selected
cell loads and the current potential using the displayed identity. Induction
shows equality of every label, candidate score, pair load and final potential.
If a certificate is requested, all Q candidate scores can be reconstructed
from the sparse dictionary and the current potential.

Let A_j be the active row set and S_a(j) the positive support of row a in the
current load table. The new scoring work is

  O(sum_j sum_{a in A_j} |S_a(j)|)

exact rational operations, plus sparse minimum lookup and sums of the same
order. It is at most O(Ncol Q^2), or O(W Q) where W is the number of nonzero
aggregated row-column incidences. By contrast, the delivered cached
asymmetric scorer computes Q candidates, each summing Q by Q cells, using
Theta(Ncol Q^3) additions/lookups and Theta(Ncol Q^2) multiplications.
Our dense-delta comparison already reduces this to O(W Q), while sparse
delta can reduce its actual work to the support sum above.

These are arithmetic-operation statements, not unit-cost bit complexity.
All rationals are exact. The implementation also pays for reading the dense
input, shared heap row grouping, q^0 through q^M caching, future factors,
O(Ncol Q) list copies, and Q^2 dense output. M is total edge multiplicity,
not its binary bit length. Thus the cache is pseudo-polynomial if adjacency
multiplicities are regarded as a succinct input; the contraction interface
already measures size in the number of edges. Certificate output costs
O(Ncol Q) additional exact values and is disabled equally in all timing runs.

Benchmark policy: common preprocessing and output are identical and timed
for cubic, dense-delta and sparse-delta references. Exact output equality is
checked for every fixture; input generation is outside timing. Full raw
samples, Python/platform, deterministic seed and rotated order are recorded.
Small timings may be noisy; neither sparse-delta nor any measured ratio is
asserted universally faster than all possible implementations. No measured
ratio is a complete-SAT speedup.
