# Sparse incremental conditional expectation

## Scope and prior work

The incoming `eth_packet_refinement` already maintains row power sums and
suffix products in `code/packet_packing.py`, lines 125–163. That routine uses
O(n Q²) rational operations to compare Q candidate labels at each of n
column vertices. The incoming asymmetric report uses a slower, literal
triple sum, but comparison with that alone would overstate novelty.

The additional step here is to subtract the candidate-independent base and
touch only row labels incident to the current column. It preserves exactly
the minimizers, including first-label tie breaking, of both existing
conditional-expectation formulations for the same chosen base z, row labels,
and column order. In particular, using the sharper column-degree base C
need not produce the same labels as an upstream run using its larger
maximum-degree parameter Delta. The benchmark matches bases exactly.
The asymmetric report's pair-load
theorem therefore applies unchanged. No improvement to its padding bound
or to the global SAT logarithmic order is asserted.

## Identity and algorithm

Fix row labels, Q column labels, rational z>1, and a column processing order.
Let w_aj be the multiplicity between row label a and column vertex j. At
step j let X_ab be already assigned load, S_a=Σ_b z^{X_ab},
f_aj=(Q−1+z^{w_aj})/Q, and U_a=∏_{k≥j}f_ak. The current conditional
expectation of Φ=Σ_ab z^{X_ab} is E=Σ_a U_a S_a.

Write A_j={a:w_aj>0}. For a∈A_j set U'_a=U_a/f_aj; outside A_j set U'_a=U_a.
The candidate-independent part and label-dependent increments are

 B=E+Σ_{a∈A_j}(U'_a−U_a)S_a,
 δ_b=Σ_{a∈A_j}U'_a z^{X_ab}(z^{w_aj}−1).

Assigning j label b gives exactly B+δ_b. This follows by replacing the
factor f_aj by z^{w_aj} in cell (a,b) and by 1 in the other cells. Choose
the least b minimizing δ_b, set E←B+δ_b, U←U', and update
S_a←S_a+z^{X_ab}(z^{w_aj}−1), X_ab←X_ab+w_aj for a∈A_j only.
All factors f_aj are positive, so rational divisions exist. Averaging over
b recovers E before the update, since Q f_aj=Q−1+z^{w_aj}. Induction proves
the maintained conditional expectation, exact equivalence to the dense
algorithm, and the nonincrease certificate. Empty columns select label 0
and leave E unchanged. Parallel edges are bundled into w_aj, not incorrectly
treated as independently labeled edges.

## Arithmetic and storage bounds

Put D=Σ_j |A_j|. With powers z^0,…,z^M precomputed, initialization takes
O(M+D+Q²) rational operations after constructing weights; processing takes
O(QD+nQ) elementary rational operations/comparisons (the nQ term includes
argmin scans and may be removed for empty columns). Dense cached comparison
takes Θ(nQ²) such operations even for sparse columns. Since
D≤min(M,nQ), the gain in the dominant score step is up to a factor Q.
For dense support D≈nQ the arithmetic order is unchanged. The additional
base calculations mean no universal finite speedup is promised.

Streaming U_a by exact division avoids the earlier Q by n suffix table.
Stored rational scalars comprise O(M+Q²+D+Q) entries including a deliberately
shared power table and sparse factors. The adjacency-matrix prototype also
stores and scans the supplied matrix and scans Q bins for each greedy row
assignment: its input/preprocessing cost O(n_rows n+n_rows Q)
must not be hidden. A sparse edge-list implementation can avoid that matrix,
but is not claimed as the delivered implementation.

These are arithmetic counts, not unit-cost bit bounds. For z=(hC+1)/(hC),
all power and product operands have polynomial bit length in the explicit
graph size and Q,h,C. Products over sparse factors have total degree at
most M and denominators involving at most n factors Q. Reduced fractions,
exact divisions, and additions thus give polynomial bit complexity. An
arithmetic-count reduction alone does not establish the same ratio of bit
times; actual measured timings are reported separately.

## Implementation and evidence

`incremental.py` is authored for this study and includes three independent
score paths: literal candidate sums, prior-style cached row sums, and the
new sparse increment. All share preprocessing and power tables. The cached
baseline also receives streaming future products, making it stronger than
the supplied suffix-storage code for this comparison. Imported executable
code is not run. Thus timings compare fresh implementations of the same
mathematical operation, not a measured run of the upstream program.

Normal and optimized Python each pass 140 fixture/label configurations,
with identical candidate scores, labels, loads, and final potentials across
all three engines; 470 independently enumerated label completions verify
the conditional means, and four invalid inputs are rejected. Tests use
explicit exceptions and do not depend on assert statements.

The benchmark records three repetitions in alternating order, times all
setup and invariant checks, and omits verbose trace generation equally.
Five seeded graph fixtures use Q=8,16,24,24,12 and column degrees 2,2,2,8,24.
Observed median speedups over the dense-cached engine in the recorded run
were 3.63,9.51,12.45,4.61,1.50 respectively. Candidate term counts were
2048→504, 12288→1488, 36864→3048, 36864→10584, 4608→3924.
Operation counters cover candidate-score computations, excluding the common
setup and state updates; the timing includes those common operations.
Exact timings, environment, seed, and counts are in `benchmark.json` and
the reproducible script. Timing variation is expected on rerun. Fixtures
were selected to span sparse and denser column support, not representative
SAT workloads. These are component performance results, not end-to-end SAT
speedups and not evidence that the enormous asymptotic crossover is practical.
