REPRODUCING THE COMPUTATIONS AND FIGURES

From the extracted article directory, run:

    python code/reproduce.py

The script uses Python 3, SymPy, mpmath, NumPy, and Matplotlib. It reads no
network resources. It recreates CSV tables and a machine-readable verification
summary in data/, plus vector PDF and 300-dpi PNG figures in figures/.
Figures render into memory before publication. The script checks each PDF's
final trailer, all cross-reference object offsets, and single-page count, then
replaces its destination atomically. An incomplete render therefore raises an
error instead of leaving a partially written figure at its final filename.

The determinant checks build the weighted rows from their recurrence and
inclusion-exclusion before taking an exact determinant. Thus they do not obtain
the rows from the Hankel product. Twelve symbolic polynomial identities
are checked, as well as rational specializations and a nonreal algebraic root.
These finite checks support, but do not replace, a proof for arbitrary k.

The probability measure in the figures is the normalized zero measure of the
reduced polynomial R_k. Its zeros have real part -1/2; Y denotes their imaginary
coordinate. Repeated roots are counted with multiplicity. W_k(q) first aggregates
the pair weights 2*gcd(i,j) for q=(j-i)/gcd(i,j). A primitive angle of denominator
m has multiplicity E_m(k)=sum_{q divisible by m} W_k(q), using the article's
notation. The code stores this multiplicity internally as M, and the CSV field
M_k_m in primitive_multiplicities.csv is exactly E_m(k).

The empirical CDF discrepancies use every reduced rational support angle and
both one-sided CDF values. They are exact fractions; they are not numerical-grid
estimates. The moments for p=2,4 are exact rational numbers, calculated using
finite cotangent sum identities. Separate high-precision evaluations check those
identities for q=2,...,40.

The tail grids use exact integer root masses and floating-point transcendental
thresholds. Generic thresholds are checked independently using 70-digit direct
root evaluations. Asymptotic constants and their plotted ratios use floating
point. See data/verification_summary.txt for the completed checks and limitations.

FIGURES

central_cdf: Empirical imaginary-coordinate CDFs against the Cauchy limit;
the right panel shows their exact piecewise-linear discrepancy after the change
of variable t=F_C(y), making arithmetic jumps visible.

edge_tail: The two-sided tail k*nu_k(|Y|>k*x) and the proved limiting arithmetic
profile E(x), with a second panel enlarging the outer edge near x=1/(2*pi).

discrepancy_moments: Exact CDF discrepancy on the log(k)/k scale, with the lower
bound from half the order-2 jump and the limit 9/pi^2 established by the article's
proof; normalized p=2 and p=4 moments on the right. The discrepancy data remain
far from their proved limiting constant at the computed finite sizes.

fixed_order_multiplicities: Exact primitive-order multiplicities m=2,3,5,6 divided
by their leading asymptotic terms. Their slow logarithmic convergence remains
visible at k=4096.

DATA

determinant_checks.csv: The symbolic, rational, and algebraic determinant checks.
degree_checks.csv: Three exact expressions for the reduced degree.
cotangent_identity_checks.csv: High-precision finite cotangent identity checks.
tail_count_checks.csv: Independent root-tail counting checks.
exact_CDF_discrepancies.csv: Full-support exact Kolmogorov discrepancies.
scaled_moments.csv: Exact normalized p=2,4 moments and asymptotic ratios.
first_absolute_moment.csv: Numerically summed first absolute moments, using
extended-precision cotangents, and the residual after the proved logarithm and
constant. Two cases are independently checked using 70-digit arithmetic.
fixed_order_multiplicities.csv: Selected fixed-order multiplicity asymptotics.
primitive_multiplicities.csv: All primitive multiplicities E_m(k) at table values
of k, stored in the field M_k_m; W_k_m denotes the unreduced denominator weight
W_k(m).
full_zero_measure_weights.csv: Exact zero masses at 0 and -1, and the mass of
the reduced zeros, for several shifts s relative to k^2.
edge_tail_grid.csv: The complete integer masses and floating-point edge curves
used to generate edge_tail.
verification_summary.json and verification_summary.txt: Results and scope.
