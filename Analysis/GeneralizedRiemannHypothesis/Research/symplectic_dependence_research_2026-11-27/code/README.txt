EXACT SYMPLECTIC CYCLE LAW CALCULATOR

Requires Python 3.10 or later. No third-party packages are needed.

Model
-----
There are independent uniform nonzero vectors at the vertices of a cycle.
The ambient space has dimension 2*n over a field with q elements, with a
fixed nondegenerate alternating bilinear form. The observed edge labels
are the symplectic pairings of consecutive vectors.

The comparison law has independent edge labels with the same individual
edge distribution. It is NOT the uniform law on edge labels.

Commands
--------
python3 cycle_laws.py --q 2 --n 3 --length 3
python3 cycle_laws.py --q 4 --n 2 --length 6 --format text
python3 cycle_laws.py --q 3 --n 2 --length 4 > cycle_example.json
python3 cycle_laws.py --self-check

q may be any prime power at least 2; n must be at least 1; the cycle
length must be at least 3. The code validates the prime-power condition.
Very large parameter values may produce large exact integers.

JSON output
-----------
All exact fractions are JSON strings such as "7/15". The keys tv_decimal
and chi_square_decimal give 18-significant-digit decimal summaries.

groups contains all possible outcomes of an exactly sufficient statistic:
* Odd cycle: the number z of zero edge labels.
* Even cycle of length 2*k: z, and when z=0, the resonance bit
  a_1*a_3*...*a_(2*k-1) = (-1)^k*a_2*a_4*...*a_(2*k).

For each group, multiplicity counts full edge-label vectors; point masses
are the probabilities of each full vector; group masses aggregate them;
and likelihood_ratio is actual mass divided by independent comparison
mass. The ratio is constant on each group, which makes the statistic
exactly sufficient for this hypothesis comparison. Impossible groups
(for example the nonresonant all-nonzero group when q=2) are omitted.

Cycle labels must use the cyclic orientation 1->2->...->length->1.
For a reversed edge, negate its observed label before evaluating the
resonance condition. In characteristic two this has no effect.

Using the functions from another Python program
---------------------------------------------
from cycle_laws import (
    edge_marginal, cycle_groups, cycle_tv, cycle_chi_square,
    cactus_chi_square, verify_law
)

p_zero, p_each_nonzero = edge_marginal(4, 2)
groups = cycle_groups(4, 2, 6)
tv = cycle_tv(4, 2, 6)                  # fractions.Fraction
chi2 = cycle_chi_square(4, 2, 6)        # fractions.Fraction
chi2_cactus = cactus_chi_square(2, 3, {3: 2, 4: 5})
verify_law(4, 2, 6)

The cactus function uses exact independence of the whole cycle blocks.
It takes a dictionary mapping each cycle length to its number of cycles.
Bridges do not affect the divergence. It returns the complete cactus
chi-square divergence, not a sum of the cycle divergences:
product_over_cycles(1 + cycle_chi_square) - 1.

Validation and scope
--------------------
--self-check performs 432 exact parameter checks, including extension
field orders 4, 8, 9, 16, and 25. It checks normalization, nonnegativity,
group multiplicities, and agreement of grouped pointwise divergences
with separately coded closed formulas. It does not construct finite
fields or enumerate vectors. The accompanying independent enumeration
artifact checks actual finite-field vectors separately.

These computations are exact-arithmetic checks of the formulas. They do
not assert a compiled Lean proof or replace the mathematical proof in
the paper.
