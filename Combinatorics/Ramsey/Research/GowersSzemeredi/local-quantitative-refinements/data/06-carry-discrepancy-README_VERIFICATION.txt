Exact carry-pattern enumeration
==============================

Definitions
-----------
C_k counts the distinct integer-valued functions on Boolean k-vectors

  e -> floor(sum_i e_i x_i),       0 <= x_i < 1.

D_k counts the corresponding affine functions

  e -> floor(x_0 + sum_i e_i x_i), 0 <= x_0,x_i < 1.

The offset x_0 is coordinate zero in D-case witness vectors. Boolean
vertices are stored in binary-mask order: bit i selects coefficient i.

Certified results
-----------------
 k       0    1    2     3      4
 C_k     1    1    2    10    154
 D_k     1    2    6    38      -

There are 215 final chamber witnesses and 1,165 certificates for discarded
sign-prefix branches. Every rational certificate has been checked exactly.
The small C_3 patterns are also listed in carry_results.json by the tuple
of carries on {1,2}, {1,3}, {2,3}, and {1,2,3}.

Files
-----
compute_carry_chambers.py  Candidate generation using NumPy and SciPy.
verify_carry_certificates.py
                          Independent checker using only Python's standard
                          library and fractions.Fraction.
carry_certificates.json   All rational witnesses, dual certificates, and
                          sign-prefix tree data.
carry_results.json        Compact result table and SHA-256 file hashes.
verification_log.txt     Output of the successful independent checker.

Why this is an exact computation
-------------------------------
In a C_k case, the only hyperplanes that can change a floor value inside
the open unit cube are

  sum_{i in S} x_i = j,  |S| >= 2, 1 <= j <= |S|-1.

In a D_k case, they are

  x_0 + sum_{i in S} x_i = j,  S nonempty, 1 <= j <= |S|.

Hyperplanes are processed in increasing subset-cardinality order, then
binary-mask order, then level order. A sign bit 0 means that the linear
form is strictly below the level; a bit 1 means that it is strictly above.

For each partial sign assignment the generator maximizes the common
strict margin t. Every inequality is put in the form

  a_i . x + t <= b_i.

The unit-cube inequalities are -x_j+t<=0 and x_j+t<=1. The variable t is
unrestricted. Thus the LP is always feasible (sufficiently negative t
satisfies every finite system) and is bounded above by 1/2 in positive
dimension. A branch meets an open chamber precisely when max(t)>0.

SciPy is used only to propose witnesses and dual multipliers. Before
saving a feasible branch, the program replaces its coordinate values
by rational numbers and computes an exact positive margin.

Every discarded branch comes with rational multipliers y_i satisfying

  y_i >= 0,   sum_i y_i a_i = 0,   sum_i y_i = 1,
  sum_i y_i b_i <= 0.

Adding the original inequalities with these weights proves

  t <= sum_i y_i b_i <= 0.

Hence that branch has no strictly feasible point. The exact checker
verifies all these equalities and inequalities using Fraction arithmetic.
It does not call an optimizer.

The checker also traverses the entire binary prefix tree. Every possible
child is either certified infeasible for positive margin or continued;
every unpruned terminal branch has a rational positive-margin witness.
It checks that no branch certificate is missing, duplicated, or orphaned.
Distinct terminal branches have distinct floor-value vectors. This proves
that the enumeration is complete for the open-unit-cube complement.

Boundary patterns are included
------------------------------
Every pattern realized in the half-open unit cube [0,1)^d is also realized
in an open chamber. Increase every coordinate by one sufficiently small
positive epsilon. There are finitely many subset sums; all sums initially
below their next integer remain below it, and sums initially equal to an
integer move above that same integer. The new coordinates stay below 1.
The floor values are unchanged, and epsilon can avoid the finitely many
remaining threshold intersections. This also makes initially zero
coordinates strictly positive.

Conversely every witnessed open chamber is already inside the domain
[0,1)^d. Therefore the exact chamber counts equal C_k and D_k as defined.

Reproduction
------------
From this directory, with ordinary Python 3:

  python verify_carry_certificates.py

This needs no third-party package. The checker explicitly rejects Python's
optimization option -O, because it uses assertions for exact checks.

To regenerate candidate certificates (NumPy and SciPy required):

  python compute_carry_chambers.py
  python verify_carry_certificates.py

The original candidate generation used SciPy 1.17.0. Different solver
versions may choose different rational witnesses or dual supports; the
counts and the exact validation conditions are invariant.

Scope
-----
These are exact finite computations with independently checkable rational
certificates. They are not Lean formalizations. The all-dimension
factorization, perturbation, arrangement, and entropy arguments are
mathematical arguments in the accompanying article; this package certifies
the listed finite chamber counts.
