# The mixed BR quadratic derivatives of the quartic truncation

## Status and target

The full exact 89-profile coefficient batch has passed: 4,539 basis-cone
polynomials and 43,344,919 nonnegative coefficient entries. The mathematical
reduction and all ten R-block determinants have an independent review. A fresh
full coefficient reconstruction remains pending; the entire quartic theorem
also needs its separate RR and BB cases.
The unit-left scope is retained. All right activities remain separate variables.
Let B0 be the forced core column and let R0 have nonempty A-neighborhood U.
The quadratic derivative of

F4=15s^4+10p1 s^3+6p2 s^2+3p3 s+p4

in B0,R0 has pivot 12E, cross entries 3a_l, and off-diagonal entries b_lm,
where E=a_{B0,R0}, a_l=a_{B0,R0,l}, b_lm=a_{B0,R0,l,m}.
Its Schur matrix is Q=3aa^T/(4E)-B. The task is Q>=0.

Throughout, h(C,D) counts two-element A supports matching C,D, and
chi(C,D,E) is the Boolean three-row matching indicator. Counts are endpoint
supports, never matching allocations. The core masks are J,C1,C2.
Write n,m_i,t_i,p_i for the same exterior-left population statistics as in
the cubic reduction, so p_i=n m_i-t_i(t_i+1)/2. Genuine rank six gives a
three-row L basis and n>=1.

## 1. Exact coefficients

For an additional exterior column of type S,

E=n|U|+h(J,U),
r_S=n h(U,S)+chi(J,U,S),
x_i=p_i|U|+n h(C_i,U)+m_i h(J,U)
    -t_i[h(J,U)+h(C_i,U)-h(J union C_i,U)]+chi(J,C_i,U),
z_i(S)=p_i h(U,S)+n chi(C_i,U,S)+m_i chi(J,U,S)
    -t_i[chi(J,U,S)+chi(C_i,U,S)-chi(J union C_i,U,S)].

These are E, a_R, a_Bi and b_Bi,R, respectively. The R-to-R pair coefficient
is n chi(U,S,T). This last expression uses all three A rows for the three R
columns and one L neighbor for B0. For z_i(S), either two selected L rows match
the two B columns, or a single L row leaves three A rows. In the latter case
the Boolean union of the two eligible core-column allocations gives exactly
the displayed overlap subtraction.

The remaining coefficient is q_BR=a_{B0,B1,B2,R0}. It has a compact direct
support formula. Let q_L count L bases of B. For an unordered L-row pair let
T be the set of B columns that may be left unmatched by that pair; let P_T
count pairs with this exact nonempty profile T. Put C_T=union_{i in T} C_i,
where C_0=J. Let D be the set of indices i for which chi(U,C_j,C_k)=1, with
{j,k} the other two core columns. Then

q_BR=|U|q_L + sum_{T nonempty} P_T h(U,C_T)
                   + sum_{S: S intersects D} N_S.

This partitions the selected A set into sizes one, two and three. In the
middle case, the two A rows must match U and one core column that the chosen
L pair can leave unmatched. Its exact Boolean union support is C_T.
The last term selects all three A rows and one L row; the latter must use a
core column in D. The generator also reconstructs q_BR by direct Hall tests
on selected labeled A rows and L class multisets, rather than using this formula.

## 2. Exact reduction to three or four R classes

The preceding formulas use only h(U,C), h(U,C union D), and chi(U,C,D).
After permuting A, take U=1,3,7. The following reduced core and R categories
preserve all of these functions:

* U=1: discard bit1. The categories are 0,2,4,6. The zero R category is absent
  from the conditional marginal. Retain R representatives 2,4,6.
* U=3: replace a nonempty intersection with {1,2} by bit1, retaining bit4.
  The categories are 0,1,4,5. Retain R representatives 1,4,5.
* U=7: retain the three singleton masks and replace every mask of size at least
  two by a common generic category, represented by 3. Categories are 0,1,2,4,3.
  Retain R representatives 1,2,4,3.

Here the generic category is a category of distinct columns, not a parallel
class: chi(7,3,3)=1. Explicitly h(7,C) is 0,2,3 for zero, singleton, generic;
chi(7,C,D) is zero exactly when one argument is zero or both are the same
singleton. This proves the claimed size-three-root collapse, including unions.
For U=3, h has values 0,1,2,3 in the displayed category order and chi is the
ordinary rank-two matching indicator. For U=1 the corresponding h values are
0,1,1,2 and the same rank-two indicator applies.

Grouping arbitrary signed test coordinates by these R categories gives the
reduced class-limit matrix plus the exact nonnegative correction

n sum_S chi(U,S,S) sum_{r in category S} z_r^2.

Thus the smaller matrix suffices for every finite exterior-right population.
Its R block is

Q_R(S,T)=3r_S r_T/(4E)-n chi(U,S,T),

its B-to-R columns are 3x_i r/(4E)-z_i, and its two-by-two B block has diagonal
3x_i^2/(4E) and off-diagonal 3x_1x_2/(4E)-q_BR.

## 3. Positive principal blocks and the remaining determinant

Delete the other unforced B vertex. The graph has a displayed 3+2 cover.
The previously proved retained-variable two-vertex-cover theorem, after
transposition, gives the full original-right marginal homogenized to degree
five. Differentiate in B0 and R0, then in s. The quadratic is

3E s^2+2s sum_l a_l z_l+sum_{l<m} b_lm z_l z_m,

so its Schur coefficient is 2/(3E). The BR target has 3/(4E), adding the
positive rank-one matrix aa^T/(12E). Hence every principal matrix containing
R and just one B_i is positive semidefinite. Arbitrarily many twins with test
coordinates divided by their population give the same class-limit conclusion.
This argument avoids any unsupported large-neighborhood root compression.

For A_R=4E Q_R the retained determinants are:

U=1,J=0: 32 n^6.
U=1,J=2: 32 n^3(n+1)^3.
U=1,J=6: 16 n^2(n+2)^2(2n^2+4n+3).
U=3,J=0: 256 n^6.
U=3,J=1: 32 n^3(2n+1)^3.
U=3,J=4: 256 n^3(n+1)^3.
U=3,J=5: 16 n^2(2n+3)^2(4n^2+6n+3).
U=7,J=0: 10368 n^8.
U=7,J=1: 128 n^4(3n+2)^4.
U=7,J=3: 5184 n^3(n+1)^3(2n^2+2n+1).

All are positive for n>=1. Together with principal-block positivity this
makes Q_R positive definite. Both diagonal Schur entries are nonnegative.
Only the determinant of the remaining two-by-two Schur matrix is unresolved.

## 4. Finite certificate plan

For U=1, permute the two unforced A coordinates and swap B1,B2; this leaves
24 reduced rooted cores. For U=3 the two reduced A types have different weights,
so only swap B1,B2; there are 40 profiles. For U=7 permute the three singleton
categories while fixing the generic category, and swap B1,B2; there are 25.
Thus there are exactly 89 reduced profiles, including empty core columns.

For each, the exact generator clears a positive common univariate denominator
in n, computes the two-by-two determinant, and clears its rational scalar
denominator. It then translates the seven populations by each of the 51
Hall-feasible exterior-left basis multisets and checks every ordinary
coefficient. This covers all genuine integer populations without a bound on
population size. Records include exact coefficient-list hashes, counts,
minimum coefficients, denominator, positive scalar and total degree.

The completed batch has 11,820,833 coefficient entries for U=1, 19,282,707
for U=3, and 12,241,379 for U=7. Its cleared polynomial degrees are 8,10,12.
All 952 category identities and 1,396 direct endpoint-polynomial checks pass.
After the pending fresh full coefficient reconstruction, these identities
prove every BR quadratic derivative of F4 has at most one positive Hessian
eigenvalue. They do not by themselves settle RR, BB or scalar rank-six ULC.
