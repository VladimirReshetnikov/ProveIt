# Independent review of the tower example

**Final disposition:** the scope correction below has been applied throughout
the report and Lean targets. The finished report also gives a full rational
bisection construction of the upper branch, with a standalone exact reference
script and recorded checks. The text below preserves the review and its
calculations as supporting evidence.

All proposed numerical constants and indices are valid, with synchronous
rounded updates. One essential scope correction is needed: uniqueness holds
inside the certified unit box, not among arbitrary bounded solutions of the
nonlinear equations. A second bounded branch exists near 7.

## 1. Setting and contraction

For n >= 1, take X_n = ([0,1] intersect Q)^n and

    d_n(x,y) = max_{0 <= i < n} 2^(-i) |x_i-y_i|.

Let P_n : X_(n+1) -> X_n delete the last coordinate. Define

    a_i = 1 / (4(i+1)),
    F_(n,i)(x) = a_i + x_i^2/8 + x_(i+1)/8,

with the last missing coordinate x_n = 0. All projections are nonexpansive,
and prefix projections compose exactly.

Because a_i <= 1/4 and x_i,x_(i+1) <= 1, F_n(x)_i lies in [0,1/2].
For two input vectors in X_n,

    |F_n(x)_i - F_n(y)_i|
      <= |x_i-y_i|/4 + |x_(i+1)-y_(i+1)|/8.

Multiplication by 2^(-i) gives coefficients 1/4 and 1/4 against d_n.
Thus q = 1/2 is valid. The final coordinate has only the diagonal term.

## 2. Adjacent commutation defect

The vectors P_n F_(n+1)(x) and F_n(P_n x) agree in coordinates i < n-1.
Their difference in coordinate n-1 is x_n/8. Consequently

    eta_n <= 2^(-(n-1))/8 = 2^(-n-2).

This is uniform on the whole X_(n+1).

## 3. Rounded iteration residual

Use t = n+4 synchronous iterations at dyadic precision p = n+8, starting
from 0. Each full vector step evaluates F_n on the previous vector and rounds
each coordinate down to a multiple of 2^(-p). Do not silently change this to
an in-place coordinate update: that would be a different map.

The dyadic floor stays in [0,1/2] and has d_n error at most epsilon = 2^(-p).
Let z_t be the exact rational iterate and y_t its rounded counterpart.
Induction on delta_t gives

    delta_(t+1) <= delta_t/2 + epsilon,
    delta_0 = 0,
    delta_t <= 2 epsilon.

Since d_n(0,F_n(0)) = a_0 = 1/4, the exact residual at step t is at most
2^(-t-2). Therefore the rounded residual is bounded by

    r_n <= (1+q) delta_t + 2^(-t-2)
         <= 3*2^(-p) + 2^(-t-2)
          = 7*2^(-n-8)
         <= 2^(-n-4).

The factor 3, exponent t+2, and factor 7 are all correct. Evaluation of the
rational coefficient a_i and of the dyadic floor uses bounded integer
arithmetic. A common denominator must be carried explicitly in an iPRA
implementation.

## 4. Adjacent comparison and telescope

Set e_n = d_n(y_n, P_n y_(n+1)). Inserting the two finite fixed-point residuals
and the commutation defect gives

    e_n <= r_n + q e_n + eta_n + r_(n+1),
    e_n <= 2(r_n + r_(n+1) + eta_n)
        <= (11/16) 2^(-n)
         < 2^(-n).

The coefficient is exactly

    2(1/16 + 1/32 + 1/4) = 11/16.

Using the sharper r_n instead gives 149/256, but the proposed 11/16 is
simpler and sufficient.

For m >= n, nonexpansiveness and the finite triangle inequality give

    d_n(y_n, P_(n,m) y_m)
      <= sum_{j=n}^{m-1} e_j
      <= sum_{j=n}^{m-1} 2^(-j)
      <= 2^(1-n).

No infinite sum is required: the finite geometric identity suffices. The
case m=n is zero and presents no problem.

## 5. Coordinate name and same-precision equation

Define

    Q(i,k) = y_(i+k+3)[i].

This index is valid for every i,k >= 0. If k <= l and n=i+k+3, m=i+l+3,

    |Q(i,k)-Q(i,l)|
      <= 2^i d_n(y_n,P_(n,m)y_m)
      <= 2^(-k-2).

Thus the asserted modulus with min(k,l) is correct.

At a fixed i,k, let n=i+k+3. Then i+1<n, so the coordinate equation at
level n uses a genuine coordinate y_n[i+1], not the zero boundary. The next
coordinate name at the same precision is Q(i+1,k)=y_(n+1)[i+1]. Hence

    |Q(i,k)-a_i-Q(i,k)^2/8-Q(i+1,k)/8|
      <= 2^i r_n + (1/8) 2^(i+1) e_n
      <= 2^(i-n-4) + 2^(i-n-2)
       = 5*2^(i-n-4)
       = 5*2^(-k-7)
       < 2^(-k-4).

This is valid for every k including k=0. The use of n+1 for the second name
is exactly the reason the adjacent consistency term appears.

## 6. Finite uniqueness inside the unit box: tower proof

Define the admissible class precisely. A candidate name U(i,p) must be a
rational array, with 0 <= U(i,p) <= 1, a stated regular Cauchy modulus in p,
and the same-precision equation residual

    |U(i,p)-a_i-U(i,p)^2/8-U(i+1,p)/8| <= 2^(-p).

Let U and V be two such candidates. The proof below only needs a finite
rectangle of their data; regularity is used later to interpret the conclusion
as equality of the represented coordinates.

Fix i,k. Choose

    N = i+k+3,       p = i+k+5.

Take the first N coordinates of U(-,p) and V(-,p), denoted u and v. Their
finite-map residuals satisfy

    d_N(u,F_N(u)) <= 2^(-p) + 2^(-N-2),
    d_N(v,F_N(v)) <= 2^(-p) + 2^(-N-2).

Indeed, only the last coordinate has an additional boundary term, at most
2^(-N-2); every coordinate's given equation residual contributes at most
2^(-p). Applying q=1/2 contraction and canceling the recurrent half yields

    d_N(u,v) <= 4*2^(-p) + 2^(-N).

Thus

    |U(i,p)-V(i,p)|
      <= 2^(i+2-p) + 2^(i-N)
       = 2^(-k-3) + 2^(-k-3)
       = 2^(-k-2).

This is a fully finite uniqueness certificate. It queries coordinates only
through N and equations only through N-1. All exponents and prefix bounds
are primitive recursive; the final inference is rational arithmetic and the
already established contraction inequality. Together with regularity of
each name, it proves equality of the represented coordinates without using
an infinite supremum or an infinite-space fixed-point theorem.

## 7. Alternative finite uniqueness by one-dimensional elimination

The special triangular form supplies a second proof with a precision shift
independent of the coordinate i. Fix p and put

    E_j = |U(j,p)-V(j,p)|,      epsilon = 2^(-p).

Because the candidates lie in [0,1], |U_j^2-V_j^2| <= 2 E_j. Subtracting the
two residual equations gives

    6 E_j <= E_(j+1) + 16 epsilon.

After m finite steps,

    6^m E_i <= E_(i+m) + 16 epsilon sum_{s<m} 6^s,
    E_i <= 6^(-m) + (16/5) epsilon (1-6^(-m))
         <= 6^(-m) + (16/5) epsilon.

Here E_(i+m) <= 1 uses the common unit box. Taking p=m=k+3 gives

    |U(i,k+3)-V(i,k+3)| <= (21/40)2^(-k) < 2^(-k).

Only a finite span of m equations is used. The induction can be performed
on the cleared inequality 6^m E_i <= E_(i+m)+16 epsilon sum_{s<m}6^s,
with rational numerators and denominators encoded as natural data.

## 8. Essential scope correction: arbitrary bounded uniqueness is false

Do not state that the equations have a unique solution among *all bounded*
regular names. Rewrite the equation as

    x_i = 4 +/- sqrt(16 - x_(i+1) - 2/(i+1)).

The plus branch

    H_i(z) = 4 + sqrt(16-z-2/(i+1))

maps [6,8] into [4+sqrt(6),4+sqrt(10)], a subset of [6,8]. Moreover,

    |H_i(z)-H_i(w)|
      = |z-w| / (sqrt(16-z-2/(i+1)) + sqrt(16-w-2/(i+1)))
      <= |z-w|/4,

since each square root is at least 2. This bound is uniform in i.

For a finite terminal index L set z_L=7 and compute backwards
z_j=H_j(z_(j+1)) for j=L-1,...,i. Every value stays in [6,8]. Changing the
terminal value inside [6,8] changes coordinate i by at most
2*4^(-(L-i)). Increasing L therefore gives an explicit Cauchy family and a
bounded solution on the upper branch. Rational bisection for each square
root supplies primitive-recursive regular names with explicit precision
budgets. This branch is separated from the constructed unit-box solution.

The correct uniqueness statement is consequently:

    The construction yields the unique represented solution in the countable
    unit cube (all coordinates in [0,1]), with the stated regular-name
    interpretation.

This example reinforces the framework's requirement to retain the certified
region as part of the contract. A residual equation alone does not record
which nonlinear branch is intended.
