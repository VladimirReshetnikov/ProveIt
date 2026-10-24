# Signed-frame elimination for simultaneous positive powers

## Scope and result

For every fixed r >= 1, the simultaneous relations m_i = n_i^k_i, on
inputs n_i,k_i >= 1 and m_i >= 0, have an explicitly displayed ordinary
polynomial representation with **4r+5 auxiliary natural variables** and
degree at most **12r+8**. No power graph, divisibility predicate, bounded
quantifier, or uncounted auxiliary remains in that polynomial.

For r=1 this is **nine auxiliaries and degree 20**, with four squared
residuals. For r=2 it is thirteen auxiliaries and degree 32. These degrees
are also attained when all input and auxiliary ports are independent.
The positive-base/exponent domain is essential; no zero-input claim is made.

The common Pell scale and common auxiliary index certificate are inherited
from the project's synchronized construction. The new step is to eliminate
the common Pell base as a potentially signed polynomial, prove its entire
negative branch harmless, and orient/eliminate all local X,S,R coordinates
and power-modulus slacks. We make no literature-wide priority claim.

## 1. Literal polynomial

Inputs are n_i,k_i,m_i (1 <= i <= r). Quantify only the naturals

    z, U, v, q, b, and y_i, h_i, s_i, t_i (1 <= i <= r).

Define the following abbreviations, each an ordinary integer polynomial:

    W = 2 + sum_i (n_i+k_i+m_i),
    Y_i = k_i+y_i,
    D = product_i Y_i,
    V = D^2(v+1),
    B = 1+4D(q+1),
    A = B-Ub,
    T_i = 2A n_i-n_i^2-1,
    X_i = Y_i(A-n_i)+m_i+T_i h_i,
    S_i = X_i+U s_i,
    R_i = k_i+4Y_i t_i.

In particular A, T_i and X_i are not new variables and are not assumed
nonnegative before proof. Put N(a,x,y)=x^2-(a^2-1)y^2-1 and set

    E_r = [A^2-W^3(W+2)(z+1)^2-1]^2
          + N(A,U,V)^2
          + sum_i [N(A,X_i,Y_i)^2+N(B,S_i,R_i)^2].             (1)

All displayed products have the fixed finite length r. The only exponents
in (1) are the fixed numerals 2 and 3. Its auxiliary count is exactly 4r+5.

**Theorem.** For the stated input domain, E_r=0 has a natural solution
in its 4r+5 auxiliary variables if and only if every m_i=n_i^k_i.

## 2. The negative-base lemma

This is the step which licenses deleting the old natural A coordinate.

Suppose a tuple makes (1) zero. Every residual is zero. Since W>=2 and
z+1>=1, the frame equation gives |A|>W^2. Therefore A is nonzero.
Also Y_i>=k_i>=1 and n_i,k_i,m_i<=W.

Assume A=-alpha<0. Then alpha>W^2>=W. Write
tau_i=2alpha n_i+n_i^2+1>m_i. The definition of X_i is

    X_i=-(alpha+n_i)Y_i+m_i-tau_i h_i<0.

Let x_i=-X_i>0. Its norm equation gives

    x_i^2=(alpha^2-1)Y_i^2+1 <= alpha^2 Y_i^2,

so x_i<=alpha Y_i. But its defining identity is

    x_i=(alpha+n_i)Y_i-m_i+tau_i h_i.

Consequently n_iY_i+tau_i h_i<=m_i, and hence Y_i<=m_i<=W<alpha.
If Y_i>1, then x_i<alpha Y_i and

    (alpha Y_i-x_i)(alpha Y_i+x_i)=Y_i^2-1.

Both factors are positive integers, and the second exceeds alpha Y_i.
This implies Y_i^2-1>alpha Y_i, contradicting Y_i<alpha. Thus Y_i=1,
k_i=1, and x_i=alpha. The defining identity reduces to
m_i=n_i+tau_i h_i. Because tau_i>m_i, h_i=0 and m_i=n_i=n_i^k_i.

This proves soundness of the complete negative-A branch without using
the index criterion, without changing a sign in a congruence, and without
an extra sign guard. The branch actually exists on some k_i=1 inputs;
it is not silently discarded. If any k_i>=2, the branch is impossible.

## 3. Positive-base soundness

Now assume A>0, so A>W^2, A>=2, and A>n_i. The elementary monotonicity
of 2An-n^2-1 for 1<=n<A gives

    T_i>=2A-2>W>=m_i.

Thus X_i,Y_i,U,V,B,S_i,R_i are nonnegative and Y_i,V are positive;
indeed U>=1 follows from its norm, and B>=5. The definitions give

    Y_i^2 divides V,  B=1 mod 4Y_i,  B=A mod U,
    S_i=X_i mod U,    R_i=k_i mod 4Y_i,  k_i<=Y_i.

Together with the three norms these are exactly the standard
Matiyasevich Pell-index criterion. It identifies

    X_i=chi_A(k_i), Y_i=psi_A(k_i).

Here chi_a(j)+psi_a(j)sqrt(a^2-1)=(a+sqrt(a^2-1))^j. The exact criterion
used is the one exposed by Pell.matiyasevic and the repository's
PellRepresentation.criterion_iff_pell, including its signed-index branch;
we do not replace it by an unsigned informal version.

The frame is the Pell equation at base W+1 with second coordinate
W(z+1). Classification of its nonnegative solutions gives

    A=chi_(W+1)(j), W(z+1)=psi_(W+1)(j), j>0.

Modulo W the Pell recurrence gives chi_(W+1)(j)=1 and
psi_(W+1)(j)=j. Thus W divides j and j>=W. Hence

    A>=(W+1)^j>W^W>=n_i^k_i,
    T_i>=2A-2>n_i^k_i.

For H_j=chi_A(j)-(A-n_i)psi_A(j), the exact recurrence is

    H_0=1, H_(j+1)=n_i H_j+T_i psi_A(j).

It implies H_(k_i)=n_i^k_i mod T_i. The definition of X_i asserts
H_(k_i)=m_i+T_i h_i. Both m_i and n_i^k_i lie in [0,T_i), so they
are equal. This proves positive-branch soundness.

## 4. Simultaneous completeness and every witness

Assume all m_i=n_i^k_i and first calculate W from these inputs. Choose

    A=chi_(W+1)(W), Z=psi_(W+1)(W)/W, z=Z-1.

The recurrence modulo W makes Z an integer, and Z>=1. Set
X_i=chi_A(k_i), Y_i=psi_A(k_i), D=product_i Y_i, y_i=Y_i-k_i.
These y_i are natural. Define

    h_i=sum_(j=0)^(k_i-1) n_i^(k_i-1-j) psi_A(j).

The recurrence in Section 3 proves the required definition of X_i, with
h_i natural. These powers and sums are used only to construct witnesses
in the proof; they are not symbols in polynomial (1).

To construct one shared U,V, work in the finite ring

    (Z/(4D^2)Z)[s]/(s^2-(A^2-1)).

The element A+s is a unit with inverse A-s. Its positive order gives an
index l>=1 such that U=chi_A(l)=1 mod 4D^2 and V=psi_A(l)=0 mod 4D^2.
Thus U is odd, V>0 and D^2 divides V. Put v=V/D^2-1>=0. The norm gives
gcd(U,V)=1, hence gcd(U,4D)=1. CRT supplies B congruent to A modulo U
and to 1 modulo 4D. Add enough multiples of 4DU to make B>A and B>1.
Then set

    b=(B-A)/U, q=(B-1)/(4D)-1,
    S_i=chi_B(k_i), R_i=psi_B(k_i),
    s_i=(S_i-X_i)/U, t_i=(R_i-k_i)/(4Y_i).

All are natural. For q use B>1 and 4D|(B-1). Polynomial dependence of
Pell coordinates on their base gives S_i=X_i mod U and
R_i=k_i mod 4Y_i; monotonicity in B>A gives S_i>=X_i and R_i>=k_i.
This proves integrality and nonnegativity of s_i,t_i. Every residual
vanishes, and A=B-Ub is exactly the originally selected positive A.
There is no circular witness choice and no assumption of consistency.

## 5. Exact ordinary degrees and witnesses

With the 3r input ports treated as independent variables, the degree
bounds are

    deg W=deg Y_i=1, deg D=r, deg V=2r+1,
    deg B,deg A<=r+1, deg T_i<=r+2,
    deg X_i,deg S_i<=r+3, deg R_i<=2.

The auxiliary norm has degree 6r+4; the two local norms have degree at
most 2r+6; the frame degree is at most max(2r+2,6). Thus E_r has degree
at most 12r+8. This is attained: the highest component of N(A,U,V)
contains -16 q^2 v^2 (product_i Y_i)^6. Its square is nonzero. For
r>=1 the auxiliary norm's degree exceeds every other residual's bound,
so it cannot be canceled in the sum of squares. In particular r=1
gives degree20, and r=2 gives degree32.

For comparison, retaining an independent natural A and adding the
residual B-A-Ub gives 4r+6 auxiliaries and degree at most
max(8r+8,4r+12,12). For r=2 this is fourteen auxiliaries and degree24.
The main result trades one coordinate for degree, rather than claiming
dominance in every measure.

## 6. Fully ordinary tiling composition, and its boundary

The prior packed strict-boundary tiling construction has eight natural
coordinates Q,g,Z,v0,q0,u,t,j and two positive power requests

    e=2^n, W0=(d+1)^A0,

plus one ordinary synchronization residual S=0. The reused input circuit
and unbounded proof are pinned in prior/. Their positivity argument gives
A0>=10, Y>=1, n=(A0+1)Y>=1, d>=1, e>=0, W0>=0 on every natural
assignment, before either power graph is interpreted. Therefore substitute
these exact two requests into (1), using fresh auxiliary names, and add S^2.

This is an **ordinary polynomial in 21 natural variables**, not a
special-function interface. Its zeros correspond exactly to finite
strict-boundary rectangular tilings by the supplied fixed tile set.
The retained-A variant is an ordinary polynomial in 22 natural variables.

All port substitution costs are included. If there are k tiles, the prior
literal circuit bounds give deg A0,deg Y<=48k, deg n<=96k,
deg d<=96k+1, deg e<=96k+2, deg W0<=96k+3 and deg S<=192k+3.
For the signed-frame composition the auxiliary norm has degree at most
864k+4; every other residual has lower degree for k>=1. Hence the final
degree is at most **1728k+8**, not32. For retained A the corresponding
bound is **1152k+8**, not24. The emitted DAG independently recomputes
all actual syntactic upper bounds, which can be smaller.

This packet materializes the complete four-corner fixture, and supplies
the compiler for any explicit nonempty fixed tile set. It does **not**
claim a new calibrated Con(ZFC) endpoint: a strict-boundary tile set
equivalent to an actual ZFC proof checker still has to be supplied and
proved correct. In particular, the repository's raw 943-tile list includes
an all-zero tile, so feeding it unchanged into a generic strict-rectangle
existence test would admit a trivial one-cell rectangle. We do not make
that invalid source substitution. The nine-auxiliary power graph is a
complete reusable ordinary result independent of this source obligation.

## 7. Verification status

The supplied ordinary-polynomial DAG contains only integer constants,
variables, addition, multiplication and fixed nonnegative powers. Literal
SOS residuals, all coordinates, topology and degree bounds are checked.
An independent evaluator tests its values modulo several primes on random
assignments, including signed eliminated bases. Separate constructive
fixtures test shared CRT indices, full true k=1 power witnesses, genuine
negative-A witnesses, and the negative-base obstruction. Deliberate DAG
and witness corruptions must be rejected. These finite tests supplement
the universal proof; they do not certify it in Lean or prove consistency.

All arguments use finite integer arithmetic, induction, Pell theory and
finite-ring/CRT constructions formalizable in ZFC. No encoded internal
ZFC proof object or new proof-assistant verification is asserted.
