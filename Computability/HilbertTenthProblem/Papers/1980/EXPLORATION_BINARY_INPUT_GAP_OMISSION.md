# The binary input gap cannot be inferred from the other 90-operation equations

Deleting just the equation `b=x+beta` from the established binary
90-operation system gives an **unsound 89-operation system**, with
48 multiplications, 41 additions, 33 positive unknowns and 21 equations.
There is a fixed genuine compiler index for the singleton predicate
`x=2` at which the deletion accepts infinitely many larger inputs.
Every member has a complete positive Pell extension. This is a scoped
refutation of this deletion, not an obstruction to another 89-operation
construction.

The author and two independent complete proof/source reviews and fresh
verification runs pass without findings. The fixed-index counterfamily
and the finite numerical examples have the distinct evidence scopes
described below.

The unchanged system, arithmetic and positive converse are in
[BINARY_PRODUCT_90_PROOF.md](BINARY_PRODUCT_90_PROOF.md),
[BASE_TWO_PELL_90_PROOF.md](BASE_TWO_PELL_90_PROOF.md), and
[round37_1980_binary_product_certificate.py](../verification/round37_1980_binary_product_certificate.py).
No published file is changed.

## 1. The precise deletion and its dependencies

The published register `bx=x+beta` has one consumer: the free equality
`b=bx`. The positive coordinate `beta` occurs nowhere else. Delete that
one addition, that equality, and that coordinate. All other registers,
including `C=x+g`, the positive product bound, the radix threshold and
both Pell exponent blocks are retained verbatim.

This is 90 minus one addition. The checker expands all 21 remaining
source residuals afresh. The published triangular corrections at original
indices 2, 16 and 17 are unchanged, with their exact prerequisite
equations at indices 3 and 15 still present.

The other relevant coding quantities are

    B=H0+1+b, theta=B-2, lambda(B-1)=q^2-1,
    C=x+g, sigma=(e-ell)C^2, ell+sigma+alpha=q,
    S2=ell+eq=V+t*theta, n=q^8,
    S=g+q^2(S2+q^2 sigma),
    T=q^2(1+theta*lambda)+ell(theta*q^4-b),
    r=S(n^2-n)+T(n^2-1).                              (1)

In particular, the new system still enforces `theta=H+b`, where
`H=H0-1`. The earlier counterexample to deleting that threshold equation
is a different construction.

## 2. A fixed genuine singleton index

Apply the published binary coefficient compiler to the predicate
`x=2`. It supplies one fixed triple `(H,V,Tindex)`, one fixed power of
two `L`, and the fixed finite support layout, independently of the
queried input. Use the canonical accepting assignment at `x0=2`.
In that assignment the logical unit `delta` is one. Its representation
has a true non-input physical coordinate of value one; if its group
has more coordinates, the other pieces are zero. Let its permitted
positive weight be `v`. The layout gives `v>=8`.

Choose an arbitrarily large power-of-two radix `B` as in the published
positive necessity argument. All physical coordinates and their
forbidden-bit splits have been fixed before choosing `B`. Put

    h=B^v,  x'=2+h,  g'=g-h.                           (2)

The digit of `g` at this physical coordinate is exactly one. Subtracting
`h` therefore clears one existing bit, with no borrow. The helpers have
positive values at distinct true-coordinate positions, so `g'>0`.
Both `g` and `g'` have zero unit digit. Also

    x'+g'=2+g=C,  x'>B>b.                              (3)

Keep `b,theta,lambda,ell,e,sigma,alpha,q,n,t` and all three fixed index
parameters unchanged. Every retained equation in (1) except its last
two occurrences of `g,r` is consequently unchanged. In particular,
the exact nonlinear product and the original strong bound are preserved:

    (e-ell)(x'+g')^2=sigma,  ell+sigma+alpha=q.

This argument uses an actual compiled predicate, not an arbitrary
admissible-looking polynomial code. Since the fixed predicate contains
only 2, every `x'` in (2) is a false input. The unbounded choices of
`B` give infinitely many distinct false inputs for this same index.

## 3. All masks and pre-Pell bounds survive

The normalized mask has the same three blocks as in the original proof:

    T-1=T1+q^2*T2+q^4*T3,
    T1=q^2-1-b*ell, T2=theta*lambda, T3=theta*ell.     (4)

The three tests are `g&T1=0`, `S2&T2=0` and `sigma&T3=0`, with
the bounded block widths established in the published proof. Equation
(2) only clears one bit of `g`, so its new first test holds. The other
two tests do not change. No coefficient-level claim about the new input
is needed: the loss of the input bound is exactly what prevents that
interpretation.

Define afresh

    S'=S-h,
    r'=S'(n^2-n)+T(n^2-1)
      =r-h(n^2-n).                                    (5)

We retain `0<S'<S<n` and `0<T<n`. Thus

    n^2-1 <= r' < 2n^3.

The independent bounds `n>=64` and `3L<=B<=n` are unchanged. The
combined mask is still `S'&(T-1)=0`; the published packed binary lemma
therefore gives

    n^2 divides binom(2r',r').                         (6)

Both `g'` and `ell` are divisible by the even radix `B`. Equation (1)
then makes `S',T,r'` even. Consequently the required half-parameter
parity is preserved as well. These are exact integer mask statements,
not assumptions that the transported physical assignment has input
`x'` or that its decoded circuit remains valid at `x'`.

## 4. Complete positive Pell witnesses at the changed index

The old Pell coordinates generally do not survive (5). Reconstruct
them at the new index using Section 6 of
[BASE_TWO_PELL_90_PROOF.md](BASE_TWO_PELL_90_PROOF.md).
Although that section starts with canonical coding witnesses, its
construction uses only the following properties of them:

* `B,q,n` are powers of two, `q=B^L`, `n=q^8`, `L>=2`;
* `r'` is even and satisfies the displayed pre-Pell bounds;
* (6), `L<2r'+1`, and the unchanged fixed index `psi_2(L)`.

Every one has just been established independently for (2)--(5).
For clarity, set

    J'=2r'+1, U=2^J', w=U/n^2,
    Y=floor((U+1)^(2r')/U^r'), s=Y/n^2,
    a=Y(U+1), A=a+2, E=UY, P=2UY^2+1,
    c=psi_A(J'), d=chi_A(J'), k=psi_P(r'+1).

The power divisibility and central-binomial identity make `w,s`
positive integers. The exact ratio estimates give

    Y < c/k < Y+3/4,

so `eta=c-kY` and `zeta=k-eta` are positive. The standard formulas for
`tau` and `h` give positive integral values. Since even `r'` gives
`J'=1 mod 4`, the published relaxed and half-parameter construction
provides positive `i,f,o,j,y_aux` with the required two positive signs.
Set `kappa=psi_A(L)`, `mu=chi_A(L)`,
`phi=c-kappa`, and `Delta=(psi_A(L)-psi_2(L))/a`; these are positive
with the indicated integral quotient because `2<=L<J'`.

Finally the same exponent congruences supply positive integral
`gamma,rho`. The inequalities certifying their signs are unchanged:

    d-a*c > c > U,
    mu-(A-B)*kappa > (B-1)*kappa > q.

Their moduli are positive, and the retained growth assumptions hold.
This constructs every remaining supplied Pell coordinate. There is
therefore a complete positive solution of all 21 equations at the false
input `x'`. No old auxiliary coordinate or unproved continuity of Pell
witnesses is being reused.

## 5. Exact regression and its boundary

[explore_binary_input_gap_omission.py](../verification/explore_binary_input_gap_omission.py)
checks the exact deletion, all 21 symbolic residuals and the unchanged
acyclic corrections. Its finite coding examples use

    ell=B^v+B^s, e=ell+B^(s+1), g=B^v+B^s, x0=2,

with `0<v<s`, sufficiently large power-of-two `L`, and a power-of-two
`B` above a fixed numerical threshold. Their fixed congruence parameter
is evaluated at two and remains unchanged across the transport. They
test both choices of the cleared physical bit. The test checks all
positive coding witnesses, the unchanged product and congruence,
every mask block, the complete combined mask, the exact changed `r`,
its actual popcount valuation, parity and every stated numerical
precondition for the positive Pell converse.

These finite codes illustrate the arithmetic transport; they are not
claimed to be the genuine singleton compiler index in Section 2.
That application and its complete Pell extension are mathematical
constructions. The enormous compiler powers and Pell coordinates are
not materialized. The checked finite count and review status are
recorded in the companion receipt.
