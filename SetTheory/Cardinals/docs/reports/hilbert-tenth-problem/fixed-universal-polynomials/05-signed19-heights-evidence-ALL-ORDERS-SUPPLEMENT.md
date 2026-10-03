# Separate supplement: all-orders canonical height and cutoff expansions

3 October 2026. This supplement leaves the frozen proof packet unchanged. Its scope is the same fixed-input/compiler/repunit/prime-scale canonical signed19 family. It refines its height and real cutoff only; it does not improve the rotation discrepancy or establish a second counting coefficient.

## Result

Put d=sqrt(Delta), ell=(1/2)log Delta, epsilon=exp(-alpha p), and

    m=p(epsilon^(-1)-epsilon)/(2d),
    A_p=d(1-1/p), B_p=d log Delta/(alpha p),
    G0(p)=2alpha p+2log p+log(alpha/(2Delta)).

For each fixed integer N>=1 there are explicit coefficients a_n(p), polynomial in 1/p of degree at most n, such that

    loglog y(p)=G0(p)+sum_{n=1}^N a_n(p) exp(-n alpha p)
                         +O(exp(-(N+1)alpha p)).            (1)

All constants may depend on the fixed parameters and N. The coefficient algorithm is

    S_0(C)=2, S_1(C)=-C,
    S_n(C)=-C S_(n-1)(C)+S_(n-2)(C),
    a_n(p)=-[S_n(A_p)+S_n(B_p)]/n.                         (2)

For a height cutoff B, put

    t=alpha^(-1)W(sqrt(2alpha Delta log B)), w=exp(-alpha t).

There are rational functions c_n(t) of t and the fixed constants such that the exact real cutoff obeys, for every fixed N,

    p_B=t+sum_{n=1}^N c_n(t) exp(-n alpha t)
                         +O(exp(-(N+1)alpha t)).            (3)

The c_n(t) remain bounded as t tends to infinity and are analytic in 1/t near zero. An explicit triangular recurrence is given below.

The two height logarithms and the inverse normal-form series described below converge for all sufficiently large p or t. Their sums solve the **normal form**. The exact height and cutoff retain a smaller, beyond-all-orders correction; neither convergent normal-form series is asserted to equal the exact quantity.

## 1. Exact factorization and error scale

The frozen proof established, for the real extension and fixed parameters,

    log y(p)=F(p)+O((m+p)exp(-2alpha m)),
    F(p)=(2m+p-1)(alpha m+ell).

The two factors satisfy the exact identities

    2m+p-1=(p/d)epsilon^(-1)(1+A_p epsilon-epsilon^2),
    alpha m+ell=(alpha p/(2d))epsilon^(-1)
                           (1+B_p epsilon-epsilon^2).

Consequently

    F(p)=[alpha p^2/(2Delta)]epsilon^(-2)
             (1+A_p epsilon-epsilon^2)(1+B_p epsilon-epsilon^2).

Since F(p) is asymptotic to 2alpha m^2 and m>=p for p>=1, division by F followed by log(1+z)=O(z) gives

    loglog y(p)=G0(p)
       +log(1+A_p epsilon-epsilon^2)
       +log(1+B_p epsilon-epsilon^2)+R(p),
    R(p)=O(exp(-2alpha m)/m).                              (4)

Here m is asymptotic to p exp(alpha p)/(2d). Therefore, for every fixed K>0,

    R(p)=o(exp(-K alpha p)).

This is the precise beyond-all-orders remainder. In particular it must not be silently discarded when claiming an exact convergent expression.

## 2. Uniform convergent coefficient expansion

For a real parameter C, set

    r_+(C)=(-C+sqrt(C^2+4))/2,
    r_-(C)=(-C-sqrt(C^2+4))/2.

Then 1+C epsilon-epsilon^2=(1-r_+ epsilon)(1-r_- epsilon), and the power sums S_n(C)=r_+^n+r_-^n satisfy exactly recurrence (2). In the disk |epsilon| max(|r_+|,|r_-|)<1, using logarithm branches that vanish at epsilon=0,

    log(1+C epsilon-epsilon^2)
        =-sum_{n>=1} S_n(C)epsilon^n/n.                   (5)

For p>=1, both A_p and B_p lie in a fixed bounded nonnegative interval. Thus a constant K0>=1 bounds both root moduli uniformly. For |epsilon|<=1/(2K0), the tail after degree N in the sum of the two logarithms is at most

    4 sum_{n>N}(K0|epsilon|)^n/n
        <=[8K0^(N+1)/(N+1)]|epsilon|^(N+1).

The normal-form expansion is therefore absolutely and uniformly convergent for all sufficiently large p. Each S_n is an integer polynomial in C of degree at most n, while A_p and B_p are affine in 1/p. This proves the stated coefficient class and, together with (4), proves (1).

For checks, the first two coefficients are

    a_1=A_p+B_p
        =d[1+(log Delta/alpha-1)/p],
    a_2=-2-(A_p^2+B_p^2)/2.

The first reproduces the frozen proof. The second equals the independently obtained expression

    -2+[Delta log Delta/alpha](p-1)/p^2
       -(Delta/2)[1+(log Delta/alpha-1)/p]^2.

## 3. Uniform analytic inverse normal form

For the Lambert-W cutoff t, put p=t+u. Define

    H_t(u,w)=2alpha u+2log(1+u/t)
      +log(1+A_(t+u) w exp(-alpha u)-w^2 exp(-2alpha u))
      +log(1+B_(t+u) w exp(-alpha u)-w^2 exp(-2alpha u)).   (6)

The normal-form cutoff is the small root H_t(u,w)=0. To justify uniformity as t tends to infinity, introduce z=1/t and replace

    1/(t+u)=z/(1+zu),
    A_(t+u)=d[1-z/(1+zu)],
    B_(t+u)=[d log Delta/alpha]z/(1+zu).

Equation (6) becomes a jointly analytic function H(u,z,w) in a complex neighborhood of (0,0,0), with all logarithms taken near 1. It satisfies H(0,z,0)=0 and

    partial_u H(0,z,0)=2alpha+2z,
    partial_u H(0,0,0)=2alpha !=0.

The analytic implicit-function theorem supplies a unique analytic small root U(z,w) in a fixed neighborhood of (0,0). Since U(z,0)=0, it has a power series

    U(z,w)=sum_{n>=1} c_n(1/z) w^n.

On a smaller fixed polydisk this series converges uniformly, and its remainder after degree N is O_N(|w|^(N+1)), uniformly in z. The notation c_n(1/z) has no singularity at z=0: it denotes an analytic coefficient function of z there.

For a direct algorithm, let u_<n=sum_{j=1}^{n-1}c_j(t)w^j. Then

    c_n(t)=-[w^n]H_t(u_<n,w)/(2alpha+2/t).                 (7)

Indeed, inserting c_n(t)w^n adds exactly (2alpha+2/t)c_n(t) to the coefficient of degree n; every other occurrence contributes only to higher degrees. Expanding rational functions, exponentials and logarithms at zero shows inductively that c_n is rational in t and the fixed constants. Equivalently it is rational in z=1/t and analytic at z=0. In particular

    c_1(t)=-d[1+(log Delta/alpha-1)/t]/(2alpha+2/t),

which reproduces the previously audited first inverse correction.

## 4. Transfer from the normal form to the exact cutoff

The frozen inversion already gives u_exact=p_B-t=O(w). Applying (4) at the actual cutoff gives

    H_t(u_exact,w)=-R(t+u_exact).

On the same small real neighborhood, partial_u H_t is bounded below by alpha>0 after taking t sufficiently large. The mean value theorem therefore yields

    |u_exact-U(1/t,w)| <= alpha^(-1)|R(t+u_exact)|.

Since u_exact=O(w), m(t+u_exact)/m(t) tends to 1. In particular it is at least 1/2 eventually, so the last error is

    O(exp(-alpha m(t))/m(t))=o(w^K)

for every fixed K. Combining this with the uniform analytic-series truncation proves (3). This establishes actual fixed-order asymptotic inversion, not merely a formal recurrence. It does not identify the convergent normal-form series with the exact cutoff.

## Boundaries

This supplement does not improve any discrepancy estimate. Smooth all-orders height and cutoff expansions still coexist with the unbounded exact rotation-discrepancy term in the count. In particular they do not establish a triple-log counting coefficient or an O(1) counting remainder.

No upstream code was executed, no repository was edited, and no numerical giant witness was materialized. Frozen parent proof: SHA256 ff9d116c90b058be082c2c9d6ee051ccf537d80821c14d10b28aec9a96d5a533.
