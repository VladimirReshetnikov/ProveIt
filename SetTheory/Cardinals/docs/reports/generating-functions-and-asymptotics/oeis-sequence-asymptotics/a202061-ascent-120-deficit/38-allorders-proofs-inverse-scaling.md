# Inverse-sector scaling check

Let lambda=log mu>0, q0=log lambda, T=log p and S=log T. To avoid collision with the peak variable q=3k/L in proof.md, this note writes q0 for log lambda.

Suppose the deficit has, at each fixed order J, the established expansion

    D_n=C n^{1/3}(log n)^{2/3}
          sum_{j=0}^J P_j(kappa+(7/3)log log n)/(log n)^j
          +o(n^{1/3}(log n)^{2/3-J}).

For its smooth finite truncation d_J, the inverse correction has expansion

    lambda^{-1} d_J(T/lambda)
      =C lambda^{-4/3} T^{1/3} S^{2/3}
          sum_{j=0}^J P_j(kappa_inv+(7/3)log S)/S^j
          +o(T^{1/3}S^{2/3-J}),

where

    kappa_inv=kappa-(2/3)log lambda.

The power lambda^{-4/3} is important: lambda^{-1} from inversion and lambda^{-1/3} from the n^{1/3} factor both occur.

## Direct check through the requested fourth scale

Put B=kappa+(7/3)log S. Then

    (1-q0/S)^{2/3}
       [1+(kappa+(7/3)log(S-q0))/(S-q0)
         +P2(kappa+(7/3)log(S-q0))/(S-q0)^2]

has coefficient at S^{-1} equal to B-2q0/3, and coefficient at S^{-2} equal to

    P2(B)+(q0/3)B-7q0/3-q0^2/9
       =P2(B-2q0/3).

Thus the proposed fourth-scale shift is exactly correct. verify_inverse_scaling.py checks the identity by independent series expansion.

## Why the shift persists to every fixed order

The logarithmic duration equation in the peak parameter k is

    L=3k-(7/2)log k-(3/2)kappa-(7/2)log 3-3log 2
           +3log Srow(1/k)+log J_-(1/k),

where Srow denotes the Watson series, not log T. The parameter pair (L,kappa) therefore enters the equation determining k only through L+(3/2)kappa. Replacing L by S-q0 is exactly equivalent to replacing kappa by kappa-2q0/3.

Furthermore, elimination of the peak height in the action formula gives

    A(n)/(C n^{1/3})=(3k)^{2/3}
                      J_-(1/k)^{-1/3}[J_-(1/k)+2J_+(1/k)]/3.

The right side has no further L or kappa dependence. This proves the shift as a formal identity at every finite order, and the uniform remainders in proof.md make it an asymptotic identity at every fixed order.

Equivalently the polynomials obey

    P_{j+1}'(B)=(1-3j/2)P_j(B)+(7/2)P_j'(B).

Indeed, f(L,kappa)=sum L^{2/3-j}P_j(kappa+(7/3)log L) obeys f_L=(2/3)f_kappa because it depends only on L+(3/2)kappa. Equating powers proves the recurrence. It determines P_{j+1} only up to an additive constant, so beta-moment information remains necessary.

## Remainder and notation warning

The estimate D'(n)D(n)=O(n^{-1/3}(log n)^{4/3})=o(1) is valid for a fixed smooth action approximant, or for any fixed finite smooth truncation of its expansion. If D_n means the exact discrete sequence deficit, a derivative is not defined without an additional interpolation argument.

In particular, an all-finite-orders action reduction does not by itself imply an o(1) approximation to the inverse index. What follows is the inverse asymptotic expansion at each retained scale T^{1/3}S^{2/3-J}; the original reduction error must be propagated at that scale. Any O(1) index rounding is negligible at every such fixed scale. A claim of an o(1) absolute inverse error would require stronger information than this hierarchy.

## Uniform covariance with a quantitative finite-order remainder

For every fixed J and Q, and kappa in a fixed compact interval, define

    f_J(L,kappa)=L^{2/3} sum_{j=0}^J
                 P_j(kappa+(7/3)log L)/L^j.

Then, uniformly for |sigma|<=Q,

    f_J(L-sigma,kappa)-f_J(L,kappa-2sigma/3)
       =O_J,Q(L^{2/3-J-1}(1+log L)^{m_J})                    (U)

for some finite m_J, as L tends to infinity.

To justify the uniform error, take the peak-k and beta-integral expansions one order beyond the required order, always keeping enough Watson terms. All estimates of proof.md are uniform when c varies in a compact interval: a single fixed b can be chosen, the inverse derivative remains bounded away from zero, and the central bounds |log z|<=C0 log L have constants uniform in those parameters. Bounded L shifts also keep every large argument within fixed ratios of L. The exact dependence of the finite-model peak equation on L+(3/2)kappa gives covariance before re-expansion, while all omitted terms have the displayed finite-order bound. Alternatively, directly Taylor-expand the two finite polynomial-log expressions in sigma/L: the formal peak equation proves equality of every coefficient through order J, and finite Taylor's theorem gives (U), uniformly on |sigma|<=Q. There are only finitely many polynomial-log terms, so this is an ordinary uniform Taylor remainder, not a claim about a convergent infinite series.

## Full monotone inverse corollary

Assume a_n>0 is nondecreasing and, for every fixed J>=0,

    log a_n=lambda n-d_J(n)+r_J(n),                           (H_J)

where lambda>0,

    d_J(x)=C x^{1/3} f_J(log x,kappa),
    r_J(n)=o(R_J(n)),
    R_J(x)=x^{1/3}(log x)^{2/3-J}.

For A202061, monotonicity is supplied by appending a copy of the last letter to the avoiding ascent sequence; the coefficient/action theorem supplies (H_J). Define

    N(p)=min{n:a_n>=p},
    T=log p,  S=log T,  kappa_inv=kappa-(2/3)log lambda.

Then for every fixed J,

    N(p)=T/lambda
          +(C/lambda^{4/3}) T^{1/3} S^{2/3}
             sum_{j=0}^J P_j(kappa_inv+(7/3)log S)/S^j
          +o(T^{1/3}S^{2/3-J}).                             (I_J)

**Proof without differentiating the exact discrete deficit.** Put x0=T/lambda and

    x*=x0+d_J(x0)/lambda,
    F_T=T^{1/3}S^{2/3},  E_J(T)=T^{1/3}S^{2/3-J}.

The finite expression d_J is smooth and, uniformly for x=x0+O(F_T),

    d_J(x)=O(F_T),
    d_J'(x)=O(T^{-2/3}S^{2/3}).

The derivative estimate follows by differentiating the finitely many terms: P_j has degree j, and (log log x)^j/(log x)^j is bounded for large x. Thus x*=x0+O(F_T), and the mean-value theorem gives

    d_J(x*)-d_J(x0)
       =O(T^{-1/3}S^{4/3})=o(1).

Consequently the smooth log-coefficient approximation satisfies

    lambda x*-d_J(x*)=T+o(1).                                (20)

Fix epsilon>0 and define integers

    n_minus=floor(x*-epsilon E_J(T)),
    n_plus=ceil(x*+epsilon E_J(T)).

Both lie in x0+O(F_T). Because E_J(T) tends to infinity for every fixed J, the rounding errors are o(E_J(T)). The same derivative estimate gives d_J(n_+/-)-d_J(x*)=o(1). Moreover the sequence remainder in (H_J) obeys

    r_J(n_+/-)=o(E_J(T)).

This last statement does not assume smoothness or local regularity of the remainder: its defining eventual bound |r_J(n)|<=eta R_J(n) holds at every sufficiently large integer n, and R_J(n_+/-)/E_J(T) stays between fixed positive constants. Substitution in (H_J) and (20) yields

    log a_{n_minus}=T-lambda epsilon E_J(T)+o(E_J(T))<T,
    log a_{n_plus} =T+lambda epsilon E_J(T)+o(E_J(T))>T

for large T. Monotonicity therefore places N(p) between these two indices. Letting epsilon decrease to zero proves

    N(p)=x*+o(E_J(T)).                                       (21)

Finally, apply (U) with L=S and sigma=log lambda:

    d_J(T/lambda)/lambda
      =(C/lambda^{4/3}) T^{1/3}f_J(S,kappa_inv)
        +O(T^{1/3}S^{2/3-J-1}(1+log S)^{m_J}).

The last error is o(E_J(T)); combining this with (21) proves (I_J).

This is a complete finite-order squeeze argument. The only differentiated object is the explicit smooth truncation d_J, and the all-integer remainder from the coefficient theorem is used unchanged. It gives no exact rounding rule and no o(1) absolute inverse error.
