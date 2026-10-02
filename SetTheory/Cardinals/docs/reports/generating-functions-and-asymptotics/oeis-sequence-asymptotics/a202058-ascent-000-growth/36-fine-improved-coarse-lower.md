# Optional quantitative lower bound from the new barriers

This retains the broad-window method; it is not a matching fine asymptotic.

The padded upper barrier and global unpadded lower barrier imply uniformly in N>=1

    log F(t(q),(N,1,N)) = N p(q) + O((q+1)²).

Indeed the unpadded rank correction lies between 0 and q. In the padded upper function the additional exponent is Lp−q(r_padded−r), bounded by Lp+q, with L=ceil(q), while the new scalar barrier is quadratic.

The Chernoff lemma from the frozen report therefore improves to

    P(|J−N M(q)|>ε N M(q))
      <=2 exp(−cNε²+C(q+1)²),

for all sufficiently large q, where M(q)=t(q)p_t(t(q)), 0<ε<1/2, and constants c,C do not depend on N,q,ε. Its proof is unchanged: compare q with q±ε/8 and use the uniform growing-state estimate.

For n large choose

    N=ceil(K n^(2/3)(log n)^(2/3)), ε=2N/n,

where K is a sufficiently large fixed constant, and choose q by

    N M(q)=(1−4ε)n.

M is continuous and eventually strictly increasing, with

    M(q)~ T e^(q/2)/(sqrt(2)q),
    q=(2/3)log n+(2/3)log log n+O(1).

Then Nε²=4N³/n² >=4K³(log n)², while (q+1)²=O((log n)²). Taking K sufficiently large forces the displayed Chernoff tail below 1/2 for every sufficiently large n.

Thus some j in the central window has

    (T_op^j 1)(N,1,N) t(q)^j/j!
      >= F(t(q),(N,1,N))/(4εNM(q)+6).

The central window satisfies j>=n−6εn and N+j<=n for large n. The root reaches (N,1,N) by N−1 new-maximal-label transitions. The established monotone extension injection then gives a_n>=(T_op^j 1)(N,1,N), and hence

    log(a_n/(n! μ^n)) >= −C1 n^(2/3)(log n)^(5/3).

The contributions O(q²), logarithmic pigeonhole loss and t(q)−T correction are smaller than this bound; as in the frozen proof one may directly use −j log t(q)>=−n log T, because T>1 and eventually 1<t(q)<T.

Combined with the padded upper theorem, this proves the asymmetric enclosure

    −C1 n^(2/3)(log n)^(5/3)
      <= log(a_n/(n! μ^n))
      <= C2(log(n+2))².

The lower exponent 2/3 is a limitation of this broad-window argument, not an asserted subexponential exponent of the counting sequence.

## One-sided inverse consequence

For y→∞ put x=y/W(y/(eT)), so x log(x/(eT))=y, and let N(y)=min{n>=1:log a_n>=y}. Stirling's formula and monotonicity give

    x−O(log x) <= N(y) <= x+O(x^(2/3)(log x)^(2/3)).

This is an asymmetric controlled inverse enclosure only. It is not an all-orders inverse or a claim about the true displacement.
