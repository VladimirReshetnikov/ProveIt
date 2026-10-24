# One binomial simultaneously certifies a factorial and every CRT modulus

## Scope and novelty

This is an ordinary, existence-preserving arithmetic replacement of the round14 direct C222 certificate. It uses neither a universal-polynomial black box nor a numerical execution of K215. Its final polynomial is the sum of squares of the entire quadratic residual list in each natural/equation.json. Every variable ranges over the nonnegative integers, including zero. All powers and binomials in this proof are explanatory notation: the generator emits the inherited finite ordinary Pell and digit graphs, with no variable-exponent primitive remaining in the polynomial.

The square-output factorial identity and the uniform lower-binomial coefficient bound already occur in the supplied Synchronized Exponents package, which credits the earlier Bootstrap package. They are explicitly inherited, not claimed new. The new architecture identifies the square-radius factorial binomial with the reciprocal CRT product from round14. Their raw ceiling equations then give a new bootstrap inequality V<B^2, which permits the common radix to depend only on the amplified CRT modulus. There is now one exact binomial, rather than two, and eighteen power requests, rather than nineteen. No additional guard or unproved fixed-point condition is introduced.

The logical endpoint retains the ordinary C222 calculus calibration, the pairwise-coprime Horn-flow theorem, the simultaneous positive-power/Pell graph, and the exact natural-domain contraction from the pinned round14 archive. With these retained dependencies, the equation has a natural zero if and only if that calculus has a finite refutation; ZFC proves that its unsolvability is equivalent to Con(ZFC). This is not a proof of consistency or a newly built Lean/Rocq/object-language ZFC derivation.

## 1. The unified arithmetic graph

Let t=t0+16. F is initially only a proposed natural factorial output. Define

    rho=F^2,        V=(rho+1)^t,
    B=binom(rho+t,t),        R=2+t+x+y+F,
    K=2R,          N=B^K.

The graph for B is initially an uninterpreted exact-binomial digit graph. Its intended meaning must not be used in the bootstrap below. Impose the same natural ceiling rows as before:

    V+B=BF+u+1,       B=u+v+1.                    (1)

The base radix variant is q=N^K. The squared-base companion is

    q=(N^2)^K.                                    (2)

The square N^2 already occurs in the representative bound, so the companion adds neither a new variable-power request nor a new exponent index. The companion is useful for subsequent signed-domain compilation because its base is a square. Every natural-domain argument below applies to both variants.

All independent CRT representatives C,A_j are positive. There are nine independent representatives for the derived-label variant and ten for the local-slack variant, with the aggregate equation

    C+sum_j A_j+g=cN^2,       c=9 or c=10.         (3)

The polynomial derived label expression J(A) is NOT included in (3).

## 2. Uniform coefficient lemma (inherited; complete proof)

For positive integers r,n and 0<=j<=n,

    binom(r+n,j)<=(r+1)^n.                       (4)

Induct on n. The case n=1 is immediate. The case j=0 is immediate for every n. If 1<=j<n, Pascal's identity and the induction hypothesis bound the coefficient by 2(r+1)^(n-1)<=(r+1)^n. If j=n, use

    binom(r+n,n)=product_(i=1)^n (r+i)/i
                <= product_(i=1)^n (r+1).

Unlike a unimodality proof, this requires no hypothesis r>=n. This is essential because F has not yet been identified as a factorial.

## 3. Noncircular bootstrap: B>F and V<B^2

The inherited simultaneous positive-power theorem first recovers V=(F^2+1)^t from an independently positive base and exponent. Thus V>=1. The second raw row in (1) gives B>=1. Subtracting the rows gives

    V+v=BF.                                       (5)

Since v is natural, (5) excludes F=0 and gives V<=BF. Because t>=1,

    V=(F^2+1)^t>F^2.

Consequently BF>F^2; division by the already positive F gives B>F>=1, so B>=2, and

    V<=BF<B^2.                                    (6)

These are consequences of raw polynomial rows and an independently valid power. They do not assume that the binomial graph is exact. Now the base B and exponent K are positive, so the inherited power graph recovers N=B^K. The bases N and N^2 are positive, so the graph recovers the selected q in (2). Since K>=2,

    q>=N^K=B^(K^2)>=B^4>V.                       (7)

Apply (4) with r=F^2,n=t. Every coefficient needed in the sole exact-binomial digit is <=V<q. The digit graph therefore really returns

    B=binom(F^2+t,t).

There is no circular factorial, binomial, positivity, or radix assumption in this ordering.

## 4. Square-output fixed point at the padded horizon

For completeness the inherited fixed-point theorem is reproved in the restricted t>=16 range used here. Put H=t! and f=V/B. Equation (1) is equivalent to

    F-1<f<=F,       or F=ceil(f).                  (8)

Indeed 0<=u<B, and solving the first row for V gives B(F-1)<V<=BF. Conversely, if (8) holds, u=V+B-BF-1 and v=B-u-1 are natural.

The exact product expression is

    f=H product_(i=1)^t (F^2+1)/(F^2+i).

Every factor is positive and at most one, so F<=H by (8). Every factor is nondecreasing in F^2; since F>=1,

    f>=2^t/(t+1)>t^2.                             (9)

The strict inequality at t=16 is 65536>4352. If 2^t>t^2(t+1), then 2^(t+1)>2t^2(t+1)>=(t+1)^2(t+2), because t^2>=3t+2 for t>=4. Hence (9) holds for all t>=16. In particular F>t^2.

Let a_i=(i-1)/(F^2+i). Then

    sum_i a_i < t(t-1)/(2F^2)<1/(2F).

The finite product inequality product_i(1-a_i)>=1-sum_i a_i gives

    H(1-1/(2F))<f<=F.

Thus

    H<2F^2/(2F-1)=F+F/(2F-1)<=F+1.

Integrality gives H<=F. Together with F<=H, this proves F=t!.

Conversely let F=H=t!. Since H>t^2, the same estimate gives H-1/2<f<=H, so (8) and both natural ceiling witnesses exist. Thus the proposed unified graph admits exactly the intended factorial value, not an additional small fixed point.

## 5. The same B is the reciprocal CRT product

With F=t!, each i in 1..t divides F, and

    d_i=1+F^2/i

is an integer congruent to 1 modulo F. Every prime dividing d_i is greater than t. If a prime p divided two different d_i,d_j, it would divide i*d_i-j*d_j=i-j, contradicting p>t. The d_i are pairwise coprime and

    product_(i=1)^t d_i=binom(F^2+t,t)=B.

The factorial binomial and the required CRT product are therefore literally the same integer and the same digit graph, not just two equal outputs retained with an extra equality.

## 6. All other low digits fit the pure radix

The inherited local majorant certificate has E=8388608. The label certificate has ell=4194304 for the derived-label variant. Its raw positive-gate ledger gives local L and J less than R^E. Because F>=16!>2^44, R>=2^44. At r0=2^44, 44E<2^44, so r0^E<2^r0. For every r>=r0, E/r<=1/2 and

    (1+1/r)^E<=sum_(j=0)^E (E/r)^j<2.

Integer induction gives R^E<2^R<2^K. This is used only after factorial recovery.

For any independent representative n, equation (3) gives n<=cN^2<=10N^2. Every lower range index satisfies 1<=k<=R-1. For j<=k, if j>n the coefficient is zero; otherwise

    binom(n,j)<=n^k<=10^k N^(2k)
                 <2^(4R) N^(2k)
                 <=N^(2k+2)<=N^K<=q.            (10)

The first strict inequality uses k<R and 10<16. The penultimate comparison uses N=B^K>=2^K and K=2R. Thus every independent range digit is carry-free for q=N^K and a fortiori for q=(N^2)^K. In both variants N divides q.

For the derived label only, the separate literal ledger bounds J(A)<=(n+1)^ell where n=max of the four encoded schema parameters. The aggregate gives n<=9N^2 and N>=10, hence n+1<=N^3 and J(A)<=N^(3ell). The exact base inequality 2*16!>=3ell*17 and induction give 3ell(t+1)<=2F<K. Thus for every j<=t+1,

    binom(J(A),j)<=J(A)^(t+1)
                       <=N^[3ell(t+1)]<N^K<=q.   (11)

As before, coefficients with j>J(A) are zero. Consequently the additional fused graph represents exactly N|binom(J(A),t+1). It does not constrain J(A) to satisfy the independent aggregate bound.

## 7. CRT decoding and the derived-label range

For a prime p and positive integers e,k, p^e|binom(a,k) implies a mod p^e<k. If a<k this is immediate. Otherwise the valuation formula is a sum of terms each in {0,1}. If [a-k+1,a] contained no multiple of p^e, every summand for powers p^j with j>=e would vanish, leaving valuation at most e-1, a contradiction.

For row i-1 choose p|d_i and m=v_p(d_i). The retained raw index congruence B|C+F^2+1 gives C=i-1 modulo p. The index range N|binom(C,t) gives C=s modulo p^(Km), 0<=s<t. Since p>t, necessarily s=i-1. Every column range similarly gives A_j=w_j modulo p^(Km) in its intended bounded interval. The nonnegative local polynomial satisfies N|L(C,A), so p^(Km)|L(i-1,w). Its bound 0<=L<2^K<=p^(Km) forces L=0.

For the derived-label variant, N|binom(J(A),t+1) gives J(A)=s modulo p^(Km) with 0<=s<=t. Polynomial congruence gives J(w)=s modulo p^(Km). Since both J(w) and s lie in [0,2^K), they are equal. Thus every decoded row has J(w)<=t without a ninth independent local coordinate. For the local-slack variant, the unchanged local square directly gives t=w+J.

Conversely choose a bounded tuple for every row and use CRT at precision d_i^(2K), choosing positive representatives in [1,B^(2K)]=[1,N^2]. For a range lower index k<=K, a falling-factorial numerator has a factor divisible by p^(2Km); division by k! loses at most k-1<K<=Km in p-valuation. This proves all required range divisibilities. The same argument applies to J(A) when J(w)<=t, because polynomial congruence gives J(A)=J(w) modulo p^(2Km). The aggregate slack exists since only independent representatives are included. The raw index and local divisibilities follow from the same CRT congruences.

## 8. Full existence equivalence and source calibration

Given a natural zero, Sections 3-6 interpret every power, the only exact binomial, the factorial, the product, and every fused range graph in noncircular order. Section 7 yields a valid bounded source row at every i<t with all formula labels <=t. The unchanged beta equations identify adjacent positive accumulator states, starting at W_1=1+F and ending at 1, where W_j=1+jF. Positive labels <=t have pairwise-coprime weights. Multiplication of the selected valid Horn-rule equations and prime valuations gives one net production of falsity and balance at every other nonzero label. If falsity were outside the closure of truth under those rules, counting conclusions outside the closure would be at most the number of outside premises, contradicting that net production. Thus the decoded rules contain a finite C222 refutation. This argument does not require acyclic supplied rule multisets and does not mistake the unit weight of truth for a nonzero label.

Conversely start from a finite calibrated refutation, expand it to a finite proof tree, and choose the padded t>=16 beyond its length, its finite schema parameters and all complete label sums J, before defining F. Set F=t!, construct the pending-multiset positive accumulator path with truth padding, and choose the beta encoding x,y. Sections 5 and 7 provide B,N and all independent representatives. Set V and the chosen pure radix q. Sections 4 and 6 provide the natural ceiling and digit witnesses. The inherited simultaneous Pell theorem supplies all eighteen power graphs at once. Every residual is zero. The exact nonnegative projection restores every eliminated coordinate, preserving both directions.

The C222/ZF/ZFC calibration is unchanged and explicitly retained from the source archive. Finite coefficient checks and finite semantic regression tests are not substitutes for this unbounded argument and do not decide solvability.

## 9. Artifacts and reproduction

Run build_unified_product.py with --output DEST. The default is the derived-label Cantor syntax and q=N^K. Select --syntax xx0 for the square-shell syntax, --labels slack for a ninth local label slack, and --squared-radix-base for q=(N^2)^K. The endpoint includes raw/equation.json, raw/raw_audit_input.json, a literal majorant ledger, the natural projection certificate, the whole expanded quartic and an independent exact projection receipt.

The generator imports only the previously reviewed round14 release read-only. Every new artifact is written under the explicit output directory. SOURCE_BINDING.json records the imported executable closure and its bytes; REPRODUCTION.json records byte-exact normal/optimized rebuilds. The natural equation is sum(r_i^2)=0 over its complete residual list, not an abbreviated schematic or a square of a sum.
