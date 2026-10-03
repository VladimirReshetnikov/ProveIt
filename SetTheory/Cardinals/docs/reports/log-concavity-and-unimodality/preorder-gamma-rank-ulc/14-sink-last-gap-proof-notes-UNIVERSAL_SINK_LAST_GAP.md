# Sharp final coefficient bounds for directed cores with universal sinks

## Precise result and scope

Let C have r>=4 vertices, let H be any loopless directed relation on C, and let W be an independent set of universal sinks. The full relation has exactly the arcs of H and every arc C -> W. It has no arcs from W. Give every physical vertex arbitrary nonnegative independent tail and head activities. A support is an ordered pair of disjoint endpoint sets (S,T), |S|=|T|, that admits a directed perfect matching; it is counted once with weight u_S v_T, regardless of the number of witnesses.

Write Gamma(z)=sum_k gamma_k z^k. Assume gamma_r>0, and let m be the number of sinks whose head activity is positive. Then m>=r and the actual degree is exactly r. The sharp bound is

    gamma_(r-1)^2 >= K(r,m) gamma_(r-2) gamma_r,
    K(r,m) = 2r^2(m-r+2) / [(r-1)^2(m-r+1)].

The constant is attained when H has no active internal arcs, the r positive core tail activities are equal, and the m positive sink head activities are equal. Thus it cannot be increased for fixed r,m.

Uniformly over all finite sink counts, the optimal constant is

    K(r,infinity) = 2r^2/(r-1)^2.

It is approached by these same edgeless, equal-activity examples as m tends to infinity. It is not attained at a finite m when gamma_r>0. This constant is strictly larger than the actual-degree Newton constant 2r/(r-1).

For r=4, in particular,

    gamma_3^2 >= [32(m-2)/(9(m-3))] gamma_2 gamma_4
               > (32/9) gamma_2 gamma_4
               > (8/3) gamma_2 gamma_4.

The theorem applies to arbitrary loopless directed H, not just preorders, and arbitrary nonnegative independent role activities subject to gamma_r>0. It is invariant under reversing every arc and exchanging the two role-activity families, giving the universal-source version. It does not prove the middle gap or the whole rank-ULC conjecture for weighted degree four.

Without the gamma_r>0 assumption, the unnormalized inequality

    (r-1) gamma_(r-1)^2 >= 2r gamma_(r-2) gamma_r

still holds. When gamma_r=0 it is trivial and must not be substituted for the appropriate inequality at the smaller actual degree.

## Three top coefficients

Let u_i and v_i be the core tail and head activities; let w_x be the sink head activities. Sink tail activities never appear. Write

    e_j = elementary symmetric polynomial of degree j in (u_i : i in C),
    E_j = elementary symmetric polynomial of degree j in (w_x : x in W),
    p=e_r, q=e_(r-1), e=e_(r-2).

Set E_0=1 and E_j=0 when j>|W|. Let N^-(j) be the in-neighborhood of j inside H. Define

    d = sum_(j : N^-(j) nonempty) v_j u_(C\{j}),

    c = sum_j v_j c_j,
    c_j = sum_(S subset C\{j}, |S|=r-2, S intersects N^-(j)) u_S,

    b = sum_({j,k} admissible) v_j v_k u_(C\{j,k}).

Here an unordered pair {j,k} is admissible precisely if there are distinct i,l in C\{j,k} with arcs i->j and l->k. The sum defining b counts that head pair once, not once per witnessing pair of arcs.

The exact identities are

    gamma_r     = p E_r,
    gamma_(r-1) = q E_(r-1) + d E_(r-2),
    gamma_(r-2) = e E_(r-2) + c E_(r-3) + b E_(r-4).

To see them, a size-k support uses k core tails and h core heads, so k+h<=r and it uses k-h sink heads. In the three top ranks h is at most 0, 1, and 2 respectively. For h=1, a selected tail must be an in-neighbor of the core head. For h=2, the selected core tails must cover the two core heads by two distinct tails. All remaining tails can then be matched to the selected universal sinks, so no other condition remains. The identities therefore enumerate supports, rather than witnesses.

## Core inequalities

Put K=2r/(r-1). Newton's inequality in exactly r tail variables gives

    q^2 >= K p e.

Two other inequalities are coefficientwise polynomial inequalities:

    q d >= p c,
    d^2 >= 2 p b.

For the first, it is enough to check a head j of positive in-degree. With positive tail variables,

    q/u_j = e_(r-2)(u_i : i != j) + u_(C\{j})/u_j
            >= c_j.

Multiplying by p v_j and summing proves the claim; equivalently it is a coefficientwise comparison without divisions, so zero activities are allowed. If the in-degree is zero, c_j=0 as well.

For the second, every admissible head pair has two heads of positive in-degree. The two ordered cross terms of d^2 for j,k sum to

    2 v_j v_k u_(C\{j}) u_(C\{k})
      = 2 p v_j v_k u_(C\{j,k}).

These supply 2pb exactly. The same-head terms and all other pairs are nonnegative.

## Sink inequalities

The elementary symmetric sequence E_j is ultra-log-concave at its number m of variables. In particular, its factorial normalization j!E_j is log-concave. When E_r>0, the ratios j E_j/E_(j-1) are nonincreasing; comparison of these ratios yields

    E_(r-1)^2 >= E_(r-2) E_r,
    E_(r-2) E_(r-1) >= [r/(r-2)] E_(r-3) E_r,
    E_(r-2)^2 >= [r(r-1)/((r-2)(r-3))] E_(r-4) E_r.

If E_r=0, the required inequalities with E_r on their right are immediate. Since

    2r/(r-2) >= K,
    2r(r-1)/((r-2)(r-3)) >= K,

all three sink brackets in the identity below are nonnegative.

## Sharp finite-sink-count proof

Delete sinks of zero head activity. Assume gamma_r>0, so all r core tail activities are positive and the remaining sink count is m>=r. Set s=m-r>=0. Newton's normalized log-concavity gives the precise sink estimates

    E_(r-1)^2 >= [r(s+2)/((r-1)(s+1))] E_(r-2)E_r,

    E_(r-1)E_(r-2) >= [r(s+3)/((r-2)(s+1))] E_(r-3)E_r,

    E_(r-2)^2 >= [r(r-1)(s+4)(s+3) /
                    ((r-2)(r-3)(s+2)(s+1))] E_(r-4)E_r.

For completeness, these follow by applying ordinary log-concavity to

    A_j=E_j/binom(m,j).

The pairs of indices (r-1,r-1), (r-2,r-1), and (r-2,r-2) are each more balanced than the respective pairs (r-2,r), (r-3,r), and (r-4,r), with the same total sum. Monotonicity of consecutive ratios of A_j gives the comparisons, and the displayed constants are the corresponding binomial ratios.

Combining them respectively with q^2>=2r pe/(r-1), qd>=pc, and d^2>=2pb gives

    q^2 E_(r-1)^2 >= K_0 pe E_(r-2)E_r,
    2qd E_(r-1)E_(r-2) >= K_1 pc E_(r-3)E_r,
    d^2 E_(r-2)^2 >= K_2 pb E_(r-4)E_r,

where

    K_0=2r^2(s+2)/[(r-1)^2(s+1)]=K(r,m),
    K_1=2r(s+3)/[(r-2)(s+1)],
    K_2=2r(r-1)(s+4)(s+3) /
                [(r-2)(r-3)(s+2)(s+1)].

We have K_1>K_0 and K_2>K_0. Indeed

    K_1/K_0 = [(r-1)^2/(r(r-2))] [(s+3)/(s+2)] > 1,

    K_2/K_0 = [(r-1)^3/(r(r-2)(r-3))]
               [(s+4)(s+3)/(s+2)^2] > 1,

because (r-1)^3-r(r-2)(r-3)=2r^2-3r-1>0 for r>=4. Adding the three termwise bounds and using the top-coefficient identities proves the sharp theorem.

Sharpness is exact: for an edgeless core with all tail activities equal to u>0 and all m active sink head activities equal to w>0,

    gamma_k=binom(r,k)binom(m,k)(uw)^k,

so gamma_(r-1)^2/(gamma_(r-2)gamma_r)=K(r,m). Sending m to infinity proves optimality of the uniform constant.

## A six-term certificate for the ordinary Newton gap

The following earlier, weaker identity is retained as a convenient direct certificate. With K=2r/(r-1), substitution and expansion give

    gamma_(r-1)^2 - K gamma_(r-2) gamma_r
      = (q^2-Kpe) E_(r-1)^2
        + Kpe [E_(r-1)^2-E_(r-2)E_r]
        + 2(qd-pc) E_(r-1)E_(r-2)
        + pc [2E_(r-1)E_(r-2)-K E_(r-3)E_r]
        + (d^2-2pb) E_(r-2)^2
        + pb [2E_(r-2)^2-K E_(r-4)E_r].

Each summand is nonnegative by the preceding inequalities. This proves the theorem. No conjectured rank-ULC statement or real-rootedness of Gamma is used.

For r=4 the corresponding integer-scaled identity is

    3 gamma_3^2 - 8 gamma_2 gamma_4
      = (3e_3^2-8pe_2) E_3^2
        + 8pe_2(E_3^2-E_2E_4)
        + 6(e_3d-pc) E_2E_3
        + 2pc(3E_2E_3-4E_1E_4)
        + 3(d^2-2pb) E_2^2
        + 2pb(3E_2^2-4E_4).

## Classical input, sources, and boundary

The only classical inequality used is Newton's inequality for elementary symmetric functions. One modern primary source for the requisite normalization is Petter Branden and June Huh, *Lorentzian polynomials*, Annals of Mathematics 192 (2020), 821-891, especially Example 2.26 (bivariate homogeneous Lorentzian polynomials and coefficient ULC), with the stable-to-Lorentzian inclusion of Proposition 2.2 applied to the product of linear factors prod_i(z+u_i t). The primary article was inspected on 2026-10-01:

https://annals.math.princeton.edu/wp-content/uploads/annals-v192-n3-p04-s.pdf
https://arxiv.org/abs/1902.03719

The support partition and the core comparisons above are supplied explicitly; no literature theorem about counting matching witnesses is transferred to Boolean supports. No novelty or priority claim is made.

The included verifier independently enumerates full supports by Hall's condition, compares the three top coefficients with the displayed formulas, and checks the identity and all six nonnegative terms in exact rational arithmetic. Its finite checks corroborate the proof, not replace it. The separate numerical weighted-preorder search is exploratory only and is not a logical dependency.
