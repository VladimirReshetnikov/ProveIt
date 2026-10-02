# From the proposed relaxed amplitude proof to the DFA amplitude

Status: transfer proof built on the independently reviewed relaxed tracking theorem in amplitude-proof-candidate.md. The needed uniform high-path tail is proved with the corrected bound below; the false printed assertion U≤2 is not used. This extension is independently approved in dfa-transfer-audit/verdict.md, separately from the relaxed theorem.

## Finite-time endpoint ratios

The tracking estimates are linear and apply to an arbitrary vector v at a fixed time L, with zero-padding on later physical phase spaces. They show that its endpoint value, divided by

 S_n=27^n exp(3·3^(1/3)a_1 n^(1/3)) n^(13/6),

has a finite limit. The limit need not be known to be positive. The reference relaxed array has a strictly positive limit, by the published Theta lower bound. Consequently every fixed-time prefix reweighting has a convergent ratio to the reference endpoint count.

## Finite-level defects are uniformly approximable by finite-time defects

Under the probability measure proportional to relaxed path weights, with terminal point (2n,n), the ternary DFA ratio is

 ρ_n=B_n/(2^(n−1)R_n)
     =E_n Π_(m=1)^(n−1) [1−1/(2(m+1)²) 1_{L_m≥3}],

where L_m is the horizontal-run length at vertical level m before the rise to m+1. This is the positive completed-run representation already proved in the comparison package.

First retain only factors with m<M, giving ρ_n^[M]. The established pointwise product comparison gives, uniformly in n,

 |ρ_n−ρ_n^[M]|≤(1/2)Σ_(j>M)j^−2 ≤1/(2M).

For fixed M, additionally ignore a retained factor if its terminating rise occurs after total path time L; call the resulting expectation ρ_n^[M,L]. This is a fixed-time prefix reweighting. Hence ρ_n^[M,L] has a limit as n→∞ by the previous paragraph.

The two products in ρ_n^[M] and ρ_n^[M,L] can differ only if a rise at level m+1≤M occurs at a time i>L. At its endpoint the transformed height is

 j=i−3(m+1)≥i−3M.

Let p=3 floor(i/3). The preceding point of the path at time p has height at least j−(i−p), since each forward step increases height by at most 1. Therefore its height is at least p−3M. For fixed M and all sufficiently large p this exceeds the published tail threshold 3(p/3)^(3/4).

The corrected uniform high-path lemma proved below shows that, uniformly in terminal n, the relaxed bridge mass of paths visiting such high points after a growing starting block time tends to zero. Thus for fixed M there is η_M(L)→0 such that

 sup_n |ρ_n^[M]−ρ_n^[M,L]|≤η_M(L).

(The finite number of terminal sizes with 3n≤L cause no problem: the two products then agree.) This proves that ρ_n^[M] converges, since it is a uniform limit, in n, of sequences having limits. Sending M→∞ by the preceding 1/(2M) bound proves that ρ_n converges.

The comparison theorem supplies the positive lower bound

 lim ρ_n≥P_3=(2sqrt(2)/π)sin(π/sqrt(2))>0.

Together with the relaxed amplitude theorem this gives

 B_n∼C_B (n!)²(27/2)^n exp(3·3^(1/3)a_1 n^(1/3))n^(5/3),

where C_B=(lim ρ_n)C_R/2>0. The factor 1/2 comes from 2^(n−1), rather than 2^n.

## Corrected uniform high-path lemma

This repairs a false pointwise claim in the printed arXiv-v1 proof of Lemma 14. At active up destinations j≥1,

 U(i,j)≤U(i,1)=2[1+3/(2i+1)]≤2[1+3/(2i)].

Therefore every path of length t has weight at most C t^(3/2)2^(number of up steps), and

 d_(3x,3y)≤C x^(3/2)2^(2x+y) binom(3x,x−y).              (T1)

For weighted continuations p(r,s;T), the normalized sequence u_r(s)=p(r,s;T)/(s+1) is nonincreasing on each physical residue class. Here is a direct proof. Its backward coefficients are

 A_r(s)=4(r−s+3)(s+2)/[(2r+s+3)(s+1)],
 B_r(s)=(s−1)_+/(s+1).

For s≥1 their row sum is

 V_r(s)=3−6[(s−1)/(s+1)][(s+2)/(2r+s+3)],

which decreases with s because both bracketed factors increase and are nonnegative. At s=0 the sole coefficient A_r(0)≥4, while V_r(1)=3, so the row sums decrease across the bottom as well. Adjacent same-phase starts s,s+3 have next supports {s−2,s+1} and {s+1,s+4}. Assuming the next normalized sequence decreases, all values on the first support are at least its value at the common height s+1, and all on the second are at most it. Comparing row sums proves the backward induction. The terminal normalized sequence has value1 at0 and0 at other physical coordinates, so the induction starts.

Consequently p(3x,3y;T)≤(3y+1)p(3x,0;T). Comparing path mass through these points gives

 P_T(path visits (3x,3y))≤(3y+1)d_(3x,3y)/d_(3x,0).      (T2)

The known relaxed lower bound gives d_(3x,0)≥c27^x exp(−C x^(1/3))x^(13/6) for all sufficiently large x. Moreover

 2^(2x+y)binom(3x,x−y)/27^x
 =P(Binomial(3x,1/3)=x−y)≤exp(−2y²/(3x)),

by the elementary Hoeffding bound (or a direct Chernoff estimate). Combining with (T1),(T2), summing over y>x^(3/4) and y≤x, and then over x>I bounds the total forbidden bridge mass by

 Σ_(x>I) C x^A exp[−c x^(1/2)+C x^(1/3)] →0.

The estimate is uniform in T; constants are independent of the terminal size. This supplies precisely the tail statement needed above. It also shows why the polynomial correction to the paper's claimed critical domination does not affect that conclusion.

## Scope

This reduction gives the leading positive amplitude, not an all-orders expansion. The height-truncation error is only O(M^−1), and the tail lemma is qualitative; higher-order DFA expansions would require quantitative versions and detailed asymptotics of the growing number of defects.

Primary tail source: https://arxiv.org/html/2404.08415v1#S3.SS4 (Lemma 14 and its preceding path coordinates). Exact numbering in the published AofA paper may differ; no claim of a new published amplitude result is made.
