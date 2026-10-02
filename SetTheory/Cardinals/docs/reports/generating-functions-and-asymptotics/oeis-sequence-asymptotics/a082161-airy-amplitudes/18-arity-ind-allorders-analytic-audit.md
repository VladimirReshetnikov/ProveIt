# Independent audit: relaxed fixed-arity expansion to every finite order

Date: 2026-10-02. Scope: each fixed integer k≥3, q=k−1, for the exact relaxed-tree recurrence initialized by d_(0,0)=1. Constants may depend on k and on the prescribed finite order.

## Verdict

**Approved for every finite order, with one common strictly positive amplitude.** The reviewed proof extends the previously approved leading theorem to a genuine Poincaré expansion in powers of n^−1/3, with no logarithmic powers. I found no unresolved gap in the polynomial–Airy inverse, all-order bottom condition, high-order norm defect, scalar matching, common-amplitude normalization, or zero-limit bootstrap. I independently reproduced the first and second relative coefficients over symbolic q, rather than relying on the producer's code.

The conclusion is

R_n = C_k (n!)^q (k^k/q^q)^n exp[3(kq/2)^(1/3)a_1 n^(1/3)] n^((2k−1)/3)
      × [1 + Σ_(r=1)^M c_(k,r)n^−r/3 + O_(k,M)(n^−(M+1)/3)]

for every fixed M≥0, with the same C_k>0 for every M. This is an expansion of the exact relaxed initialization, not a claim about arbitrary initial data. Positivity uses the published lower Theta bound already verified in the leading audit. It is not a convergence theorem for the infinite formal series, a uniform-in-k theorem, or a theorem for compacted trees or DFA.

## Reviewed files and exact hashes

All hashes are SHA-256. The leading file was read but not modified.

- all-orders-proof.md: 7a67a0230c49f4d463fd24c31c94ca04aee32b3a8d1f9382917a6c460804dee0
- fixed-arity-proof.md: 9be0c0aaf02b6918a8015c6d059664851d393e9ea8e75ac4a31e082c34434ee2
- independent-analytic-audit/analytic-audit.md: 974c250275efc483acec31d9ea3806ba91a670d70cb70071ae757eaa1f45cbe9
- independent-analytic-audit/verdict.md: f717c400036d8e415d049b917fef9db91945b2b8fd94c3980a56c8c1d771dc00
- coefficients/derive_c2.py: a2447595c17d5be9314d49d8f204ead8fdcc9d4e9c42a3a212f249a64e9a838f
- coefficients/c2-output.txt: 4e74d774d02e10a010fdd4f7eec32ce75e333464653decfb9ef485f4729592db
- /workspace/shared/root-fixed-arity-recursion/check_general.py: 7fa6c732191f14e90af40645b019d2abc604d8e1785e68e3cae1a22fea9a8f73

Independent calculation artifacts in this audit directory:

- check_independent.py: 37edc8a29d7d69b6f92f0504b2bd2185f2e447a016f7d225ef30491577cc597c
- independent-output.txt: f781e4488fabb09b2fb01c8e04b5e1025e1a2b01f6b10239cde24506da8a59e0

## 1. Precisely inherited analytic input

The leading audit approves, for each fixed k≥3, the actual phase spaces and fixed weighted norm, forward residual O(i^−4/3), adjoint residual O(i^−1), adjacent-phase norm ratio 1+O(i^−1), and the compressed singular gap 1−c_k i^−2/3. Consequently the four displayed blocks in the extension are available. The exact normalized solution is bounded and its scalar projection tends to a strictly positive C. The phase-zero endpoint of ψ_i is comparable to i^−1/2.

The extension does not assume a higher-order eigenvector or eigenvalue expansion. Its high-order formal profiles need only be forward approximate solutions; the original two-block bounds are sufficient to transfer their accuracy to the exact solution. No new high-order weighted-adjoint boundary construction is required.

The leading reviewed hash is exactly the hash certified by the leading verdict. There is no mismatched-file substitution here. I rely on that audited analytic input rather than claiming a second independent reconstruction of its compactness theorem in this audit.

## 2. Exact formal equation and triangular recursion

For ε=i^−1/3 and x=ε(j+1), the previous-time arguments are ετ and (x−ε)τ or (x+qε)τ, where τ=(1−ε³)^−1/3. Direct substitution into q²(i−j+k)/(qi+j) gives exactly the U displayed in the extension. The distinction between time dilation and spatial shift is respected.

At orders zero and one the critical zeroth and first moments are k and zero. At order ε² the operator on a newly entering profile is k[(q/2)∂²−x−λ]. Thus at coefficient ε^(m+2), φ_(m+2) cancels by the zeroth moment, φ_(m+1) cancels by the first moment, and the new unknowns are precisely φ_m and σ_(m+2). Every other term depends only on earlier stages. Differentiation preserves pairs A(x)f(x)+D(x)f′(x) because f″=2(x+λ)f/q. Rational and dilation Taylor coefficients are polynomial in x. This proves the claimed polynomial forcing closure at all finite stages.

For the polynomial inverse, differentiation gives

L_q(Af+Df′) = [(q/2)A″+2(x+λ)D′+D]f + [qA′+(q/2)D″]f′.

Eliminating A yields exactly K_qD=P−Q′/2. Its action on x^d has leading term (2d+1)x^d and only lower-degree corrections, so it is invertible on each finite polynomial space. Constants map to constants. The new scalar adds σ/k to P, therefore adds exactly σ/k to D. Choosing σ cancels D(0) uniquely. Integration of A′ then leaves precisely one free additive constant, fixed by A(0)=0.

Since f(0)=0 and f′(0)≠0, D(0)=0 is equivalent to the bottom Dirichlet condition for the new profile. This condition is achieved exactly, not just to an asymptotic order. The scalar coefficient is also the compatibility condition that a decaying inhomogeneous Airy solution would require; the explicit polynomial construction supplies it without a separate unproved solvability assertion. All profiles are decaying polynomial–Airy pairs. No resonance or logarithmic profile is forced.

## 3. Boundary and norm remainder to arbitrary order

The exact forward stencil has only one possible absent lower input, at j=0 and j−1=−1. Its previous-time x-coordinate is zero. Every retained φ_m vanishes there exactly, so inserting the formal profile does not create a fictitious bottom contribution. There are no additional forward negative sites for larger q; those arose only in the leading adjoint problem, already handled in the input proof.

For any finite number of profiles, all required derivatives are bounded near zero and admit polynomial times exp(−c_k x^(3/2)) bounds at large positive x. One must use an absolute envelope permitting f′ at the origin, as the proof does. A bound relative to f would not be valid there.

On the effective support x≤2 log i plus the stencil margin, q+xε²−ε³ is uniformly separated from zero for sufficiently large i. The rational and time-dilation remainders have any requested power of ε times polynomial factors in x. Profile Taylor remainders remain bounded by a fixed square-integrable envelope after a small weakening of its exponential constant. Because q is fixed, the shifts are O_k(ε+ε³x), uniformly small on this support.

The fixed weights are bounded. Summing the square of this envelope over any phase mesh of width kε costs O_k(ε^−1), so the norm remainder has scale O(ε^r ε^−1/2), or O(ε^r N_i). There is no unaccounted endpoint loss at this step. Cutoff mismatches are confined to x≥log i−O_k(ε+ε³ log i), where Airy decay is superpolynomial in i. The finite top lies far outside the cutoff support. These facts establish arbitrary algebraic accuracy in the fixed norm from a sufficiently long finite formal truncation.

The stated conservative rule K>3p_*+4 is more than sufficient. It is important to retain all intermediate profile coefficients and to match both the recurrence and scalar ratio to the chosen stage. No bound uniform in the number of stages is claimed or needed.

## 4. Scalar matching, no logarithms, and amplitude normalization

Subtract log k when comparing log(H_i/H_(i−1)) to log(σ/k); this is the intended coefficient comparison. The leading contributions of log G are λ ε² and β ε³. A term h_r i^−r/3 contributes first at −(r/3)h_r ε^(r+3). Since this coefficient is nonzero for every r≥1, scalar matching can be continued uniquely at every finite order. The only logarithmic summation occurs at i^−1 and is already represented by i^β.

The leading product satisfies P_i/G_i→κ>0 because log(t_i/k)−λi^−2/3−βi^−1 is summable, and the corresponding sum-integral differences have finite limits. Fixing the multiplicative leading coefficient of every H_i to one is essential. With S_i=P_iN_i/N_(L−1), the prescribed Z_i simplifies to

Z_i = (κH_i/P_i) Φ_i/N_i.

The scalar prefactor tends to one, and Φ_i/N_i−ψ_i tends to zero in norm. In fact φ_0 and φ_1 match the leading profile, and the remaining finite sum has relative norm O(ε²). Hence every high-order Z_i has the same central limit one. Dividing the unnormalized defect by S_i gives O(i^−p_*) because H_iN_i/S_i remains bounded. The fixed multiplier κ/N_(L−1) has no effect on the error order.

Thus the exact solution is compared to C times each Z_i with one and the same C. There is no order-dependent amplitude hidden in scalar integration constants.

## 5. Zero-limit bootstrap

Let E_i=α_iψ_i+w_i. Boundedness holds because both y_i and Z_i are bounded, and α_i→0 follows from their already established central limits. The two inequalities in the reviewed proof follow immediately from the inherited block estimates and the forward defect, including its scalar and transverse components.

Assuming α_i=O(i^−ν), the stable recurrence has forcing O(i^−ν−4/3)+O(i^−p_*). The product of stable factors is bounded by exp[−c(i^(1/3)−m^(1/3))]. For m≥i/2 its summed mass is O(i^(2/3)); earlier sources and the fixed initial condition have stretched-exponential suppression. This gives w_i=O(i^−ν−2/3)+O(i^(2/3−p_*)).

The central increment then has terms O(i^−ν−4/3), O(i^−ν−5/3), O(i^−p_*−1/3), and O(i^−p_*). All are summable for ν≥0 and p_*>1. Summation backward from the known zero limit gives

α_i=O(i^−ν−1/3)+O(i^(1−p_*)).

Starting at ν=0, finitely many iterations reach ν=p_*−1. At that stage w_i actually decays faster than i^(1−p_*), and therefore ||E_i||=O(i^(1−p_*)). Equality at the capped exponent creates no logarithm: the summations stay strictly away from the harmonic exponent. This argument uses a prescribed zero central limit, not an unjustified claim that every formal approximate solution tracks the exact one.

Coordinate evaluation at the endpoint is bounded in the fixed norm. Dividing by the asymptotic endpoint scale i^−1/2 gives relative error O(i^(3/2−p_*)). The condition p_*>3/2+(M+1)/3 therefore gives the requested remainder for each fixed M. This is the only endpoint loss in the transfer argument, and it has been explicitly paid for.

## 6. Independent symbolic verification of c1 and c2

The independent script in this directory imports neither supplied calculation. It obtains the Taylor coefficients of U by coefficient division, uses the finite exact dilation jet τ=1+ε³/3+O(ε⁶), forms derivative jets in the two-dimensional differential module, and solves directly for all unknown polynomial coefficients and the new scalar. The bottom and amplitude conditions are built in by omitting constant terms of both coefficient polynomials. This is a direct linear system, not a copy of the producer's descending K_q inverse algorithm.

After inserting each new stage it checks both recurrence components, then verifies every coefficient from ε⁰ through ε⁵. The computation is symbolic in q and λ with exact rational arithmetic. It reproduces

σ_3 = k(7q+1)/6,
σ_4 = −kλ²(6q²−81q+46)/(270q),
σ_5 = −kλ(8q³−327q²+657q−92)/(810q).

It also reproduces φ_1=pf with D_1=0, and finds unique polynomial φ_2 and φ_3 in the stated gauge.

At order ε⁴, log G has zero coefficient and the h_1 contribution is −h_1/3. Thus

h_1 = −3(σ_4/k−λ²/2) = λ²(3q²+27q+23)/(45q).

The endpoint φ-series has leading εf′(0). There is no relative ε term because f″(0)=0 and φ_1′(0)=0. Stirling begins at relative ε³. Since i=kn, the independent first correction is exactly

c_(k,1)=k^−1/3 λ²(3q²+27q+23)/(45q).

At order ε⁵, log G contributes λ/3 and h_2 contributes −2h_2/3. The calculation yields

h_2=λ(4q³+309q²+531q−46)/(270q).

Endpoint Taylor expansion gives

e_2=f‴(0)/(6f′(0))+p′(0)+φ_2′(0)/f′(0)
   =λ(6q²−51q+86)/(135q).

Here A_2(0)=D_2(0)=0 implies φ_2′(0)/f′(0)=D_2′(0). Therefore

c_(k,2)=k^−2/3[h_1²/2+λ(4q³+321q²+429q+126)/(270q)],

exactly as in the reviewed proof. The ternary values follow on setting q=2; the q=1 algebraic specialization is a consistency check only and does not extend this audited analytic scope to k=2.

## 7. Endpoint conversion and exact scope

At a residue-zero endpoint, undoing normalization gives the common leading multiplier Cκ/N_(L−1) times H_iΦ_i(0), with relative remainder as above. The leading endpoint power is β−1/3. The exact conversion R_n=(qn)!q^−2qn d_(kn,0), followed by Stirling, contributes power (1−q)/2 and a full series in n^−1. Their sum is (2k−1)/3. Multiplication of these finite expansions preserves the required integer powers of n^−1/3. Coefficients are unique by the usual first-differing-coefficient argument for an asymptotic scale.

The common amplitude can, if desired, be written

C_k=(Cκ/N_(L−1)) f′(0) k^(β−1/3) √q (2π)^((1−q)/2),

using exactly the normalization adopted in this proof. Every factor is independent of truncation, and positivity follows from the inherited C>0. Its numerical value is not computed here.

No missing analytic step was found. For standalone exposition, state d_(0,0)=1 in the theorem itself; use distinct letters for requested final order and retained profile order; and explicitly subtract log k in the scalar coefficient comparison. These are clarifications, not restrictions or new hypotheses. No assertion is certified for compacted trees, signed delay transforms, DFA, uniform arity growth, or convergence of the formal infinite series.
