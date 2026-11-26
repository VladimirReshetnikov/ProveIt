# Analytic transfer investigation

## Deliverable

`notes/sparse_sampling.tex` is a complete, self-contained section ready for the main LaTeX manuscript. It contains the positive-measure interpolation theorem with exact Jensen loss, sharp mesh characterization, integer atomic sharpness example, finite-increment centering elimination, and a root-count criterion for any number field. No conjectural arithmetic bound is claimed proved.

The fourth-power scale is **already known**: Sandi Setiawan, *The Primacohedron Trace Formulation of the Riemann Hypothesis: A Guide to Reconstructing the Alpöge–Claude Proof in Lean*, v2 posted 25 November 2026, https://www.preprints.org/manuscript/202611.0738. Its abstract explicitly states that sample gaps of order X^((1+theta)/2) preserve X^theta estimates, with fourth powers reaching square-root scale. The authored exposition at https://www.trureturing.org/knowledge/node/4d72d0555a496625197ed94251fd5fced85ad597ca9e166fafe772d8a25f21e8/ also names a fourth-power theorem and provides a source-coordinate link. This second page alone does not expose the statement/proof, so the preprint is the stronger specific prior-art pointer. Do not claim invention of fourth-power sampling.

## Exact source mechanism

All repository paths below are relative to `grh/src` at commit `72fead102f663d5c7a407964a13dc0cf9d977207`.

1. `Lib/Analytic/EntireLFunction.lean:72–85`, `New.IsPolar`: measurable E, |E(v)| <= C exp(v) for v>=0, a globally meromorphic continuation Phi of its Laplace transform initially for Re(s)>2, and at most simple poles with prescribed residues for Re(s)>0. Mere numerical oscillation or generic Euler-product positivity is not this hypothesis.
2. `Lib/Analytic/Landau.lean:212–259`, `New.IsPolar.landau`: beta>0, eventual E(v)<=exp((beta−1)v), **nonnegative real part of residues at every real x>beta**, then every residue at Re(s)>beta vanishes. It does not itself know anything about Dirichlet characters; this lemma is analytically portable. A positive constant multiplier in the one-sided bound can be accommodated by rescaling E or the positive majorant. A theorem needing only a half-plane continuation is proved by the same argument but is not verbatim the globally meromorphic source signature.
3. `New/Reduction/Zeros/PrimeError.lean`: `lambdaKResidueClass` is Lambda(n)(1−chi_d(n)) supported n≡1 mod q, nonnegative; the residue is a difference of total zero multiplicities, divided by phi(q)s(1−s). A target and auxiliary zero can cancel.
4. `New/Reduction/Zeros/Criterion.lean:37–91`, `New.LFunction_ne_zero_of_primeRemainder_le`: fixes q0 divisible by 8, a coprime d0≡7 mod8, beta>1/2; **for each prime d≡d0 modq0** assumes its own eventual remainder upper bound. For a hypothetical zero rho it chooses d whose twists are simultaneously zero-free throughout beta<=Re(s), |Im(s)|<=|Im(rho)|, proves nonnegative real residues, invokes Landau, and uses nonnegative target multiplicities to conclude no target zero.
5. `Lib/Analytic/QuadraticTwist.lean:724–800`: `zero_density_quadTwist` bounds bad primes by O(X^(1−delta/2)) for beta=1/2+9delta and fixed height H; `exists_entireL_quadTwist_ne_zero` gives the box-zero-free witness. This is for Dirichlet characters over Q, not arbitrary Hecke or Artin representations.

Pinned links are obtained by concatenating:
`https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/`
with each path.

## Already covered in prior reports

The prior reports already prove a complete one-sided test for nonabelian cubic fields (`grh-lean-transfers/grh-transfers/cubic.tex`), a completely-split-prime criterion for arbitrary Galois fields and a centering-free dyadic increment (`grh-transfer/grh-transfer/report.tex`), a degree-two S3 target with positive |trace|^2(1−quadratic twist) coefficients and explicit unproved arithmetic/zero-separation hypotheses (`grh_transfer_analysis_2026-11-25/.../report.tex`), and an exact endpoint limsup in the Galois split case. Repeating those as new would be wrong. The current section extends/composes these ideas into a sparse centering-free root-count test for arbitrary non-Galois fields and makes the interpolation loss and its sharpness explicit.

## Main precise statements proved in the section

For positive locally finite mu, S(x)=integral_(1<=u<=x)(1/u−1/x)dmu and R=S−Alog x−c, A>=0:

* H(t)=S(1/t) is convex. If t=λt0+(1−λ)t1, then R(1/t)<=λR(1/t0)+(1−λ)R(1/t1)+A[logt−λlogt0−(1−λ)logt1].
* The bracket is <=(log(t0/t1))^2/8. Exact maximum for r=t0/t1 is J(r)=log((r−1)/log r)−1+log r/(r−1). This is the logarithm of the familiar Specht ratio; do not claim this scalar function is new.
* If log(x_(j+1)/x_j)=O(x_j^(−theta/2)), sampled R(x_j)<=C x_j^(−theta) implies continuous R(x)<=C' x^(−theta). On x_j=j^r the positivity-only threshold is r theta<=2.
* For fourth powers and theta=1/2, if R(n^4)<=C/n^2, C>=0, then R(x)<=(C+8A)/sqrt(x). The root suggested useful improvement uses concavity sqrt(t) on the sample-value term; the Jensen loss alone costs <=2A/n^2<=8A/sqrt(x).
* The exact interpolation gap has positive discrete sharpness: on x_j=j^r choose D_j=Alog(x_(j+1)/x_j)/(1/x_j−1/x_(j+1)) and masses D_j−D_(j−1)>0. Then R(x_j)=0 but the maximum between nodes is A J((1+1/j)^r)~Ar^2/(8j^2). Thus rtheta>2 fails in this general positivity class; critical r=4 has asymptotic normalized loss 2A. For integer r the atoms are integers. These masses are not bounded von Mangoldt weights, so this does not prove arithmetic sampling sharpness.
* If R→0, B_q(n)=4Alogq−[S((qn)^4)−S(n^4)]=R(n^4)−R((qn)^4). Its upper bound C/n² yields R(n⁴)<=C/((1−q^-2)n²) by telescoping along q^k n. The reverse direction requires a two-sided R bound (which target RH supplies); two upper bounds cannot simply be subtracted.

## Number-field specialization, beyond Dirichlet GRH

For any monic irreducible f∈Z[T], K=Q[T]/f, omit p|disc f. Let r_f(p) count roots mod p. Let S_f=sum_(p<=x)r_f(p)logp(1/p−1/x). Its main coefficient is A=1, because degree-one prime ideals have mean count one. Define finite statistic

B_f(n)=log16 −15/(16n⁴) sum_(p<=n⁴) r_f(p)logp − sum_(n⁴<p<=16n⁴) r_f(p)logp(1/p−1/(16n⁴)).

Then RH(zeta_K) iff sup_n n² B_f(n)<∞. Full proof in section: prime powers beyond the first contribute a function holomorphic in Re(s)>1/2 to the prime-only Dirichlet series; the Mellin transform of the centered remainder has residues m_rho/[rho(1−rho)] at Dedekind zeros; Landau's sign argument yields the reverse implication. In the forward direction the integrated explicit formula gives O(sqrt(x)) after ramp normalization, including exact endpoint without epsilon; then sampling and telescoping complete equivalence. This requires no Artin holomorphy hypothesis because zeta_K itself is meromorphic with only its pole at one.

Worked target changed at root request to f=T³−T−1, discriminant −23. For p≠23, root count is deg gcd(T^p−T,f) over F_p. Factorization types111,12,3 give roots3,1,0. Its Galois closure is S3, quadratic subfield Q(sqrt(−23)), with ζ_M=ζ L(χ_−23)L(ρ_std)^2 and ζ_K=ζ L(ρ_std). Under imported Dirichlet GRH, RH_K and RH_M are equivalent. For full prime-power checks the local p=23 factor is (1−23^-s)^−2, because f mod23=(T−3)(T−10)^2 and the polynomial discriminant is squarefree. Thus arithmetic input is very concrete. Establishing the uniform bound remains precisely the unsolved step; a finite table does not prove it. The source has no theorem permitting arbitrary positive Frobenius coefficients to be substituted in its arithmetic determinant construction.

## Primary sources retrieved

* Setiawan preprint above (specific fourth-power prior art), retrieved as `turn719327915view0`.
* Grenié–Molteni, *Explicit smoothed prime ideals theorems under GRH*, https://arxiv.org/abs/1312.4465, final v5 17 Sep 2015, Math. Comp. DOI 10.1090/mcom3039; retrieved `turn850601358view0`.
* Grenié–Molteni, *Explicit versions of the prime ideal theorem for Dedekind zeta functions under GRH*, https://arxiv.org/abs/1312.4463, final v4 17 Sep 2015, DOI 10.1090/mcom3031; retrieved `turn850601358view1`.
* Suzuki, *On variants of Chebyshev's conjecture*, https://arxiv.org/abs/2411.07436, v3 10 Nov 2025, Ramanujan Journal 68 article95 (2025), DOI 10.1007/s11139-025-01238-9; retrieved `turn850601358view2`. Confirms earlier one-sided weighted-Mangoldt methods, so not new generically.

Root must open any desired web references itself before using their search citation ref in the final response. The manuscript can use stable paper URLs and repository commit URLs directly.
