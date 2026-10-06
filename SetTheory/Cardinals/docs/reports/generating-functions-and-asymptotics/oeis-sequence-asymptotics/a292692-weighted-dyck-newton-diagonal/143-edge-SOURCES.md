# Public mathematical sources and scope

No external resource is needed for offline replay. The following public
sources provide the sequence definitions and relevant prior results. The
complete external papers and OEIS data are not redistributed.

1. OEIS A258219, https://oeis.org/A258219. The peak weight k+a/b defines
   the weighted-Dyck polynomial. A258220, https://oeis.org/A258220, is its
   falling-factorial triangle Delta^m p_N(0)/m!. A292692,
   https://oeis.org/A292692, is P_(2n,n). The ordinary evaluation p_n(n)
   instead belongs to A292693, https://oeis.org/A292693.
2. OEIS A292186, https://oeis.org/A292186. This is the classical rooted
   connected four-regular-map sequence V_a. Its recurrence, Riccati equation,
   map interpretation, and leading factorial asymptotic are prior art.
3. R. J. Martin and M. J. Kearney, An exactly solvable self-convolutive
   recurrence, Aequationes Mathematicae 80 (2010), 291-318,
   https://arxiv.org/abs/1103.4936. Under the shifted convention V_a=u_(a+1),
   the parameters are S(4,-6,1). Section 2.4, Theorem 3 supplies the classical
   factorial leading constant. Its fixed-parameter result does not by itself
   give a growing-deficit Newton extraction.
4. L. Ciobanu and A. Kolpakov, Free subgroups of free products and
   combinatorial hypermaps, Discrete Mathematics 342 (2019), 1415-1433,
   https://doi.org/10.1016/j.disc.2019.01.014 and
   https://arxiv.org/abs/1708.03842. Theorem 4.1 and Examples 4.4 and 5.3
   identify the hypergeometric logarithmic derivative, rooted-map sequence,
   and factorial asymptotics.
5. L. C. Hsu and P. J.-S. Shiue, A unified approach to generalized Stirling
   numbers, Advances in Applied Mathematics 20 (1998), 366-384,
   https://doi.org/10.1006/aama.1998.0586. Its connection coefficients give
   Q_(N,m)/gamma_N=S(N,m;-2,1,1). Theorem 5 and the fixed-r specialization
   in Section 5.2 cover near-diagonal asymptotics with deficit o(sqrt(m)).
   Thus the auxiliary leading Q estimate is classical. The nonlinear
   ordinary coefficients of p_N require the separate comparison proof.
6. R. Arratia and S. DeSalvo, Completely effective error bounds for Stirling
   numbers of the first and second kinds via Poisson approximation,
   https://arxiv.org/abs/1404.3007. The paper discusses earlier Moser-Wyman
   estimates and effective near-diagonal bounds. This concerns the Stirling
   conversion factor rather than the nonlinear coefficient comparison.
7. NIST Digital Library of Mathematical Functions, Section 5.11,
   https://dlmf.nist.gov/5.11, especially Eq. 5.11.8 and Section 5.11(ii).
   Fixed-shift Gamma expansions supply the Bernoulli-polynomial normalization
   in the constructive profile algorithm, with a fixed-order remainder.

Reports 141 and 142 are included unchanged as source/PDF pairs. Report141,
A weighted Dyck path Newton diagonal (October 2, 2026), supplies the exact
path-to-recurrence interpretation. Report142, All orders for the weighted
Dyck Newton diagonal (October 2, 2026), supplies only the explicit
compact-interior coefficient functions quoted for comparison. Its remainder
is uniform on fixed compact interior sets; it is not asserted to hold at a
moving boundary.

The substantive statement of Report143 is the nonlinear all-a,n comparison
and the resulting joint upper-edge Newton profile with explicit relative
bounds. A bounded primary-source check did not locate this comparison or an
equivalent quantified theorem for the defining nonlinear recurrence. This
is not an exhaustive worldwide novelty or priority claim. Classical
identifications and auxiliary asymptotics are explicitly credited.

The exact finite-index bounds include q<=floor(N/2). The relative profile
limit requires q=o(sqrt(N)). Profile expansions are proved at each fixed
order; they are not all-orders finite-N expansions. To separate the last
profile correction at order K>=2, the present error bound suffices when
q=o(N^(1/(K+1))). The inverse concerns only the one-variable F_q profile and
retains uncertainty inside ceilings. Effective numerical onset constants,
a growing truncation order, a global moving-ratio bridge, and cancellation
of finite-N corrections are not established.
