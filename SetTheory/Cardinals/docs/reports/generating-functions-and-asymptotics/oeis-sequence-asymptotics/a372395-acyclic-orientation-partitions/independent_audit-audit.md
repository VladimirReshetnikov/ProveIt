# Mathematical audit of the partition orientation asymptotics

Review date: 1 October 2026

Reviewed core manuscript SHA256: 7e50c1b82bc4bdacf50671a4a1ff347ba1ba6b992d80eb929d4857da19667ab8

## Conclusion

The reviewed argument establishes the stated leading amplitudes, the expansion in powers of n^(-1/2) to every fixed algebraic order, and the smooth inverse and integer-threshold conclusions for A372395 and A370613. I found no remaining mathematical defect that blocks those conclusions in the reviewed revision. The all-order assertion is a Poincare expansion; it is not a claim that its infinite series converges or captures all exponentially small terms.

The decisive estimates are the uniform quadratic profile majorant, relative-precision removal of large parts and Gamma tails, and the joint real-axis/Fourier Gaussian control. The revised proof handles the otherwise invalid step of applying a fixed-total profile estimate directly to the full generating product. It also specifies a valid logarithmic interpolation for the inverse.

This is an independent mathematical and computational audit, not a machine-checked proof or a certification of historical priority. A public manuscript should retain the precise Poincare qualification and credit the prior exact representation and logarithmic constants.

## Scope and sources

The audit covers the manuscript, the exact-value algorithm, the first-correction calculation, and the subsequently supplied second-order generator. I independently rederived the central algebra and ran different exact and numerical calculations, described below.

The sequence identities agree with the [A372395](https://oeis.org/A372395) and [A370613](https://oeis.org/A370613) entries. [Sun's arXiv version 2605.04006v1](https://arxiv.org/html/2605.04006v1), Theorem 11, supplies the logarithmic asymptotics. Section 11 explicitly leaves their prefactors and complete expansions open. This verifies the claimed relationship to that version; an exhaustive search for all subsequent literature was outside this audit.

## Exact representations and arithmetic

The chromatic-polynomial block decomposition is correct. A coloring partitions each independent part into monochromatic blocks, and distinct parts use disjoint colors. Evaluation at -1 followed by the acyclic-orientation identity gives the alternating factorial sum and the displayed Gamma integral. The normalization by t^n is valid because every extracted profile has total size n. Coefficient extraction precedes integration; no convergence of an untruncated product-integral and no positivity outside the central interval is needed.

The recurrence P_(k+1)=t(P_k-P_k') gives the stated exponential generating function and is compatible with all initial cases. The finite product permits repeated parts for eta=+1 and distinct parts for eta=-1.

The Kronecker-encoding exact algorithm is sound. Products of Bell numbers for disjoint blocks inject into the set partitions of their union. Consequently each positive polynomial coefficient is at most Bell(n), and summing profiles gives at most p(n)Bell(n). The bound p(n)<=2^n and Bell(n)<=n^n therefore bounds every intermediate dynamic-programming coefficient. The chosen digit width exceeds this bound for every n<=N. Ascending updates implement unlimited multiplicity; descending updates implement distinct parts. Alternating factorial evaluation is performed only after decoding, using exact integers.

Independent checks used ordinary coefficient arrays rather than integer packing. Every term through n=40 agrees with the supplied exact data for both sequences. A further check enumerated every orientation and tested acyclicity for every complete multipartite graph of total size at most six. Its resulting unrestricted sums are 1, 1, 3, 11, 65, 411, 3535; the distinct sums are 1, 1, 1, 5, 9, 63, 509. These agree with the polynomial method and the sequence entries.

The completed n=300 computation has been checked for exact agreement with the n=150 prefix. That is a consistency check, not a second independent n=300 enumeration.

## Roots and the quadratic majorant

Interlacing is correctly proved. At consecutive simple roots of P_k, the values of P_k-P_k' alternate signs. There is one root in each intervening gap and one beyond the largest root, giving k positive roots. Multiplication by t introduces the simple zero root. The base case is P_1=t.

The power-sum recurrence follows directly from the logarithmic derivative of P_k. At coefficient u^r, each monomial has degree at most r in k; summation therefore gives degree at most r+1. I independently generated p_1 through p_6 from this recurrence and compared their values against Newton sums extracted from the exact signed Stirling polynomials for k=1,...,12. All checks passed, including the four printed formulas.

The root estimate max(root)<=p_4(k)^(1/4)=O(k^(5/4)) is sufficient. Taking beta between 3/4 and 4/5 simultaneously makes all roots o(n) for k<=n^beta and makes the eventual far-tail exponent dominate sqrt(n).

The majorant's two key inequalities are correct:

    A^2/n <= sum k(k-1)^2/4 <= B.

The first is weighted Cauchy-Schwarz. The second has nonnegative termwise difference k(k-1)(k-2)/12. On t=nx, the logarithm of the relative upper bound is

    n[log(x)-x+1+a(1-1/x)-a^2/x^2],  a=A/n^2.

For x<=1 the a contribution is nonpositive. For x>=1 its unrestricted maximum is (x-1)^2/4. The remaining expression is strictly negative away from x=1 on [1/2,2], and its quadratic ratio has limit -1/4 at one. Thus the claimed Gaussian integral and pointwise bounds follow with an absolute positive constant.

For the signed tails, unsigned first-kind Stirling coefficients dominate second-kind coefficients because a set partition can be obtained by forgetting the cyclic ordering in each permutation cycle. This gives |P_k(t)|<=(t+M)^k for k<=M. Shifting the integral by M and using Gamma tails yields exp(-Omega(n)+O(M)) times n!. With M=o(n), this is uniformly negligible even compared with exp(-A/n), since A/n<=M/2. The resulting quadratic majorant is therefore justified for the full orientation count, not merely its positive central integral.

## Relative tail removal

For sqrt(n)log(n)<max(part)<=n^beta, the quadratic majorant reduces the problem to a positive weighted partition model. The proposed union bound is valid for geometric multiplicities and Bernoulli occupancies. With x=k/sqrt(n)>log(n), the factor exp(-x^2/2-cx) gives a tail smaller than every inverse power. The real fugacity for the distinct model may exceed one for individual part weights; this does not invalidate its finite Bernoulli factors.

For a part L>n^beta, splitting all other parts into singletons only adds edges and hence cannot decrease the number of acyclic orientations. Ordering the singleton clique and allocating the L independent labeled vertices to its gaps gives exactly (n-L)!(n-L+1)^L. The displayed product inequality yields exp(-L(L-1)/(2n)). Multiplication by p(n)=exp(O(sqrt(n))) is harmless because 2beta-1>1/2.

Gamma localization is applied after coefficient extraction, where total profile size is n. Its pointwise profile Gaussian bound can therefore be summed legitimately. The signed contribution outside [n/2,2n] is separately bounded in absolute value. These arguments establish errors smaller than every relative algebraic order without presupposing global positivity of the original integrand.

## Product expansion and the Bose endpoint

The finite positive-root remainder formula controls the logarithm of R_k to arbitrary order. For k<=sqrt(n)log(n), its denominator is bounded away from zero. All root-power coefficients are fixed polynomials, so the subsequent expansion in epsilon=1/sqrt(n) has polynomial coefficients in x=k epsilon and z. Each correction polynomial vanishes at x=0.

For eta=+1, the mth outer-logarithm derivative has a pole of order at most m at zero. Every product of m correction factors supplies at least x^m, so each f_j for j>=1 extends smoothly through zero. The corresponding remainder bounds retain the same cancellation: the first-order root remainder may be taken as epsilon^2(1+z^2)x times a fixed polynomial in x. This detail is explicitly included in the revised proof.

The only singular Euler-Maclaurin term is f_0. Subtracting -log(1-exp(-cx)) removes it exactly. The standard product expansion has the correct sign -c epsilon/24. The Bose boundary derivative is d_0'(0)=-1/(2c); f_1(0)=1/(2c). Their combined contribution to H_1 is therefore

    -c/24 - 5/(24c).

For eta=-1, f_0'(0)=-c/2 and f_1(0)=0, giving c/24. Both boundary constants and all indices and signs in the stated Euler-Maclaurin algorithm check out.

At infinity the relevant derivatives have Gaussian decay times a polynomial. Near zero their smooth extensions are uniform in a sufficiently small complex neighborhood of c. The Bose neighborhood must retain Re(c)>0; for the distinct model a sufficiently small neighborhood avoids the possible denominator zeros. Such neighborhoods exist at both real saddles.

## Fourier localization and amplitudes

On the central Gamma interval all R_k are positive. For k in any fixed nonempty interval [a sqrt(n),b sqrt(n)], the geometric or Bernoulli distributions are uniformly nondegenerate. Their characteristic-function moduli give the first arc inequality.

The second arc inequality genuinely covers the entire circle. For small theta, the quadratic estimate applies termwise. For theta sqrt(n) in a compact set bounded away from zero, the limiting integral of 1-cos(vx) is positive. For larger theta, the exact geometric-series bound and |sin(theta/2)|>=|theta|/pi on [-pi,pi] bound the cosine sum by a sufficiently small fraction of the number of consecutive indices. There is no unaddressed secondary lattice arc.

The substitution c'=c-i u sqrt(epsilon) has the correct sign. The linear phase cancels because J'(c)=-1; the quadratic phase is -V u^2/2. The Gamma density is centered at n, not n+1, and its first correction is epsilon z^3/3. Its first Stirling correction is -epsilon^2/12. These features are all reflected correctly in the manuscript and scripts.

The Gamma tilt has mean M_2/2 and contributes exp(1/2-M_3/3+M_2^2/8). Combining its integral with the Fourier factor and the endpoint factor gives exactly p_+=1 and p_-=3/4 and the two stated amplitudes.

Independent automatic-differentiation quadrature, avoiding the supplied hand-expanded cumulants, gives:

    Unrestricted
    c  =  0.764996442279544301923924458653560665247
    C  =  2.15875200565778553173735731440478257232
    A  =  0.164817523964420503961876721348383656148
    a1 = -0.307565333551633696638541971219346663091

    Distinct
    c  = -0.323697314095031871610959180763652891005
    C  =  0.905729821720199017889162500160568815679
    A  =  0.217999212918202522339360311708474398588
    a1 =  0.230950213208614981019579804666956607999

The first-correction results agree with the supplied values to the precision of the independent 40-digit computation. These are high-precision numerical checks, not certified interval enclosures.

## All-order coefficient and remainder control

The formal coefficient rule has the correct ingredients and signs. Each requested coefficient requires only finitely many root power sums, endpoint derivatives, convergent integrals, and Gaussian moments. For a_L, root powers through p_(L+2) suffice for the product expansion; only finitely many derivatives of J and H_j then enter. In powers t=sqrt(epsilon), every coefficient of odd degree is odd in U and vanishes on the symmetric Fourier interval. Thus no odd half-powers of epsilon and no extra logarithms survive.

The corrected joint-envelope argument is valid. One cannot use a bound that assumes total profile size n on the full product F(q_0,T), since that product also sums other total sizes. Instead the local product expansion gives

    log F(q_0,T)=sJ+r log(epsilon)+d+H_0(c,z)
                  +O(epsilon(1+z^2)).

Since H_0 is affine in z, multiplying by the Gamma density yields a uniform bound proportional to exp(-d_3 z^2). The cubic Gamma remainder is absorbed because epsilon log^2(n) tends to zero. The characteristic-function bound adds exp(-d_2 u^2).

For additional detail on the last Taylor-remainder step, after extracting the leading two Gaussians the remaining logarithm Q starts at sqrt(epsilon) times a fixed polynomial in u,z. On the retained logarithmic windows, every fixed finite collection of these corrections is uniformly o(1). Finite Taylor expansion of exp(Q), together with the already established polynomial bounds for the logarithmic remainders, therefore gives epsilon^(L+1) times a fixed polynomial in |u|+|z| times an integrable Gaussian. Integrating gives a constant independent of n. Expanding through the next odd half-power before integration removes that term exactly. This supplies the stated O_L(epsilon^(L+1)) error without residual powers of log(n).

The second-order generator was inspected separately. Its H_2 boundary constants agree with -f_2(0)/2-f_1'(0)/12: they are 5z/(24c)+1/48-1/(24c^2) for the unrestricted case and -1/48 for the distinct case. Its fourth-order exponential coefficient, Gamma/Stirling corrections, derivatives, and Gaussian moment evaluation are consistent with the general algorithm. Its values are

    a2 unrestricted =  0.01872663225856492421076350893...
    a2 distinct     = -0.004247066120392842830553218765...

The n=300 exact data support both second corrections. After subtracting 1+a1/sqrt(n)+a2/n and multiplying by n^(3/2), the unrestricted residual is approximately -0.00559, -0.00557, -0.00553 at n=200,250,300; the distinct residual is approximately 0.0420, 0.0418, 0.0413. This behavior is consistent with the next term, while finite data alone cannot establish the all-order theorem.

## Smooth inverse and integer envelopes

A smooth realization of the logarithmic asymptotic expansion exists by the stated cutoff construction. Correcting it with fixed-width disjoint bumps having coefficients log B(m)-G(m) is rigorous: those coefficients are smaller than every algebraic order, and fixed derivatives of the bump functions preserve this property. Exponentiation guarantees positivity; the logarithmic derivative is asymptotic to log(x), so the interpolant is eventually strictly increasing.

The inverse ansatz and the first printed terms are correct. With N(log N-1)=log Y, expanding about N gives the leading correction -C sqrt(N)/log N. At the next order, solving the residual equation gives

    -alpha0-d0/log N+C^2/(2(log N)^2)-C^2/(2(log N)^3).

At every following order the new unknown enters multiplied by log N, giving the stated polynomial dependence on 1/log N. The mean-value error conversion divides the log residual by a quantity asymptotic to log N. This proves a controlled inverse expansion for the specified class of interpolants.

The integer conclusion is appropriately limited. Eventual monotonicity of the exact sequence follows already from its leading asymptotic. For a strictly increasing exact interpolant, the threshold is its inverse rounded up. A finite asymptotic approximation only gives the two ceiling bounds; it cannot be rounded unconditionally when its error interval straddles an integer. The manuscript makes this distinction correctly.

## Reproducibility and qualification

The audit's independent test program is checks.py in this directory; its numerical and exact outputs are checks.json and checks.log. The n=300 residual calculations are recorded in convergence_300.json. The reviewed input hashes are recorded separately in reviewed_hashes.json. The test run in checks.json records the immediately preceding manuscript revision f0212f82877311956a234b181dadd8b1050e10e0e70c7f5d96e04944119a690b; the final reviewed revision changes only the computational status paragraph, and its mathematics is identical.

No external submission, website modification, or communication with the cited authors or sequence editors was made. The proof is at the level of a detailed analytic research argument. Ordinary external mathematical peer review remains appropriate before publication, and numerical decimals should not be represented as rigorously certified intervals.
