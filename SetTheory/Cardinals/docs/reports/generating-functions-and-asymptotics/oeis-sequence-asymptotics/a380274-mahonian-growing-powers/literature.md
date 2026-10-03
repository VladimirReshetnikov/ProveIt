# Literature boundary: growing powers of Mahonian coefficients

Checked 1 October 2026. This is a targeted primary-source search, not an exhaustive novelty certificate.

## Bottom line

I did not locate a primary source stating the proposed Mahonian-specific critical-window result

\[
\sum_j (M_n(j)/C_n)^{r_n}\longrightarrow
\sum_{x\in\mathbb Z+\delta}\exp[-\lambda(x^2-\delta^2)/2],
\qquad r_n/\sigma_n^2\to\lambda\in(0,\infty),
\]

with the subsequence-dependent shift \(\delta=0\) or \(1/2\), exact modal normalization \(C_n\), and the adjoining growing-power regimes. That is a plausible specific contribution to investigate, but it should be called an extension beyond the located fixed-power results, not an established first-in-the-literature theorem.

The ingredients have substantial prior art: Mahonian local limits, high-order central curvature of related q-binomial coefficients, discrete Rényi inequalities, theta-normalized discrete Gaussians, and discrete Laplace methods. The existence of theta functions or of a Gaussian-to-lattice crossover is not itself a safe novelty claim.

## Most directly relevant verified sources

### 1. Wang (2026): fixed powers, expressly excluding varying order

Xinjun Wang, *Fixed-Power Sums of Mahonian Coefficients*, June 2026 preprint, DOI [10.5281/zenodo.20548010](https://doi.org/10.5281/zenodo.20548010); [author-uploaded full text](https://www.researchgate.net/publication/406002366_Fixed-Power_Sums_of_Mahonian_Coefficients).

Theorem 1 covers each fixed real \(r>1\), including the leading equivalent and three relative correction terms through \(n^{-3}\). Remark 2 explicitly rules out an assertion for \(r=r(n)\). The introduction also disclaims uniformity near 1 or infinity. It uses local Edgeworth expansion, Poisson summation and separate tail bounds. Thus neither the fixed-order equivalent nor those three corrections should be claimed as new. The critical-window question is genuinely outside the stated theorem. The DOI landing page did not fetch, but the author's full manuscript was available on ResearchGate.

There is an earlier author-uploaded version dated May 27–28, 2026: [*Third-Order Asymptotics for Power Sums of Mahonian Coefficients and OEIS Conjectures A380274–A380275*](https://www.researchgate.net/publication/405388470_Third-Order_Asymptotics_for_Power_Sums_of_Mahonian_Coefficients_and_OEIS_Conjectures_A380274-A380275). It likewise states fixed real \(r>1\).

### 2. Canfield–Janson–Zeilberger: local limits and central curvature

E. Rodney Canfield, Svante Janson and Doron Zeilberger, *The Mahonian probability distribution on words is asymptotically normal*, [arXiv:0908.2089](https://arxiv.org/abs/0908.2089), [full text](https://arxiv.org/pdf/0908.2089).

Theorem 4.5 provides a uniform local Gaussian approximation for a broad family of q-multinomials, including ordinary permutations. More pointedly, §4.1 sharpens Fourier expansion to study the central q-binomial coefficients for multiplicities \((n,n)\). Equation (4.11), on a fixed standardized central window, gives

\[
p(k)^2-p(k-1)p(k+1)
=\{\sigma^{-2}+O(n^{-4})\}p(k)^2.
\]

Theorem 4.6 concludes central log-concavity. This is close methodological prior art for obtaining microscopic log-curvature, though the displayed calculation is for the q-binomial case and it is not a growing-power-sum theorem. Cite it if presenting a high-order Fourier/curvature proof.

### 3. Vilenkin–D'yachkov (1998): discrete entropy asymptotics

P. A. Vilenkin and A. G. D'yachkov, *Asymptotics of the Shannon and Renyi Entropies for Sums of Independent Random Variables*, **Problemy Peredachi Informatsii 34**(3) (1998), 17–31, [journal archive](https://www.mathnet.ru/eng/ppi413).

The indexed primary abstract treats both discrete and absolutely continuous i.i.d. sums; it announces leading entropy asymptotics under finite variance and cumulant expansions under higher moments, with binomial, Poisson and geometric examples. This is important prior art against a broad claim that discrete Rényi CLT expansions are new. I could verify the journal's abstract, but not retrieve the full Russian text. Accordingly, I have not verified the precise order range or any uniformity in Rényi order. Do not state that this paper excludes growing order without checking the full text. Its i.i.d. setting also differs from the Mahonian independent, non-identically-distributed sum.

### 4. Bobkov–Marsiglietti (2019): continuous Rényi CLT, including infinity

Sergey G. Bobkov and Arnaud Marsiglietti, *Asymptotic Behavior of Rényi Entropy in the Central Limit Theorem*, **High Dimensional Probability VIII** (2019), chapter 11, DOI [10.1007/978-3-030-26391-1_11](https://doi.org/10.1007/978-3-030-26391-1_11); [author PDF](https://www-users.cse.umn.edu/~bobko001/papers/2019_HDP-VIII_BM_Asymptotic.behavior.R%C3%A9nyi.entropy.pdf), [extended preprint](https://arxiv.org/abs/1802.10212).

Theorem 11.1.1 treats each given \(1<r\le\infty\), for normalized continuous i.i.d. sums under a smoothing condition. Theorem 11.1.2 gives cumulant corrections for finite orders; §11.10 treats infinity separately. The stated results are not a discrete, simultaneous \(r_n\)-versus-variance theta law. Including \(r=\infty\) as a separate endpoint should not be confused with a uniform critical-window result.

### 5. Madiman–Melbourne–Roberto: all-order discrete inequalities

Mokshay Madiman, James Melbourne and Cyril Roberto, *Bernoulli sums and Rényi entropy inequalities*, [arXiv:2103.00896](https://arxiv.org/abs/2103.00896), [full text](https://arxiv.org/pdf/2103.00896).

Theorem 3.3 bounds Rényi entropy of Bernoulli sums for every \(\alpha\in[2,\infty]\), explicitly in the variance and conjugate exponent. Theorem 3.7 is an entropy-power inequality, and §4 includes uniform variables and min-entropy inequalities. These are genuine results covering arbitrarily high orders, so it would be false to imply that high-order discrete Rényi analysis was previously absent. They are inequalities, not the Mahonian exact-modal theta asymptotic, and Mahonian sums are not Bernoulli sums.

## Theta/Gaussian boundary

### 6. Agostini–Améndola and Nielsen: the theta representation is established

Daniele Agostini and Carlos Améndola, *Discrete Gaussian distributions via theta functions*, [arXiv:1801.02373](https://arxiv.org/abs/1801.02373), published 2019, DOI [10.1137/18M1164937](https://doi.org/10.1137/18M1164937). This identifies the discrete Gaussian as a theta-normalized exponential family and studies its statistical properties. It is not a Mahonian approximation theorem.

Frank Nielsen, *The Kullback–Leibler Divergence Between Lattice Gaussian Distributions* (2022), DOI [10.1007/s41745-021-00279-5](https://doi.org/10.1007/s41745-021-00279-5), [author PDF](https://franknielsen.github.io/papers/LatticeGaussian-2022.pdf). Definition 1 writes its partition function as a Riemann theta function. Proposition 3 evaluates mixed powers of discrete exponential-family pmfs through the log-normalizer. In particular, taking the second exponent zero yields the standard identity \(\sum p_\xi^r=\exp(F(r\xi)-rF(\xi))\); this specializes to ratios of theta partition functions for lattice Gaussians. The novelty, if any, must concern proving that Mahonian coefficients enter this regime with sufficient uniformity.

### 7. Salminen–Vignat: both integer- and half-shifted Gaussian laws

Paavo Salminen and Christophe Vignat, *Probabilistic aspects of Jacobi theta functions*, [arXiv:2303.05942](https://arxiv.org/abs/2303.05942), [full text](https://arxiv.org/pdf/2303.05942), DOI [10.7146/math.scand.a-148416](https://doi.org/10.7146/math.scand.a-148416).

Definition 7.1 explicitly defines both the \(\theta_2\) law, proportional to \(e^{-c\pi(k+1/2)^2}\), and the \(\theta_3\) law, proportional to \(e^{-c\pi k^2}\). Section 7 studies their duality and identities. Thus the two candidate limiting distributions are familiar objects; their specific selection by \(n\bmod4\) in the Mahonian high-power limit is the issue to establish.

### 8. Discrete Laplace methods: classical mechanism, distinct scaling hypotheses

Ruiming Zhang, *On A Limiting Relation Between Ramanujan's Entire Function \(A_q(z)\) And \(\theta\)-Functions*, [arXiv:math/0606782](https://arxiv.org/abs/math/0606782), [full text](https://arxiv.org/pdf/math/0606782), derives theta leading terms using discrete Laplace analysis. This already demonstrates the general saddle-on-a-lattice mechanism in a different problem.

J. William Helton, Jared A. Hughes and Peter Schlosser, *The discrete Laplace asymptotic method and its application to the 3XOR satisfiability problem*, [arXiv:2509.16420](https://arxiv.org/abs/2509.16420), [full text](https://arxiv.org/pdf/2509.16420). Theorems 2.7–2.8 use a grid of scale \(1/n_k\) and exponent \(n_k\), with limiting nonsingular Hessian. Lemma 2.5 rescales to a mesh \(1/\sqrt{n_k}\) and obtains a Gaussian integral. Those hypotheses describe a dense-mesh regime; they do not directly give the critical nonvanishing-mesh theta law here.

## Suggested positioning and caution

A defensible introductory sentence is: “We study a growing-power regime beyond the fixed-power expansion of Wang, and prove a parity-sensitive theta limit at the scale \(r_n\asymp\sigma_n^2\) after normalization by the exact modal coefficient.” Add “we have not found this specific result in the literature” only as a qualified search statement.

Do not describe the outcome as a new theta identity, a new discrete Gaussian distribution, the first Rényi CLT, or a resolution of the already-covered fixed-power conjectures.

For entropy terminology, the exact elementary identity is worth emphasizing. If \(p_*=C_n/n!\) and \(T_{n,r}=\sum_j(p_n(j)/p_*)^r\), then

\[
(r-1)H_r-rH_\infty=-\log T_{n,r}.
\]

The theta factor remains order one in this rescaled entropy difference, whereas its contribution to \(H_r\) alone is only order \(1/r\). Calling this merely an entropy convergence theorem risks hiding the actual refinement.

Remaining literature uncertainty: the full Vilenkin–D'yachkov text was unavailable in this pass; the negative search result is not proof of absence of a general theorem that implies the claim. An eventual submission should check that paper and specialist references on simultaneous order/sample-size asymptotics before asserting priority.
