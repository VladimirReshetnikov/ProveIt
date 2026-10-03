# Independent mathematical and source review

Date: October 2, 2026

Reviewed document: `article.tex`, **Fixed Forbidden Distances in Involutions: Uniform expansions and two Gaussian sectors**

Reviewed SHA256: `eca7101832e9a1c40108a808c632775e6dc6c0b575dc3c47fe10ac086e5c23cb`

## Verdict

**PASS for the stated mathematical results and bounded historical framing. No required mathematical or attribution revision was identified.**

This is a fresh integrated review of the complete article source, including the uniform remainder proof, its Gaussian-window lemma, fixed-distance stabilization, weighted errors, and all three inversion conventions. The displayed universal coefficients were independently recomputed through order six. The verdict concerns the source identified above; subsequent changes require comparison against that source.

This review is a mathematical assessment supported by exact symbolic computation. It is not formal proof-assistant verification, a certificate of worldwide priority, or a certification of explicit finite-input error constants. PDF layout, archive installation, and the final portable replay are separate reproducibility checks, not part of this source-review verdict.

## Exact identities and the uniform theorem

The marking identity is a finite sum: a selected forbidden matching of size k has exactly I_(n−2k) completions. Gaussian moments therefore give the stated shifted identity without an exchange of infinite sums. Pairing the nonzero real matching roots gives the correct factorizations of both the signed matching polynomial and its marked counterpart. The normalization a_j = (sum of all 2j-th root powers)/(2jn) is consistent with the logarithmic matching enumerator. In particular, a_1 = m/n and n a_2 = m/2 + W are correct.

The conservative common root bound covers maximum degrees zero and one. The path-tree interpretation is correctly distinguished from ordinary closed walks in the original graph. A returning walk of length 2j in that rooted tree cannot reach depth greater than j, which proves the required finite-radius locality.

The factorial-moment domination holds for the entire feasible range of k. Counting ordered disjoint edges gives the product of Δ(n−2i)/2; monotonicity and the involution recurrence give I_N ≥ N I_(N−2), canceling those factors. The convention beyond the matching range and the k = 0 case are handled explicitly. The resulting entire-function bound does not rely on a fixed-k approximation.

The main theorem has the appropriate quantifiers: Δ, the requested finite order J, and the complex radius R are fixed; the constants are independent of the graph on n vertices. Each a_j is evaluated at the actual graph for that n. The theorem assumes neither convergence nor an asymptotic expansion of these graph statistics. Consequently it does not mistakenly turn an arbitrary graph sequence into a constant-coefficient expansion.

## Local expansion and global control

The saddle normalization is correct. With y = √n + u, the reference Gaussian has mean σ/2 and variance 1/2, and the extracted scale is

L_n^σ = 2^(−1/2)(n/e)^(n/2) exp(σ√n − 1/4 − a_1).

On the stated window |u| ≤ n^(1/12), the logarithmic series is valid because |εu| ≤ n^(−5/12), and the nonconstant exponent is O(ε(1 + |u|³)) = o(1). The Taylor remainder of the logarithm after division by ε² is O(ε^(J+1)|u|^(J+3)). Retaining root moments through j = floor((J+2)/2) suffices: the first omitted power is at least ε^(J+1), for either parity of J, and the remaining root sum is geometrically bounded. The retained rational terms have polynomial-envelope Taylor remainders.

Both the exact local exponent and its finite truncation are uniformly small on the window. Exponentiation thus preserves an O(ε^(J+1)(1 + |u|^N)) envelope for a fixed N depending on J. Gaussian integration gives the claimed uniform integrated error. The same argument remains valid for a_j replaced by (−1)^j a_j w^j on a fixed complex disk. No derivative of a moving graph statistic is taken.

Outside that window, the proof uses global inequalities rather than the local logarithmic series. Strong concavity controls the exterior Gaussian tails; the region below √n/2 has the exponentially decaying comparison (e/4)^(n/2) times subexponential factors. For complex marking, the bound |F_(G,w)(y)| ≤ (y² + RB²)^(n/2) correctly includes zero-root factors. It supplies both central and exterior control uniformly on the disk. Division by the unrestricted involution expansion is safe because its normalized leading term is one.

The polynomial generator follows from collecting powers of ε in the local exponent. The stated maximum moment index and degree-at-most-h bound in w are valid. An independent calculation using integer partitions to exponentiate the direct local series, and a closed Gaussian moment formula to integrate it, reproduced all sector and PGF coefficients through order six. This also verifies the displayed D_1, D_2, D_3 and P_1, P_2, P_3. Independent substitution and formal logarithms verify the fixed-distance avoidance coefficients through n^(−3/2) and all three displayed γ coefficients.

## Sectors and weighted probability errors

The exact split has the correct parity sign:

A_G = K_G^+ + (−1)^n K_G^− + C_G.

Each exterior integral is nonnegative. On the central interval, each paired factor has magnitude at most B², giving |C_G| ≤ B^n. Its ratio to either sector scale is smaller than every fixed inverse power of n. Reflection of the centered Gaussian and the parity of each coefficient give the factor σ^h in the separate expansions.

The article correctly distinguishes two separately controlled integrals from recovery of the smaller sector by a finite truncation of the total count. A positive-sector algebraic truncation error is larger than the negative sector. The cutoff dependence of the exact integrals is also disclosed; their algebraic coefficients remain unchanged under another fixed common root bound.

The weighted coefficient argument is sound. For any fixed q ≥ 0, choose a circle |z| = S > q and apply the complex theorem with w = z−1. Cauchy's estimate gives an ε^(J+1) S^(−ℓ) coefficient bound, which is summable after multiplication by q^ℓ. The approximation is explicitly signed. The stated moving-parameter Poisson consequence is valid, and the article does not infer a smooth all-orders total-variation expansion across absolute-value branch changes or integer Poisson means.

## Fixed distances and inversion

The connected-support argument proves exact stabilization, rather than extrapolating a numerical pattern. A degree-j logarithmic monomial has at most j support edges. A disconnected incompatibility support contributes zero; a connected support has span at most j max(S). Each normalized pattern therefore contributes its fixed coefficient times n minus its span when n > j max(S). Thus n a_j is exactly affine in n, equivalently a_j = α_j + β_j/n, in the stated range. Substitution yields genuine constant-coefficient finite-order expansions for every fixed finite distance set.

The first path-power ratio and marked-PGF corrections agree with this substitution. The r = 0 and r = 1 specializations of the logarithmic coefficients also agree with the unrestricted and adjacent cases.

All inverse claims are correctly restricted to fixed r:

- The smooth asymptotic root has node error O(n^(−(J+1)/2)/log n), by the eventual derivative bound for L_(r,J)
- The Lambert-W seed solves the leading equation exactly, and the stated Newton error recurrence yields the displayed exponents; ceil(log₂(J+3)) updates suffice, including the equality case because of the extra logarithmic decay
- Monotonicity of the actual sequence follows from the terminal-fixed-point embedding and an additional allowed transposition for n ≥ r+2; the strict inequalities used to obtain the two-ceiling enclosure are valid
- The exact log-linear convention preserves endpoint logarithmic errors, and its slopes have a common lower bound of order log x, including across knots; the resulting inverse bound is valid

The smooth/chord discrepancy of order 1/(x log x) is correctly retained as an obstruction to identifying those conventions at arbitrary order. The article does not claim an unconditional single-ceiling formula, or numerically certified thresholds without effective constants.

## Historical scope

The article’s attribution is appropriately strong and specific. In particular:

- It credits the shifted Gaussian duality itself to Godsil through Lass, rather than presenting the shift as a new device. Lass’s author manuscript explicitly attributes the displayed shifted integral to Godsil’s Theorem 2.4 and restates the duality in its main text. [Lass author manuscript](https://math.univ-lyon1.fr/homes-www/lass/articles/pub4godsil.pdf)
- It credits matching-root and walk-based structural expansion methodology to its classical sources
- It identifies McLeod’s thesis as especially close prior work and states its substantial high-order content. The inspected printed pages 80–81 confirm the perfect-matching, k-regular setting, the k = O(n^(1−δ)) range, explicit corrections through n^(−5), the O(k^6/n^6) remainder in the exponent, and the structural walk/subgraph terms. These results are not reduced to a leading equivalent. [McLeod thesis](https://hdl.handle.net/1885/150677)
- It credits the selected-pair formula and adjacent avoidance limit to Ganjtabesh–Steyaert, recognizes the recorded Kotesovec first absolute correction, and identifies A239144 as an existing counting family. [Ganjtabesh–Steyaert](https://match.pmf.kg.ac.rs/electronic_versions/Match66/n1/match66n1_399-414.pdf), [A170941](https://oeis.org/A170941), [A239144](https://oeis.org/A239144)

The bounded literature materials and the relevant primary passages support these statements. The article preserves the essential distinctions between perfect matchings and unrestricted involutions, between finite high-order corrections and a theorem parameterized by every fixed order, and between a negative search result and a novelty proof. Its caveats concerning the final McLeod journal text and the full Wanless paper are necessary and remain explicit. No worldwide-priority claim is made or certified here.

## Reproducibility scope and limitations

The exact symbolic checks performed for this review support the displayed coefficients and the order-six generator. The article’s numerical table was checked against its supplied high-precision reference values, including the sign and scaling of the order-six residual. The descriptions of the 120 finite-graph comparisons, 1,199 factorial-moment cases, stabilization checks, inverse tests, and separate-sector tests were compared with their supporting scripts or recorded results; this review does not represent a fresh execution of every one of those computations.

The final portable archive and its end-to-end replay should be assessed using their own run results. Neither numerical tests nor this review replace the analytic proof of uniformity. The PASS verdict does not extend to growing degree or growing forbidden range, convergence of the infinite formal series, effective finite-input error constants, arbitrary-graph inverse theorems, or numerical extraction of the exponentially smaller sector from a finitely truncated total asymptotic expansion.
