# Literature Reconnaissance for the ProveIt Alaoglu–Erdős Program: New Works and Research Directions

## TL;DR
- The single most actionable near-term win is replacing the team's per-value interval certificates with a uniform criterion built from **Qiang Wu's linear-independence measure μ(1, log 2, log 3) ≤ 7.6155** (Math. Comp. 72 (2003) 901–911, verbatim: "µ(1, log 2, log 3) ≤ 7.6155 (replacing 7.616) with the exponents 0.55255, 0.70451,…") and the **Laurent–Mignotte–Nesterenko two-logarithm bound** (log|b₁log2+b₂log3| ≥ −C(log B)²); these are established theorems directly usable now, but they constrain θ = log₂3 only, not the unknown generator β = log₂M.
- The deepest structural matches to the team's own reformulations are three bodies of literature they do not cite at all: **Bombieri–Cohen effective Diophantine approximation on 𝔾_m** (the archimedean+p-adic interpolation-determinant framework that is exactly the Priority-A "p-adic amplification" template), **Roy's small-value-estimate program** on 𝔾_a×𝔾_m (which targets the precise four-exponentials/Schanuel frontier), and the **×2×3 rigidity literature** (Furstenberg / Bourgain–Lindenstrauss–Michel–Venkatesh / Shmerkin–Wu); each is a technique needing adaptation, not a plug-in.
- No discovered work closes the "one-logarithm deficit" or defeats the exponentially-shrinking-target obstruction; the conjecture remains genuinely open and every route inherits the rank-two-to-rank-one collapse, but three formalization targets — the now-completed **Gelfond–Schneider Lean 4 development (Karatarakis–Wiedijk)**, the five-/strong-six-exponentials theorems, and Wu-type measures — have strong cost/benefit.

## Key Findings

1. **Effective measures for log 2, log 3 (Priority H) are the ripest fruit.** The current sharpest linear-independence measure for the triple is μ(1, log 2, log 3) ≤ 7.6155 (Wu 2003, improving Rhin's 7.616). For the single logarithm, μ(log 3) ≤ 5.1163051 (Wu–Wang 2014, improving Salikhov's 5.125; both improve Rhin's 1987 value of 8.616 for log 3). Equivalently, γ = 5.117 is admissible as the irrationality exponent for ϑ := (log 2)/log 3 (de la Bretèche–Stoll–Tenenbaum, quoting Wu–Wang). For two-logarithm forms, Laurent–Mignotte–Nesterenko (1995) and Laurent (2008) give explicit log|Λ| ≥ −C(log B)² with C on the order of a few tens. These yield a uniform polynomial zero-free criterion for θ = log₂3 but say nothing about the generator β = log₂M for unknown M — exactly the limitation the team already flagged.

2. **Bombieri–Cohen 𝔾_m is the missing template for Priority A.** Their two-part "Effective Diophantine approximation on 𝔾_m" (Ann. SNS Pisa 1993, 1997) combines archimedean and non-archimedean interpolation determinants (the equivariant Thue–Siegel principle) to extract effective irrationality measures for high-order roots — the only non-Baker route to effective results on the multiplicative group. This is the closest existing realization of "choose rows/columns so a nonzero integer determinant has large p-adic valuation while archimedean size stays controlled."

3. **Roy's small-value-estimate program is the state-of-the-art assault on the exact frontier.** Roy's arithmetic criterion (Acta Arith. 2001) is provably *equivalent* to Schanuel; his subsequent small-value estimates for 𝔾_a, 𝔾_m, and 𝔾_a×𝔾_m, and the Nguyen–Roy (2016) dimension-two estimate, are the deepest partial progress toward the four-exponentials/Schanuel circle. Roy's Strong Six Exponentials Theorem (J. Number Theory 1992) is the correct object to formalize for Priority G.

4. **The ×2×3 rigidity literature is conceptually adjacent but blocked by the shrinking-target mismatch.** Bourgain–Lindenstrauss–Michel–Venkatesh give effective density with density gap only of order (log log L)^(−κ₁₂) (verbatim: "the set X3.d⁻¹.L − X3.d⁻¹.L is 2κ₁₁(log log L)⁻ᵏ¹² -dense"); Shmerkin and Wu resolved Furstenberg's intersection conjecture. None can force visits to targets shrinking like M^(−k); the mismatch is, as the team suspects, essentially fatal for a direct application, but the *effective* BLMV rate is the only quantitative handle and deserves a documented compatibility check against the kernel-verified equidistribution module.

5. **Pila–Wilkie sharpenings exist but lack denominator-support sensitivity (Priority C).** Binyamini–Novikov(–Zak) proved Wilkie's conjecture (polylog counting) for restricted elementary/Pfaffian functions, and the Cluckers–Comte–Loeser / Binyamini non-archimedean point-counting gives p-adic analogues. Boxall–Jones–Schmidt count algebraic points with bounds polynomial in log height and combine this with p-adic methods. But none is sensitive to *which primes* divide the denominators, which is precisely what the team's compact-arc reformulation needs.

6. **S-unit / gcd technology yields finiteness, not nonexistence.** Bugeaud–Corvaja–Zannier ("Let a,b∈ℤ, a,b≥2, multiplicatively independent, ε>0. For sufficiently large n, log gcd(aⁿ−1, bⁿ−1) ≤ εn") and the Corvaja–Zannier subspace-theorem machinery confirm the team's diagnosis that S-unit methods cannot convert their 3-term-progression equation into nonexistence.

## Details by Thematic Area

### 1. Four exponentials neighborhood; Roy's small-value program
- **D. Roy, "Matrices whose coefficients are linear forms in logarithms," J. Number Theory 41 (1992) 22–47** (DOI 10.1016/0022-314X(92)90081-Y). Already cited by the team, but the content worth foregrounding is the **Strong Six Exponentials Theorem**: for {x₁,x₂} and {y₁,y₂,y₃} each Q̄-linearly independent, the six products xᵢyⱼ cannot all lie in L* (the Q̄-span of 1 and logarithms of algebraic numbers), hence some e^{xᵢyⱼ} is transcendental. The Strong Four Exponentials *Conjecture* (the 2×2 version) is what would settle Alaoglu–Erdős. Established theorem (six-case); the four-case is conjectural.
- **D. Roy, "An arithmetic criterion for the values of the exponential function," Acta Arith. 97 (2001) no. 2, 183–194** (DOI 10.4064/aa97-2-6). NOT in the team's bibliography. Roy constructs a small-value/approximation criterion on 𝔾_a×𝔾_m and proves it *equivalent* to Schanuel's conjecture (equivalence in both directions). It reframes transcendence (td ≥ n) as the non-existence of anomalously good integer-polynomial approximations — of an integer polynomial P_N with bounded degrees and coefficients ≤ e^N — to the derivatives D^k P_N at the lattice of points (Σⱼmⱼxⱼ, Παⱼ^{mⱼ}) on the one-parameter subgroup of 𝔾_a×𝔾_m, where D = ∂/∂X₀ + X₁∂/∂X₁. **Type (ii), technique needing adaptation**: this is exactly the "integer polynomial small on a group orbit" language the team's determinant results already use, and is directly relevant to Priorities A and F.
- **D. Roy, "Small value estimates for the multiplicative group," Acta Arith. 135 (2008) 357–393** (DOI 10.4064/aa135-4-5); **"Small value estimates for the additive group," Int. J. Number Theory 6 (2010) 919–956** (arXiv:0708.2307); **"A small value estimate for 𝔾_a×𝔾_m," Mathematika 59 (2013) 333–363.** This trilogy generalizes Gelfond's algebraic-independence criterion to sequences of polynomials taking small values on large subsets of a subgroup — the natural home for the team's "candidates as small-value nodes" picture. **Type (ii).**
- **N. A. V. Nguyen and D. Roy, "A small value estimate in dimension two involving translations by rational points," Int. J. Number Theory 12 (2016) 1273–1293** (arXiv:1412.5163). Best-possible (for the parameter regime σ ≥ 3/2) small-value estimate on 𝔾_a×𝔾_m: from an integer polynomial P_D (deg ≤ D, ‖P_D‖ ≤ e^{D^β}) taking values ≤ e^{−D^ν} at translated orbit points (ξ+ir, ηs^i), one concludes ξ, η are algebraic and the values vanish. Its Corollary 1.2 concludes Q-linear dependence of 1, ξ₁,…,ξ_ℓ. A partial, sharp step toward Schanuel, not a resolution. **Type (ii).**
- **M. Waldschmidt, "The Four Exponentials Problem and Schanuel's Conjecture," in Mathematics Going Forward (LNM 2313, 2023).** Already cited, but note its explicit statement of the p-adic four/six exponentials open problems and the Leopoldt-conjecture connection, which the team may wish to mirror for a p-adic amplification narrative. (The survey opens with precisely the Alaoglu–Erdős question: "Let t be a real number such that 2ᵗ and 3ᵗ are integers; does it follow that t is a nonnegative integer?")
- **L. A. Butler, "Some cases of Wilkie's conjecture," Bull. London Math. Soc. 44 (2012) 642–660.** NOT cited (the team cites Butler's 2017 Ramanujan J. paper). Shows some Wilkie-conjecture cases are equivalent to real forms of the three/four exponentials conjectures — a direct bridge between Priority C (counting) and the four-exponentials core. **Type (ii/iii).**

### 2. Products of logarithms; algebraic independence
- The team's log-product independence wall (the vanishing of D = Σ_p (m_p log 3 − a_p log 2) log p) is a statement about ℚ-linear independence of {log p · log q}. The relevant unconditional frontier is **G. Diaz's large-transcendence-degree results**: for β algebraic of degree d ≥ 2 and α ≠ 0 algebraic, among α^β,…,α^{β^{d−1}} at least ⌈(d+1)/2⌉ are algebraically independent (see M. Waldschmidt, "Report on some recent advances in Diophantine approximation," arXiv:0908.3973, Theorem 57, attributing the sharpest result to Diaz). This is "half" of what is expected from Gelfond's conjecture and does not reach products of two logarithms, but is the closest unconditional algebraic-independence technology. **Type (iii) for this problem.**
- **Nesterenko's linear-independence criterion** and the Gelfond–Philippon–Nesterenko method underlie all of the above; the team should cite Nesterenko's criterion as the tool that would upgrade a small-value estimate into an independence statement. No existing lower-bound technology handles linear/bilinear forms whose coefficients are themselves logarithms — corroborated by every survey consulted, confirming the team's assessment.

### 3. Effective irrationality/independence measures (Priority H)
- **Q. Wu, "On the linear independence measure of logarithms of rational numbers," Math. Comp. 72 (2003) 901–911** (DOI 10.1090/S0025-5718-02-01442-4). μ(1, log 2, log 3) ≤ 7.6155 (with optimizing exponents 0.55255, 0.70451); also ν(1,log2,log3,log5) ≤ 15.27049 and ν(1,log2,log3,log5,log7) ≤ 256.865. Method: polynomials of small norm on real intervals via integer transfinite diameter + Müntz–Legendre + LLL, applied to Rhin-type integrals. **Established theorem, directly usable — the single best import for Priority H.**
- **G. Rhin, "Approximants de Padé et mesures effectives d'irrationalité," Progr. Math. 71 (1987)** — the 7.616 predecessor for the triple (and the 8.616 predecessor for log 3 alone). Historical context.
- **V. Kh. Salikhov, "On the irrationality measure of ln 3," Dokl. Math. 76 (2007) 955–957** (μ(log 3) ≤ 5.125) and **Q. Wu & L. Wang, "On the irrationality measure of log 3," J. Number Theory 142 (2014) 264–273** (μ(log 3) ≤ 5.1163051; equivalently γ = 5.117 admissible for ϑ = (log 2)/log 3, per de la Bretèche–Stoll–Tenenbaum, arXiv:1806.09670). **Established.**
- **M. Laurent, M. Mignotte, Y. Nesterenko, "Formes linéaires en deux logarithmes et déterminants d'interpolation," J. Number Theory 55 (1995) 285–321** (DOI 10.1006/jnth.1995.1141) and **M. Laurent, "Linear forms in two logarithms and interpolation determinants II," Acta Arith. 133 (2008) 325–348.** Explicit log|b₁log2+b₂log3| ≥ −C(log B)² with C a few tens (parameter-dependent, ≈25.2–30.9). **Established; formalizable in principle.**
- **N. Gouillon, explicit two-logarithm bounds** (log B dependence) and the p-adic analogue **K. C. Chim, "Lower bounds for linear forms in two p-adic logarithms," J. Number Theory (2025)**, improving Bugeaud–Laurent's (log B)² to log B. **Established; directly relevant to Priority A because it gives explicit p-adic size for exactly the |α₁^{b₁} − α₂^{b₂}|_p quantities the team wants to amplify.**
- **Y. Bugeaud & M. Laurent, "Minoration effective de la distance p-adique entre puissances de nombres algébriques," J. Number Theory (1996)** and **Y. Bugeaud, "Linear forms in two m-adic logarithms," Compositio Math. (1999).** The p-adic two-logarithm workhorses. **Established.**
- **K. Yu, p-adic Baker theory (series, 1990s–2000s).** General p-adic linear forms; larger constants than Bugeaud–Laurent for two logs but general n. Context.

### 4. Interpolation determinants with p-adic amplification (Priority A)
- **E. Bombieri, "Effective Diophantine approximation on 𝔾_m," Ann. Scuola Norm. Sup. Pisa 20 (1993) 61–89** and **E. Bombieri & P. B. Cohen, "Effective Diophantine approximation on 𝔾_m, II," ibid. 24 (1997) 205–225**; plus the elementary account **Bombieri–Cohen, "An elementary approach to effective Diophantine approximation on 𝔾_m," LMS Lecture Notes 303 (2003) 41–62.** These combine archimedean and non-archimedean interpolation determinants (the equivariant Thue–Siegel principle, based on refined constructions of "anchor pairs") and are the *only* non-Baker route to effective 𝔾_m results. **Type (ii), highest-priority technique import for Priority A.**
- **"Local positivity and effective Diophantine approximation," Abh. Math. Sem. Hamburg (2022)** (DOI 10.1007/s12188-022-00260-8) — a modern reworking using measures of local positivity of divisors + Faltings's version of Siegel's lemma instead of a zero estimate. **Type (ii/iii).**
- **V. Dimitrov, F. Calegari, Y. Tang et al., "Arithmetic Holonomy Bounds and Effective Diophantine Approximation," ICM 2026 proceedings (SIAM/epubs 10.1137/25M1806776) / CaltechAUTHORS.** A "multivalent continuation" of the hypergeometric Thue–Siegel–Baker method giving effective irrationality measures for high-order roots via a Dirichlet argument of Bombieri; relevant to sharpening the archimedean side of a determinant. **Type (iii), recent.**
- **M. Laurent, interpolation-determinant papers (Acta Arith. 66 (1994) 181–199; 133 (2008)).** The determinant method itself, in the form the team already uses. **Established.**

### 5. Counting points on transcendental curves with denominator constraints (Priority C)
- **G. Binyamini & D. Novikov, "Wilkie's conjecture for restricted elementary functions," Ann. of Math. 186 (2017) 237–275**, and **G. Binyamini, D. Novikov, B. Zak, "Wilkie's conjecture for Pfaffian structures," Ann. of Math. 199 (2024) 795–821.** Polylog (log H)^κ counting for restricted elementary / Pfaffian sets. **Type (ii)** — the team's arc {(2^t,3^t)} is a restricted exponential curve, so these bounds apply *in shape* and give (log H)^κ, still far above the o(H)-with-synchronized-denominators the team needs.
- **G. Binyamini, "Point counting for foliations over number fields," Forum Math. Pi; G. Binyamini, R. Cluckers, D. Novikov, "Point counting and Wilkie's conjecture for non-archimedean Pfaffian and Noetherian functions," Duke Math. J.**; **"Counting rational points on transcendental curves in valued fields," arXiv:2506.19411 (2025)**; **R. Cluckers, G. Comte, F. Loeser, "Non-archimedean Yomdin–Gromov parametrizations and points of bounded height," Forum Math. Pi 3 (2015).** The non-archimedean / valued-field counting analogues — the closest existing machinery to *denominator-support-sensitive* counting. **Type (ii/iii): the most promising place to look for a Priority-C refinement.**
- **G. Boxall & G. Jones, "Algebraic values of certain analytic functions," IMRN 2015 (4) 1141–1158**; **"Rational values of entire functions of finite order," IMRN 2015 (22) 12251–12264**; **G. Boxall, G. Jones, H. Schmidt, "Rational values of transcendental functions and arithmetic dynamics," J. Eur. Math. Soc. 24 (2022) 1567–1592** (arXiv:1808.07676). Bounds polynomial in log height and degree; the last combines archimedean counting with *p-adic methods* — a concrete model for merging counting with valuation data. **Type (ii).**
- **P. Habegger, "Diophantine approximations on definable sets," Selecta Math. 24 (2018) 1633–1675**; **Habegger–Jones–Masser, "Six unlikely intersection problems in search of effectivity," Math. Proc. Camb. Phil. Soc. 162 (2017) 447–477.** Unlikely-intersection tools potentially repurposable. **Type (iii).**
- Honest assessment: no cited counting theorem is sensitive to the *arithmetic* of denominators (which primes, synchronized exponents ⌊kβ⌋). The team's required statement — a compact transcendental arc of nonzero curvature carries o(H) points of height ≤ H whose first coordinate's denominator is a power of 2 and second a power of 3 — is not implied by any of these and would be a genuinely new theorem. Binyamini's non-archimedean program is the group closest to the needed tools.

### 6. ×2 ×3 rigidity and dynamics (not in the team's report at all)
- **J. Bourgain, E. Lindenstrauss, P. Michel, A. Venkatesh, "Some effective results for ×a×b," Ergodic Theory Dynam. Systems 29 (2009) 1705–1722** (DOI 10.1017/S0143385708000898). The only *effective* Furstenberg-type density result; the density gap is of order (log log L)^(−κ₁₂), far too weak for exponentially shrinking targets. **Type (iii).**
- **H. Furstenberg (1967) orbit-closure theorem**; **D. Rudolph / A. Johnson measure rigidity**; **M. Einsiedler & E. Lindenstrauss, "Rigidity properties of ℤ^d-actions on tori and solenoids," ERA-AMS 9 (2003) 99–110.** Foundational; qualitative. **Type (iii).**
- **P. Shmerkin, "On Furstenberg's intersection conjecture, self-similar measures, and the L^q norms of convolutions," Ann. of Math. 189 (2019) 319–391**, and **M. Wu, "A proof of Furstenberg's conjecture on the intersections of ×p- and ×q-invariant sets," Ann. of Math. 189 (2019) 707–751**; plus **H. Yu, "An improvement on Furstenberg's intersection problem."** Resolve the intersection conjecture; concern Hausdorff dimension of intersections, not orbits hitting shrinking targets. **Type (iii).**
- **"Quantitative Density under Higher Rank Abelian Algebraic Toral Actions," arXiv:1004.0035** generalizes BLMV to unit-group actions with number-theoretic invariants governing the rate. **Type (iii).**
- Honest verdict: the mapping is conceptually attractive (the team's (U_k,V_k) = (2^{kβ},3^{kβ}) is a ×2×3-flavored orbit) but the target-width mismatch (M^{−k}) is fatal for a direct application; metric/dimension results say nothing about a *single* orbit with special Diophantine β. The one usable item is the *effective* BLMV rate, which should be recorded as the best available quantitative equidistribution and cross-checked against the team's kernel-verified equidistribution module — with the expectation that it confirms, rather than defeats, the shrinking-target obstruction.

### 7. S-unit equations, gcd bounds, multiplicative dependence
- **Y. Bugeaud, P. Corvaja, U. Zannier, "An upper bound for the G.C.D. of aⁿ−1 and bⁿ−1," Math. Z. 243 (2003) 79–84** (MR1953049). Precise statement: for a,b ≥ 2 multiplicatively independent and ε > 0, log gcd(aⁿ−1, bⁿ−1) ≤ εn for all sufficiently large n; sharp in that a lower bound exp(c·n/log log n) holds for infinitely many n. **Established** — confirms only finiteness/subexponential control, matching the team's wall (d).
- **P. Corvaja & U. Zannier, "A lower bound for the height of a rational function at S-unit points," Monatsh. Math. 144 (2005) 203–224**; **"Finiteness of integral values for the ratio of two linear recurrences," Invent. Math. 149 (2002) 431–451.** Subspace-theorem gcd machinery. **Established (finiteness).**
- **J.-H. Evertse & K. Győry, "Unit Equations in Diophantine Number Theory" (Cambridge, 2015)** and effective S-unit solving; **C. Stewart & K. Yu, abc-type bounds.** Give *effective* but only *finiteness*-type conclusions, confirming the team's diagnosis that S-unit theory cannot supply the exponential-in-q divisibility lower bounds the rational-approximation route needs.

### 8. Integer-valued entire functions (Pólya–Gelfond–Pisot)
- **Pólya (1915)**: 2^z is the smallest transcendental entire function integer-valued on ℕ (limsup R^{-1}log|f|_R > 0). **Gelfond**: analogue on geometric progressions {aⁿ}. See **M. Waldschmidt, "Auxiliary functions in transcendence proofs," arXiv:0908.4024, §2.2** and **"Integer valued entire functions"** (Ramanujan-2020 note).
- **J.-P. Bézivin, "Sur les points où une fonction analytique prend des valeurs entières," Ann. Inst. Fourier 40 (1990) 785–809** (DOI 10.5802/aif.1235), and his series on q-arithmetic entire functions (Acta Arith. 68 (1994) 11–25; Ann. Fac. Sci. Toulouse 3 (1994) 313–334). Study functions integer-valued on {aⁿ} — the natural setting for encoding "2^x, 3^x ∈ ℤ." **Type (iii).**
- **M. Waldschmidt, "On transcendental entire functions with infinitely many derivatives taking integer values at several points," arXiv:1912.00174**, using Gontcharoff interpolation. The interpolation framework closest to the team's divided-difference setup; could conceivably encode two-base integrality more efficiently. **Type (iii).**
- **Corvaja–Zannier proof of Pisot's d-th-root conjecture** (finiteness/arithmetic of power sums). Context.

### 9. Kummer theory / radical extensions with logarithmic constraints (Priority D)
- **A. Perucca, P. Sgobba, S. Tronto, "The degree of Kummer extensions of number fields," Int. J. Number Theory 17 (2021) 1091–1110** (DOI 10.1142/S1793042121500263), and **"Kummer theory for number fields via entanglement groups," Manuscripta Math. 169 (2022) 251–270.** Compute [K(ⁿ√G):K] exactly via entanglement (Lenstra) groups: [K(ⁿ√G):K] = (#⟨K^×, ⁿ√G⟩/K^×)/#E_n · ∏_{p|n, ζ_p∉K}(p−1)/p. Directly relevant to controlling the degree/structure of the team's radical field ℚ(E, ζ_d) with E = w^θ. **Type (ii): the right tool for the algebraic side of Priority D.**
- **C. W. Chan, A. Pajaziti, F. Perissinotto, A. Perucca, "The entanglement of radicals," arXiv:2508.19211 (2025)**, completing Kneser's theorem on linear independence of radicals ("over any field there are extremely few additive relations among radicals"). **Type (ii/iii).**
- Honest verdict: Kummer/entanglement theory rigorously controls conjugates of E and additive relations among radicals but does not see the special value θ = log3/log2; the "mixed archimedean–radical invariant" the team needs is not supplied by any Kummer-theoretic result found. These references make the *algebraic* half rigorous and formalizable; the analytic half (the log identity log E·log 2 − log w·log 3 = 0) remains the gap.

### 10. Colossally abundant interface and provenance (Priority J)
- **L. Alaoglu & P. Erdős (1944)** already cited. New context: **P. Erdős & J.-L. Nicolas** showed exactly 1, 2, or 4 integers can attain the max in the CA construction, so a positive answer to the rational-power conjecture bounds this to ≤ 2 → ratio of consecutive CA numbers is prime. **J. C. Lagarias, "An elementary problem equivalent to the Riemann hypothesis," Amer. Math. Monthly 109 (2002) 534–543** (arXiv:math/0008177) — the RH/Robin reformulation. **K. Briggs, "Abundant Numbers and the Riemann Hypothesis," Experiment. Math. 15 (2006) 251–256** (DOI 10.1080/10586458.2006.10128957) — a computational study of successive maxima of σ(n)/n at superabundant/colossally abundant numbers (the frequently-quoted "22 CA numbers below 10^18" figure could not be verified in the accessible abstract and should be re-checked before use). **OEIS A073751** records the ratio-is-prime check for at least the first 10^7 terms (the 10^7-th term is a 77,908,696-digit number). **B. Zimova, "On the Least Colossally Abundant Exception to Robin's Inequality," arXiv:2510.23889 (2025)** — recent CA structure lemmas. These give the exact chain the rational-power form feeds (Priority J formalization target). Note the historical nuance: Alaoglu–Erdős *proved* the ratio of consecutive *superabundant* numbers is prime, and using the three-prime (six-exponentials) case that Siegel claimed, showed the CA ratio is a prime or semiprime.

### 11. Formalization landscape
- **M. Karatarakis & F. Wiedijk, "A formalization of the Gelfond–Schneider theorem," arXiv:2603.24823 (2026)** (Radboud University, Nijmegen). The first formalization of Gelfond–Schneider in any theorem prover, in Lean 4/Mathlib, including a formalized Siegel's Lemma for algebraic integers and the auxiliary-function/growth-estimate machinery — *directly reusable* for the team's Gelfond–Schneider port (their kernel-verified θ transcendence). **Highest cost/benefit formalization import.**
- **Mathlib's `NumberTheory.Transcendental.Lindemann.AnalyticalPart`** provides the analytic scaffolding of Lindemann–Weierstrass (the full theorem, and even transcendence of e/π, remain open `sorry`s per the Lean formalization leaderboard). Useful auxiliary-function/growth infrastructure for Priorities E/G.
- No existing Lean/Isabelle/Coq formalization of Baker's theorem, the six exponentials theorem, or linear forms in logarithms was found — Priority G would be substantially greenfield, but the Karatarakis–Wiedijk development supplies the Siegel-lemma and auxiliary-function patterns.

### 12. Other promising items
- **M. Bays, J. Kirby, A. J. Wilkie, "A Schanuel property for exponentially transcendental powers," J. London Math. Soc. (2010), arXiv:0810.4457.** Proves the Schanuel analogue for raising to an exponentially transcendental power λ: for such λ and multiplicatively independent ȳ, td(ȳ, ȳ^λ/λ) ≥ n. **Limitation the team correctly anticipated: θ = log₂3 is very likely NOT exponentially transcendental** (as a ratio of two logarithms of algebraic numbers it is plausibly exponentially algebraic), so the theorem does not apply to β/θ directly — but the *method* (Ax–Schanuel + o-minimality) is the model-theoretic frontier, and the paper's general several-powers version encompasses the complex case. **Type (iii).**
- **J. Kirby, "Finitely presented exponential fields," arXiv:0912.4019**, and Zilber's exponential-field / pseudo-exponentiation program: recast the four-exponentials conjecture as a statement about exponential fields (viewing it as the conjunction of particular transcendence problems), giving the cleanest logical formulation and possibly the cleanest Lean encoding. **Type (iii).**
- **Mahler's 3/2 problem literature** (K. Mahler, J. Austral. Math. Soc. 8 (1968) 313–321; Flatto–Lagarias–Pollington, Acta Arith. 70 (1995) 125–147; Dubickas; Akiyama) as an *analogy* for shrinking-target Diophantine control of {ξ(p/q)ⁿ} — it shows how hard even one-base fractional-part control is, calibrating expectations for Priority C. **Type (iii), analogy only.**

## Recommendations (staged, with thresholds)

**Stage 1 — immediate, low-risk, high formalization value (0–3 months).**
1. Import Wu's μ(1, log 2, log 3) ≤ 7.6155 to produce a *uniform* zero-free criterion for solutions with output 2^x, replacing per-value certificate tiers. Concretely: a nonintegral solution forces a small linear form in 1, log 2, log 3; Wu's bound gives an explicit lower bound whose failure is a finite, checkable inequality. **Benchmark that would change the plan:** if the uniform bound only reproduces the existing 2^x < 2^20 barrier rather than extending it, treat measures as a formalization convenience rather than a frontier tool. Hard limitation to state up front: this constrains θ, not the unknown β, so it cannot alone prove the conjecture.
2. Port the Karatarakis–Wiedijk Gelfond–Schneider Lean 4 development to replace/scaffold the team's Hua-based port and reuse its Siegel-lemma module (Priority E/H).

**Stage 2 — technique adaptation (3–12 months).**
3. Attempt Priority-A p-adic amplification by *literally following the Bombieri–Cohen 𝔾_m construction*: build the interpolation determinant with O(log X) candidate rows, fix the non-archimedean place p ∈ {2,3}, and use the Bugeaud–Laurent / Chim explicit p-adic two-logarithm bounds to lower-bound the p-adic size of the nonzero integer determinant. **Precise target:** log|D|_p^{−1} ≫ (log X)² with archimedean size o((log X)²). **Main obstacle:** the exponent set contains (0,0), killing naive row/column factoring — Bombieri–Cohen's equivariant/anchor-pair device is the candidate fix, combined with the team's own min-plus/tropical determinant estimates after finite-difference operations. **Benchmark:** if after finite-difference row operations the guaranteed p-adic valuation is still only O(log X), the one-logarithm deficit is confirmed structural and effort should shift to Stage 3.
4. Consult the Binyamini non-archimedean point-counting program (arXiv:2506.19411; Binyamini–Cluckers–Novikov, Duke) to determine the minimal additional hypothesis under which a denominator-support-sensitive o(H) count on the arc {(2^t,3^t)} could hold. **Target statement:** a compact real-analytic arc of nonzero curvature carries o(H) points with x-denominator a power of 2, y-denominator a power of 3, and synchronized exponents ⌊kβ⌋. **Who is closest:** Binyamini, Cluckers, Novikov. **Obstacle:** existing valued-field counts are per-place, not "synchronized across two places."

**Stage 3 — deep frontier (12+ months, contingent).**
5. Engage Roy's small-value-estimate framework: express the four-exponentials instance in Roy's 𝔾_a×𝔾_m criterion language (Acta Arith. 2001; Mathematika 2013) and test whether the team's candidate-count and determinant results supply the auxiliary-polynomial input a small-value estimate needs. **Obstacle:** Roy's estimates conclude *linear dependence* / bounded transcendence degree only for exponents ν below a threshold that current auxiliary constructions do not reach — the same "one power of log" gap in disguise.
6. Formalize Roy's Strong Six Exponentials Theorem and the Five Exponentials Theorem (Priority G) *after* Stage 1, reusing the Karatarakis–Wiedijk auxiliary-function/Siegel-lemma infrastructure; greenfield but well-scoped.
7. Make the algebraic half of Priority D rigorous and formalizable via Perucca–Sgobba–Tronto Kummer-degree formulas for ℚ(E, ζ_d); document explicitly that the analytic identity log E·log 2 − log w·log 3 = 0 remains the irreducible gap.

**Formalization cost/benefit ranking:** (1) reuse Karatarakis–Wiedijk Gelfond–Schneider Lean development — best; (2) Wu-measure uniform zero-free region — high, self-contained; (3) Alaoglu–Erdős → CA-ratio-prime application (Priority J) using Lagarias/Nicolas — moderate, isolated; (4) new determinant results (Priority E) — moderate; (5) five-/strong-six-exponentials — high value, high cost.

## Caveats
- Every route surveyed inherits the rank-two-to-rank-one collapse; nothing found is a proof or a clear path to one. The conjecture is genuinely open and, per multiple 2023–2026 surveys, sits inside the four-exponentials/Schanuel circle with no known partial-progress crack for the integer case.
- Effective-measure imports (Wu, LMN, Bugeaud–Laurent, Chim) constrain θ = log₂3 and the *outputs* of solutions, never the unknown generator β = log₂M; they cannot close the conjecture, only enlarge finite zero-free regions.
- The ×2×3 dynamics literature is included for conceptual completeness and honest negative assessment; the shrinking-target mismatch (targets of width ≈ M^{−k}) is very likely fatal to a direct application, and no effective ×2×3 result found overcomes it — the best available quantitative statement (BLMV) has only a (log log L)^(−κ₁₂) density gap.
- Two-logarithm and p-adic bounds are parameter-dependent (constants vary with the auxiliary parameter m); cited constant ranges (C ≈ 25–31) are representative, not canonical.
- The "22 colossally abundant numbers below 10^18" figure attributed to Briggs was not confirmed in the accessible source and should be re-verified before publication; the OEIS A073751 datum (ratio prime for ≥10^7 terms) is directly sourced.
- Some records were read via publisher/aggregator pages (ResearchGate, Springer previews) rather than full text; DOIs and venues were cross-checked, but a few page ranges for very recent (2025–2026) items (Chim; Perucca 2025; ICM 2026 proceedings) may shift at final publication.

## Bibliography of Newly Identified Works (not in the team's exclusion list)

**Four exponentials / small-value / Schanuel**
1. D. Roy, "An arithmetic criterion for the values of the exponential function," Acta Arith. 97 (2001) 183–194.
2. D. Roy, "Small value estimates for the multiplicative group," Acta Arith. 135 (2008) 357–393.
3. D. Roy, "Small value estimates for the additive group," Int. J. Number Theory 6 (2010) 919–956 (arXiv:0708.2307).
4. D. Roy, "A small value estimate for 𝔾_a×𝔾_m," Mathematika 59 (2013) 333–363.
5. N. A. V. Nguyen & D. Roy, "A small value estimate in dimension two involving translations by rational points," Int. J. Number Theory 12 (2016) 1273–1293 (arXiv:1412.5163).
6. L. A. Butler, "Some cases of Wilkie's conjecture," Bull. London Math. Soc. 44 (2012) 642–660.
7. M. Bays, J. Kirby, A. J. Wilkie, "A Schanuel property for exponentially transcendental powers," J. London Math. Soc. (2010), arXiv:0810.4457.
8. J. Kirby, "Finitely presented exponential fields," arXiv:0912.4019.

**Effective measures / linear forms in logarithms**
9. Q. Wu, "On the linear independence measure of logarithms of rational numbers," Math. Comp. 72 (2003) 901–911.
10. G. Rhin, "Approximants de Padé et mesures effectives d'irrationalité," Progr. Math. 71 (1987).
11. V. Kh. Salikhov, "On the irrationality measure of ln 3," Dokl. Math. 76 (2007) 955–957.
12. Q. Wu & L. Wang, "On the irrationality measure of log 3," J. Number Theory 142 (2014) 264–273.
13. M. Laurent, M. Mignotte, Y. Nesterenko, "Formes linéaires en deux logarithmes et déterminants d'interpolation," J. Number Theory 55 (1995) 285–321.
14. M. Laurent, "Linear forms in two logarithms and interpolation determinants," Acta Arith. 66 (1994) 181–199; "…II," Acta Arith. 133 (2008) 325–348.
15. Y. Bugeaud & M. Laurent, "Minoration effective de la distance p-adique entre puissances de nombres algébriques," J. Number Theory (1996).
16. Y. Bugeaud, "Linear forms in two m-adic logarithms," Compositio Math. 132 (2002)/(1999 CUP variant).
17. K. C. Chim, "Lower bounds for linear forms in two p-adic logarithms," J. Number Theory (2025).
18. R. de la Bretèche, T. Stoll, G. Tenenbaum, "Somme des chiffres et changement de base," arXiv:1806.09670.

**Interpolation determinants / effective approximation on 𝔾_m**
19. E. Bombieri, "Effective Diophantine approximation on 𝔾_m," Ann. Scuola Norm. Sup. Pisa 20 (1993) 61–89.
20. E. Bombieri & P. B. Cohen, "Effective Diophantine approximation on 𝔾_m, II," ibid. 24 (1997) 205–225.
21. E. Bombieri & P. B. Cohen, "An elementary approach to effective Diophantine approximation on 𝔾_m," LMS Lecture Notes 303 (2003) 41–62.
22. "Local positivity and effective Diophantine approximation," Abh. Math. Sem. Hamburg (2022), DOI 10.1007/s12188-022-00260-8.
23. V. Dimitrov, F. Calegari, Y. Tang, "Arithmetic Holonomy Bounds and Effective Diophantine Approximation," ICM 2026 proceedings, DOI 10.1137/25M1806776.

**Point counting on transcendental curves**
24. G. Binyamini & D. Novikov, "Wilkie's conjecture for restricted elementary functions," Ann. of Math. 186 (2017) 237–275.
25. G. Binyamini, D. Novikov, B. Zak, "Wilkie's conjecture for Pfaffian structures," Ann. of Math. 199 (2024) 795–821.
26. G. Binyamini, R. Cluckers, D. Novikov, "Point counting and Wilkie's conjecture for non-archimedean Pfaffian and Noetherian functions," Duke Math. J.
27. "Counting rational points on transcendental curves in valued fields," arXiv:2506.19411 (2025).
28. R. Cluckers, G. Comte, F. Loeser, "Non-archimedean Yomdin–Gromov parametrizations…," Forum Math. Pi 3 (2015).
29. G. Boxall & G. Jones, "Algebraic values of certain analytic functions," IMRN 2015(4) 1141–1158.
30. G. Boxall & G. Jones, "Rational values of entire functions of finite order," IMRN 2015(22) 12251–12264.
31. G. Boxall, G. Jones, H. Schmidt, "Rational values of transcendental functions and arithmetic dynamics," J. Eur. Math. Soc. 24 (2022) 1567–1592.
32. P. Habegger, "Diophantine approximations on definable sets," Selecta Math. 24 (2018) 1633–1675.
33. P. Habegger, G. Jones, D. Masser, "Six unlikely intersection problems in search of effectivity," Math. Proc. Camb. Phil. Soc. 162 (2017) 447–477.

**×2×3 rigidity and dynamics**
34. J. Bourgain, E. Lindenstrauss, P. Michel, A. Venkatesh, "Some effective results for ×a×b," Ergodic Theory Dynam. Systems 29 (2009) 1705–1722.
35. M. Einsiedler & E. Lindenstrauss, "Rigidity properties of ℤ^d-actions on tori and solenoids," ERA-AMS 9 (2003) 99–110.
36. P. Shmerkin, "On Furstenberg's intersection conjecture…," Ann. of Math. 189 (2019) 319–391.
37. M. Wu, "A proof of Furstenberg's conjecture on the intersections of ×p- and ×q-invariant sets," Ann. of Math. 189 (2019) 707–751.
38. "Quantitative Density under Higher Rank Abelian Algebraic Toral Actions," arXiv:1004.0035.

**S-unit / gcd / entire functions**
39. Y. Bugeaud, P. Corvaja, U. Zannier, "An upper bound for the G.C.D. of aⁿ−1 and bⁿ−1," Math. Z. 243 (2003) 79–84.
40. P. Corvaja & U. Zannier, "A lower bound for the height of a rational function at S-unit points," Monatsh. Math. 144 (2005) 203–224.
41. P. Corvaja & U. Zannier, "Finiteness of integral values for the ratio of two linear recurrences," Invent. Math. 149 (2002) 431–451.
42. J.-H. Evertse & K. Győry, "Unit Equations in Diophantine Number Theory," Cambridge, 2015.
43. J.-P. Bézivin, "Sur les points où une fonction analytique prend des valeurs entières," Ann. Inst. Fourier 40 (1990) 785–809.
44. M. Waldschmidt, "On transcendental entire functions with infinitely many derivatives taking integer values at several points," arXiv:1912.00174.
45. M. Waldschmidt, "Auxiliary functions in transcendence proofs," arXiv:0908.4024.

**Kummer theory**
46. A. Perucca, P. Sgobba, S. Tronto, "The degree of Kummer extensions of number fields," Int. J. Number Theory 17 (2021) 1091–1110.
47. A. Perucca, P. Sgobba, S. Tronto, "Kummer theory for number fields via entanglement groups," Manuscripta Math. 169 (2022) 251–270.
48. C. W. Chan, A. Pajaziti, F. Perissinotto, A. Perucca, "The entanglement of radicals," arXiv:2508.19211 (2025).

**Colossally abundant / RH interface**
49. J. C. Lagarias, "An elementary problem equivalent to the Riemann hypothesis," Amer. Math. Monthly 109 (2002) 534–543 (arXiv:math/0008177).
50. K. Briggs, "Abundant Numbers and the Riemann Hypothesis," Experiment. Math. 15 (2006) 251–256.
51. P. Erdős & J.-L. Nicolas, "Répartition des nombres superabondants," Bull. SMF 103 (1975) 65–90.
52. B. Zimova, "On the Least Colossally Abundant Exception to Robin's Inequality," arXiv:2510.23889 (2025).
53. OEIS A073751 (ratios of consecutive colossally abundant numbers).

**Algebraic independence / surveys**
54. M. Waldschmidt, "Report on some recent advances in Diophantine approximation," arXiv:0908.3973 (Diaz's large-transcendence-degree theorem, Thm 57).

**Mahler analogy**
55. K. Mahler, "An unsolved problem on the powers of 3/2," J. Austral. Math. Soc. 8 (1968) 313–321.
56. L. Flatto, J. C. Lagarias, A. D. Pollington, "On the range of fractional parts ζ{(p/q)ⁿ}," Acta Arith. 70 (1995) 125–147.

**Formalization**
57. M. Karatarakis & F. Wiedijk, "A formalization of the Gelfond–Schneider theorem," arXiv:2603.24823 (2026).
58. Mathlib, `Mathlib.NumberTheory.Transcendental.Lindemann.AnalyticalPart` (Lean 4).