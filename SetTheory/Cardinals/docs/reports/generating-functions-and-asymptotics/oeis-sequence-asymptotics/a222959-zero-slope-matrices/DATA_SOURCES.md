# Primary sources, data provenance, and scope

Sources below were inspected in a focused comparison on 4 October 2026. The statements describe the inspected results, not an exhaustive literature or priority certificate. No third-party paper PDF or copied article text is redistributed in this package.

## Definition and finite values

- [OEIS A222959](https://oeis.org/A222959): definition of binary arrays whose individual rows and columns have zero least-squares slope; the displayed array supplies the square diagonal through n=9
- [OEIS A222955](https://oeis.org/A222955), [A222956](https://oeis.org/A222956), and [A222957](https://oeis.org/A222957): associated one-dimensional and array sequences

The A222959 page and displayed array were available. Direct retrieval of its b-file returned HTTP 403; no b-file is bundled. The package's nine recorded square values were independently recomputed with a C++ meet-in-the-middle count. The default Python replay independently enumerates through n=8; n=9 is explicitly identified as recorded evidence with an optional Python rerun. Row alphabets/ranks are recomputed through n=14. See `data/README.md`.

## Earlier one-dimensional results

Helmut Prodinger, *On a generalization of the Dyck-language over a two letter alphabet*, Discrete Mathematics 28 (1979), 269–276. [Author PDF](https://www.finanz.math.tugraz.at/~prodinger/dyck.pdf); [DOI](https://doi.org/10.1016/0012-365X(79)90134-1).

The inspected Theorem 4, pp. 273–274, gives parity-sensitive asymptotics for binary words with equal scattered ab and ba counts. This is the one-row weighted condition. The author's PDF was available; its OCR was poor, and the modern characterization was cross-checked below. The publisher DOI endpoint was unavailable during this retrieval. The row alphabet and its asymptotics are prior work.

Gwenaël Richomme, *On some 2-binomial coefficients of binary words: geometrical interpretation, partitions of integers, and fair words*, arXiv:2510.07159v1 (2025). [Primary HTML](https://arxiv.org/html/2510.07159v1).

Corollary 5.11 gives the centered sign-sum characterization. Theorem 5.12 attributes the one-word asymptotic to Prodinger. Theorem 5.13 identifies binary fairness with zero least-squares slope. These are word results, not the simultaneous growing-dimensional square-matrix enumeration proved here.

## Nearby array and nullvector models

Somnath Bera, Sastha Sriram, Atulya K. Nagar, Linqiang Pan, and K. G. Subramanian, *Algebraic Properties of Parikh Matrices of Binary Picture Arrays*, Journal of Mathematics (2020), article 3236405. [Publisher text](https://onlinelibrary.wiley.com/doi/10.1155/2020/3236405).

Definitions 2 and 5, Theorem 4, and Sections 3–7 were inspected. Fair picture arrays require aggregate row and column balance, a weaker condition than each individual row and column being fair. The paper concerns algebraic operations and closure properties. For example, the 2 by 2 identity array satisfies the aggregate balances but no individual length-two row is fair.

Richard Arratia and Stephen DeSalvo, *On the singularity of random Bernoulli matrices—novel integer partitions and lower bound expansions*, arXiv:1105.2834v2 (2012). [Primary PDF](https://arxiv.org/pdf/1105.2834).

Theorem 1, Proposition 9, Lemma 3, and Section 5 Propositions 10–11 were inspected. They concern singularity lower bounds and prescribed nullvector templates, including support-dependent interaction estimates. They do not supply a uniform joint count for both prescribed growing arithmetic-progression nullvectors. Extending fixed-template estimates uniformly to this regime is not automatic.

Matthew T. Harrison and Jeffrey W. Miller, *Importance sampling for weighted binary random matrices with specified margins*, arXiv:1301.3928v1 (2013). [Author PDF](https://jwmi.github.io/publications/Nonuniform_matrices.pdf).

Definition (1) and Section 4.2 concern nonuniform cell odds with ordinary unweighted row and column sums. The word “weighted” describes probabilities, not growing signed coefficients in margin equations.

Alan J. Aw, *Asymptotic enumeration of admixed arrays and a different independence heuristic*, arXiv:2604.08857v1 (2026). [Primary HTML](https://arxiv.org/html/2604.08857v1).

The model, Theorem 4.3 setup, reduced cosine-squared integral, and local expansion were inspected. These arrays have paired binary matrices and unweighted margins. The quartic method is relevant, but does not discharge a growing-weight global localization argument.

## Gaussian, Edgeworth, and lattice-LLT framework

Alexander Barvinok and John A. Hartigan, *Maximum entropy Gaussian approximation for the number of integer points and volumes of polytopes*, arXiv:0903.5223v2 (2009). [Primary PDF](https://arxiv.org/pdf/0903.5223).

Theorem 2.6 and its definitions, printed pp. 9–10 (PDF pages 8–9, zero-indexed), impose a covariance lower bound relative to dimension and constraint-column norms. In the natural saturated coordinates used here, deleting a weight-one column margin gives a truncated-gauge Bernoulli Rayleigh quotient S/[4(2S-1)]. Consequently the needed sufficient condition fails in this realization. The code checks that quotient exactly. The factor 4 is the Bernoulli covariance normalization. In the theorem's quadratic-form convention q(t)=t^T Cov t/2, the corresponding upper bound for its lambda is S/[8(2S-1)]. Both bounds are O(1); the distinction does not change the failure of the sufficient condition. This obstruction concerns these coordinates, not every possible reformulation.

Alexander Barvinok and John A. Hartigan, *Maximum entropy Edgeworth estimates of the number of integer points in polytopes*, arXiv:0910.2497v2 (2010). [Primary PDF](https://arxiv.org/pdf/0910.2497); [HTML](https://arxiv.org/html/0910.2497v2).

Theorem 1, pp. 5–7, explicitly retains conditions I–V. Condition V requires relative negligibility of the outer characteristic integral. Theorem 2 concerns ordinary contingency margins; it does not automatically verify that condition for the present growing weights. The maximum-entropy, Fourier, Gaussian, and Wick/Edgeworth strategy is established method precedent. Report194 supplies a problem-specific localization argument.

Greg Kuperberg, Shachar Lovett, and Ron Peled, *Probabilistic existence of regular combinatorial structures*, arXiv:1302.4295v3 (2017). [Primary PDF](https://arxiv.org/pdf/1302.4295).

Theorems 2.4–2.5 and basis-free Theorem 4.15 require transitive coordinate symmetry and a dimension-dependent size bound. The varying projector diagonal in this problem prevents transitive coordinate symmetry for large n, and the stated dimension-six size requirement exceeds the n-squared cell count. These theorems are methodological predecessors, not direct applications here.

## Positioning and computational limits

The focused primary-source comparison did not locate an identical theorem for the simultaneous prescribed centered-arithmetic-progression left and right nullvectors. That is a bounded negative search result, not proof of novelty. One-dimensional fairness, general Fourier/Edgeworth methods, nullvector methods, and high-dimensional lattice approximation are credited as prior work.

The exact checks corroborate finite algebra, normalization, and enumeration. They do not formally verify the global analytic proof, locate a practical asymptotic onset, or establish a convergence theorem for the formal expansion. The report's all-fixed-orders prescription is mathematical; the package does not implement an unrestricted all-orders symbolic engine.
