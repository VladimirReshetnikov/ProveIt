# Sources and scope

Consulted 2 October 2026. The model is a tuple of k named total maps on n states, with strong connectivity, loops and repeated destinations allowed, and no terminal or output labels. Isomorphisms permute states only.

## Primary exact enumeration sources

1. V. A. Liskovets, *Enumeration of non-isomorphic strongly connected automata*, Vesti Akad. Nauk Belarus. SSR, Ser. Phys.-Mat. 3 (1971), 26–30 (Russian). [Author record](https://www.researchgate.net/publication/268532943_Enumeration_of_non-isomorphic_strongly_connected_automata). The author abstract and the later English restatement establish priority of the labeled recurrence and exact unrooted divisor formula. A complete reading of the 1971 original remains desirable.
2. R. W. Robinson, *Counting strongly connected finite automata*, in *Graph Theory with Applications to Algorithms and Computer Science*, Wiley (1985), 671–685. [Author-permitted OEIS scan](https://oeis.org/A006689/a006689_1.pdf). The model and rooted normalization are in Sections 2 and 4; equations (4.2) and (4.3), pages 681–682, give the auxiliary recurrence and formal logarithm. Table 2, page 683, resolves the normalization of the rooted sequences. The conference occurred in 1984; the volume appeared in 1985.
3. V. Liskovets, *Reductive Enumeration Under Mutually Orthogonal Group Actions*, Acta Applicandae Mathematicae 52 (1998), 91–120. [DOI](https://doi.org/10.1023/A:1005950823566), [author text record](https://www.researchgate.net/publication/225938499_Reductive_Enumeration_Under_Mutually_Orthogonal_Group_Actions). Section 3, Corollary 3.2 and Theorem 3.3, formula (3.1), give the free automorphism action and the exact unrooted count. Rewriting its Möbius sum as a Jordan totient produces the divisor formula used in the article. The article's voltage proof explains this classical identity and does not claim it as new.

## Classical leading order and historical limits

4. A. D. Korshunov, *The Number of Automata, Boundedly Determined Functions and Hereditary Properties of Automata*, Kybernetika 12(1) (1976), 31–37. [Publisher PDF](https://www.kybernetika.cz/content/1976/1/31/paper.pdf). Section 2, Theorem 3, printed page 32, states a strong-connectivity leading equivalent for complete Mealy automata. Setting the output alphabet size to one gives the transition structures considered here. The theorem page was inspected, including its displayed formula. This short announcement does not provide all the underlying proofs.
5. A. D. Korshunov, *Enumeration of finite automata*, Problemy Kibernetiki 34 (1978), 5–82, 272 (Russian). The full text was not obtained. Its bibliographic identity and its use for a leading strong-graph estimate are supported by the primary article of Bassino and Nicaud: [author PDF](https://www-igm.univ-mlv.fr/~nicaud/articles/tcs07.pdf). This indirect evidence does not establish the complete theorem scope of the monograph.
6. A. D. Korshunov, *On the number of nonisomorphic strongly connected finite automata*, Elektronische Informationsverarbeitung und Kybernetik 22(9) (1986), 459–462. The full article was not exhaustively inspected. Later primary citations include Bassino, David, and Nicaud: [author PDF](https://www-igm.univ-mlv.fr/~nicaud/articles/algorithmica12.pdf). No assertion that the older article contains only a leading term is warranted.
7. E. A. Bender, *An asymptotic expansion for the coefficients of some formal power series*, Journal of the London Mathematical Society (2) 9 (1975), 451–458. [DOI](https://doi.org/10.1112/jlms/s2-9.3.451). A generic classical antecedent for asymptotic composition; the article gives a direct two-endpoint proof specialized to the strong-count logarithm.

The inspected sources establish that the leading equivalents and exact enumeration identities are old. No matching all-fixed-order constructive theorem was located in the bounded literature examination. This is not a global priority certificate. The article presents the higher-order calculation and proof at full mathematical depth while explicitly retaining this historical qualification.

## Exact OEIS conventions

The offset pairs below are copied from the primary records. R_n = L_n/(n−1)! and B_n = L_n/n!; R_n counts rooted classes, whereas B_n is symmetry weighted.

- [A027834](https://oeis.org/A027834): offset 1,2; binary L_n; begins 1, 9, 296, 20958, 2554344
- [A027835](https://oeis.org/A027835): offset 1,2; binary U_n; begins 1, 6, 52, 892, 21291
- [A006691](https://oeis.org/A006691): offset 1,1; at index r it is binary R_(r+1); its comments explicitly correct the old state-count interpretation
- [A006692](https://oeis.org/A006692): offset 1,1; at index r it is ternary R_(r+1); displayed terms begin 49, 6877, 1854545; Robinson's Table 2 identifies the normalization despite the generic title
- [A304312](https://oeis.org/A304312): offset 0,2; binary R_(r+1), including R_1 = 1
- [A304313](https://oeis.org/A304313): offset 0,2; ternary R_(r+1), including R_1 = 1

The A30431x records define a formal logarithmic derivative and retain conjectural identification language. Section 1 of the article derives the identification from the classical recurrence. Both records already post leading Lambert-W equivalents credited to Václav Kotešovec, 31 August 2020. A missing formula on another equivalent record is not evidence of novelty.

## Nearby literature and model distinctions

- X. S. Cai and L. Devroye, *The graph structure of a deterministic automaton chosen at random*, Random Structures & Algorithms (2017). [DOI](https://doi.org/10.1002/rsa.20707), [author version](https://arxiv.org/abs/1504.06238). The named-arc k-out model agrees with the present one. Giant components, local limits, and growing-k thresholds must be distinguished from an all-order enumeration of the rare event of full strong connectivity.
- P. Chassaing, J. Flin, and A. Zevio, *Pascal's formulas and vector fields*, Electronic Journal of Combinatorics 32(1) (2025), P1.38. [Publisher PDF](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v32i1p38/pdf/). Section 1.5 concerns an accessible leading formula via coupon paths; accessibility from a specified root and full strong connectivity are different conditions.
- X. Pérez-Giménez and N. Wormald, *Asymptotic enumeration of strongly connected digraphs by vertices and edges*. [Author record](https://arxiv.org/abs/1005.1285). The n,m digraph model is different from k named outgoing arcs at every vertex.
- B. Pittel, *Counting strongly connected (k_1,k_2)-directed cores*. [Author record](https://arxiv.org/abs/1609.00290). Minimum in- and out-degree constraints at least two omit the indegree-one boundary central here.
- S. Dovgal and V. Nurligareev, *Asymptotics for graphically divergent series: dense digraphs and 2-SAT formulae*. [Author record](https://arxiv.org/abs/2310.05282). Complete expansions in dense regimes do not directly establish the fixed-k automaton theorem.

All third-party articles are linked rather than bundled. The mathematical proof, code, and generated numerical data in this package are original work; citations identify the classical identities and prior results on which it depends.
