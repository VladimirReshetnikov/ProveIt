# Sources and scope

Accessed 4 October 2026. These are references, not bundled source snapshots.

1. **OEIS A064856**, Catalan-weighted Stirling transform: <https://oeis.org/A064856>. Source for sequence identification, initial values, and the previously known hypergeometric and Bessel generating functions. The first 23 listed values are used in the independent finite exact check.
2. **Alexey Spiridonov**, *Spectra of sparse graphs and matrices*, senior thesis, 2004: <https://alexey.im/papers/sparse-random-graphs-senior-thesis.pdf>, especially page 13. The numerical exponential-ratio estimate is distinguished from the spectral-moment inequality, which already follows from Bauer–Golinelli’s prior coefficientwise theorem below.
3. **Mourad Rahmani**, *Generalized Stirling transform*, arXiv:1212.0957 (2012), subsequently *Miskolc Mathematical Notes* 15(2) (2014), 677–690: <https://arxiv.org/abs/1212.0957>. Structural transform background; see its Catalan example.
4. **Hsien-Kuei Hwang, Chong-Yi Li, Vytas Zacharovas**, *Elementary asymptotics for the Stirling numbers of the second kind: The central range*, arXiv:2605.29633 (2026): <https://arxiv.org/abs/2605.29633>, including Appendix A. Background on Bell/Stirling and Touchard saddle expansions.

The source comparison is bounded. It supports neither an exhaustive novelty search nor a claim of global priority. No third-party full text, private research notes, credentials, or browser snapshots are included in this package.

5. **M. Bauer and O. Golinelli**, *Random incidence matrices: moments of the spectral density*, arXiv:cond-mat/0007127v2 (2001), *Journal of Statistical Physics* 103 (2001), 301–337: <https://arxiv.org/abs/cond-mat/0007127>, DOI <https://doi.org/10.1023/A:1004879905284>. Section 5.3 gives the normalized tree-walk moment polynomial; Section 5.5, equation (9), pp.26–30, proves S(k,l) <= I(k,l) <= C_l S(k,l). At alpha=1 this yields B_k <= M_{2k} <= a_k and already implies Spiridonov’s Conjecture 3.3. The revised report gives the normalization and derived root-scale corollary without a novelty claim.

## Revision status

The first release mistakenly listed proving the spectral comparison as future work. Revision 2 corrects that status. It does not change the Stirling–Catalan asymptotic proof, explicit inverse, exact coefficients, or numerical tables. No claim about the present literature status of full spectral-moment asymptotics is made.
