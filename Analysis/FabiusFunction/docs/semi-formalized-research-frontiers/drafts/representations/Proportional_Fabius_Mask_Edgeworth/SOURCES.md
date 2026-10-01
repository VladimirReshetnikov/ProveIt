# Source question and attribution

Repository HEAD was checked on 1 October 2026 and was `7421a4ca60fdf125411edf412f825aac54278b37`.

The primary source is `Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/representations/Sharp_Conditioning_Laws_Uniform_Random_Series/article.tex`, blob `2df4dfd46ae60a8e3ba273399112c1a1b22a6ae9`.

Pinned source: https://github.com/VladimirReshetnikov/ProveIt/blob/7421a4ca60fdf125411edf412f825aac54278b37/Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/representations/Sharp_Conditioning_Laws_Uniform_Random_Series/article.tex

Its variance-fraction theorem and likelihood-ratio lemma already establish the arbitrary-mask Gaussian limit, explicit TV profile and forward relative-entropy limit, even for general positive summable weights. Those conclusions are background here. The requested extensions are explicitly labeled `q:rates` (uniform finite-parameter errors) and `q:edgeworth` (phase-sensitive higher corrections). This report proves a quantitative second-order result for fixed geometric parameters and proportional hidden/observed bulk counts; it does not solve all regimes posed in those questions.

Classical context:

A. Dembo and O. Zeitouni, Refinements of the Gibbs conditioning principle, Probability Theory and Related Fields 104 (1996), 1–14. DOI https://doi.org/10.1007/BF01303799 ; author manuscript https://www.wisdom.weizmann.ac.il/~zeitouni/pdf/sanovreffull.pdf . Growing-block Gibbs conditioning and Edgeworth expansion methods are not claimed as new principles.

Related research companions prepared 1 October 2026:

- Second Order Critical Complements in Fabius Conditioning, `Second_Order_Fabius_Crossover.tex`: signed-Gamma correction measures and a different critical-complement regime
- Strict Conditioning Order for Fabius Observation Masks, `strict_fabius_conditioning_order.tex`: the exact all-q strict comparison; the present canonical-mask formula quantifies its gap in the proportional regime

The paper's contribution relative to the inspected source is the explicit uniform second-order coefficient, its signed-Gamma error proof, variance-only cap-profile dependence at order 1/n, and canonical mask separation. A bounded literature check is not a certification of worldwide novelty.
