# Source and novelty audit

Access date for the research review: **4 September 2026**.
The article and tests were assembled in a runtime whose UTC clock had crossed
into 5 September; the date on the article is the research request's date.

## Repository baseline

User-specified directory:
https://github.com/VladimirReshetnikov/ProveIt/tree/main/Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/thue-morse/Thue_Morse_Atlas_and_Frontiers

Consolidated source inspected through the web reader:
https://raw.githubusercontent.com/VladimirReshetnikov/ProveIt/refs/heads/main/Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/thue-morse/Thue_Morse_Atlas_and_Frontiers/Thue_Morse_Atlas_and_Frontiers.tex

Review included the source's visible organization and relevant passages on
finite blocks, moments, products, correlations, scale calculus, and the
Fabius/Rvachev connections. The raw source was available through the browser.
Network retrieval from the build container did not succeed, and no complete
recursive, commit-pinned repository checkout was obtained. In particular,
this report does not claim to have compared every formula in every draft.
The mutable `main` URL is not an immutable source snapshot.

## Primary literature consulted or screened

- Allouche and Shallit, *The ubiquitous Prouhet–Thue–Morse sequence*:
  https://cs.uwaterloo.ca/~shallit/Papers/ubiq15.pdf
  Classical background; not evidence of priority for the present refinements.
- Baake and Coons, *Correlations of the Thue–Morse sequence*, arXiv:2209.07102v2:
  https://arxiv.org/html/2209.07102v2
  Essential baseline for all-order correlations and odd-order vanishing.
- Bolker, Offner, Richman, Zara, *The Prouhet–Tarry–Escott Problem and Generalized
  Thue–Morse Sequences*, arXiv:1304.6756:
  https://arxiv.org/abs/1304.6756
  Generalized partition constructions; bibliographic and topic comparison.
- Allouche, Riasat, Shallit, *More Infinite Products: Thue–Morse and the Gamma
  function*, arXiv:1709.03398:
  https://arxiv.org/abs/1709.03398
  Classical sign-weighted products and the Woods–Robbins context.
- Yao-Qiang Li, *Infinite products related to generalized Thue–Morse sequences*,
  arXiv:2006.04187:
  https://arxiv.org/abs/2006.04187
  Generalized automatic products with rational factors in the index.
- Flajolet, Gourdon, Dumas, *Mellin transforms and asymptotics: Harmonic sums*:
  https://specfun.inria.fr/dumas/Publications/FlGoDu95.pdf
  Context for harmonic sums and log-periodic asymptotics. The present saddle
  proof is given independently, rather than borrowed as an unstated theorem.
- DLMF, section 4.13:
  https://dlmf.nist.gov/4.13
  Lambert-W branch convention.
- Benoit Cloitre, *The Thue-Morse Transform*, arXiv:2604.06243v2:
  https://arxiv.org/abs/2604.06243
  Current 2026 preprint screened through its abstract and bibliographic record.
  It is not represented as having been audited line by line.

## What is claimed

The article proves the formulas it states. The potentially new material is the
specific finite boundary functional and endpoint refinements, the nonlinear
cover/hafnian/matching applications, and the detailed automatic geometric-product
asymptotics and flat boundary-layer realization.

## What is not claimed

- Not a discovery of Thue–Morse, Prouhet cancellation, the generating product,
  higher-order correlations, hafnians, matching polynomials, saddle-point
  analysis, or the Woods–Robbins constant.
- Not a global historical-priority determination. Search absence is not a proof
  that no equivalent result exists in a different notation or source.
- Not a complete resurgent transseries or an analysis of all complex saddles.
- Not uniformity at parameter boundaries omitted from the theorem hypotheses.
- Not a Lean proof or an interval-certified numerical computation.

The results are therefore described as independently derived refinements and
novelty candidates relative to the inspected material. A publication-level
priority review should compare them against specialist correlation, automatic
product, and Boolean-function literature, including sources not retrieved here.
