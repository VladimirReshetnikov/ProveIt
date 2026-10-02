# Bounded literature and overlap receipt

Check window: **2026-10-02, 01:22–01:39 UTC**. This receipt records evidence available in the checked sources. It does not establish global novelty, exclude unpublished results, or certify the accompanying new proof.

## Established primary reference

Éric Fusy, Erkan Narmanli, Gilles Schaeffer, **Enumeration of Corner Polyhedra and 3-Connected Schnyder Labelings**, *The Electronic Journal of Combinatorics* **30**(2) (2023), article **P2.17**. DOI **10.37236/11174**. Publisher PDF lists submission 6 April 2022, acceptance 7 April 2023, publication 5 May 2023.

- Publisher: https://www.combinatorics.org/ojs/index.php/eljc/article/view/v30i2p17
- Published PDF: https://www.combinatorics.org/ojs/index.php/eljc/article/download/v30i2p17/pdf/
- Latest listed arXiv version inspected: https://arxiv.org/html/2202.09172v3 ; v3 dated **29 October 2023**
- Author PDF: https://monge.univ-eiffel.fr/~fusy/Articles/corner_schnyder.pdf

Theorem 24 proves only the exponential growth rates. Conjecture 25 states the positive-amplitude equivalents with the two irrational power exponents. The paper explains the state-dependent obstacle to applying the usual iid cone result; its endpoint CLTs are not killed-walk local limits.

## Later status and relevant methodological checks

- Éric Fusy, *Enumeration of corner polyhedra*, Rutgers Experimental Mathematics seminar, **12 December 2024**. Slides explicitly retain the conjectured equivalent. https://sites.math.rutgers.edu/~zeilberg/expmath/fusy2024.pdf . Downloaded successfully; SHA256 **f2745b873e93cc0e4d5d582514e72296c0649ee87aecb1ef15d273c984eb6eae**
- Author publication-page web snapshot inspected: https://monge.univ-eiffel.fr/~fusy/ ; still describes the two exponents as heuristic. The web service reported a crawl age of four weeks. A direct fetch later failed with HTTP 403, so the receipt does not claim a freshly fetched origin copy.
- Denis Denisov and Kaiyuan Zhang, *Markov Chains in the Domain of Attraction of Brownian Motion in Cones*, *Journal of Theoretical Probability* **38**, article **14** (2025), online 20 November 2024. DOI **10.1007/s10959-024-01369-7**; https://arxiv.org/abs/2309.16311 . Read M1/M2 and Theorems 5–6: finite-state averaged covariance is insufficient for direct application, and the main survival theorem is not a fixed-endpoint local limit.
- Relevant all-orders boundary: Andreas Nessmann, arXiv2307.11539, treats finite-group orbit-summable walks; Andrew Elvey Price, Andreas Nessmann and Kilian Raschel, arXiv2309.15209, treats scalar decoupled theta-function models and demonstrates logarithmic corrections. Neither was identified as a ready-made theorem for these parity-modulated kernels.

## Public search queries

Exact queried strings included:

- “Enumeration of corner polyhedra” asymptotic exponent
- “corner polyhedra” OEIS
- “3-connected Schnyder” site:oeis.org
- “corner polyhedra” “asymptotic” 2025 2026
- “corner polyhedra” “Conjecture 25”
- “Schnyder labelings” asymptotics 2025 2026
- “corner polyhedra” Fusy exponent proof
- “Schnyder” “22/27”
- “polyhedra” “9/16” asymptotic
- “2202.09172”
- “Schnyder” “non-D-finite”
- “bimodal” “quadrant” “walks”
- “polyhedral orientations” “asymptotic”
- “A377922” asymptotic; “A377920” asymptotic
- “Markov-modulated” “cone” “conditioned”
- “random walks” “internal states” “cone”

No matching later proof of the exact exponents or non-D-finiteness was found in these results or the inspected primary sources. Search omissions and indexing delays remain possible. “Corner polyhedra” also denotes unrelated integer-programming objects, which were excluded.

## OEIS export and entry dates

Official repository: https://github.com/oeis/oeisdata . Its time.txt recorded **2026-10-01T03:00:24-04:00** (07:00:24 UTC). The verified current export commit was **da8d37c6de95fccdc6caffee958a010bfd9172bc**, authored **2026-10-01T07:03:41Z**.

Full entries were retrieved and saved as A377920.seq through A377923.seq. Their internal `%I` revision dates are **15 December 2024** for A377920, A377921, A377922, and **13 December 2024** for A377923. These entry dates are distinct from the October 2026 export refresh. A377922 identifies p_n; A377920 identifies s_n; A377921 identifies tilde_s_n. A377923 is a different graph-counting sequence and is outside the proposed theorem.

## ProveIt overlap check

Authorized current GitHub code-search queries restricted to **repo:VladimirReshetnikov/ProveIt** for **A377920**, **A377921**, **A377922**, **Schnyder**, and **"corner polyhedra"** each returned **total_count:0**, **incomplete_results:false**. Query receipts: `sources/public-overlap-check.json`.

Scope: indexed default-branch code for the public repository queries. No claim is made about all repository branches, unindexed new uploads, or unpublished work.
