# Provenance and source boundaries

Research date: September 30, 2026.

## ProveIt

Repository: https://github.com/VladimirReshetnikov/ProveIt
Inspected tree commit: e8bb0931d67f80d9fce87a8cddb0f661ff19f956

The key directly inspected source was:

`Computability/HilbertTenthProblem/Lean/Diophantine/Common/DiophantineTrace.lean`

Its theorem interfaces provide ordinary Diophantine closure for bounded
universals, exact iteration, and reachability. The manuscript does not
attribute a single-fold theorem to those interfaces. The HilbertTenthProblem
README and STATUS register supplied project context. The repository was not
independently compiled or axiom-audited in this work.

## Primary literature checked

1. Yu. V. Matiyasevich, *Towards finite-fold Diophantine representations*,
   Journal of Mathematical Sciences 171 (2010), 745–752.
   DOI: 10.1007/s10958-010-0179-4.
   Publisher abstract and bibliographic record checked. Used for the
   distinction between ordinary polynomial and single-fold exponential
   representation.

2. D. Cantone, L. Cuzziol, E. G. Omodeo, *On diophantine singlefold
   specifications*, Le Matematiche 79(2) (2024), 585–620.
   DOI: 10.4418/2024.79.2.18.
   Article page and PDF checked; PDF pages 588 and 590 visually inspected.
   Used for single-fold context, arithmetic normalization issues, and the
   stated classical exponential normal form. Not used as evidence that the
   new sign-table construction has no predecessor.

3. M. Hark, F. Frohn, J. Giesl, *Termination of Triangular Polynomial Loops*.
   arXiv:1910.11588v7, February 13, 2024.
   Used to distinguish the present certificate theorem from established
   triangular-loop termination and closed-form analysis.

4. N. Lommen, F. Meyer, J. Giesl, *Automatic Complexity Analysis of Integer
   Programs via Triangular Weakly Non-Linear Loops*.
   arXiv:2205.08869v3, November 15, 2024.
   HTML abstract/introduction and publication metadata checked. Used for
   prior modular analysis and stabilization-threshold context.

5. D. Larchey-Wendling, Y. Forster, *Hilbert's Tenth Problem in Coq (Extended
   Version)*, Logical Methods in Computer Science 18(1) (2022), article 35.
   DOI: 10.46298/lmcs-18(1:35)2022. arXiv:2003.04604v5.
   Abstract and journal metadata checked. Used for the established
   mechanized MRDP/Minsky/FRACTRAN landscape, not as a claimed verification
   of this manuscript's code.

The original mathematical proofs and examples are supplied in article.tex.
The literature review is selective; historical priority is not established.
