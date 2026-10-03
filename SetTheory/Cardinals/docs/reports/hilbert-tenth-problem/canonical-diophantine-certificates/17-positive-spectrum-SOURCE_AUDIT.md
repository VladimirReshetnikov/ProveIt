# Source audit and status

Date: 2026-10-02.
Repository: https://github.com/VladimirReshetnikov/ProveIt
Inspected main snapshot: `e58b724c25bd34533b7a5834cfcbe873dfa01288`.
The audit is targeted, not exhaustive. No modifications to the repository were made.

## Repository sources

1. `Computability/HilbertTenthProblem/README.md`.
   Inspected the project overview and its current representation work. This
   established that generic finite-execution encodings and universal arithmetic
   count optimization were already extensively explored. Their reported global
   counts were not independently reconstructed or benchmarked here.

2. `SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/README.md`.
   Inspected the merged report guide. Its Part IV describes canonical ordinary
   Diophantine certificates for polynomial trajectories, with a fixed-degree
   cubic-size construction independent of the horizon. This is the immediate
   baseline for the manuscript's positive-base exponential extension. The
   merged report also contains numerous unrelated computation substrates that
   this manuscript deliberately does not recapitulate.

3. `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1984/DPR.lean`.
   Inspected the introductory declarations, counter-program compilation, and
   final `acceptsStop_sfu`, `re_sfu`, `re_single_equation`, and
   `re_exp_diophantine` theorems. The file explicitly states uniqueness of
   witnesses in its unary exponential representation. Its source was read,
   not compiled, and its complete dependency closure was not audited here.

All repository bibliography links in the article are pinned to the exact commit.
These repository claims are distinguished from this manuscript's independently
presented mathematical proofs and from its executed Python checks.

## Primary literature consulted

* Jones and Matijasevic, Journal of Symbolic Logic 49(3), 818–829 (1984),
  DOI 10.2307/2274135. The publisher metadata and extract were accessible;
  fetching the publisher's full PDF timed out. The exact unary single-fold
  formulation used in the manuscript is also explicitly present in the
  inspected repository declarations. It is a cited classical input rather
  than a theorem newly proved in the manuscript.
* Matiyasevich, “Matiyasevich theorem,” Scholarpedia (2012). The author-written
  article and its multiplicity-question discussion were located in search;
  full-page retrieval was unreliable. No historical or current solution of
  the single-fold/finite-fold conjectures is claimed on the basis of that
  search result.
* Tiwari, “Termination of linear programs,” CAV 2004. Read the author's
  publication page, including its scope and the explicit Example 3 erratum
  notice. Used only as related-work context.
* Hosseini, Ouaknine, Worrell, “Termination of linear loops over the integers,”
  ICALP 2019. Consulted the author manuscript, author abstract, and official
  Dagstuhl publication page. The published DOI and article number are
  10.4230/LIPIcs.ICALP.2019.118 and 118. An author/arXiv manuscript carries 114
  in its page header; the bibliography follows the publisher's metadata.
  The distinction between all-initial-input termination and one specified
  input is retained in the paper.
* Hark, Frohn, Giesl, “Termination of triangular polynomial loops,”
  DOI 10.1007/s10703-023-00440-z. Consulted the primary publisher text and
  abstract. The version of record was published online in 2023 and appears
  in volume 65, pages 70–132 (2025). The class of triangular weakly nonlinear
  loops, its linearization, and known termination analysis are credited as
  prior work; the manuscript does not claim to discover the class.
* Chonev, Ouaknine, Worrell, “On the zeros of exponential polynomials,”
  JACM 70(4), Article 26 (2023), DOI 10.1145/3603543. Consulted the
  author-hosted manuscript. Used to contextualize spectral/zero problems,
  not as the source of an alleged new general positivity result.

## Scope of verification

Executed: exact scalar profile construction and endpoint verification; randomized
and exhaustive small-profile tests; parametric arithmetic compilation; exported
quadratic/power and expanded-quartic checks; individual witness mutations;
explicit nonlinear-lift, parity, minimum, and matrix-product examples.

Not executed: a Lean/Rocq formalization of the new theorems; a full repository
build; a general symbolic Jordan or triangular polynomial front end; a general
ordinary Diophantine power-elimination compiler.

The PDF was compiled with pdfLaTeX, rendered with Poppler, and visually reviewed.
No claim of peer review or exhaustive novelty certification is made.
