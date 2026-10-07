# Source provenance and scope of inspection

Research date: 7 October 2026. Commit pins below refer to inspected snapshots,
not to a claim that those snapshots were built or fully audited.

## ProveIt

Repository: https://github.com/VladimirReshetnikov/ProveIt
Inspected snapshot: `52faf9fcdc7214af5c3a130c6c3bd6d50bbdacae`.

The targeted repository path was:

    Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements/

The README inventory was read in multiple relevant ranges. It distinguishes
unrefereed manuscripts from proof-assistant results and records newer sources
not yet integrated into the large thematic report. In particular, it records
independent all-degree Boolean threshold results in placed sources 65 and 69.
The older report's unresolved septic question was therefore not selected as
an allegedly new open problem. The source-47 verifier was also inspected.

## Immediate project manuscripts

1. **Sharp Boolean Phase Integration in Every Degree: Defect-radical slicing,
   exact nonintegrability thresholds, and extremal tensor rigidity in Gowers's
   framework.** Read in full through the Library TeX
   `all_degree_boolean_integration.tex` (1,459 lines).
   Author disclosure: prepared with ChatGPT for Vladimir Reshetnikov and the
   ProveIt project. Date: 6 October 2026. Its own comparison snapshot is
   `8c40adc24df2e6f338cea728887772aead4bf144`, distinct from the current inspected
   repository snapshot. Research Question 3 explicitly asks for maximizing
   functions and dimension-independent phase stability. Its universal threshold,
   tensor classification, canonical energy proof, and amplitude-only estimate
   are credited as existing results.

2. **Exact Boolean Obstruction Energies: Derivative periods, sharp quartic--sextic
   integration, and dimension-free higher-degree extremizers.** Relevant
   statements, derivative constraints, canonical proof, and defect/support
   sections were inspected in the Library TeX
   `article(20261007-014512).tex`. It is source 47 in the project inventory.
   Its recorded comparison snapshot is
   `5c9a442d263632fdcd4e9690154c12c2dcc70b53`. Its title, not its generic filename,
   identifies the source. The canonical all-degree cap is not a new claim here.

3. **Sharp Second-Order Stability at the Polynomial-Phase Endpoint of Gowers
   Norms: A parity-sensitive refinement of the Szemeredi framework.** Inspected
   through the Library PDF `gowers_endpoint_stability.pdf`, including its
   abstract, method description, relevant limitations, and coset/quotient
   comparison. It is source 55 in the placed-source inventory. Its use of the
   disk constraint, independent cube vertices, and exact finite-product
   expansion is methodological precedent. Its untwisted endpoint and second
   coefficient are different from the twisted canonical problem studied here.

4. **Sharp Boolean Phase Integration from Gowers Derivative Spectra.** Source
   43 is credited for the earlier cubic/projective framework through the above
   inspected manuscripts. The present paper supplies the cubic bound it uses;
   no uninspected source-43 statement is required as an additional assumption.

The Library was used to read these concrete newer manuscripts and avoid
repeating their completed results. No Library file was altered or copied into
the delivered archive.

## VladimirReshetnikov/math

Repository: https://github.com/VladimirReshetnikov/math
Inspected snapshot: `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Read: README, relevant portions of `CONTENTS.md`, `lean/docs/159.md`, and

    preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/
        build/main.tex
        build/sections/00-introduction.tex

The main source names OpenAI as author and is dated 23 September 2026.
The introduction reports a quasipolynomial arithmetic-progression bound and a
triangular precision architecture. The formal-comparator document selects a
reciprocal-sum consequence and explicitly excludes the quantitative bound from
that comparator statement. The neighboring van der Waerden family was reviewed
at the level of its contents description, not its full proof.

These are reported manuscript claims, not results certified by the present
work. No theorem from either of these two quantitative preprints is a premise
of the new Boolean proofs. No full audit of the math repository is claimed.

## Published primary sources

- Tanja Eisner and Terence Tao, *Large values of the Gowers--Host--Kra seminorms*,
  Journal d'Analyse Mathematique 117 (2012), 133--186;
  arXiv:1012.3509v2, 26 June 2011. Theorem 1.1 was checked in the primary PDF,
  including the image of printed page 7. It provides a dimension-uniform
  qualitative L1 approximation by circle-valued polynomial phases at an
  almost-maximal Gowers norm. This is the substantive imported analytic theorem.

- Jonathan Tidor, *Quantitative bounds for the U^4-inverse theorem over low
  characteristic finite fields*, Discrete Analysis 2022:14, arXiv:2109.13108.
  Definition 3.1 and Proposition 3.5 were checked in the primary source for the
  established nonclassical integration framework. The needed Boolean
  coefficient criterion is proved separately in the delivered paper.

- W. T. Gowers, *A new proof of Szemeredi's theorem*, GAFA 11 (2001), 465--588,
  DOI 10.1007/s00039-001-0332-9. The comparison is to its phase-integration
  architecture, especially Section 17. No unchecked global estimate from the
  reviewed contemporary drafts is inferred from that comparison.

## Priority and verification boundaries

Targeted searches and source comparisons establish the specific open question
in the preceding project manuscript. They do not establish exhaustive external
novelty or publication priority. The proofs and checks were developed during
this task, without an independent referee or proof-assistant build. The PDF is
compiled from the delivered TeX; ordinary and optimized Python checks agree.
