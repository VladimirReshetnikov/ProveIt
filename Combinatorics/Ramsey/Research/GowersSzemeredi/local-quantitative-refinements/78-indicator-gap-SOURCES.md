# Sources and provenance for Report 290

## Mathematical predecessor reports

1. *Sharp Hereditary Energy Rigidity on Arbitrary Abelian Groups*, ProveIt Report288, prepared for Vladimir Reshetnikov, 7 October 2026.
   - Frozen TeX SHA-256: 9e2d258dfa94b20b74846b7fc870c4a8b7213b203e63508c1268112a837c9840
   - Its division-free index-two energy identity, cyclic endpoint calculations and small-order cyclic arguments are fully rederived in the present article. The five-cycle full-indicator estimate is sharpened to 17/25. New complete histogram arguments cover orders seven through nine; an eight-branch arbitrary-target symbolic certificate sharpens the cyclic witness cutoff to 19/27 on at most ten points. Every no-wrap histogram, nonzero positive-wrap polynomial and finite-wrap maximum is printed in the article.
   - The present classification proof is self-contained apart from standard finitely generated abelian-group structure. The predecessor is not edited, bundled or needed by the executable companion.

2. *Optimal Weighted Witness Size and Torsion at the Energy Endpoint*, ProveIt Report289, prepared for Vladimir Reshetnikov, 7 October 2026.
   - Frozen TeX SHA-256: 8db376cf0f4c7928d4de904898bb5bb18b49ac4076f3c97edd75a49961822acb
   - Theorem 1.2 and Sections 3–4 establish the fixed-weight equation e*e=o*o, pair-free torsion-spectrum criterion and existential torsion dichotomy within the nonzero-defect index-two family.
   - Report290 applies those identified results to all hereditary endpoint maps using its classification. This is a corollary of the two reports, not a silent enlargement of the earlier report's hypotheses.

## Primary-source historical comparison

The comparison was made on 7 October 2026. It is bounded and does not establish priority or exhaustive novelty. The statistic, recurrence, parity quotient and pushout construction have important known antecedents.

- W. T. Gowers, *A new proof of Szemerédi's theorem*, Geometric and Functional Analysis 11 (2001), 465–588, Section 6, especially the respected-quadruple and graph-energy discussion before Lemma 6.2.
  Primary paper: https://www.cs.umd.edu/users/gasarch/TOPICS/vdw/sz-thm-gowers-proof.pdf
  Relevant Section 6 passage inspected; no claim that the full paper was independently audited.

- *Nearly Sharp Relative Affine Repair on Fourier-Uniform Domains*, project research source 56, 6 October 2026, Sections 1 and 11.
  Pinned repository archive: https://github.com/VladimirReshetnikov/ProveIt/blob/aa1d86f6f5db46a5a4b6a99735587b31cbbafb54/docs/incoming/gowers_relative_affine_repair.zip
  The same fixed-weight relative quadruple ratio appears there, under Fourier-uniformity and small-error repair hypotheses. This is repository research, not an independently certified published source.

- David Conlon and W. T. Gowers, *Freiman homomorphisms on sparse random sets*, preprint arXiv:1603.01734 (2016), Theorem 1.2.
  Record: https://arxiv.org/abs/1603.01734
  Author PDF: https://www.its.caltech.edu/~dconlon/homomorphisms.pdf
  Introduction and theorem statements inspected. This concerns exact extension from one sparse random domain, not a positive-defect hereditary infimum over every finite test.

- M. Arunkumar, G. Shobana and S. Hemalatha, *Ulam-Hyers, Ulam-Trassias, Ulam-Grassias, Ulam-Jrassias stabilities of a additive-quadratic mixed type functional equation in Banach spaces*, International Journal of Pure and Applied Mathematics 101(6) (2015), 1027–1040, equation (18), p.1030.
  Publisher PDF: https://www.acadpubl.eu/jsi/2015-101-5-6-7-8/2015-101-6/20/20.pdf
  Section 2 assumptions and the displayed identity were inspected. The recurrence of this report appears there after translating variables; the setting is real vector spaces and an odd solution of a different functional equation. This citation records prior occurrence of the identity, not an imported arbitrary-target classification theorem.

- Miklós Laczkovich, *Polynomial mappings on Abelian groups*, Aequationes Mathematicae 68 (2004), 177–199.
  Primary publisher record: https://link.springer.com/article/10.1007/s00010-004-2727-9
  Only the publisher abstract was inspected; the full article was unavailable in the comparison. It records torsion-sensitive links between diagonal and mixed differences. Its complete theorem system is a remaining historical-check lead, and no theorem from the unavailable full text is used in the present proof.

- G. M. Feldman, *Solution of the Kac–Bernstein functional equation on Abelian groups in the class of positive functions*, arXiv:2102.01592 (2021), Lemma 2.2.
  Primary text: https://arxiv.org/html/2102.01592v1
  Lemma, proof and scalar-valued application inspected. It gives a quadratic-plus-additive-plus-parity-quotient decomposition for a different mixed-difference equation and uses division by 2 and 4. It supplies context, not an arbitrary-torsion justification for the present grid reduction.

- The Stacks Project Authors, *The Stacks Project*, Section 19.2, tag 05NM.
  Primary reference: https://stacks.math.columbia.edu/tag/05NM
  The explicit pushout construction is standard algebra. The needed injectivity and extension properties are proved directly in Report290.

No equivalent all-abelian-source-and-target hereditary endpoint theorem was located among the inspected results. That statement is not a priority certificate. The complete Laczkovich paper and older group-valued finite-difference literature remain worthwhile further checks.

## Authored source inventory

There are exactly ten authored source files:

1. `README.md`
2. `REPRODUCING.md`
3. `SOURCES.md`
4. `Report290.tex`
5. `build.py`
6. `companion/__init__.py`
7. `companion/README.md`
8. `companion/exact_checks.py`
9. `tests/test_build.py`
10. `tests/test_companion.py`

The prepared PDF and canonical manifest are generated artifacts. A separate ZIP SHA-256 pin is generated outside the archive. Logs, receipts, review images, research drafts, internal audits and third-party papers are excluded from the public package.

The guarded build and regression-test design are adapted from the verified Report289 template, with new report identifiers and archive name. They retain the duplicate-PDF-destination quality gate, no-follow snapshot guards, source immutability checks and deterministic archive contract. The manuscript retains the monospace ligature fix and title-page anchor fix. Earlier reports remain untouched.

## Proof and verification boundaries

The general theorem is established by the written arbitrary-group arguments, not by bounded maps or sampled weights. The cyclic certificate is an exhaustive symbolic calculation: after normalization it retains v=Nd, prints every defect coefficient, and reduces all possible target collisions to obstruction order 2, 3, or at least 4/infinite. Its completeness is proved algebraically; it is not a finite-target empirical search. The full indicator C5 sharpness is distinct from any weighted-infimum claim. Limiting original-group box indicators establish an infimum at most 5/8; a strict larger threshold yields a finite witness but does not prove finite attainment at 5/8. The order-four obstruction must be retained. The pushout is injective on the original target, and descent explicitly reflects the nonzero defect. The quotient-plane kernel is L∩2G and is not assumed to equal 2L.

The universal third-branch indicator bound 19/27 is optimal, with equality for the C3→Z representative example. Weighted optimality is not asserted; that same example has a rational weight of ratio 467/683<19/27. The preliminary four-point 8/11 bound remains only an auxiliary step. Equality of weighted and indicator infima is asserted only in the affine and index-two classes. Fixed-weight endpoint criteria are applied only when the map's hereditary infimum is 3/4. No publication-priority, nonabelian, global Ramsey, or proof-assistant certification claim is made.
