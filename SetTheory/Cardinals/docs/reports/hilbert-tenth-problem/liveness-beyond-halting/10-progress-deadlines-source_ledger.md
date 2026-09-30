# Source and provenance ledger

Research date: September 30, 2026.

## Repository inspection

The GitHub connector was used to inspect repository contents, rather than treating
an unsourced repository summary as a proved result. No repository files were
changed and no Lean build was run.

1. Public MRDP theorem source, pinned commit:
   https://github.com/VladimirReshetnikov/ProveIt/blob/b6bf6406a4c49017fedc6fba068b36c634987150/Computability/HilbertTenthProblem/Lean/Diophantine/MRDP.lean
   Inspected declarations: `mrdp`, `mrdp_iff`, `mrdp_dioph_iff`.
   Supports the fixed-polynomial/fixed-witness-dimension natural-number interface.

2. MRDP guide:
   https://github.com/VladimirReshetnikov/ProveIt/blob/b998f70c6886e6a00339a6f4a02ed8625324d357/Computability/HilbertTenthProblem/Lean/MRDP.md
   Supports the existence/extraction distinction and describes the proof and
   axiom-audit interfaces. Audit claims are repository reports, not a new audit
   performed for this manuscript.

3. Turing-degree project guide:
   https://github.com/VladimirReshetnikov/ProveIt/blob/b998f70c6886e6a00339a6f4a02ed8625324d357/Computability/TuringDegrees/README.md
   Supports the stated distinction between Lean, Rocq, and separately conditional
   coarse-degree developments. No admitted coarse-degree theorem is used here.

4. Root README and HilbertTenthProblem README were inspected for orientation.
   The article does not rely on unrelated headline claims in the root README.

The GitHub commits endpoint confirmed the public MRDP-source commit. The earlier
revision is also identified as an arrival commit in the later commit message.
Repository HEAD can change; the article cites inspected immutable revisions.

## Primary literature

- Jockusch and Soare (1972), Pi^0_1 classes and degrees of theories,
  Transactions of the AMS 173, 33–56.
  https://doi.org/10.1090/S0002-9947-1972-0316227-0
  The original theorem attribution and metadata were cross-checked. The AMS
  endpoint did not serve the complete paper through the browsing tool.

- Ng, Stephan, Yang, and Yu (2013), Computational aspects of the hyperimmune-free
  degrees, Proceedings of the 12th Asian Logic Conference, 271–284.
  https://doi.org/10.1142/9789814449274_0015
  Author manuscript: https://personal.ntu.edu.sg/kmng/Files/Papers/hif_ALC.pdf
  The primary author manuscript was read, including page images of its opening
  two pages. It explicitly states the domination characterization and HIF basis
  theorem, attributing the latter to Jockusch and Soare.

- Harel, Pnueli, and Stavi (1983), Propositional dynamic logic of nonregular
  programs, Journal of Computer and System Sciences 26(2), 222–243.
  https://doi.org/10.1016/0022-0000(83)90014-4
  Original bibliographic attribution and Proposition 5.1 were checked through
  Esparza–Krasotin's primary paper, which explicitly states the recurrent-machine
  completeness result. The full 1983 article was not retrieved. The manuscript
  gives its own recursive-tree reduction rather than relying on unseen details.

- Chatterjee and Fijalkow (2011), Finitary languages.
  https://arxiv.org/abs/1101.1727
  Primary abstract used for the finitary-acceptance context. Its Borel hierarchy
  concerns infinite words, not the arithmetical hierarchy of finite input codes.

- Moore (1990), Unpredictability and undecidability in dynamical systems,
  Physical Review Letters 64, 2354–2357.
  https://doi.org/10.1103/PhysRevLett.64.2354
  Author summary: https://sites.santafe.edu/~moore/pubs/gs.html
  Used only as dynamical-universality precedent. The new article's affine
  realization is proved directly; no continuity or robustness theorem is borrowed.

- Esparza and Krasotin (2025), Regular model checking for systems with effectively
  regular reachability relation, MFCS 2025, LIPIcs 345, Article 45.
  https://doi.org/10.4230/LIPIcs.MFCS.2025.45
  Full primary HTML inspected:
  https://drops.dagstuhl.de/storage/00lipics/lipics-vol345-mfcs2025/html/LIPIcs.MFCS.2025.45/LIPIcs.MFCS.2025.45.html
  Used for recent regular-model-checking context and explicit confirmation of the
  classical recurrent-Turing-machine result. Its hypotheses are not silently
  transferred to the binary-controlled systems in this manuscript.

- Matiyasevich (1970), Enumerable sets are Diophantine, Soviet Mathematics Doklady
  11, 354–358. Bibliographic data and the English reprint were checked.
  Reprint DOI: https://doi.org/10.1142/9789812564894_0013
  For the actual computational interface used here, the pinned ProveIt source is
  the immediately relevant source.

## What the package does not establish

No independent priority claim is established for the integrated theorem package.
No new Lean or Rocq proof was built. No general explicit MRDP polynomial extractor
was implemented. Finite tests are not evidence by themselves for an infinite
recurrence theorem, a hierarchy completeness result, or a degree lower bound.
The article gives conventional mathematical proofs for those claims and states
their classical dependencies separately.
