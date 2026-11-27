SYMPLECTIC DEPENDENCE: RESEARCH PAPERS AND REPRODUCIBLE ARTIFACTS
Prepared for Vladimir Reshetnikov — 27 November 2026

START HERE
----------
paper.pdf is the main paper, “Exact cycle dependence and sharp detection
in finite symplectic observations.” Its complete LaTeX source is paper.tex
plus sections/*.tex and references.tex.

companion/critical_profile.pdf is a separate self-contained paper,
“Universal critical profiles for many prescribed symplectic frames.”
Its complete source is companion/critical_profile.tex.

The results extend the finite-field Fourier, Gram-matrix, and symplectic
counting methods in the supplied ProveIt research program. The proofs here
are unconditional: they do not use RH or GRH as a hypothesis.

MAIN RESULTS
------------
1. Exact cycle laws in every characteristic.
   Put independent uniform nonzero vectors at the vertices of a finite
   simple graph in a symplectic space of dimension 2n over F_q. Reveal the
   pairings on its edges. Compare with independent edges having the TRUE
   one-edge marginal. Every cycle has an explicit complete labelled law,
   total variation distance, and chi-square divergence. A proper subset
   of its edges is exactly independent. The full graph has independent
   edge labels if and only if it is a forest.

2. A sharp statistical profile for growing cactus graphs.
   Distinct simple cycles in a cactus intersect in at most one vertex.
   Its cycle blocks are exactly independent. If q and the maximum cycle
   length are fixed, and the sum I_n of the individual cycle chi-square
   divergences tends to tau, the full total variation distance tends to
   2 Phi(sqrt(tau)/2)-1. Diverging I_n gives distance tending to one.
   Cycles of lengths 2r+1 and 2r+2 have the same leading information,
   (q-1)^(2r+1) q^(-4nr). Over F_2 an optimal leading score uses cycle parity.

3. An overlapping-cycle contrast.
   For K_(a,m) with a fixed number of anchors, the critical information is
   m [q^a-1-a(q-1)] / q^(4n). In particular, for K_(2,m), putting
   N=q^(2n) and m=floor(N^beta), 1<beta<2, makes full total variation tend
   to zero. Nevertheless the sum of the four-cycle chi-square divergences
   tends to infinity, and the full chi-square divergence also tends to
   infinity. A rare dependent-anchor event explains the latter phenomenon.

4. Universality for many prescribed frames (companion paper).
   Independently embed alternating spaces with arbitrary prescribed forms
   into dimension 2n. If their total dimension is 2n+c for fixed integer c
   and their largest dimension is o(n), the complete cross-pairing law has
   an explicit limiting total variation distance delta_q(c) from uniform
   independent entries. The limit is independent of all internal forms,
   including their degeneracies. Rank/nullity tests are asymptotically
   optimal. Every fixed number of frames still has asymptotically uniform
   independent cross-pairings. All finite fields are covered.

SOURCE AND NOVELTY SCOPE
-----------------------
Inspected repository: VladimirReshetnikov/ProveIt
Directory: Analysis/GeneralizedRiemannHypothesis/
Commit: 00cadb961bbe77c74e5d082c4948f8884d58a970

Read notes/SOURCE_AUDIT.txt and notes/provenance.json for the source map,
existing results excluded from the novelty claim, and primary literature.
The results are new relative to the inspected corpus and earlier delivered
work considered in this investigation. A targeted literature comparison
did not locate the combined statements; worldwide priority is not certified.
Classical Fourier, graph-spectrum, nullity-chain, and likelihood-limit
ingredients are credited rather than presented as new principles.

PROOF AND VERIFICATION STATUS
-----------------------------
Both manuscripts contain complete mathematical proofs. Separate reviews
checked the algebra, conditioning, coupling, and probability limits.
These were internal mathematical reviews, not external peer review.
No new theorem in this package has a compiled Lean formalization.
FORMALIZATION.txt describes concrete interfaces for future formalization.
The vendored RH/GRH project was inspected but was not rebuilt in this work.

Exact checks recorded in the package include:
  - 5,840,259 actual vector assignments in 45 cycle/cactus/tree/bipartite
    cases over F_2, F_3, F_4, F_5;
  - 432 additional rational checks of the grouped cycle calculator;
  - 1,607,096 vector arrays and 55,631 Gram fibers in the companion;
  - 262,144 additional conditioned arrays, including 53,550 frame tuples;
  - exact checks of character sums, proper-edge marginals, bordering
    transitions, killed-Markov estimates, and conditioning normalizers.
These checks are evidence for finite cases and implementations. The proofs,
rather than the finite checks, establish the stated general theorems.

BUILD AND REPRODUCE
------------------
Requirements:
  - Python 3.10 or later; all mathematical verifiers use only its standard
    library, including exact integers and fractions;
  - pdfLaTeX with the standard packages listed in the manuscript preambles;
  - matplotlib and numpy only if regenerating figures.

From this directory:

  make pdf
  make check
  make figures

Equivalent commands, without make:

  pdflatex -interaction=nonstopmode -halt-on-error paper.tex
  pdflatex -interaction=nonstopmode -halt-on-error paper.tex
  pdflatex -interaction=nonstopmode -halt-on-error paper.tex
  python3 code/cycle_laws.py --self-check
  python3 code/verify.py --output results/independent_enumeration.json
  python3 code/verify_anchors.py --output results/anchor_verification.json
  python3 companion/code/verify.py

To rebuild the companion PDF, run pdfLaTeX twice on critical_profile.tex
from the companion directory. Existing PDF/PNG figures are included, so
matplotlib is not required merely to rebuild the PDFs. The full exact
enumerators may take several minutes.

EXACT CALCULATOR
----------------
For example:

  python3 code/cycle_laws.py --q 4 --n 2 --length 6 --format text

The calculator supports any prime-power q, n>=1, and cycle length >=3.
It uses sufficient-statistic groups, not an exponentially large list of
all field-label vectors. See code/README.txt for its interface and scope.

FILE MAP
--------
paper.tex, sections/, references.tex     Main manuscript sources
paper.pdf                                Compiled main paper
companion/                               Second manuscript and checks
code/                                    Exact calculators and enumerators
figures/                                 Vector PDF and PNG figures
results/                                 Machine-readable and text receipts
notes/SOURCE_AUDIT.txt                    Source/literature/novelty analysis
notes/provenance.json                     Immutable source references
FORMALIZATION.txt                        Proof status and formalization plan
Makefile                                 Build and reproduction commands
SHA256SUMS.txt                            Integrity hashes for package files

The archived check outputs record the completed runs. No benchmark fitting,
Monte Carlo estimation, or numerical extrapolation is used in the proofs.
