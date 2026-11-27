UNEQUAL BRANCH DATA AND RESONANT ZERO FILTERS
Research prepared for Vladimir Reshetnikov, 27 November 2026

START HERE
  paper.pdf       Complete report, proofs, source analysis, and references.
  paper.tex       Main LaTeX source.
  sections/       The two mathematical sections and bibliography.

RESULTS
1. An exact distance theorem for recovering a formal-series jet from branch
   records of arbitrary unequal precision over any field. The worst ambiguity
   is always a product of observed branch equations. Consequences include a
   finite contact-tree algorithm, sharp errors/erasures uniqueness, the unique
   componentwise minimum precision vector attaining maximum distance, weighted
   jets, and a two-linear-system decoder under a stronger sufficient condition.
2. A complete minimum-support law for a positive measure annihilating two real
   frequencies. It classifies equality for all measures, gives an asymmetric
   cube-root cusp at every odd ratio, and computes the exact first-order cost
   of shortening the support. The filter deletes two prescribed modes of the
   article's GRH-normalized prime errors with the smallest multiplicative window.

The theorems extend explicit questions in the supplied Article. They have
conventional mathematical proofs. Global priority is not established. The
low-ratio three-atom filter is classical input shaping and is credited as such.
No new Lean formalization was compiled, and this task did not rebuild the
upstream Lean development. The supplied exports concern RH and Dirichlet GRH;
no general Artin/Hecke/automorphic RH is claimed.

REBUILD THE PAPER
  ./build.sh
Requires a working pdflatex installation and standard packages listed in the
preamble. No bibliography program is needed. The figure is already supplied.

REPRODUCE THE EXACT CHECKS (Python 3, standard library only)
  python3 code/verify_unequal_jets.py
  python3 code/verify_decoder.py
Run from this directory. The scripts write evidence/*.json.
The distance comparison passes 2,067 exact cases; the decoder passes 2,685
received-word cases. These are finite consistency checks, not formal proofs.

REPRODUCE NUMERICAL ILLUSTRATIONS
  python3 -m pip install -r requirements.txt
  python3 code/two_frequency.py --output evidence/two_frequency_data.json
  python3 code/make_figures.py
The filter calculations use mpmath at 90 decimal digits. They are not interval
certificates. The zeta-zero example is illustrative, not a certified zero file.

OTHER FILES
  evidence/                 Stored exact and numerical outputs.
  figures/                  Vector PDF and PNG of the proved resonance law.
  SOURCE_MANIFEST.json       Pinned source paths, repository blob identifiers,
                            local byte hashes, and inspection scope.
  PROOF_REVIEW.txt           Independent agent review of both new arguments.
  FORMALIZATION_PLAN.txt     Concrete obligations for a future Lean proof.
  SHA256SUMS                 Checksums for every other packaged file.

SOURCE SNAPSHOT
ProveIt commit: 2a9f8e3ee74a1824d57546f0b1b4f1cef5df93d6
Vendored upstream: 72fead102f663d5c7a407964a13dc0cf9d977207
https://github.com/VladimirReshetnikov/ProveIt

The archive contains the newly prepared work, not a redistributed copy of the
818-file Lean project or the supplied 689-page article. Immutable links and
source identifiers make the connection to those materials explicit.
