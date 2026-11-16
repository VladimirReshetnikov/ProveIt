# Source baseline and review scope

The report compares against ProveIt commit
`052fbaebfc955294b4c02f6532ab7e7a3f760f7a`. The selected-source manifest
records 31 paths with pinned URLs, Git blob identities, byte counts,
SHA-256 hashes, and review roles. The working source files were checked
against those Git identities before the manifest was assembled.

The collection index was used as a catalog, not as a proof certificate.
The review examined the foundational Lean interfaces, all three earlier
framework packets, and the specific analytic and Diophantine obstacles
addressed in the report. It does not claim to audit all 54 packets.

## Main antecedents

- The existing three framework packets provide finite observations,
  certificates, guarded loops, simple-branch analysis, hyperelliptic
  zero counts, and power-gap height bounds. The report credits those
  contributions and explains what it adds.
- The Platonic-solids packet already contains a special backward
  coefficient budget; the new backward-demand theorem generalizes it.
- The Puiseux report identifies the singular coefficient-selection
  obstruction. The new result changes the representation to aggregate
  root support and does not claim to solve that impossible selection
  contract.
- Section 4 of the existing FTA article supplies the explicit rational
  descent lemma. Its unchanged source and PDF are included under
  `dependencies/FTA_iPRA/`, together with the original README and Lean
  plan. This is the one substantive inherited analytic existence proof.
- The Siegel, Mordell-Weil, and Faltings reports supply the specific
  geometric-count, quotient-cover, and height-bound distinctions.

The bibliography also cites Fred Richman, *The fundamental theorem of
algebra: a constructive development without choice*, Pacific Journal of
Mathematics 196(1) (2000), 213-230, DOI 10.2140/pjm.2000.196.213, for the
established completed-finite-set approach. No mathematical priority
claim is made for the underlying ideas.

## Reproducing provenance

For a source in the manifest, check out the pinned commit, compute the
file SHA-256, and compare both it and `git rev-parse COMMIT:path` with
the recorded identities. `MANIFEST.sha256` at the package root covers
the deliverable files themselves; it is separate from this upstream
source manifest. Hashes identify bytes, not the truth of a theorem.
