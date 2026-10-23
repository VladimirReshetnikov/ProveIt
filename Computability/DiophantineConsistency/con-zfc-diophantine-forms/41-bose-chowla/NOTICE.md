# Attribution, licensing, and mathematical scope

This package was prepared with OpenAI assistance for incorporation into
Vladimir Reshetnikov's ProveIt repository. The new exposition, scripts,
and local reductions are provided under the MIT No Attribution (MIT-0)
terms reproduced in `upstream/source31/LICENSE`. Existing source material
retains its own terms, authorship, and notices. This notice does not
relicense inherited third-party material or the cited research papers.

## Mathematical attribution

- R. C. Bose and S. Chowla supply the classical finite-field construction
  of additive `B_h` sets. The weights used here are a concrete transformed
  instance of their construction, with an exhaustive finite certificate.
- Zhi-Wei Sun supplies the explicit source-coding and binomial/Lucas
  reductions in his 2021 paper and the general ten-integer-variable
  theorem in his 2026 preprint. The present package does not claim the
  general ten-unknown theorem as new.
- The pinned ProveIt source `31-sun10` supplies the complete fixed
  coefficient tuple, source quartic, specialized ten-integer formulas,
  coprime positivity merger, quintic merger, and structural norm weights.
  Its source notices credit the earlier ProveIt packages and mathematical
  ancestry. Those notices are preserved in `upstream/source31/`.
- The twelve-positive-variable result builds on source 34's translated
  carrier and uniform coefficient interface, source 37's coordinate
  change, and the earlier Pell/root-recovery arguments they cite. Its
  new separator and the proof of its sharper bound are documented in
  `positive/POSITIVE_PROOF.md`.
- The new contributions in this package are the verified use of the
  finite additive code throughout the complete source-packing reduction,
  the resulting explicit lower-degree consistency polynomial, efficient
  sharing of its fixed powers, and the positive-form separator reduction.
  No claim of global discovery priority or global optimality is made.

## Machine and compiler ancestry

The fixed consistency instance is the calibrated blank-input K215
machine. Its inherited notices credit the contributing ProveIt
constructions and, within their stated scopes, Elliot Glazer's theory K
work, Jeff's busy-beaver/Rocq reference, Andrew James Wade's compiler
ancestry, BusyCoq, and the Coq Library of Undecidability.

The supplied machine-derived data remains accompanied by
`upstream/source31/coefficients/licenses/NOTICE-K215.md`,
`upstream/source31/coefficients/licenses/LICENSE`, and
`upstream/source31/coefficients/licenses/LICENSE.Wade`. Preserve those
files and the other upstream notices on redistribution.

The source snapshot is
`VladimirReshetnikov/ProveIt@22e75dd6b87b1b199bb08c778d7cf075ae5aae08`.
The package retains source 31's coefficient tuple as one complete object;
it does not combine coefficient ports from different source recipes.

## Verification and review scope

The mathematical claims are ordinary proofs formalizable in ZFC,
composed with the explicitly identified inherited compiler/calibration
results and external number-theoretic theorems. Finite checks certify
the delivered arithmetic data and polynomial implementation; they do
not by themselves prove the unbounded equivalence. No new end-to-end
proof-assistant certificate is asserted.

References to independent checks or audits mean separate checking work
within this AI-assisted collaboration. They do not constitute an
external human endorsement, peer review, or a proof of consistency.
