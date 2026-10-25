# Integration and review

This archive is a self-contained contribution prepared for ProveIt.
No remote branch was changed.

## Suggested placement

Choose the next available numbered directory under:

    Computability/DiophantineConsistency/con-zfc-diophantine-forms/

Use a descriptive suffix such as fixed-base-modular-binomial-weights.
Scripts derive paths from their own locations, so moving or renaming
the packet root is supported. No absolute workspace path is required.

Keep the packet intact for initial review. If inherited source files are
later deduplicated against repository paths, update explicit paths and
provenance without weakening hash or coefficient checks.

## Exact endpoints

Balanced equation JSON SHA-256:

    ef5a5c1e75e5f56673ffc1b600b5d02e6ac97a8e874f0d37695a959f4dd5e9bd

Compact equation JSON SHA-256:

    e5b28dc3abdf8db0747e68fb29b6fd3fb4b9f425da014e84a7c651594a6b43ec

Both are unrestricted-integer quartics of height 7,968. The balanced
version has 230 variables and 4,482 monomials; the compact version has
229 variables and 12,006 monomials.

## Review priorities

1. **Fixed-base/binomial coupling.** Check the lcm bound, both directions
   of the selector theorem, and the multiplicity proof using
   \(B>(t+1)^t\). The selector theorem and large-evaluation method are
   inherited; the dual use of B is the new composition.
2. **Signed modular composition.** Check the positivity bootstrap,
   base-one case, generalized binomial truncation/range lemma, normalized
   remainder norm, and signed derived-label ledger.
3. **Two-square cofinal center.** Check the odd-part order choice in the
   full finite quadratic ring, the ramified case, and parity of
   \(Y_{Wk}(W+1)/W\). The arbitrary-frame counterexample shows why the
   choice of frame is a substantive completeness condition.
4. **Literal source connection.** Run both Python verification modes and
   inspect the raw-source changes and integral restoration certificates.
5. **Logical calibration.** Retain the explicit dependency on
   KEndpoint.c222_iff_zf_refutation and
   ConstructibleChoice.zf_refutation_iff_zfc_refutation.
   A new full proof-assistant build is not part of this packet.

The separate reviews in proofs/ were produced within the same
AI-assisted research process. They are not external peer review.

## Acceptance wording

A defensible description is:

> A fixed-base/binomial-weight successor with a signed modular numerator
> composition and a cofinal two-square Pell center, delivering explicit
> 230- and 229-integer quartics at coefficient height 7,968, with ordinary
> proofs and independently replayed finite certificates.

Avoid describing this as the globally simplest equation, as a new
invention of modular Pell numerators, as a proof of Con(ZFC), or as a
newly completed end-to-end formalization.
