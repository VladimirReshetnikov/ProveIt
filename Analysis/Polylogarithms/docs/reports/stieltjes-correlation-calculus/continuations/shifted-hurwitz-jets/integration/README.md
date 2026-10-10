# Integration notes

Proposed report path:
`Analysis/Polylogarithms/docs/reports/shifted-hurwitz-jet-correlations/`

The archive is a new report package, not an applied change to ProveIt.

## Natural insertion points

The normalized primitive identities and log-Gamma correlation fit after the existing integration/negative-polygamma development. The contact theorem fits after the pointwise Stieltjes derivative tower. The coefficient-closure theorem supplies a shared intermediate section.

Preserve the distinction between:

- ordinary shifted integrals for spectral orders with real parts below one;
- canonical finite-part products at distinct singular points;
- periodic distribution derivatives and pointwise derivatives;
- zero-mean primitives in this report and base-point primitives elsewhere.

The pointwise Stieltjes master theorem needs no repair. Its periodic finite-part extension needs the contact terms in Theorem 6.1.

## Source compatibility

All equation/theorem labels and bibliography keys use `shj:`. To import `sections.tex`, retain suitable theorem environments and definitions of:
`\FP`, `\Li`, `\Res`, `\sgn`, `\dd`, `\ii`, `\T`, `\R`, `\C`, `\Q`, and `\src`.

Review macros already defined by the book instead of blindly importing the standalone preamble. The code-generated symbols `gaK`, `gbK`, `zK`, `QaK`, and `QbK` are explained in the JSON files.

Spectral derivatives use square brackets, `zeta^[j]`, while round-parenthesis derivatives of Stieltjes and polygamma functions refer to the argument.

## Proposed source edit

`make_basis_patch.py` reads an explicit local ProveIt checkout and produces a unified diff for the one overstrong basket-independence sentence. It does not modify the checkout:

    python integration/make_basis_patch.py --repo /path/to/ProveIt --output basis_note.patch

The script refuses to generate the patch if the exact expected source text is not present once. This is intentional: refresh and reconcile an upstream change instead of blindly applying a stale edit.

`periodic_extension_note.tex` is a proposed warning paragraph to accompany integration of the contact theorem. It references this report's prefixed labels and therefore belongs with the integrated report material, not in isolation.

## Acceptance sequence

Preserve the delivered package according to the repository's incoming procedure. Replay exact and numerical scripts on a separate working copy. Review the finite-part and Fourier arguments independently. Only then integrate accepted results into the canonical book, keeping worldwide-priority and arithmetic-independence questions separate.
