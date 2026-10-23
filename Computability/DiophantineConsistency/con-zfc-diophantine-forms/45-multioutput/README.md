# Simultaneous quadratic coding for ZFC consistency

Source snapshot: 22e75dd6b87b1b199bb08c778d7cf075ae5aae08.
Postscript reviewed: 8747904f8b973f9016434993e7ec6ae6ec7549ef.

Read report/report.pdf (17 pages) and report/report.tex first.

Main results:
- Nine strictly positive variables: 788 live binary operations; exact degree 129875980. Nine nonnegative variables: 791 operations, same degree.
- Ten unrestricted integers: 936 operations; exact degree 237526776.
- Twelve strictly positive variables: 121 operations/degree941, or a three-equation system with116 shared operations/maximum degree932. Other cost-degree tradeoffs are supplied.

The structural contribution is simultaneous extraction of22 quadratic outputs using31 B2 positions, rather than squaring the source into a quartic and using exponential positions. All17 actual fixed coefficients of each main nine/ten instance are included, as are the coherent four compiler ports. These are mathematical equivalence proofs using stated compiler and arithmetic dependencies, not new Lean/Rocq or checked object-level ZFC derivations. No global minimality or new variable-count theorem is claimed. The67-operation scalar and59-operation systems remain unbeaten on operation count alone.

## Reproduce without changing the release

Requires Python3.10+ with SymPy and NumPy installed. Run:

    python verify_release.py

This checks every release hash and84 Git blob source pins, copies the release to a temporary directory, and runs only newly authored finite checks there. It never imports or runs upstream programs and never rewrites files in the sealed release. Success means the listed finite checks passed, not that consistency has been decided or that all inherited theorems have been re-proved. Temporary work is removed automatically.

For rebuilding the PDF on a normal TeX Live installation, run pdflatex twice in report/. report/build.sh supplies explicit paths and a local format/font cache for the research environment where automatic kpathsea configuration was incomplete. It has no shell-escape requirement. The build cache is deliberately not shipped.

## Canonical data and proof boundaries

- nine/ and sun/: primary exact polynomial DAGs, complete fixed-leaf manifests, coefficient payloads, mathematical proofs and authored builders/checkers. The nine degree-certificate DAGs are larger803/806-operation equal-polynomial certificates, not the primary788/791-operation forms.
- quartic/: name retained for compatibility; active files describe the common quadratic parent and simultaneous target certificate, not a preliminary B4 source.
- positive/: independent smaller separation weight and exact twelve-positive DAGs.
- audit/: independent full-equation replay, exact-degree audit and fixed-binding audit.
- short/: unsuccessful local simplification directions and exact67/59 source ledgers. These are not improvement claims.
- review/:84 pinned files, corrected catalogue, independent multi-output review, and later formalization-status documents. Source files are inert provenance.
- weights/MULTI_OUTPUT_EXTRACTION_PROOF.md: independent universal source proof.

The parent transport z_old=z+1 requires the canonical bound z_old>=2, not a blanket positive-domain bijection. Sun source bounds for square b do not assert b is a power of two; the reverse arithmetic bridge supplies that extra condition before binary decoding. The four coefficient ports always travel as one coherent tuple.

## Licenses and provenance

Inherited files retain their included LICENSE/NOTICE files and exact source pins. Newly authored report, proofs and scripts are provided for incorporation in ProveIt. No third-party licensing terms are overridden. RELEASE_HASHES.json authenticates all delivered files other than itself.
