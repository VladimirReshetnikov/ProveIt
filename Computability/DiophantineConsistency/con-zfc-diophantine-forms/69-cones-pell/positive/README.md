# Pell descent: twelve positive unknowns, degree 82

This component supplies one explicit fixed-coefficient polynomial with **12 strictly positive integer unknowns**, **exact degree 82**, and **102 live binary arithmetic operations**. Its complete definition is `equation.json`; the readable equation and proof are in `PROOF.md` and `section.tex`.

Relative to the inspected package61 twelve-positive equation, degree decreases from **118 to 82** and evaluator cost decreases from **104 to 102**. No reduction of the nine-positive-variable bound or global optimality claim is made.

## Main idea

The elementary descent theorem

    Q>1, Q integer, V integer, y rational,
    Q V²-(Q-1)y²=1  =>  y integer

permits two source coordinates to be merged without additional coprimality guards. The inverse Pell step strictly lowers the nonzero integer |V| while preserving the rational ordinate's reduced denominator. A quadratic norm then replaces the strong ordinate and auxiliary gap by one positive sum coordinate.

The new descent and elimination proofs are self-contained. Their application retains package61's two carriers and its inherited compiler/refutation calibration. Therefore the mathematical conclusion is, formalizably in ZFC,

    no positive integer zero  <=>  Con(ZFC).

This contribution does not provide a new end-to-end Lean/Rocq certificate or a checked derivation in the repository's object-language ZFC calculus. It does not prove consistency or inconsistency.

## Exact coefficients

The whole compact44 tuple is supplied under `native/`: four gzip payloads containing unsigned little-endian integer bytes, totaling 295,388 raw bytes. `native/ACTIVE_BINDING.json` explicitly maps the evaluator's `beta,K0,MC,MF` to `beta,K,MC,MF_source`; the high mask is already shifted. The coefficients are fixed numerals, never quantified inputs.

The literal transition data, coefficient recipe, independent native audit, inherited proofs and original notices are retained. No consistency oracle enters the recipe.

## Reproduce

With ordinary Python 3 and its standard library:

    python3 verify.py
    python3 -O verify.py

The driver checks exact sparse polynomial identities and degree certificates, all live gates, the literal coefficient payloads, the new descent identity, canonical local Pell examples, and byte-identical circuit regeneration. It authenticates 28 retained source/provenance entries by both Git blob SHA1 and SHA256, using portable relative paths. It rebuilds and independently audits the complete native tuple in a temporary directory. It writes the corresponding receipts under `certificates/`.

To regenerate the circuit alone:

    python3 build.py

Only these two root scripts are supported entrypoints for this new component. Files under `upstream/source61/` preserve historical source material and provenance; their own historical replay context is not the new component's entrypoint.

## Review order

1. `PROOF.md`: complete equation, descent theorem, rational-to-integer elimination, source lift, completeness, and exact degree proof.
2. `REVIEW.md`: independent AI-assisted mathematical review, with the proof boundary stated explicitly.
3. `equation.json` and `verify.py`: authoritative circuit and an independent finite checker that does not import its builder.
4. `native/ACTIVE_BINDING.json`, `native/PROOF.md`, and retained package61 source proofs.

The snapshot used for the comparison is `9cca523d9f27ad39d52993f4065cbd7e58f8bdd4`. `SOURCE_PINS.json` authenticates retained package61 files; the separate native manifests pin their older coefficient sources. Local finite checks are not substitutes for the unbounded semantic arguments.
