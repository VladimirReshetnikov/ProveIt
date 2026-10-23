# New odd-scale unrestricted-integer frontier

The preferred new explicit family is:

| Integer variables | Single equation degree | Binary gates | Comparison-system equations | System max degree | System gates |
|---:|---:|---:|---:|---:|---:|
|24|2240|165|3|2224|161|
|25|920|131|4|872|126|
|26|214|123|5|128|117|

The complete signed-domain proof, including negative s/H, w=0, T=0, t=0, both main-root signs, auxiliary saturation, and canonical completeness, is `SIGNED_ODD_SCALE_FAMILY_PROOF.md`. Preferred circuits are `integer24_sharp_pair_norm165_degree2240.json`, `integer25_small_weight131_degree920.json`, and `integer26_ordinary_two_root123_degree214.json`.

These improve the preceding locally audited family (26 variables /degree2465 /192 gates; 27 /1116 /136; 28 /258 /128). The upstream collection's fewer-gate27-integer equations and lower-degree27-integer systems remain useful tradeoffs. This is not a global minimality claim; classical universal-polynomial variable bounds belong to a different comparison.

Construction: combine package23's odd half-binomial scale with the prior odd strong multiplier and square w; then use package21's cheaper pair-ring norm, the prior rational auxiliary Pell saturation, and the new signed extensions of the small-weight and ordinary two-root mergers. The six positivity guards cost18 variables, the two odd maps and square map add3, and the retained source coordinates add3,4, or5.

`ODD_SCALE_FAMILY_CHECKS.json` records independent local checks. `SOURCE_MANIFEST.json` pins all newly consulted upstream mathematical sources to commit ae3007ca4467011e0e051c84acb4a1dd13971b0e and hashes the earlier local dependencies. No received source program was executed. The two locally written Python files emit and independently check the new circuits.

`COEFFICIENT_BINDINGS.json` points to complete, hash-verified earlier coefficient tuples. Coefficients are fixed integers, not free unknowns. MF is always the shifted source mask. A newer compiler tuple may be used only after its complete transfer is independently established.

The theorem is an ordinary mathematical reduction formalizable in ZFC: with an authentic compiler and the inherited exact K215 calibration, each lack-of-solutions assertion is ZFC-provably equivalent to Con(ZFC). The work does not decide whether solutions exist and is not a new proof-assistant certificate.

Independent review is complete: `../audit/pell_independent_audit.md` reports no remaining mathematical issue. Its separately written evaluator checks the norm by determinant, and verifies the final packets on250 signed/zero assignments each, complete liveness and operation ledgers, two affine degree diagnostics, the compact coefficient payload hashes, and the uniform leading-form proof for the sharp2P separator.
