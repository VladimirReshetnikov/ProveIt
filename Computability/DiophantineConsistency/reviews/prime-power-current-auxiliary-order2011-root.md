# Independent root review: exact prime-power order

PASS for the four frozen sources in the [author receipt](prime-power-current-auxiliary-order2011-author.md). Root read all231 source/check lines, the complete receipt, Mathlib's actual natural LTE interface and the used prime-power order characterization before executing the independent replay. Root did not author these four modules. Existing finite-controller dependencies were reused; this is not a new full dependency-closure or umbrella build.

The generic theorem derives the required positivity and prime nondivisibility from exactly the displayed assumptions. Natural subtraction is justified before the cast bridge. Exact valuation gives both vanishing at the proposed prime-power order and nonvanishing at its predecessor; the modulus-p case is handled separately. The actual wrapper derives every premise from the checked literal lift modulo120199². No orbit, order, or nontrivial-lift hypothesis remains in `generator_order_succ`.

Root freshly compiled generic main, generic Checks, actual main, and actual Checks using `lake env lean -M6000 -j1`, `Elab.async false`, and the named output objects. All four terminal exit codes were zero. Both main logs are empty. All14 axiom reports contain only subsets of `propext`, `Classical.choice`, and `Quot.sound`. Each of the four fresh objects is byte-identical to its author's object. The checks retain g=0/1, modulus0/exponent0 cast behavior, oddness and nontrivial-lift negative controls, and actual auxiliary powers1/2/3.

Source SHA-256 identities:

- PrimePowerOrder: `781aa36c18153b4f7e7e6b7df204b3b42545bc8cabf0f9f25736d012e598dd47`.
- PrimePowerOrderChecks: `c7f8fe09ae961e9879e166a62cbc299b2995702e432323ad4dd00a7f9b165eaa`.
- CurrentAuxiliaryOrder2011: `67db5e89285d56908ce482ffd72108c909ccc5e4f505ac2d324157344048e08e`.
- CurrentAuxiliaryOrder2011Checks: `5f5c6ea233495dec39d7842ce0393b5ba7d607a10a16ca78ef63f2a41953aca1`.

Fresh object SHA-256 identities, in that order:

- `348b7f689fd74a426167fa298fb71575d67e78627894ac4b2b98d3c67751f27b`.
- `789ee101c1e65b0c837e60e6ade67d650ead6c6c85ba39d3eb1eaa29179f334b`.
- `a444266e8175211407a465402fc5f2ae65023025654df86ff1f743b145ba1899`.
- `57d48fb13c6aa5442668633d785a188c7a37ce05dac6a46d9f1d7e82717f6475`.

Fresh log paths are `/tmp/prime-power-order-root-main.log`, `/tmp/prime-power-order-root-checks.log`, `/tmp/current-auxiliary-order2011-root-main.log`, and `/tmp/current-auxiliary-order2011-root-checks.log`. The check logs have hashes `31d7c7bb08b174805a6a40e02f6c6c0567b78afc2244da346288c800087e30b5` and `3495b16063934dcb8c62cf805161124e322958847444825311525f0728a13601`; empty main logs have the standard empty-file hash.

The result proves the auxiliary prime-power order. Full CRT orbit coordinates, safe physical dummy placement, the rank constraint, positive Pell witnesses, the equation converse and internal ZFC formalization are separate obligations. The maintained decimal equation artifacts and all equation constants are unchanged.
