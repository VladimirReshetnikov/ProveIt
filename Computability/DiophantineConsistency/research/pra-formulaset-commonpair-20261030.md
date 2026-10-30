# One common bound for BV pair codes

`PRABVPairFamilyBound` proves in candidate PRA that the exact BV pair polynomial `q(p) = (p*p+p)^2` is nondecreasing. The proof uses monotonicity of Foundation pairing together with the previously proved exact equality `q(p) = ⟪0, ⟪p, 0⟫⟫`.

`PRAFormulaSetCommonPairBound` uses this fact in the positive formula-set client. For all relevant `p < s`, the single condition `q(s)+1 ≤ w` supplies the pair-code size bound, replacing separate assumptions for each index. Its closed candidate-PRA sentence still assumes the universal-formula and BV recursive histories, their bounds, and the stated bit-membership and size conditions for each relevant index.

The common pair polynomial is one explicit component of a larger prospective bound; it does not construct either history and does not finish the ZFC refutation or HA proof. The focused source-current replay is recorded in `reviews/pra-formulaset-commonpair-author-replay`, which also qualifies the shared 103-module parent whose root and private independent replays passed with matching hashes.
