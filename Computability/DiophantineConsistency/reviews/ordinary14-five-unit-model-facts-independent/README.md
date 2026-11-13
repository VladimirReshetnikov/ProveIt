# Independent source review: five-unit signed-pair facts

The first pair is oriented as `(x², (m·k)(m·k+k))`. Its negative-unit equation is exactly `x²+1=(m·k)(m·k+k)`, whose right side is `m(m+1)k²`; the imported `consecutive_ne_negative` uses the same model context and requires `2≤m`, with no positivity requirement on x or k. The bound cannot simply be dropped: m=x=k=1 gives a negative unit.

For `product5_positive`, the binder and argument order is first pair, q, r, unrestricted s, t. The supplied product hypothesis has the exact `Equivalent ... (natural 1)` orientation. The three residue hypotheses on q, r and t combine with `negative_residue` in the right direction, and the guard s has no independent sign hypothesis. The output asserts all five pairs have positive unit difference. This is a fact about the explicitly supplied signed pairs and product; the graph's pair representation, its m bound and its modulo-four premises remain separate obligations.

The independent checker compares the relevant declarations and transitive direct import, replays the author's receipt, checks 7,979 finite first-factor identities/exclusions, and tests 59,049 small natural-pair assignments using pair multiplication and cross-sum equality. Its controls include negative-guard product-one cases and examples showing that each of the four negative-unit exclusions matters for the generic factor rule. Run `python3 -I -S -B reviews/ordinary14-five-unit-model-facts-independent/check.py` from `Computability/DiophantineConsistency` and compare against `observation.json`.

This is a source and finite-control review, not elaboration in Lean, a provider audit, an internal graph equivalence, or a proof of the iPRA endpoint. The controls do not establish the unbounded model theorems.
