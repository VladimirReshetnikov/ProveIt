# Intuitionistic refutation negation: conditional logical step

The guarded author run `/tmp/ipra-refutation-logic-gn0csy2d` passed. In Foundation's intuitionistic Hilbert calculus and for arbitrary source proposition `rho` and intuitionistic proposition `ordinary`, `translatedNegationEquivalent` constructs an actual Hilbert proof of `(∼rho)ᴺ ↔ ¬ordinary`, given explicit Hilbert proofs `ordinary → rhoᴺ` and `rhoᴺ → ¬¬ordinary`. It uses intuitionistic propositional rules and Foundation's `Derivation.negDoubleNegation`; it assumes no arithmetic axioms or model semantics. This is a conditional logical lemma, not an iPRA theory, not a proof of either premise, and not yet a binding to the exact ZFC refutation formula.

The proof and check modules were built from frozen source snapshots. Five directly relevant external Foundation source/object pairs and the Lean executable were hashed before and after the run; those are inherited anchors, and the run does not prove that the objects were built from those sources or authenticate their transitive package ancestry. The check log reports Lean metatheory axioms `[propext, Classical.choice, Quot.sound]`; the produced object-language calculus is intuitionistic. Independent replay is required.

Replay: `python3 Computability/DiophantineConsistency/research/ipra-refutation-logic/build.py`.

- `IPRARefutationNegationLogic`: source `d02f38bcd22fe055fc61a6890e19181fddfa1e17a4b1f207efa7fea7792467f5`, object `552bfc0e973fe5df053be1eba247ec627159ef18924d9d27fe85abe3652b028d`, full log `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `IPRARefutationNegationLogicChecks`: source `f7c2a8187f2a90d4e7375f99d0a91ce542c8485cf4e95984aa405efc800a4d95`, object `f598af52e809f65d3d63294e22963f64cba60d3591db998d9300b915e2920350`, full log `6d1959b5a32ffc43690db11a97d3c1e4e6f0a2697a6eb1b799ba87770b01d610`.

State `8001d845e895b794645bcbe607c796f0850170a39a282bd48ff0d648f41cc26b`; manifest `f2c8ee2a8c5cf71c28f8329fdafb8ad656e8bf36e411a13fc5575a26e48fe802`.
