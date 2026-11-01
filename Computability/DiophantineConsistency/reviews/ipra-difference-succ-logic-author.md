# Native open successor invariant: author replay

Guarded author run `/tmp/ipra-difference-succ-logic-0hojpt1x` passed on the independently checked successor-equality provider `/tmp/ipra-difference-succ-eq-fjr41bz0/lib`. For arbitrary open terms `x,y`, the client constructs the native implication from the actual invariant at `x` to its instance at `Sx`, using native zero decidability, native `Sx−y=0 → x−y=0`, and the checked native `x=y → Sx−y≠0`.

The proof still requires an explicit open native positive-branch proof `y−Sx=0 → (y−x≠0 → Sx=y)`. This client does not produce that branch, translate `Sx` to the induction schema's `x+1` term, or close the induction step universally. Sources and selected parent objects were reauthenticated before and after compilation. Project/Foundation and package transitive ancestry remain inherited and historical; the Lean axiom check records the standard metatheory axioms.

Replay: `python3 Computability/DiophantineConsistency/research/ipra-refutation-logic/build-difference-succ-logic.py`. State SHA-256 `dc9fb234c904a114d28cf36daf09a99b971e88d39671a0076d96e8e79857599b`; provider inventory `81376c1d427bcc1e1fcab964b37954e9420e2327ccafbf6171e50e8ef3efc08e`. Sources, driver, logs, state and inventory are retained in the evidence directory.
