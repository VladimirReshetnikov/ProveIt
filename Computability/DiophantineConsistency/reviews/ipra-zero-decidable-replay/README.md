# Conditional native zero decidability

This source-directed suffix checks that native iPRA proves `∀ x, x = 0 ∨ ¬(x = 0)` from the explicit premise that it proves `∀ x, x + 1 ≠ 0`. It constructs the base from native reflexivity and uses the actual parameter-free native open-induction instance. The premise is not proved here; no equality or order decidability is claimed.

The parent is the independently replayed finite-closure specialization provider. Its historical project-object and external package ancestry, including five unrelated post-merge source guards excluded by that parent, remain inherited. Both runs use a package-only fallback and guard the selected project objects, current source files and direct external objects.

Reproduce: `python3 Computability/DiophantineConsistency/reviews/ipra-zero-decidable-replay/replay.py`.

The author `/tmp/ipra-induction-nozero-5j_7qnf3` and independent peer `/tmp/ipra-induction-nozero-gp00c0jz` both passed. Every source, object and full-log hash matches. The check reports only `propext`, `Classical.choice` and `Quot.sound` as Lean metatheory axioms. Both runs share the authenticated parent and inherited ancestry.
