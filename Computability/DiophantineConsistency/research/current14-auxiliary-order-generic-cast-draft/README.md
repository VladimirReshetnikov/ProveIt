# Auxiliary order generic cast proof: source draft

This source-level proof refactor moves the two `Nat.cast_pow` simplifications to private lemmas over abstract base, exponent and prime, then specializes them to the unchanged original theorem statements. Every other source byte is retained and the original project file is untouched. It does not change assumptions or assert new mathematical claims beyond these generic consequences. Lean syntax, type checking, kernel memory and resource feasibility remain untested.
