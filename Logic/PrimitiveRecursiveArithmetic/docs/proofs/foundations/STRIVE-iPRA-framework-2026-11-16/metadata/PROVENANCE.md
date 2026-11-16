# Source audit and provenance

## Repository baseline

- Repository: `VladimirReshetnikov/ProveIt`
- Branch inspected: `main`
- Pinned commit: `58627ed89814ba122e1f0f012f1aba103cda267b`
- Inspection date: 2026-11-16

The packet treats the following repository components as authoritative checked
infrastructure at the pinned commit:

- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean`
  for `PR`, `PTm`, `PRAAx`, and `PRA.qfInd`;
- `ConciseIPRA/Deduction.lean` for `Prf`, substitution, weakening,
  simultaneous cut, and existential elimination;
- `Derivations/Lean/IPRADerivations/Core/{Basic,Order,Pairing,Powers,
  Division,Search,MultiSums}.lean` for arithmetic, coding ingredients, bounded
  search, and finite sums/products;
- `Bridge/` for closed and open transport to Foundation iPRA;
- `Derivations/README.md` and `Checks/Axioms.lean` for verification status.

## Prior framework boundary

STRIVE does not claim as new:

- finite demand closure, explicit residuals, trace reflection, backward
  viability, or stable observers (FINER-iPRA and related packets);
- the distinction between local and escaping certificates (Scoped Certificate
  Realization);
- dual bounded-game certificates as an abstract schema (CBIP and the finite
  strategy research note);
- finite nets, moduli, reverse precision demands, quotient/metric observers, or
  producer/verifier separation (earlier foundation packets).

The new focus is a concrete realization layer that earlier blueprints left
abstract: heterogeneous strategy-table bounds and natural-number codes, exact
positive/negative checker recursion, and an integration path using the current
checked division, power, sum, search, and open-sequent APIs.

## External references

No external theorem is imported as an unproved mathematical premise.  The
report uses standard elementary facts about finite products, mixed-radix
notation, and structural induction, all reproved in the form needed for iPRA.

Useful repository URLs:

- https://github.com/VladimirReshetnikov/ProveIt/tree/58627ed89814ba122e1f0f012f1aba103cda267b/Logic/PrimitiveRecursiveArithmetic
- https://github.com/VladimirReshetnikov/ProveIt/blob/58627ed89814ba122e1f0f012f1aba103cda267b/Logic/PrimitiveRecursiveArithmetic/UNIFICATION-PLAN.md
- https://github.com/VladimirReshetnikov/ProveIt/blob/58627ed89814ba122e1f0f012f1aba103cda267b/Logic/PrimitiveRecursiveArithmetic/Derivations/README.md
- https://github.com/VladimirReshetnikov/ProveIt/blob/58627ed89814ba122e1f0f012f1aba103cda267b/Logic/PrimitiveRecursiveArithmetic/Bridge/README.md
