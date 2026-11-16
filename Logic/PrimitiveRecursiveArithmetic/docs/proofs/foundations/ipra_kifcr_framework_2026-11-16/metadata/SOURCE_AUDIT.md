# Source audit

## Snapshot

- Repository: `VladimirReshetnikov/ProveIt`
- Branch: `main`
- Pinned commit: `31784f0710fa04ccd8ee863ce9bad91fb1d8cf88`
- Audit date: 2026-11-16, America/Los_Angeles
- Access method: current GitHub repository interface; no full clone/build was
  available in the artifact container.

## Current files inspected

- `Logic/PrimitiveRecursiveArithmetic/README.md`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/README.md`
- `Logic/PrimitiveRecursiveArithmetic/Derivations/README.md`
- `Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations.lean`
- `.../Core/Basic.lean`
- `.../Core/Search.lean`
- `.../Core/Pairing.lean`
- `.../Checks/Axioms.lean`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/README.md`
- `.../docs/proofs/foundations/ipra_framework/README.md`

## Important current findings

1. `Derivations` exports actual `Prf PRAAx` theorems, not only semantic Lean
   propositions.
2. `Core.Search` already contains checked least bounded search, foundness, and
   minimality; KIFC-R wraps it instead of reimplementing search.
3. `Core.Pairing` already contains checked pairing/projections and two-track
   simultaneous recursion.
4. The current core additionally includes division, gcd, Bezout, Euclid,
   bounded/multiple sums, reflection/reindexing, pigeonhole, permutations,
   descent, and linear algebra.
5. `docs/proofs` currently reports 78 filed packets and explicitly does not
   claim that the packet corpus was collectively rebuilt or verified.

## Prior framework artifacts compared

- `ipra_kifc_framework_2026-11-15.zip`
- `cfp_contract_compiler.pdf`
- `cifer_ipra_framework.pdf`
- `framework(1).pdf`
- current `docs/proofs/foundations/ipra_framework`

KIFC-R retains their finite-interface, contract graph, viability, observer,
finite-net, and producer/verifier ideas. New/current contributions are:

- rebase to the current checked derivation library;
- search adapter rather than a second search blueprint;
- canonical residual formulas in the final sequent;
- capped cyclic demand closure with overflow diagnostics;
- revised module map and formalization order.

## Limitations

This artifact did not run the upstream Lean project. New Lean files are
explicit outlines. Inherited results are identified by current source path and
commit. Deep packet results are not upgraded beyond their inspected proof
status.
