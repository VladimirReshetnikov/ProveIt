# Current repository integration check

Checked read-only on 15 November 2026 (Pacific time).

- Repository: `VladimirReshetnikov/ProveIt`
- Current main commit: `bce5113f44d613f5625c274128ee761f35486fc5`
- Primary technical-audit commit retained by this report:
  `0edaf721b175de6aa219755df18b1588be803a16`

## Findings

1. `Logic/PrimitiveRecursiveArithmetic/README.md` reports 66 delivered proof
   packets, 13 of them in foundations, and explicitly says the packets were
   filed as delivered rather than independently rerun or checked.
2. The finite-use framework packet has now been placed at
   `Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/`.
3. The later packet
   `docs/proofs/algebra/ipra_stable_observables/lean/ObjectObservation.lean`
   reports five compiled combinators with conclusions in the actual
   `Prf PRAAx` type:
   `boundedInvariantAt`, `loopProducesCertificate`,
   `observableOfIndependentCertificates`, `observableFromLocalStability`, and
   `twoLoopsStableObservable`.
4. These combinators can replace duplicated induction/implication plumbing in
   the finite-use formalization. They do not construct the viability table,
   prove rational arithmetic, or prove theorem-specific estimates.
5. The core `ConciseIPRA/Lean/ConciseIPRA/PR.lean` history shows no change after
   12 November 2026, so its relevant interface predates both audit commits.

## Claim discipline

The current-repository check is an interface and integration audit. No Lean
binary was available in the artifact environment, so the reported build of the
stable-observables packet was not independently reproduced. The repository's
unverified-packet caveat is therefore preserved verbatim in substance.
