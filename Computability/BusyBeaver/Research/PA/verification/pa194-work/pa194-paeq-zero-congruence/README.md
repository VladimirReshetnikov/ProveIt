# Translated source zero-function congruence

`source_zeroExt_mem` identifies Foundation's congruence axiom for the
arithmetic zero function as a PeanoMinus axiom. Its actual PAeq syntactic
translation is `⊤ → 0 = 0`. The checked target proof derives this sentence
from the fixed reflexivity axiom by universal elimination and disjunction
introduction; it is a genuine Foundation proof object, not a new target axiom.

`internal_zeroExt_proof` quotes that proof and proves internal provability of
the actual numeric translation in every arithmetic model satisfying IΣ₁. This
is one standard finite source-axiom case. The remaining finite source cases,
arbitrary internal induction-schema supplier, and link from PAeq target
proofs to the literal PA194 machine remain open.

From the repository root with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-paeq-zero-congruence/check.sh
```

The complete standalone script passed against the audited project and
Foundation overlays, rebuilding the local chain and checking the upstream
pins. The exported theorems' axiom audits contained no `sorryAx`.
An independent complete replay also passed without `sorryAx`.
