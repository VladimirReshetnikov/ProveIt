# PAeq translation of standard syntax quotes in IΣ₁ models

`termCode_quote`, `atom_quote`, and `formulaCode_quote` identify the numeric
translation of each standard source term, atom, and formula with the quote of
its syntactic PAeq translation in every arithmetic model satisfying IΣ₁. The
formula theorem permits any model parameter, including a nonstandard one; the
source syntax argument itself is a standard Lean term/formula.

These are current-Foundation adaptations of the pinned PA196 calibration
proofs. They enable the finite source-axiom cases but do not prove a supplier
for arbitrary nonstandard induction-schema codes, an explicit finite PRA
proof transformer, or a machine equivalence.

From the repository root with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-paeq-quote-calibration/check.sh
```

The complete standalone script passed against the audited project and
Foundation overlays, rebuilding the local chain and checking the upstream
pins. The exported theorems' axiom audits contained no `sorryAx`.
An independent complete replay also passed without `sorryAx`.
