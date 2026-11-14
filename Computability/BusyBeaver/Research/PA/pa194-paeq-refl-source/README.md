# Source equality-reflexivity axiom in the PAeq fixed theory

In every arithmetic model satisfying IΣ₁, `refl_translation` identifies the
actual `formulaCode 0` translation of Foundation's arithmetic equality
reflexivity axiom with the quote of the closed PAeq reflexivity formula.
`arithmetic_refl_mem` establishes that the source sentence belongs to
PeanoMinus. `translated_reflexivity_witness` then gives an explicit one-node
internal LK proof of this translation in the Δ₁ finite target theory; all
model elements may be nonstandard, though this particular source axiom and
proof are standard fixed formulas.

This discharges one finite source-axiom case. The other finite axioms, the
arbitrary internal induction-schema supplier, the Δ₁ full target theory, and
the connection of the PAeq target proof system to the PA194 machine remain
open.

From the repository root with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-paeq-refl-source/check.sh
```

The complete standalone script passed against the audited project and
Foundation overlays, rebuilding the local chain and checking the upstream
pins. The exported theorems' axiom audits contained no `sorryAx`.
An independent complete replay also passed without `sorryAx`.
