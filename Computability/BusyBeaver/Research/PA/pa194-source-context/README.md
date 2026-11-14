# PA194 source-context compilation and adjunction interface

`compileContext` consumes a local PA194 source-LK derivation of a conclusion
from a finite list of source assumptions, a finite PA194 proof supplying the
translated code of each assumption, and the explicit name and budget bounds.
It constructs a finite PA194 proof of the translated conclusion. The local
source-LK port and its limitations are described in `pa194-source-lk`.

`adjunctionPremises` unconditionally supplies the five translated source
premises used by the upstream exact-adjunction argument: weak adjunction,
one separation instance, and equality reflexivity, symmetry and congruence.
It assumes `0 < lo` and `lo + 6 < z`. The conditional theorem
`adjunctionSupplierConditional` further requires an explicit local
`SourceLK` derivation of the adjunction instance from those five assumptions
and the bound `lo + 2 + lkBudget d ≤ z`; constructing this `d` remains
open. The theorem does not assume or establish PA consistency, a PA proof
translation, machine nonhalting, or internalization in PA/PRA.

The source files adapt the pinned upstream context and adjunction interfaces
to the checked local calculus and current `LO` Foundation; the hashes in
`upstream.sha256` identify the source material, not a definitional equality
between Foundation versions. The axiom reports contain `propext`,
`Classical.choice` and `Quot.sound`, with no `sorryAx`.

From the repository root, set `IPRA_FOUNDATION_OVERLAY` to the audited
Lean 4.32 Foundation objects and run `bash
Computability/BusyBeaver/Research/PA/pa194-source-context/check.sh`.
It rebuilds the nested source-separation chain in tmpfs, checks upstream
hashes and rejects `sorryAx` in the printed theorem dependencies. The two
new modules were checked in an overlay replay; the full standalone script
has not yet completed.
