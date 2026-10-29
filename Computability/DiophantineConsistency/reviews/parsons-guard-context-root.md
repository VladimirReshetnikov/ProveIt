# Finite marked guard contexts

`ParsonsGuardContext.Good` requires a finite marked context to carry a
`Guard` descriptor for each side occurrence; base and induction-block entries
are allowed. `shift_good` preserves this condition under a fresh-variable
shift. `sigma_or_universal` shows that either the projected disjunction of the
whole context is Σ₁, or a specific universal side occurrence can be selected
in place. The sum of side-formula complexities is invariant under shifting
and strictly decreases when such an occurrence is opened (`cost_open`).

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`; both objects and complete logs match. The
axiom reports list only `propext`, `Classical.choice`, and `Quot.sound`. The
[16-file replay manifest](parsons-guard-context-replay/FILES.json) has SHA-256
`07b37076f7c704cbd8b79292f22b4af473afd62d4580db58b0aa3a6c09ed2312`.
The direct `ParsonsGuardRewrite` source hash
`b8d4b86e32ed5a2fe28d0602eb070d436cbfa109ae9caf3e95907a9562210463`
matches its frozen snapshot, and its object hash is
`9e160d47f05156bd35199c21482c98a1209238f065f81f9468232ea4007284a3`.
Earlier provider chains, Foundation/Mathlib, and completeness objects remain
an inherited boundary, not a fresh transitive source audit.

The descriptors are hypotheses; these results do not establish that arbitrary
Π₂ sides have them. The structural measure is separate from derivation height
and does not itself prove the global recursion, conservation, or the PRA
provability target. The separate HA result for the maintained 14-variable
equation is complete.

A third independent replay at `/tmp/parsons-guard-context-build-uq81ukw2`
passed with matching sources, objects, and full logs under the same inherited
provider boundary.
