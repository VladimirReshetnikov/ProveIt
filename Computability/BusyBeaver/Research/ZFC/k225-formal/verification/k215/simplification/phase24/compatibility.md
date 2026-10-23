# Phase24 compatibility notes

**The selected compatibility, exact-profile, independent actual and capture
checks pass.** The result concerns the fifteen maintained typed clients;
external clients retain their own obligations.

All old public declaration headers, binder names and imports are preserved.
Definitions and machine data are unchanged. Four public selector helpers are
added in `L2Lib254`: `L2.dec_brk`, `L2.dec_halt`, `L2.pass` and `L2.fall`.
The existing four `L2Dom` and three `L2Perm` helpers remain at their exact old
names and types, implemented as wrappers. The eight 254/222 dispatch endpoints
keep their exact hypotheses and conclusions. `L2Root222` opens the new names
locally; no export alias or wider import is added.

`Tarski.update_comm` moves unchanged to the already imported calculus module;
its namespace, statement and proof are retained. `TarskiClean` consumers still
receive it through the old import path. The sole removed declaration is the
private `raw_rel_iff` in `WFModelCore.lean`; its uses become applications of existing
`sat_translate_relOf`. No old public declaration is retired or strengthened in
this phase. Phase23's forty retirements and three stronger types remain
historical changes and are not counted again.

All fifteen accepted typed-client source hashes remain exact. Eleven clients
compile fresh and four reuse exact phase23 bindings. All 93 client reports,
five WFTheory reports and ten fresh endpoint-audit reports retain exact accepted
profiles. Every source-transitively affected provider compiles fresh; all selected
provider and audit logs have zero warnings. The
[independent actual readback](lean/result-review.json) and
[capture review](integration/capture-review.json) verify their respective bindings.

The generic selector rules preserve decrement, zero fall-through, enclosing
breaks and halt exits; they do not widen the existing cross-program transfer
relation. WF Replacement retains its formula-indexed interpretation and both
source guards. The semantic cut adds no totality premise. Existing section
premises and exact old axiom profiles remain required validation boundaries.

The literal 215-state machine, current halting/nonhalting endpoint and active
producer stay fixed. No PA-internal endpoint, minimum-state result, object-size
saving or comparative checking speedup follows from this source reduction.
The new static batch219 review remains separate; its future mixed-control and
scheduler leads are not compiled or adopted by this phase. Phase23's eleven
Lean evidence leaves remain immutable external history.
