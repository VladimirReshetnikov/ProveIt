# A generic semantic spine for the current K215 endpoint

Baseline: ProveIt `cbf94cb552a3b49509e0eee80e7455d4eb5974c6`.
Status: **uncompiled proposal**. The checked result here is a data-only
source/import/body-preservation audit, not Lean elaboration or kernel checking.

## Main result

The proposed import cut changes the selected `KEndpoint215` project closure
from 174 modules / 1,752,650 bytes / 37,648 lines to 168 modules / 1,725,295
bytes / 37,117 lines: **6 fewer modules, 27,355 fewer bytes, 531 fewer lines**.

This is not a whole-repository deletion. Keeping every legacy adapter under
its original public namespace requires four new Core modules and adds
**1,152 bytes and 46 lines** to the twelve-file maintained-source footprint
relative to the eight changed original files. No runtime, binary-state,
kernel-axiom, proof-term-size, or compilation-time improvement is claimed.

## Why this is a new cut, rather than the earlier quotient unification

The current revision already makes `QuotientModel` a CP/GIC specialization
of the shared `KQ1*` quotient. Nevertheless four generally useful semantic
files still import that specialization to prove a few final adapter lemmas.
K215 imports their generic results, and so imports the CP-specific lane as a
side effect. The shared quotient refactor removed duplicated proofs, but did
not remove this dependency direction.

The new boundary says: generic finite-set, Infinity, and internally
well-founded-part results depend on their stated semantic hypotheses;
CP/GIC models instantiate those results in compatibility modules, not the
other way around. K215's tagged structure supplies `QHyp`, not the stronger
raw CP container property. No extra CP hypothesis was logically assumed by
the old proofs; the improvement is making the source graph match their
actual premise graph.

## Exact source decomposition

All paths below are under `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/`.

- `SingletonInfinity.lean`: move the generic prefix before line 136 to
  `SingletonInfinityCore.lean`. Retain `quotientBase` and `quotient_index`
  (lines 136--152) in the old-name wrapper.
- `FiniteSets.lean`: move the generic prefix before line 157 to
  `FiniteSetsCore.lean`. Keep the five-line `quotientBase` specialization.
- `InductiveAttempts.lean`: move the generic prefix before line 321 to
  `InductiveAttemptsCore.lean`. Keep `quotientFiniteBase`,
  `quotient_infinity`, and `quotient_inf_form` in the old module.
- `WellFoundedPart.lean`: move the prefix before the comment at line 219
  to `WellFoundedPartCore.lean`. Keep `quotient_wf_closure` and
  `quotient_domain_nonempty` in the old module.
- Change `WFRelativization`'s import to `WellFoundedPartCore`.
- Change `KQ1ZF`'s import to `InductiveAttemptsCore`.
- Change `KLowerQHyp`'s import from `QuotientModel` to `KQ1Model` and its
  two calls at lines 143 and 146 to `KQ1Model.memberForm` and
  `KQ1Model.sat_memberForm`. At this exact baseline the former is a
  definitional abbreviation and the latter a direct forwarding theorem in
  `QuotientModel` (lines 41 and 47--49).
- Add an explicit `WellFoundedPart` import to `WFModel`. Its
  `quotient_models_ZF` proof uses `quotient_wf_closure`, which previously
  arrived transitively through `WFRelativization`; the explicit import
  preserves that compatibility use without restoring the K215 leak.

All four generic bodies and all eight final CP adapter declarations are
preserved verbatim. The original namespaces are retained, so theorem and
definition names do not change. The patch adds no axioms, admissions, or
new semantic assumptions. It needs a fresh compile because changed imports
can affect available names, instances, and simplification environments.

The six legacy CP-specific modules absent from the proposed endpoint are:
`QuotientModel`, `QuotientSeparation`, `QuotientBasic`,
`QuotientReplacement`, `QuotientPower`, and `QuotientCPGIC`.
The four old mixed modules also disappear from that selected closure, but
are replaced by their four Core counterparts. The `KQ1Model`, `KQ1Basic`,
`KQ1Separation`, `KQ1Replacement`, `KQ1Power`, and `KQ1Collect` proofs remain.

## Mathematical interfaces and why the split is legitimate

1. `SingletonInfinity.Base mem` has only extensionality, exact pairs, and
   formula-indexed Separation. The least singleton-closed index proof uses
   exactly these fields, a root, and an already supplied singleton-closed
   container. It is independent of a quotient representation.
2. `FiniteSets.Base mem` extends that base with exact Union. Its finite
   constructors and graph formulas are likewise representation-independent.
3. `InductiveAttempts.ordinary_infinity_of_container` takes this finite
   base; formula-indexed functional Replacement; an empty root `e`; a set
   `Y` containing `e`; and closure of `Y` under exact singleton. Its
   conclusion is an ordinary von Neumann-successor inductive set. The
   generic theorem at lines 308--319 has no CP/GIC or quotient argument.
4. `WellFoundedPart.wf_closure B a hG ha` assumes the finite base, one
   displayed first-order GIC instance
   `Sat mem (fun _ => a) (gicForm witnessForm)`, and that every member of
   `a` lies in the internally well-founded part. It concludes that `a`
   lies in that part. Here `witnessForm` expresses a transitive internally
   well-founded witness containing the input. Collection gathers witnesses,
   their union is internally well-founded, and adjoining `a` supplies its
   witness. This uses represented subsets and the given formula instance,
   not external well-foundedness or Collection for arbitrary predicates.

These existing interfaces prove that the generic declarations can precede
the CP instantiations. The source transformation does not replace a
mathematical proof by a stronger hypothesis; it moves exactly the existing
proof across the source boundary matching its hypotheses.

## Checks performed

Run from any directory:

`python -I -B lean/audit_generic_spine.py`

The checker requires this `lean/` directory alongside `review/snapshots/current/`,
`review/snapshots/compatibility/`,
`review/source_manifest.json`, and `review/current_source_ledger.json`.
The archive retains the full 203-source current snapshot. A compact fallback
mode can check the 174 endpoint sources plus `current/WFModel.lean` under
`compatibility_source_manifest.json`, but is not the archive's full mode.
It is new proposal-owned Python,
not a repository program. It rejects optimized Python and uses explicit
failures rather than removable assertions. It writes nothing and executes
neither Lean nor any received source.

It verifies SHA-256 and Git blob identity for all 203 pinned source snapshots
(including the 174 current endpoint modules and selected compatibility
sources), reconstructs both endpoint import closures, detects unresolved imports
and import cycles, verifies the four exact generic-body moves and eight
adapter tails, restricts the four client changes to their exact intended
edits, checks the alias facts, reconstructs the unified patch byte-for-byte,
and reproduces all reported metrics. `audit_result.json` is the recorded
PASS output. `Init` is the only deliberately excluded standard import;
these are project-module/source counts, not a census of Lean's core.

Independent reviewers reproduced the import-cut counts. These checks do
not establish that the new source elaborates or that the endpoint kernel
proof has been rechecked.

## Adoption and acceptance gates

1. Apply `generic_spine.patch` to the exact pinned source, then fresh-check
   the four Core modules and their existing wrappers. Preserve source
   attribution comments; no public name or theorem statement is deleted.
2. Fresh-check `WFRelativization`, `WFModelCore`, `KQ1ZF`, and
   `KLowerQHyp`, followed by the affected dependency cone and unchanged
   K215 endpoint/audit clients. Record exact source/object hashes and full
   compiler output. Request the same axiom reports as the current endpoint;
   do not inherit historical reports as evidence for changed bytes.
3. Separately fresh-check the legacy wrappers and their clients,
   particularly `WFModel` and `WFTheory`. The explicit `WFModel` import
   fixes one identified transitive-export dependency; broader repository
   consumers still need a full producer/consumer search and compatibility
   rebuild. A client that relied on a leaked specialization should import
   the specialization explicitly, not force it back into a Core module.
4. Repeat the import audit as an acceptance guard: generic semantic Core
   modules must not acquire `Quotient*` CP adapter imports. Keep both
   selected-endpoint and total-maintenance metrics visible.

The pinned `k225-formal` directory listing (`formal_directory.json`)
contains no active `generate_kq1.py` or generator named for the four generic
semantic modules. The inspected `generate_endpoints_lean.py` emits only
machine-specific `KEndpoint{n}` files, none modified by this patch. No
received generator was run. This is a scoped producer check, not proof of
absence of every possible external or archived producer; repository-wide
regeneration/consumer compatibility is an explicit adoption gate.

## Primary sources

All source URLs use the exact baseline:

- https://github.com/VladimirReshetnikov/ProveIt/blob/cbf94cb552a3b49509e0eee80e7455d4eb5974c6/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/SingletonInfinity.lean#L136-L152
- https://github.com/VladimirReshetnikov/ProveIt/blob/cbf94cb552a3b49509e0eee80e7455d4eb5974c6/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/FiniteSets.lean#L157-L161
- https://github.com/VladimirReshetnikov/ProveIt/blob/cbf94cb552a3b49509e0eee80e7455d4eb5974c6/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/InductiveAttempts.lean#L308-L345
- https://github.com/VladimirReshetnikov/ProveIt/blob/cbf94cb552a3b49509e0eee80e7455d4eb5974c6/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/WellFoundedPart.lean#L155-L176
- https://github.com/VladimirReshetnikov/ProveIt/blob/cbf94cb552a3b49509e0eee80e7455d4eb5974c6/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/WellFoundedPart.lean#L219-L233
- https://github.com/VladimirReshetnikov/ProveIt/blob/cbf94cb552a3b49509e0eee80e7455d4eb5974c6/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/QuotientModel.lean#L41-L49
- https://github.com/VladimirReshetnikov/ProveIt/blob/cbf94cb552a3b49509e0eee80e7455d4eb5974c6/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KLowerQHyp.lean#L141-L146

