# Read-only fixed85 source selection with nine alternatives

This is a **logical source-selection plan**, not a Lean build plan or an
elaborated proof. It combines the fixed85 lexical source snapshot with the
isolated sign-free replacement and eight further abstract-model tactic
alternatives. Historical source files and receipts are not changed.

`selection.json` records one selected repository-local source and one virtual
logical `.lean` path per reachable local module. The nine overridden logical
names select the isolated alternative bytes; the originals remain available
as pinned historical files and are not selected by this plan. The remaining
local selections retain their paths and hashes from the earlier fixed85
manifest. The plan has:

* 1,354 selected local logical modules and nine explicit source alternatives;
* 93 unresolved/external import **names**, with `Mathlib.Tactic.Omega` no
  longer present in the lexical frontier after the proposed replacements;
* no cycle in the selected local lexical import graph, and a dependency-first
  local order;
* 55 local modules reverse-reachable from the overrides, including the fixed85
  root. This is a source-dependency observation, not a verified rebuild set.

The original same-name modules and the alternative files must never be loaded
together under the same declarations. The recorded paths assign unique
logical providers **within this JSON plan only**. The virtual logical paths
are labels; the files have not been copied, staged, compiled, or selected in a
Lean environment. Nothing here establishes package roots, import precedence,
external module resolution, compiled object collisions, provider provenance,
source/olean consistency, axiom boundaries, disk availability, or a safe
execution schedule. In particular, the eight alternatives still need their
own review and Lean elaboration.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-fixed85-source-selection-plan/check.py
```

The check reproduces the recorded selection from pinned local-source and
alternative receipts, confirms unique logical labels and a local lexical
order, and compares the frontier **names** to the baseline. It does not open
or verify external package files or compiled objects and does not execute
Lean. Consequently, neither this plan nor its receipt establishes the native
85 endpoint, a proof in iPRA, or a connection to the displayed PDF.
