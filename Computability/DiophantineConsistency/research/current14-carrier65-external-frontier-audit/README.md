# Carrier65 retry05 prefix: external recorded frontier

This read-only inspection follows the **recorded** dependency routes of the
239 completed retry05 stages and the reachable portion of their 1,000-module
base. It does not run Lean, execute an object-header reader, modify preserved
evidence, or prove provider compatibility. The result is a bounded frontier,
not a complete compiled-object or dynamic-runtime closure. The earlier
[prefix feasibility audit](../current14-carrier65-retry05-prefix-feasibility/README.md)
checks the project-prefix objects and guard slots; the present inspection
focuses on their external boundary.

An [independent review](../../reviews/current14-carrier65-external-frontier-independent/README.md)
reconstructs the recorded routes and rechecks the bounded Foundation and
Mathlib observations; it does not establish provider closure.

## Recorded project-to-package routes

The 239 prefix records contain **343** external direct edges to **55** distinct
names: `Init` occurs 239 times and the remaining 54 names are Mathlib modules.
Those routes' recorded object hashes, selected realpaths and 2,145 distinct
recorded guard slots currently agree with the pinned plan and filesystem. The
prefix also names 39 distinct base seeds through 48 recorded direct edges.
Following only the pinned base records' project edges from those seeds reaches
**172** base modules through **240** recorded project edges; their retained
source snapshots, successful compile logs and output `.olean` hashes agree
with their records. These 172 records add **208** external direct edges to 23
names. Their 230 recorded selected-package guard paths currently agree.

The union of the two recorded external name sets has **69** modules: 65
Mathlib modules, `Init`, and these three Foundation modules:

* `Foundation.FirstOrder.Arithmetic.HFS.PRF`
* `Foundation.FirstOrder.Arithmetic.HFS.Vec`
* `Foundation.FirstOrder.Arithmetic.IOpen.Basic`

The complete name/count sets and selected path/hash observations are in
[`observation.json`](observation.json). This recursion follows the base
receipt's declared project edges, not the compiled import graph. It does not
show that the other 828 base records are unnecessary in the actual runtime or
that the 69 names exhaust package or toolchain dependencies.

## Available Foundation and Mathlib evidence

The pinned base state names the retained Foundation provider receipt. Its
three directly reached Foundation `.olean` hashes agree with that receipt.
The inspection independently rehashes all **477** files in the pinned
Foundation source archive, all **1,540** recorded Foundation artifacts,
all **140** target objects and source names, the build log/configuration,
and all **14,764** recorded provider external-guard paths. The earlier
[independent Foundation provider audit](../../reviews/foundation-provider-independent-audit/README.md)
recorded inner Lake exit zero and an observed `BUILT` line, but the wrapper's
outer process exit was not captured. These are retained build observations,
not a second Foundation build, authentication of all inherited package
objects, or a dynamic-load audit.

All 65 Mathlib objects in the combined frontier match their recorded direct
hashes and resolve into the retained Mathlib build tree. Their 650 selected
package artifact/companion slots (`.olean`, private/server variants, `.ir`,
`.ilean` and their recorded hash sidecars) also match saved guards. Their 65
current source files each match the corresponding Git blob at Mathlib commit
`81a5d257c8e410db227a6665ed08f64fea08e997`, the revision in the pinned
Foundation input manifest. Their current Lake `.trace` files are hashed in the
receipt, but neither the Git comparison nor a trace file proves that a
particular compiled object was produced from that source and its dependencies.
The contents and provenance of the trace output identifiers are not verified.

As an explicit **source-only next boundary**, a nested-comment-aware scanner
reads the simple initial import headers of those 65 current Mathlib files.
It records 634 explicit header edges to 546 distinct names; each named module
currently has a per-file `.olean` candidate under the package or toolchain
root. This is not Lean's namespace-first resolution, is not a compiled-header
traversal, and does not follow the 546 modules transitively. Two source lines
use `import all` (`Init.Data.Nat.Bitwise.Basic` and `Init.Data.Repr`), so an
actual closure analysis must account for import mode and any relevant private
companions instead of assuming `.olean` presence suffices. The scanner stops at
the first non-header command and is not a general Lean parser.

The pinned Lean binary and observed `Init.olean` hashes are recorded, but their
implicit imports, linked libraries, dynamic/native loads and runtime inputs are
not traced here. Hash/realpath caches and filesystem reads are non-atomic, so
intervening mutation remains possible. In particular, source Git identity,
matching Lake traces and matching direct guards do not establish that the 69
objects form a coherent transitive provider closure.

## Concrete remaining closure work

Before using this as evidence for a continuation, freeze or protect the exact
provider and toolchain snapshot, determine the target invocation's **actual
ordered roots and namespace-selection rules**, and inspect the `.olean` and
relevant `.ir` compiled headers recursively from the complete external seed
set. Include `Init`, all 65 Mathlib names and the three Foundation names, with
all required private/server/hash companions and every recursively selected
package/toolchain provider. Authenticate those objects and their producer
ancestry or explicitly document the accepted trust boundary, then separately
account for dynamic/native runtime loads and race-free input protection. The
existing [compiled-import closure prototype](../../reviews/compiled-import-closure-prototype/README.md)
may help investigate compiled headers, but it invokes Lean's reader and has
only a bounded sample for this provider; it was **not run** in this inspection
and its output would still not prove source-to-object provenance or runtime
closure. Any unknown input, changed path/hash, missing required companion or
ambiguous namespace route must remain a stop condition for a future guarded
runner. A completed survey is also not a proof of the Carrier65 endpoint by
itself.

The paths and Git checkout are retained environment artifacts and may change
or disappear. Reproduce the point-in-time receipt from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/current14-carrier65-external-frontier-audit/inspect.py | cmp - Computability/DiophantineConsistency/research/current14-carrier65-external-frontier-audit/observation.json
```
