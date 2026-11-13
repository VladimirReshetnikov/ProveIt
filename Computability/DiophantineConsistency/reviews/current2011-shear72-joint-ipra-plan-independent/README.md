# Independent review of the 72/46 joint source plan

The selected 15 draft sources form a reachable acyclic lexical import graph
with 11 direct frontier names, and the joint client's map and endpoint
argument directions match the reviewed source interfaces. The one-line
forward import reconciliation is exact. No concrete error was found in this
bounded source review, but this is not a Lean dependency resolution, compiled
proof, provider closure or iPRA endpoint.

The independent checker verifies each selected byte hash and direct import
header, constructs the reachable closure and a separate Kahn topological
order, and checks that the frontier is exactly the set of nonselected direct
imports. The alternate forward source differs from the original only by
replacing `import Shear72Literal` with
`import DiophantineConsistency.Shear72Literal`; this makes the forward,
reverse and conditional sources refer to one selected logical module name.
It does not establish that any such logical name will resolve to the selected
file when Lean runs. The parent-to-child and child-to-parent maps are passed
in that order to `same_no_zero`, the bridge and the conditional endpoint;
the maps may change their valuations. The previously reviewed no-zero and
translated-consistency directions are preserved.

## Bounded frontier observations

The separate `observation.json` records point-in-time file and receipt
observations at explicitly named paths. It is not exhaustive, may change when
`/tmp` changes, and does not test Lean's actual search order or dynamic loads.

- The four historical 71/60 Generic, Literal, Model and IPRA objects exist
  and their bytes match their respective successful producer receipts. Each
  receipt records the selected source hash, Lean exit 0, outer exit 0 and
  a set of stable guard slots. This review rechecked the source-guard and
  output match, not every recorded slot or complete transitive ancestry.
- `ArithmeticPellFirstIndex` exists with a source-matched per-module record
  and object hash in the retained fresh current14 state. `ModelDifferenceRing`
  exists with a source-matched per-module compile record in the 106 stage;
  the enclosing 106 build later reported a client failure. Neither record
  alone authenticates the full transitive provider closure of this new plan.
- The surviving `ArithmeticCarrier94Extraction` object matches the successful
  stage receipt, but that stage used the private source SHA `415e74a2...`,
  while this selection pins workspace source SHA `5e7ef8c7...`. The retained
  private/workspace diff removes only `zero_mul,one_mul` from one `simp only`
  list. It is still a source-byte mismatch; a reviewed alternative selection
  or a new source-matched build and coherent provider check is required.
- A candidate `HAExpressionNoZeroEquiv` object and a candidate
  `ModelCarrierSpheres` object exist at the sampled paths, but this review
  did not authenticate their producers or compatibility with the selected
  sources. `Mathlib.olean` exists at the sampled package path and is an
  unexamined external provider.
- No `ZRows/CoprimeSquares.olean` exists at the two named overlay/workspace
  slots tested. A broader `/tmp` name search also returned no occurrence but
  encountered inaccessible directories, so this is not a global absence
  claim. The selected magnitude source uses that module's `abs_eq_ι`, whose
  source is the direct `ModelDifferenceRing.nonneg_iff` application to
  `abs_nonneg`; a different source/import selection may eliminate this
  frontier but needs separate review and Lean checking.

None of these observations authenticates an entire coherent set of objects,
external packages, implicit/runtime dependencies, shadow collisions, axiom
closure or the new draft declarations. The original strict disk guard remains
in force; at this review the workspace was below its 5.1 GB free-space floor.

From `Computability/DiophantineConsistency`:

    set -o pipefail
    timeout 30s python3 -I -S -B research/current2011-shear72-joint-ipra-source-plan/check.py | cmp - research/current2011-shear72-joint-ipra-source-plan/receipt.json
    timeout 30s python3 -I -S -B reviews/current2011-shear72-joint-ipra-plan-independent/check.py | cmp - reviews/current2011-shear72-joint-ipra-plan-independent/receipt.json
    timeout 40s python3 -I -S -B reviews/current2011-shear72-joint-ipra-plan-independent/observe.py

The last command prints a fresh observation; compare it to `observation.json`
only while its temporary inputs remain unchanged. No Lean, build, staging,
provider mutation or historical evidence mutation was performed.
