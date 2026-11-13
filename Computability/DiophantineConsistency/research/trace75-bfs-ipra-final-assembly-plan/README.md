# Held final assembly plan for the trace75 iPRA client

This plan fixes the five source stages in `plan.json`, SHA-256
`04559737ca02dc639ea0ac3a24bfd72997a9bae1f38c6d42b4da944b6a751dd6`.
It is **not a replay or a claim of a completed endpoint on the compatible
provider**. The parent result and its separately captured outer tool exit
are deliberately unpinned placeholders. Do not start an assembly build until
the 21-stage forward replay terminates, its result and outer exit are audited,
and their exact hashes and output root are pinned in a separately reviewed
runner. The direct imports listed below are requirements to check against
that actual result, not predictions that it contains them.

| Order | New module | Required direct imports |
| --- | --- | --- |
| 1 | `DiophantineConsistency.TenPositiveTrace75Syntax` | `DiophantineConsistency.TenPositiveTrace75`, `DiophantineConsistency.WeightedExpressionDegree` |
| 2 | `Trace75BFSSyntax` | stage 1, `Trace75Factors` |
| 3 | `Trace75BFSModelIff` | `Trace75BFSHaltGraph`, `Trace75BFSModelHalt`, `CompactSymbolicBetaCast`, `CompactSymbolicMaskData` |
| 4 | `Trace75BFSIPRA` | stages 3 and 2, `PositiveModelIPRAReferenceTranslated` |
| 5 | `Trace75BFSFixedIPRA` | stage 4 |

Stage 1's pinned source is the canonical syntax source, byte-for-byte, plus
one appended axiom-report command; `verify_sources.py` checks that relation.
Stage 2 binds the actual expression to the graph at every model valuation;
stage 3 joins the two model directions; stage 4 constructs the parameterized
positive bridge and native/standard/reference clients; stage 5 specializes
the four ports. Stages 2 and 3 are independent after their respective parent
requirements, but the above order gives a simple sequential build.

Before each Lean invocation, record and verify the first-selected `.olean`
and available companions for every direct import, including exact paths and
hashes. Every earlier stage import must resolve to that stage's actual
assembly output object, never to an exploratory object. Check the
Lean-resolved source import list and serialized headers against these selected
objects. After each stage, capture the actual process exit, diagnostics,
object/companion hashes and theorem-specific axiom reports: one for stages
1–3, six for stage 4, and five for stage 5. Reject any failure, warning,
`sorryAx`, missing or extra report, changed source or selected provider.
Recheck the parent and staged source/object inventories at the end and
capture the enclosing tool/runner exit separately. A later independent
result audit and an independent replay are separate from an author pass.

Use one private merged output union. In particular, stage 1 creates an object
inside the `DiophantineConsistency` namespace; simply prepending its output
directory to `LEAN_PATH` can hide that namespace in the parent provider.
Populate and inventory the parent namespace plus the stage-1 object in the
new union, without mutating the parent. Check that every intended output name
is absent before creating it and fail on any unexpected shadow or clobber.
The accepted reverse parent currently lacks all five assembly outputs and
the forward model-halt module, but the eventual forward result must be
checked directly rather than assuming this remains true.

`verify_sources.py` is a read-only source-byte and declared-import-order
check; it invokes no Lean and does not validate the future parent. Its local
author invocation exited 0. The [independent static plan audit](../../reviews/trace75-bfs-ipra-final-assembly-plan-independent/README.md)
verified the five stage sources and their declared order; it did not check a
future union or run Lean. A runnable assembly runner must additionally
pin and verify the final parent result and actual outer exit, parent union
and companion inventory, package/toolchain selections, source snapshots,
resource guard and independent prelaunch review. Mutation controls should
cover source, direct import, stage order, namespace shadowing, parent result,
failure/no-result handling and report acceptance.

Even an accepted assembly on the compatible parent would inherit four BFS
baseline source/object ancestry limitations: `ModelArithmetic`,
`ModelExponentialCongruence`, `PellOddFold` and `PellRecovery`. Other
unrebuilt project source ancestry, package-transitive and dynamic inputs,
and any noncaptured outside-provider history also remain inherited. The
fixed symbolic Lean expression is not a formal interpretation of an external
JSON, TeX or PDF. It is separate from the maintained original 14-variable
equation. None of these checks decides consistency or proves minimality.
