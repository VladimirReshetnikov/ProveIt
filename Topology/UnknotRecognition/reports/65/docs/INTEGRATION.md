# Integration notes and gate checklist

## Reviewed baseline

Revision: `3a90fb34146c915328ab8eac6250cc2514f74ed0`.

The current maintained synthesis already documents a canonical source-checked diagram-to-exterior construction (20 max(1,n) tetrahedra) and normal-component / compressing-disc certificate APIs. Do not describe the source bridge as absent based on older predecessor drafts.

Relevant existing entry points, as documented in the reviewed synthesis:

- `normal_surface_components.normal_component_census`
- `normal_component_verify.verify_normal_component_certificate`
- `normal_disk_kernel.normal_compressing_disk_count`

This report has not run those entry points or the maintained regression suite. It supplies no adapter purporting to have done so.

## Producer-to-kernel contract

For each candidate family supplied to `reduce_family`, authenticate:

1. Every connected component of each partial object is a disk and has at least one live arc.
2. Each label denotes one genuine connected, proper, closed boundary interval; different labelled intervals have disjoint endpoints and collars. Binary point ports or bundles are not interchangeable with these intervals.
3. All alternatives share a type that makes every permitted complementary surface and arc map equally geometrically admissible, independent of the omitted connectivity partition. Include boundary order, region, matching, framing, normal data or source information when relevant.
4. Costs are scalar binary integers and future contributions are additive. Store actual witnesses, not only partitions.
5. Essential-boundary parity, when used, comes from verified boundary chains and torus cocycles. Reduce separately for the four values.

The reducer cannot infer any of these geometric facts from the partition tuple. Its expansion certificate only proves the resulting finite algebraic pruning statement.

## Trust layers

- **Algebraic evidence:** `certificate_check.verify_certificate(original_partitions, original_costs, certificate)`. This imports no producer modules. The original family must come from the caller's authenticated source.
- **Abstract topology:** `assembly.replay_surface` reconstructs the selected polygon disks and invokes `surface_model`. It checks an abstract triangulated surface, not an ambient embedding.
- **Native embedding:** NOT IMPLEMENTED. Export an actual embedded surface with normal matching / local gluing evidence and validate it independently.
- **Input knot source:** Use the maintained source-checked exterior construction. Never substitute an unrelated torus-boundary manifold.
- **Search completeness:** NOT PROVED for a general knot exterior. Exhausting a finite candidate grammar only proves absence in that grammar.

## Recommended placement and dispatch policy

Intake should place this as the next `reports/<NN>/` package, without applying it to `fast/`. A suggested catalogue row is in `docs/catalogue_entry.md`. No specific report number is reserved.

A later runtime integration should be opt-in and have three-valued behavior. A verified embedded essential disk may yield a positive unknot certificate through the source theorem. Exhaustion of an unproved grammar must be inconclusive and leave the maintained exact fallback available. No default performance claim is justified by the abstract benchmarks.

## Resource engineering still required

The reducer supports a caller-supplied cooperative callback and checks width before allocating its vector. The independent checker has its own width cap. The complete grammar solver is currently an experimental finite evaluator without a shared global time budget. Add cancellation during validation, candidate generation, elimination, evidence serialization and replay; charge type discovery, full witnesses and actual arc counts. Do not reinterpret a width cap, failed evidence, or allocation failure as a negative knot result.

## Acceptance gates for an actual native integration

A useful first integration milestone is an exporter for **supplied known disks**, with source-bound interface geometry, boundary parity and embedded witness replay. Then compare abstract and native outputs. After that, supply a candidate generator and prove its completeness and encoded cost. Run the full native regression suite and paired whole-pipeline benchmarks including failed searches and the one-query overhead control. These gates are unexecuted in this package.
