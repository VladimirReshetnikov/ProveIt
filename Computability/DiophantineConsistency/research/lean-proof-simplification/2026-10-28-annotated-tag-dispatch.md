# Annotated tag-dispatch experiment

Two local validator proofs in `AnnotatedRenameLocal` and `AnnotatedBoundLocal`
check tags 0–7 in separate, similar branches and reject tags at least 8. Three
isolated alternatives grouped the eight finite cases while retaining the same
statements, lookups, tag guards and ≥8 branch. They were **deferred**: the
shortest version made the remaining ≥8 case less obvious, while the clearer
version saved only six lines across both modules and made the per-tag check
mapping less direct.

The direct grouped-disjunction variant also changed the types of the existing
public generated `localCheck_correct._proof_1` declarations. A later variant
retained the original disjunction, reassociated it for an explicit finite/≥8
split, and preserved all 119 existing declaration/type/axiom reports. It added
two generated public `_simp_1` declarations; the 25,319 global simp entries
and 11,807 instances matched. Paired target and five downstream builds passed
for this variant, with matching downstream object hashes. The checked direct
project providers were source-matched, while other transitive inputs remained
cached.

The first baseline/variant user CPU sample was 2.42/2.42 seconds for
RenameLocal and 2.74/3.21 seconds for BoundLocal. One later paired repeat gave
2.52/2.36 and 2.70/2.78 seconds respectively. These small shared-load samples
do not establish a general performance difference. The source snapshots,
superseded variants, generated-type comparisons, build and probe receipts,
timings and limitations are in the [evidence bundle](../../reviews/lean-proof-simplification-20261028-annotated-tag-dispatch-evidence/BUNDLE.json).
