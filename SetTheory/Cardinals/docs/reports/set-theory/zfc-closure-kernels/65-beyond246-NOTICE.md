# Attribution and status

This research packet was prepared for incorporation into ProveIt. Its new
material is an investigation of reductions below the already submitted
246-state consistency machine. **No successful reduction below 246 states is
claimed.** The ordinary-mathematical proof audit, finite counterexamples,
inductive certificates, bounded searches and solver experiments have the
distinct scopes stated in the report and branch READMEs.

The inherited machine and program are due to Mira-Cult, with Jeff's
verification and Andrew Wade's compiler framework. The development also
inherits mira-emmy's public 253-state reduction, ProveIt's permutation252
construction, the earlier prefix250/prefix247 work, and the incoming
context246 folds and bootstrap. The strict affine executor and universal
block/list induction machinery are attributed inherited code, not new work
authored for this report.

`baseline246/zfc-context246/` is reproduced from the incoming archive at
ProveIt commit `8cdc55ff9281b0aaba49bf74b0b225d57f12b893`. Its own notices,
source manifests, reference license and earlier provenance remain present.
The reference's historical pins identify the inputs of that earlier research;
the top-level `PROVENANCE.json` identifies the snapshot used for the present
investigation. Branch-specific provenance is also retained.

The new report and research code are supplied for use under the repository's
MIT No Attribution terms, reproduced in `LICENSE`. Existing third-party
notices and licenses continue to apply to their respective materials. No
worldwide priority or machine-size lower-bound claim is made.

Failed scanner mutations are described and recreated by counterexample code.
They are not labeled as verified consistency-machine candidates. The included
246-state tables are reference artifacts.
