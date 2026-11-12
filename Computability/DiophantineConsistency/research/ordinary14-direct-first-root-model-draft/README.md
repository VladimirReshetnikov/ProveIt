# Generic arbitrary-model direct first-root bridge: source draft

`FirstRootBridge.lean` is a **source-only proposal**. Its statements and proof bodies have not been elaborated, compiled, or checked by Lean; the Python inventory is not a Lean preflight. It does not import either graph or claim a graph-zero, degree, consistency, iPRA, provider-ancestry, PDF, JSON or gzip theorem.

In an arbitrary `ORingStructure V` modeling IΣ₁, the file proposes:

* `fiveSquares_eq_zero_iff`, for five fixed difference-ring elements, using the existing square-extraction pattern in `Compact44/FreeJSumSquares.lean`.
* `root_of_scaled_residual`: explicit positive natural scale M and radicand D, plus the scaled difference-ring equality, give a positive natural root `magnitude(P,N)` whose square is D. The proof proposes cancellation via the `DiffRing V` embedding and uses `P72Root.ι_magnitude_sq`; it does not assume P≥N or conflate natural truncated subtraction with ring subtraction.
* `scaled_residual_of_root`: a positive natural tau with tau²=D gives positive old coordinate `P+tau`, which represents the negative root. M need not be positive for this direction.
* `positive_first_zero_iff`: with M,D positive and the other four residuals fixed as difference-ring parameters independent of the changed coordinate, positive-old-coordinate existence for the five-square expression is equivalent to positive-direct-root existence. The old coordinate and root need not agree, and the two full polynomials need not agree pointwise.

The proofs are intended as generic arithmetic only. In particular, `P72Root.ι_magnitude_sq` is a source-level dependency through `Compact44.P72Root`; it brings a substantial direct/transitive provider closure, which has not been authenticated for this draft. The elaboration of `nlinarith`, coercions, typeclass instances and all rewriting and proof scripts remains unknown. The source inventory pins the proposed file and referenced source text, checks statement names and rejected proof escape markers, and tests bounded integer examples; it cannot prove a universal or model theorem.

## Graph and endpoint obligations

A separate 84↔79 client must import and elaborate the source-only `../ordinary14-qcube84-lean-draft/P84QcubeGraph.lean` and `../ordinary14-direct-pell79-lean-draft/P79DirectPell.lean`, establish exact difference-ring evaluations for the first residuals with `M=q³*J*beta`, `P=ell+k` and `D=1+ell*(ell+k)`, prove M,D positive from positive coordinates and beta, and show the other four residuals really are identical and independent of slot 8. It must construct the two `Fin 14` valuation updates, prove every coordinate positive and transport `InternalZero` through `ModelDifferenceRing.internalZero_iff`. Those graph-specific facts are not assumptions hidden inside the proposed theorem, nor are they supplied here. A direct 84↔79 client can avoid a separate 80 graph, but the prior 80 same-coordinate unscale and 80↔79 root maps are still independently unproved in Lean.

Even a compiled local client would leave the 84↔85 modified-carrier proof, compact Mersenne cancellation and signed/model growth obligations, 85↔86↔87↔88 clients, endpoint and all provider-compatibility/ancestry checks open. The existing 5.1 GB disk floor and exclusive allocation/independent prelaunch procedures apply before any future Lean run. No current build or proof result is asserted.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary14-direct-first-root-model-draft/check_source.py
```

Independent source review is recorded in
`../../reviews/ordinary14-direct-first-root-model-draft-independent/`.
