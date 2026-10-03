# Report 23 revision 1

This is a versioned extension of Report 23, not Report 24. The original delivered artifacts remain unchanged.

## What changed

The original PDF correctly reported the syntactic degree upper bound 71,731,007. A subsequently resolved all-tuple norm cancellation proves the exact degree of that same polynomial is 69,339,973, smaller by 2,391,034. The revised article integrates the complete proof, factor and residual degrees, full leading homogeneous component, explicit all-coordinate univariate ray coefficient, and its residues 3 modulo 17 and 53,942,795 modulo 1,000,000,007.

The degree theorem concerns the pinned integer polynomial without positivity or residual assumptions. The language/universality interpretation still has its explicit pinned theorem imports and valid fixed program-parameter scope.

`exact-degree/` supplies the new proofs, independent reviews, deterministic certificates, source provenance, explicit checks, and its own exact inventory. It reads the already included DAG rather than duplicating it. The main verifier runs both the original scientific suite and the extension. The article, README, build script, release-wide verifier/inventory, and revision QA are updated. Historical article QA is retained with the `v0-` prefix.

## What did not change

Every source gate, exact coefficient, supplied coordinate, witness, comparison and finalizer is unchanged. So are 3,600,546 operations (803,517M + 2,797,029A), 797,135 positive witnesses, six external coordinates, the literal 397,488-phase source program, and its semantics.

The entire 177-file `reproducibility/` subtree is byte-identical to v0. Its inventory root remains:

`95940bfa3ff6fba747fe2252b3ae8ac89e9633355a341cf6787b4b27cb85151e`

Its frozen original manifest retains the valid `degree_upper` field 71,731,007, and its older degree probes remain recorded as inconclusive. Those bytes are not relabelled or edited to look as if the exact degree was established earlier. The new theorem and certificates are in the extension.

## Original delivered v0 anchors

- Original PDF SHA-256: `757f95e438d47b0018e56482f538e60bf534705924bccebcdac7f96b5b665c24`
- Original LaTeX SHA-256: `acf5fd5e97511aec75fce3513eafce255f5f820c0b60e1fcca4bf391b86924f7`
- Original ZIP SHA-256: `467e2b4795fd484b73d94c6a006a84652fea772f1b0f870cac1a1f5d1445bf9b`
- Original release inventory SHA-256: `8cc54730b0f01a54c1bee80726a0fd0404e8e18848f63a7acd47b5824ab510d2`
- Unchanged full DAG SHA-256: `a07c1ba41e3a18fafd05c19b8ac39211b0475e30ed8a08ddf43c45a9f5f440f2`

The v1 inventory and separately supplied v1 ZIP hash authenticate this new distribution. They are separate from the v0 anchors above.
