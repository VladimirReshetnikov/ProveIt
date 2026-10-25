# Dependency closure and verification boundary

## Current execution closure

`REPRODUCE_PLAN.json` enumerates commands and exact output comparisons. `CODE_REVIEW.json` binds every executable in the selected closure to a reviewed SHA-256. Builders use local literal JSON or fixed formulas. The direct builder imports the local finite polynomial factorization and monic eliminator, and its checker independently replays the signed Horn identities and projections. The lowdegree builder uses its local DAG class. Positive code uses local old graph data rather than running an old compiler. Integer code uses its DAG helper, exact sparse ring, and fixed finite source34 coefficient recipe.

The source34 recipe reads a fixed finite transition table to reconstruct a fixed Wang tile set and integer coefficients. It does not simulate the machine, search for halting or enumerate refutations. It is the only historical recipe intentionally executed by the current integer checker; its exact source and input hashes are reviewed. Other retained historical programs are inert evidence.

The independent lowdegree and positive audits require SymPy 1.14.0. Current direct and integer arithmetic programs use the standard library unless a separate independent review lists an additional dependency. The root runner uses subprocess argument lists, not a shell; all runtime inputs are within the isolated release copy. Receipts and logs are written outside the original release.

## Coherent mathematics and provenance

The source34 integer tuple is complete, including the already-shifted MF and the cone constants. The original compact44 positive tuple is distinct and also complete. No coefficient is borrowed from a different controller, tile ordering or source family. Actual compressed payloads, raw hashes, bit lengths and finite recipes are included. Direct small coefficients appear in full sparse expansions, not as named unknown constants.

Immediate mathematical sources are copied beside each branch and pinned. The entire previous release remains under `prior/wave15/`, with every original manifest entry verified. This retains the transitive native/compiler/refutation and C222 calibration documents and their licenses without severing relative references inside the earlier packet. It does not claim to recreate every external proof-assistant dependency or rerun that earlier release's programs.

The new zero-set reductions and their finite literal certificates are distinct from the inherited ordinary semantic calibration. The latter is authenticated and its interfaces inspected, not freshly established end-to-end by the current replay. A successful numerical or symbolic check cannot prove an unbounded completeness theorem or decide consistency.

## Baseline selection

The original working comparison snapshot is much larger than the distribution. `BASELINE_CHECKS.json` authenticates 381 research inputs, including eight incoming ZIPs. `SELECTED_EVIDENCE.json` lists the actual additional comparison files retained here. Source theorem copies and the exact preceding release separately provide the mathematical dependency closure. An omitted comparison archive is not a missing runtime input.

## Documents and release

The report uses LaTeX with shell escape disabled. `report/section_copy_provenance.json` binds copied producer TeX to the compiled report and lists separately authored report material. `report/QA_RECEIPT.json` records the rendered-page inspection. Python replay does not imply a TeX build or visual review.

`seal_release.py` and `make_release_zip.py` are release-maintainer tools. The first inventories the finished release; the second validates that inventory and the frozen replay summary, makes two ZIPs with fixed metadata, requires byte identity, and verifies member bytes and CRC. These are packaging checks, not mathematical proofs.

The separate low-operation product family is retained in `integer_lowops/`. Its ordinary review and independent expression audit are in `review/lowops/`; the separate independent literal-gate and fixed-coefficient audit is in `review/integer_lowops/`. Their normal/optimized receipts record each mode independently. Complete byte-identical receipt replay uses Python 3.12.14 and SymPy 1.14.0.
