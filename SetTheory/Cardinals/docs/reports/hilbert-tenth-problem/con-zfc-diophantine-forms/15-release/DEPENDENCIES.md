# Proof dependencies and intentionally unbundled material

## Present and verified

All files listed by `evidence/diophantine_zfc_round2/review/SOURCE_PINS.json` are present with matching byte lengths and SHA-256 hashes. Every JSON parent required by the default replay is present. The direct K215 transition table, the ordinary strong-rank proof, the half-binomial Pell kernel, the native complete75 proof and the final compiler/reduction proofs are included. There is no missing executable input to the bounded replay.

The earlier source-pin file is intentionally filtered to the included prior proof dependencies; it is not represented as a full repository snapshot. Newly generated prior JSON parents are pinned by the release manifest and by their children. The release contains the final data directly, so research-only emitters and their optional dependencies are unnecessary.

## Source texts are not a complete formalization archive

The underlying K215 blank-halting/refutation calibration and the general native compiler/Pell development remain imported mathematical dependencies. The entire Lean/Rocq libraries, their build environments, and all transitive cited papers and source scripts are not vendored or rebuilt. The current source root is:

https://github.com/VladimirReshetnikov/ProveIt/tree/3b201cdea32d2c816f5f3d20734051f25fd3ef14

The earlier pinned K215 table is:

https://github.com/VladimirReshetnikov/ProveIt/blob/cdd582bec13f908df3711fa9e05d1ddac368a5db/Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm

Some retained historical proof texts have relative cross-references to upstream files not obtained for this review. Examples include `complete75_half_binomial.py` in the old kernel note, `round28_1980_relaxed_auxiliary_certificate.py` and `COMPOSED_99_PROOF.md` in the old relaxed-auxiliary note. These paths are not included as executable audit inputs, and the driver does not try to run them. Refer to the immutable repository revision in the applicable source pin to resolve historical cross-references. Their absence is not evidence of a source theorem's failure, but it means this archive is not a self-contained build of that older proof development.

The new ordinary-strong audit explicitly reviews the mathematical recovery argument instead of claiming that those unbundled historical scripts were replayed. The report and proofs state the calibration and compiler dependencies. Bounded arithmetic receipts establish their stated finite scope only; they do not replace those mathematical arguments or constitute a newly kernel-checked endpoint.
