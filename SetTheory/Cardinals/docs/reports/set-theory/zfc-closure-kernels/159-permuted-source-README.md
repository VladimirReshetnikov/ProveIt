# Source construction and calibration for the K216 candidates

The source contribution is a deterministic 202-subtree implementation of the already calibrated noncommon-input dominated calculus, followed by a permutation of its three short command tags. In both selected permutations, raw selector 2 enters MP, whose local field reader supplies the initialization path needed by the binary construction.

## Files

- `build_sources.py` reconstructs the 205-subtree semantic reference, the frozen 202-subtree source, and the two final sources from two historical input files. It performs no search.
- `audit_command_permutation.py` independently reconstructs the reference schedule, compares all primitive control-flow outcomes with the frozen source, checks the exact subtree permutation, and derives the complete selector partition and symbolic wire formats.
- `source_calibration.tex` is an include-only mathematical proof. It gives the all-natural command equations, the strong proof compiler, the exact Cantor packing, cofinality beyond cutoff 4, and the resulting source nonhalting/consistency equivalence.
- `audit210.json` and `audit120.json` are receipts against the exact source files used for the corresponding binary allocations.
- `rebuilt/` contains the deterministically regenerated sources and their build receipt.
- `source_calibration_standalone.tex` and its PDF are a standalone rendering of the source proof.

## Reproduction

Python 3 and its standard library suffice for source reconstruction and audit. Keep the two Python files together.

```sh
python3 build_sources.py \
  --baseline219 PATH_TO_BASELINE_SITES219_JSON \
  --baseline217 PATH_TO_SITES217_JSON \
  --output rebuilt

python3 audit_command_permutation.py \
  --baseline219 PATH_TO_BASELINE_SITES219_JSON \
  --frozen202 rebuilt/sites202.json \
  --candidate rebuilt/sites210.json \
  --permutation 210 \
  --output audit210.json

python3 audit_command_permutation.py \
  --baseline219 PATH_TO_BASELINE_SITES219_JSON \
  --frozen202 rebuilt/sites202.json \
  --candidate rebuilt/sites120.json \
  --permutation 120 \
  --output audit120.json
```

The historical inputs are:

1. `K218_Dominated_Rho8_2026-10-20/source/baseline_sites219.json`, SHA-256 `0f6d9d991e36dda1a7449edab72a799bb2d8c3de3ff853a26178b89bd1bc8789`.
2. `K217_Dominated_Continuation_2026-10-20/machine/sites217.json`, SHA-256 `9eac900e83742470893ea433cb0868e9ff6296f905cd6f3359b7a2c0e3114655`.

The first establishes an independently reconstructed semantic reference. The second supplies the bracketing from which the compact source is rebuilt. No mathematical correctness of a K217 binary table is needed by this source audit: the resulting 202-subtree source is separately compared with the 205-subtree semantic reference.

## Exact reconstruction of the 202-subtree source

Starting with the K217 source, in zero-based primitive ordinal intervals:

1. Delete the common counter field reader `[23,37)`.
2. Delete the AX counter reader `[187,201)`.
3. Replace the counter load `[228,254)` by a counter read followed by the original load.
4. Replace the MP counter load `[4659,4685)` by the same read-then-load sequence.

The original 14-leaf reader has the closed shape `(walk11, transfer3)`, and the original load has 26 leaves. At both insertion sites, right-associate the closed sequence:

`((walk11, transfer3), load26)` becomes `(walk11, (transfer3, load26))`.

This retains the primitive guarded control graph while reducing maximum zero run from 7 to 6. The resulting source has SHA-256 `abb7229877759170b61dfcfe21ca0889b3df2f91f4215383817a125eb0f8996c` and exactly 202 distinct subtrees.

Finally permute the closed command bodies at paths `111`, `110101`, and `110100101`. All source primitives outside these bodies, including the AX subtree, remain literal. The 210 permutation assigns these positions NIP, DROP, MP; the 120 permutation assigns them DROP, NIP, MP. Both preserve the 202-subtree count, 4,751 primitive occurrences, 6,176 guarded primitive cases, depth 44, and zero-run bound 6.

## Mathematical dependencies and scope

The inherited facts used here are the all-natural arithmetic macro contracts; the dominated-calculus theorem-set equality certificate; the strong block construction for the noncommon-input semantics; and the numerical-calculus-to-ZFC consistency calibration. They are stated in `K218_Dominated_Rho8_2026-10-20/theory/dominated_rho8.tex`, with finite certificate and checker dependencies in that archive and its retained predecessor notices.

The new proof explicitly transports this calibration through the tag change. It does not assume that raw candidate fields decode to ordinary formulas. The machine-specific binary runtime induction, literal state count, compact/native table equivalence, and blank-tape initialization are separate certificates in the enclosing K216 package.

This contribution inherits the MIT No Attribution license of its ProveIt predecessor. The existing numerical calculus, consistency interpretation, macro contracts, and previous machine constructions are not claimed as new. The source checker follows the independently structured/address-based verification method in the predecessor's `audits/verify_source_schedule.py`; the new code adds deterministic K217-to-202 reconstruction, exact command-body permutation, and an exhaustive symbolic dispatch audit.
