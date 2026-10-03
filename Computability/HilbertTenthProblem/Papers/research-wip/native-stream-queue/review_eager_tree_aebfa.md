# Independent review: Eager Tree Calculus

Archive `Eager_Tree_Calculus_Research_Package.zip`, SHA256 `5c6c100296a58df366939febf2f7b6ca57616f17f77a71520f6f3a5e20204ab4`. All 56 member identities matched the intake inventory before safe private extraction. Read the complete article (including the literal constructor tables), README, all substantive Python generators/checkers, and replay driver. No theorem-level defect was found in the reviewed construction.

## Source interface and proof scope

The five eager value-application rules agree with [Jay's pinned Rust source](https://github.com/barry-jay-personal/tree-calculus/blob/baa877d916eb640280ed2df7ef4385ecd5957d19/trees/src/lib.rs), particularly the branch-first application in `apply_values` and the eager context traversal in `eval`. The manuscript correctly distinguishes this relation from an equational quotient or a nonstrict evaluator. Its bracket-abstraction proof reconstructs both directions, and the reflection proof uses a strict decrease in target inference weight. The closure model excludes cyclic environments. Its finite Scott interpreter has value handlers and delayed recursion; it does not force unused branches. The classical CBV computational-universality premise is consistent with [Dal Lago–Martini's primary paper](https://arxiv.org/abs/cs/0511045).

The base polynomial pays actual one-hot selectors for every pointer lookup and natural additive call costs for acyclicity. Natural domain is essential. Its zero set represents terminating application with at most an **external** number `N` of distinct calls. Unreachable valid rows, inactive fields, duplication, and padding produce nonunique witnesses. The literal base counts are `3N²+19N` natural coordinates, `23N+3` quadratic rows, and `27N²+125N+8` binary arithmetic operations, with constants charged when operated on. The quartic degree is exact because nonzero quadratic homogeneous residual parts cannot disappear in a sum of real squares.

The preferred canonical refinement has exact-size, empty-or-singleton natural fibers. Positive occurrence flow excludes unreachable rows; strict ordered nonroot keys exclude duplicate nonroot calls. Root distinctness is then forced by reachability and strict cost decrease, so deleting explicit root-key comparisons is sound. The dual identities `h=1+Ah` and `μ=e_root+Aᵀμ` give `Σμ=h_root`, counting duplicate premise occurrences. For `N≥2`, the preferred counts are `3N²+22N−3` coordinates, `31N` rows, and `33N²+168N−11` gates; the separate `N=1` case is 23 coordinates, 32 rows, and 195 gates. No conversion to positive-only witnesses is supplied or silently assumed.

The 175-node universal tree is literal and fixed, with 949 unshared constructor occurrences. Its code is not materialized. The independent interval propagation reproduces `44,926,990,249…44,960,544,677` bits. Charging all 175 uniquely determined constructor coordinates/residuals gives the stated fixed-program gate overhead; this does not pay an arbitrary input loader or remove the external `N` parameter. No fixed-arity universal polynomial or improvement of the ordinary arithmetic record follows.

The fixed sharing program `R` is a different 108-node tree, not the universal interpreter. The finite symbolic proof plus induction establishes `H_n=562·2^n−468`; exact structural template classification, with its base exceptions, gives `D_0=44`, `D_1=179`, and `D_n=64n+113` for `n≥2`. The classification genuinely examines all template-pair equality forms, not just finitely many unary depths. The `O(n²)` witness-bit statement retains the enormous fixed code constant. The review's hybrid exact-until-4096-bits interval for `R` is `2,501,742,332,141…2,503,889,815,785` bits, inside the manuscript's wider proved interval. No giant scalar tuple was constructed or tested.

## One bounded API finding and repair

**P3, `code/tree_kernel.py:65`:** `Evaluation.app` checks the first code only when eventually decomposing it and does not validate the second code before cache lookup. `Evaluation().app(0,-1)` returns −1. More consequentially, `app(0,True)` creates a record whose argument is Boolean; a later valid `app(0,1)` reuses the same Python dictionary key, and the resulting generated certificate fails the natural-coordinate checker. The polynomial verifier itself rejects this malformed certificate, so this is not a false arithmetic zero.

The isolated `eager_tree_exact_application_inputs.patch` adds exact nonnegative-integer validation for both codes before cache lookup. It preserves all valid-domain outputs. The patch does not purport to turn every internal AST helper into a general untrusted-input parser.

Patch SHA256 `bb669fe7b71621d6fbe968ce8ed5833092dee996e262a78a6471f0aeb9bccdfe`; repaired `tree_kernel.py` SHA256 `763972512e621e6dde04f0721be3a27d45c2ff27227cbed0a3ba3d0e51e96d94`. The original archive is unchanged.

## Replay and independent evidence

The portable `review_eager_tree_aebfa.py` pins all 56 archive members and the patch before importing code, rejects `python -O`, privately applies with `patch --batch --fuzz=0`, and supports exact type-sensitive saved-receipt comparison:

```sh
python review_eager_tree_aebfa.py \
  --root /path/to/untouched/eager-tree-certificates \
  --patch eager_tree_exact_application_inputs.patch --authors \
  --output /path/to/new.json --expect review_eager_tree_aebfa.json
```

Both original and repaired private copies passed every one of the 19 author scripts, including optional SymPy checks:

```sh
python verify_manifest.py
python reproduce.py --symbolic
```

All 26 saved JSON objects reproduced, and repaired outputs matched after normalizing only occurrences of the changed `tree_kernel.py` source digest. Six key mathematical exports were also checked byte-for-byte unchanged. Author evidence includes 767 complete base and canonical zeros in the stated grid, 707 independently compiled normal-form comparisons, all 184 canonical identity-coordinate mutations rejected, exact cyclic-counterfeit rejection, symbolic sharing inference checks, and whole-call-set growth checks. Fuel exhaustion remains inconclusive, as the manuscript states.

The new review adds **774 assertions**: 72 independently expanded complete residual/SOS evaluations on arbitrary natural tuples; 72 literal gate/count checks; 180 preserved generator cases, matching manual zero checks and structural evaluations; 48 malformed scalar/selector rejections; 12 cold/warm evaluator rejections with valid reuse; independent cyclic counterfeits; and both literal-code interval calculations. These are regression checks supporting the written proofs, not exhaustive all-witness validation or kernel verification.
