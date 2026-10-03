# Independent review of forced Waterfall boundaries

Mathematical/source/API review **PASS**, with no unresolved finding. The only review request was to make archive and member authentication explicit instead of assertion-based; the author applied that change before freezing source `56c2c9eabad9faa51b66e02315264c93da0c9915cb406badfa1822a188f0b747`.

Read the complete 359-line compiler (plus the small subsequent explicit-digest change), complete companion note, original grouped-quadratic compiler and the article's full polynomial proof. The first/suffix affine graph proof and counts agree with [the grouped-polynomial review](waterfall_polynomial_review.md). Scope remains natural, fixed-source-TM-horizon certificates; no unbounded fixed-arity or universal arithmetic improvement is inferred.

The independent helper [waterfall_forced_boundary_review.py](waterfall_forced_boundary_review.py) exposes `verify(source, parent, helper)` and command-line `--source`, `--parent`, `--helper`, `--receipt`. Its three inputs are pinned literally before import: the final derivative source, the archived parent grouped compiler, and [waterfall_polynomial_review.py](waterfall_polynomial_review.py). All paths are arguments; it has no fixed `/tmp` dependency. Use the maintained/vendor copies of these files with identical bytes. It refuses optimized execution, while subprocess tests deliberately use optimized Python to check the public compiler's authentication boundary.

For 21 mode/horizon combinations (`parent`, `prefix`, `ends` at applicable horizons in {1,2,3,4,5,7,8,10}), independently reconstructed affine substitutions agree coefficient-for-coefficient with the emitted restoration. Substituting them into the complete parent polynomial gives the emitted complete expanded polynomial. Independently expanding **every arithmetic gate** also gives the same full polynomial. This proves actual source equality at the tested horizons, beyond numerical samples. The all-horizon proof is the structural affine substitution and natural zero-set argument in the companion note.

The arithmetic count is the number of emitted binary +, − and × instructions. Every reference is an input or earlier gate, each scalar multiplication not folded by 0 or 1 is counted, all output-reachable rows are retained, and no dead row is charged. Constant folding matches the documented model. Exact degree is certified by the unchanged coefficient one of tau squared.

At k=7 the independently expanded ledgers are:

| Form | Witnesses | Squares | Products | M | A | Total | Monomials |
|---|---:|---:|---:|---:|---:|---:|---:|
| Parent | 245 | 39 | 14 | 430 | 1128 | 1558 | 9484 |
| Prefix | 211 | 34 | 12 | 373 | 984 | 1357 | 8444 |
| Both ends | 107 | 20 | 6 | 203 | 517 | 720 | 3997 |

The k=4 both-ends polynomial retains the constant state residual 5, so its two witnesses and five squares do not falsely certify a halt. The interface explicitly rejects both-ends mode for k<4. Prefix mode handles those horizons, retaining the relevant nonzero terminal rows.

Canonical packet comparison is recursive and type-sensitive. Numerically equal float/Boolean substitutions are rejected, metadata and source rows are part of the canonical comparison, and `build` returns defensive copies of the private cached result. Natural assignment APIs require exact integer values and complete coordinate sets; the explicit signed option supports formal graph identities without extending the natural-zero theorem. `project_assignment` checks a complete parent natural zero before deleting coordinates. `canonical_assignment` rejects overlong/short nonhalting horizons by returning None and rejects nonnatural half tapes. Low-level unguarded algebra helpers are expressly outside the public untrusted-input contract.

The finite audit receipt records 21 complete parent-substitution identities, 21 complete SLP polynomial identities, 21 count/liveness checks, 21 defensive-copy cases, 126 signed replays and 9,898 malformed public calls rejected. It also checks a 501-digit exact parameter, the full k=7 zero projection/restoration, and the absence of that input's first halt at k=6 and k=8. Final authentication regressions change each expected digest in an isolated `python -O` process and require explicit rejection, ensuring disabled assertions cannot bypass either digest check.
