# Independent review of the balanced K215 source checker

Reviewed directory:
`research/proof_simplification/balanced_lookup`

Repository pin: `53269bcab1efc0f82d3022645bd7cf0c22d84959`.
This review inspected source, existing compilation receipts and logs, and
performed read-only parsing of the literal data. It did not rerun Coq or
Rocq compilation.

## Mathematical assessment

No mathematical defect was found in the new refinement chain.

1. `valid` requires every stored cut to equal the exact size of its left
   subtree. `lookup_flatten` then establishes the appropriate equality with
   `nth_error`, including empty trees, singleton trees, and out-of-range
   indices. Its invariant is sufficient; it does not presume balancing.
2. `getTree_flatten`, `branchTree_flatten`, `entryTree_flatten`, and
   `checkTree_flatten` preserve the original checker's actual semantics.
   `checkTree_halts_iff` applies the retained ordinary checker and its
   symmetry theorem. It introduces no new semantic calibration premise.
3. `tree215_exact`, `tree215_valid`, and `tree215_entries` concern the
   concrete tree built from the unchanged compact certificate. The source
   theorem checks the literal current programs. It would remain sound for
   any other certificate passing the proved checker; the generator is not
   part of its logical trust boundary.
4. The bound of 13 visits is obtained from the proved concrete height.
   The generic `lookupDepth_le_height` theorem does not claim that every
   valid tree is balanced. The reported asymptotic result must retain the
   explicit balanced-tree hypothesis.

## Independently checked data

The retained compact certificate, path codec, and symmetry module match the
corresponding principal members of the incoming
`ZFC215_Proof_Simplification_2026-10-21.zip` byte for byte.

A separate read-only parser reconstructed the 179-node literal `p215_tab`,
decoded the positive-integer paths least-significant bit first, and walked
all 2,240 source-side checkpoint paths, with the same false-bit continuation
used by the source semantics. It found 2,239 decrement checkpoints and one
halt checkpoint, at index 25. The maximum successor reference is 2,239.
An independent iterative balanced-tree traversal count gives:

| Quantity | Independently confirmed |
|---|---:|
| Entries | 2,240 |
| Queried references, including initial entry | 4,479 |
| List constructor visits | 5,018,706 |
| Tree node visits | 54,514 |
| Maximum tree visits | 13 |

All available source and log files whose hashes are listed in the selected
`evidence/result.json` match their recorded hashes.

## Complexity and timing boundaries

The 92.06 ratio is a ratio of structural traversal counts. It is not a
92-fold runtime or bit-operation speedup. Binary comparisons and subtractions
cost more than a single abstract tree-node visit. The stated
`O(N log^2 N)` indexing bit-operation bound is appropriate for balanced
trees and queried indices of `O(log N)` bits, as in the concrete passing
certificate; it is not a bound on the entire semantic checker or on
arbitrary-length malicious indices.

The single observed 16.008-to-11.314 second transaction and
33.103-to-24.772 second source-module process comparisons are accurately
reported as observations. The new construction/exactness module costs
another 13.159 seconds in that run. Therefore no end-to-end first-build or
endpoint-build speedup has been established. The README states this
limitation appropriately.

## Verification evidence correction resolved

The initial review identified a missing packaged receipt for the README's
successful recursive `coqchk` claim. That packaging issue has now been
resolved. A read-only refresh confirms that `evidence/result.json` contains
`recursive_generic_check` with target `BalancedBisim`, `exit_code: 0`,
the exact `coqchk -Q ... -silent BalancedBisim` invocation, and explicit
scope "Generic checker and its dependencies; excludes concrete
Source215Balanced". The separate manual invocation has no measured timing;
the receipt correctly leaves `seconds` null and states this reason.

The included `evidence/coqchk_BalancedBisim.log` is empty, consistent with
the successful silent invocation, and its verified SHA-256 is
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`,
matching the receipt. The refreshed result receipt has SHA-256
`32cf998829fe78ccf7a83692ede70fff7ace38473391ee3bf3b3b032b59190a9`.
No compiler or checker was rerun during this refresh. There is no remaining
evidence-packaging objection from this review.

Successful `coqc` logs and closed assumption reports for the concrete
source theorem are present. They do not establish a fresh rebuild of the
full 237-source binary/ZFC endpoint, a run of the pinned Rocq 9.1 toolchain,
or a recursive `coqchk` of the large concrete source theorem. The report
must preserve those distinctions.
