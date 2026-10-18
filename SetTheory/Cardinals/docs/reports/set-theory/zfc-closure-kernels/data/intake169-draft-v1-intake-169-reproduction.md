# Batch 169: recovery and reproduction

The six delivered archives are preserved in arrival commit `d5845120023085f81694ee5b8babb95cd5fa50ef`. The [placement map](data/intake169-placement.json) identifies every original outer-member path, blob, byte hash and destination or archive-only disposition. Exact existing-host and intra-batch aliases are recovery links, not claims of scientific novelty. Main manuscripts and delivery READMEs remain archive-only; a nested ZIP remains a single member. No line-ending normalization or checksum-manifest validation is intake work.

Actual placement: `PENDING_169_PLACEMENT_COMMIT`. Actual recovery helper/record: `PENDING_169_RECOVERY_RECORD`. The frozen proposal has 1,387 members, of which 1,301 ancillary occurrences resolve to 687 unique paths; 86 are archive-only. Root's actual recovery result must replace this pending checkpoint before the write is finalized.

Recover each original ZIP from Git into a separate scratch directory. For example:

```bash
git show d5845120023085f81694ee5b8babb95cd5fa50ef:docs/incoming/zfc242-contextual-reuse-20261018.zip > /tmp/intake169-contextual-original.zip
```

Use the same arrival and the other five archive paths listed in the placement map. Extract outside the repository, rejecting absolute paths, `..` components and symlink members. Preserve each package's original wrapper and nested paths. Run substantive tools only on a disposable copy of that reconstruction. The flattened `code/` and `data/` placement names deliberately preserve delivered bytes, so their unchanged relative imports should not be invoked directly in the host directory.

## What was actually checked

Root's [six-table comparison](data/intake169-table-comparison-root.json) is a static full transition-isomorphism check: 484 rows per report and 482 rows after the known 17/39 fold. The three pair reviews independently inspected the ordinary proofs and secondary material. Their own static scripts parsed tables, certificates or serialized syntax; they did not run the supplied simulators or proof compilers.

The earlier [batch168 fresh replay](data/intake168-fresh-replay.json) is the source of fresh full runtime evidence for primary A and current 241. It passed 19 jobs, including five complete 8,390-case universal runs for A/B/C/243/241. Exact table identity or the complete start/halt-preserving state bijection transports the machine behavior to these six presentations. It does not make their supplied wrappers, recorded timings, discovery searches, changed-source H rotations or standalone Lean project freshly replayed. No six-suite PASS is asserted.

The only new supplied-code-dependent execution in this comparison is the derived joint packet builder. Root reviewed the builder, both inherited imported modules, the Horn helper and proof first, then ran on copied inputs. The [exact terminal command](data/intake169-joint-execution.json), stdout/stderr, copied dependencies, output packets and finite verification are preserved. The [actual peer review](data/intake169-joint-actual-review.json) reconstructs the encoded bits without re-executing that builder. No TM simulation, proof compiler, theorem search, NAND synthesis or TeX build occurs in this joint run.

## Replaying the joint packet on copied inputs

The preserved code files are byte-identical to the executed builder and imported dependencies. From the host root, create a fresh reference directory and restore the four required basenames:

```bash
mkdir /tmp/intake169-joint-reference
cp code/intake169-joint-reference-equational_search.py /tmp/intake169-joint-reference/equational_search.py
cp code/intake169-joint-reference-build_equations.py /tmp/intake169-joint-reference/build_equations.py
cp data/intake169-joint-reference-FC13B_complete.json /tmp/intake169-joint-reference/FC13B_complete.json
cp data/intake169-joint-reference-baseline_grouped.json /tmp/intake169-joint-reference/baseline_grouped.json
python3 -B code/intake169-build-joint.py \
  --reference /tmp/intake169-joint-reference \
  --horn-helper code/intake169-horn-certificates.py \
  --output /tmp/intake169-joint-new-output
```

The output path must not exist and must be outside the input/program directories. Use a bounded process-group runner. Root's existing run took 1.06645 seconds; that observation is not a new machine's runtime bound. The builder checks its input pins and rehashes afterward, emits both variants plus `verification.json`, and retains failure evidence after output creation if a check fails. Current results are 1,768 and 1,750 bits with 18 and 21 equations respectively.

## Delivered entry points retained, not rerun

| Source | Main substantive entry points in restored package | Additional scope |
| --- | --- | --- |
| 74 | `code/build_and_audit.py`, `check_execution.py`, `check_expanded.py` | Semantic-target, scanner and H-rotation checks; discovery searches separate. |
| 75 | `code/verify_reduction.py`, `discovery/check_borrow242_independent.py` | `formal/verify_formal.py` invokes Lean with its supplied limits; orientation/emitter work is separate. |
| 76 | `code/construct.py`, `verify_local.py`, `verify_blank.py`, `verify_literal.py`, `verify_runtime.py` | Independent local/blank checks, acceptance residues and bounded source screens. |
| 77 | `code/verify_local.py`, `verify_induction.py`, `verify_blank.py`, `verify_literal.py`, `verify_runtime.py` | Independent audit and `research/formalism_dispatch/formalism_dispatch_packing.py`. |
| 78 | `code/build_machine.py`, `verify_local_detour.py`, `verify_blank.py`, `verify_literal.py`, `verify_runtime.py` | Exact packet checks separate from MILP, annealing and exchange searches. |
| 79 | `code/prove_zero_reuse242.py`, `code/verify_candidate.py` | `research/stack-kernel/stack_kernel.py`; contextual fold search is separate. |

This table identifies preserved programs, not a reviewed command line or authorization to run all searches. Aggregate wrappers may perform delivery-manifest checks and overwrite their evidence; those manifest operations are excluded from intake. Any additional replay must read the chosen program and its arguments, use a copied package and record the actual bounds, outputs and dependencies. Delivered search or Lean logs retain their historical status.

The reconciliation workflow changes no host article or PDF. The collection catalogue's updated manifest PDF is a separate required catalogue build, owned by root. See [the main note](intake-169.md) for current formal and consistency limits.
