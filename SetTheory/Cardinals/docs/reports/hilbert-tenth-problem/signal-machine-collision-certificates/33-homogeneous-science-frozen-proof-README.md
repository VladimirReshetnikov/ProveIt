# Compatible homogeneous five-signal realization

**Result:** the proposed criterion is established, relative to the preserved and freshly reviewed fixed-center compiler. A rational 3×3 matrix N is locally realizable on a nonempty full-dimensional open part of the original stationary-marker section if and only if det N≠0 and C∩N⁻¹C≠∅.

The missing construction is a physical shape translation. A rational interior point p can be sent to any other rational interior point q using 26-event steps, with four temporary marker labels per step and all intermediate corner guards retained. Then T_(−q)NT_p fixes the standard ray and can be compiled by the preceding theorem. Executing the physical translations on either side realizes N itself, without a rational eigenray or a changed encoding.

## Files

- `PROOF.md`: all-parameter theorem, physical chronology, exact guard lists, phase interfaces, endpoint-feasibility algorithm, worked previously uncovered example, Diophantine corollary, and conditional clock statements
- `CERTIFICATE_DAG_SIGNED.json`: literal 48-operation arithmetic DAG for nine signed integer gap-matrix inputs
- `CERTIFICATE_DAG_POSITIVE.json`: literal 57-operation arithmetic DAG for eighteen positive external input leaves encoding those entries by differences
- `static_algebra.py`: freshly authored source, displayed and inspected before its only run
- `evidence/static_checks.json`: PASS, 98 named static checks, checker hash, dependency source hashes, and exact execution boundary
- `evidence/exact_lp_fixtures.json`: seven exact feasibility fixtures separating singularity from cone incompatibility
- `evidence/translation_fixtures.json`: 36 exact endpoint/margin fixtures, including identity and near-boundary shapes
- `evidence/diophantine_fixtures.json`: positive witnesses for identity, a determinant-negative coordinate swap, the positive no-rational-eigenray example, and a compatible escaping-gap map
- `dependencies/`: unchanged proof/review text supplying the prior interfaces
- `MANIFEST.json`: hashes and byte lengths of the packet files and original-source bindings

## Exact Diophantine ledger

For a native integer gap matrix K, the single polynomial is

    Σ_i((Kg)_i−h_i)² + [det K−(2b−3)d]² + [(b−1)(b−2)]².

All eight witnesses g₁,g₂,g₃,h₁,h₂,h₃,b,d are positive integers. There are five squared residuals and exact total degree six. The signed-input DAG uses 26 multiplications, 11 additions, and 11 subtractions; nine external positive-input differences raise the total from 48 to 57. These are counts for this particular decidable local-realizability predicate, with no optimality or universal-representation comparison. Fibers are infinite under simultaneous positive-integer scaling of g,h.

Centered integer numerator input M is handled explicitly by K̃=SMB with S=3H, B=3H⁻¹ and K̃/(9q)=H(M/q)H⁻¹. The centered formula retains degree six and eight witnesses. The native 48/57 operation counts do not include this conversion.

## Boundaries that matter

- Endpoint feasibility is polynomial-time decidable in rational input size; the selected physical word compilation can be much larger
- The result is a local exact complete-word theorem, not all-cone realization or an invariant-chamber theorem
- Infinitely valid inputs need not exist: the gap map (g₁,g₂,g₃)↦(g₁,g₂,g₃−g₁) is compatible locally but every positive orbit eventually leaves the cone
- Any clock classification is explicitly conditional on infinite validity of the actual constructed word
- No author/upstream program, physical trajectory simulator, or saved collision schedule was run; the new emitted DAGs are arithmetic expressions only
- The 98 checks support a conventional proof; they are neither 98 independent theorems nor proof-assistant formalization
- No novelty, priority, Turing-completeness, global reversibility, or optimality claim is made

This packet has not yet received its own independent audit. The included accepted review concerns the prior fixed-center dependency, not this new theorem.
