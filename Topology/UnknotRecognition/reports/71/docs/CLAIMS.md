# Claim and evidence ledger

Delivery date: 9 October 2026. This ledger distinguishes mathematical proofs,
executed finite checks, supplied-language algorithms, and unproved geometric
obligations. No assertion of worldwide priority or proof-assistant verification
is made.

| Claim | Article location | Evidence and exact scope |
|---|---|---|
| Separated boundary-arc gluing adds surface defects and the attachment graph's cycle rank | Lemma 2.1 | A complete Euler-characteristic and component proof. All components have nonempty boundary; arcs are actual intervals with disjoint endpoints and collars. Circle gluing and surgery are excluded. |
| Splitting the envelope vertices imposes linear constraints on its cycle space | Lemma 3.1 | An explicit edge-chain correspondence and parity proof. Parallel edges remain distinct. |
| Disk completion factors through the exterior coordinates of the cycle space | Theorem 3.3 | A square-determinant test and characteristic-two Laplace expansion, including empty determinants. |
| A connected envelope has exact rank `2^lambda`; grade-j rank is `binomial(lambda,j)` | Theorem 3.6 | Upper bound from the factorization; matching permutation submatrices from chord detachments, for every connected envelope. |
| Some families require all `2^lambda` original candidates | Theorem 4.2 | Each chord-detachment candidate has a cap that completes only it in the constructed family. This is a subset-size lower bound, not a lower bound against every decision algorithm. |
| Cost-ordered bases preserve all minimum-cost allowed completions | Theorem 4.1 | Expansions in no-more-expensive retained rows; nonzero pairing supplies an actual retained witness. Sectors are separated. Neither counting nor arbitrary Pareto frontiers are preserved. |
| Alternative cycle coordinates preserve pruning identities | Proposition 4.3 | Invertible exterior-power coordinate change and invertible omitted-equation changes. The checker uses different coordinates. |
| Safe past/future envelopes can be compiled without enumerating suffix assemblies | Theorem 5.1 | Forward/backward joins of the explicit option lists; refinement induction. A separate whole-graph implementation checks the result. |
| Repeated reduction preserves the optimum of the complete supplied layered grammar | Theorem 5.2 | Whole-context replacement, defect monotonicity, static option availability, additive costs, and sector preservation. |
| Explicit layered search has bit complexity `poly(I,B) 2^(3 lambda_max)` | Theorem 6.1 | Charges the explicit input, integer costs, feature construction, elimination, candidates, witness paths, and checking. The constant base is not optimized. |
| Large raw arc width can coexist with constant representative dimension | Corollary 6.2 | Tree appendages do not change cycle rank. Executed 256-arc, rank-three sharp example keeps eight candidates. |
| The method implies quasi-polynomial unknot recognition under a complete low-cycle geometric producer | Corollary 7.1 | **Conditional.** Polynomial auxiliary costs and `lambda_max = O(log^2 n)` are explicit hypotheses. No such producer for all knot exteriors is proved. |
| Two certified torus-boundary bits suffice for the terminal essentiality refinement | Proposition 7.2 | Requires actual chain-level source cocycles and seam cancellation. The code's generic XOR sectors are not evidence that this geometric contract holds. |

## Executed evidence

- **42 test methods passed.** The retained transcript is `results/tests.txt`.
- `results/audit.json` records **3,162** envelope matrices, **633,531** direct
  compatibility entries, and **3,556** graded-rank checks.
- **1,000** weighted families and **16,904** cap/sector optimum queries passed.
- **600** grammars were compared in exact, unrestricted-root, and cycle modes.
  **639** successful mesh replays count outputs across those three modes, not
  distinct source grammars.
- **1,000** random surface pairs and all **1,412** assignments in **40** small
  grammars were checked by literal triangulated-surface computations.
- Paired five-repeat abstract-grammar timings are retained in full. Independent
  checking and mesh replay occurred outside solver timing in every mode and are
  separately recorded. The same viability filter is used in all modes.
- The single-cap control is a negative result: direct scanning is faster than
  either basis-preprocessing route on that supplied workload.

These finite checks are executable corroboration, not proofs of universal claims.
The rank checks build the matrices using an independent graph predicate; they do
not merely calculate the rank of the proposed feature vectors.

## Explicitly not established or executed

1. A general quasi-polynomial unknot recognizer, a complete low-cycle grammar for
   every knot exterior, or an unconditional geometric width theorem.
2. Native production integration, native repository regression tests, a benchmark
   of the maintained recognizer, or a production knot speedup.
3. A source-bound embedded disk exporter, normal-vector search, or certified
   geometric meaning for the prototype's abstract sector labels.
4. Proof-assistant verification, external peer review, or exhaustive literature
   novelty certification.
5. Support for arbitrary component-dependent guards, whole-circle attachments,
   surgery, or binary multiplicities masquerading as individual arcs.
6. Preservation of solution counts, all witnesses, lexicographically first
   witnesses, or arbitrary multiobjective optima.
7. An efficient algorithm for generating an explicitly Bell-sized input list.

Successful code outputs are `FOUND_ABSTRACT_DISK`, not `UNKNOT`.
Unsuccessful complete searches are `NO_DISK_IN_GRAMMAR`, not `KNOTTED`.
A resource interruption is `RESOURCE_LIMIT`, not a negative mathematical result.
