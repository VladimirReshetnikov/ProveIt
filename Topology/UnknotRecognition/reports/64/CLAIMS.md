# Claim and evidence ledger

## Proven in article.tex

- **Theorem 2.1:** the component, Euler characteristic, and binary first-Betti identities for two compact boundary surfaces glued along individually labelled, endpoint-disjoint, collared intervals. Every component touches the interface; quotient components retain boundary.
- **Corollary 2.2:** disc forests glue to a disc exactly when the join is connected and the component counts sum to `r+1`.
- **Theorems 3.2–3.3:** rooted-transversal exterior coordinates and the exact acyclic-gluing wedge test.
- **Theorems 4.1–4.2:** exact disc matrix rank `2^(r-1)`, grade rank `binomial(r-1,d)`, and a matching lower bound for every subfamily-selection algorithm preserving all disc-completion queries.
- **Theorem 5.2 / Corollary 5.3:** optimal-size weighted representatives, including negative costs, and grade-wise acyclic/completion-count preservation. Actual original candidates are retained; linear combinations are proof witnesses only.
- **Theorems 6.1–6.2:** homogeneous projection of cut rows; exact cut-stratum ranks and full cut-basis size `(r-1)*2^(r-2)+1`.
- **Theorems 7.2–7.3:** context replacement and a single-exponential-width algorithm for a supplied uniform collared assembly description. These explicitly assume the geometric input contract and charge candidate generation, control count, description length, and validation.

The optimal-size bound is a specialization of established linear-matroid representative-family machinery. The acyclic-completion predicate is not new. No universal priority claim is made for every derived identity.

## Executed

- 18 test methods in `tests/test_disc_basis.py`, recorded in `results/tests.txt`.
- Exhaustive graph/exterior comparisons and matrix ranks; independent scalar minors; weighted optimum comparisons with both exterior and classical cut representatives.
- A standalone checker that imports no producer module. Source/claim mutation tests and execution with the producer feature routine disabled.
- Ribbon-surface boundary-cycle comparisons and a theta-graph negative control.
- Repeated algebraic acyclic joins followed by reduction; all terminal optima compared with unreduced joins.
- Paired local timings with A/A, easy-query, rejection-rich, and no-compression controls; preprocessing included, certificate generation/checking excluded.

Raw data and scope are in `results/audit.json` and `results/benchmark.json`. Source hashes for the executed code are in `results/code_hashes.json`.

## Conditional and NOT established globally

The polynomial-auxiliary-cost substitution `w=O(log^2 n)` gives `n^O(log n)` for the supplied assembly problem. There is no construction here proving that arbitrary knot inputs admit such a complete, bounded-width, bounded-type assembly.

## Not executed or not claimed

No native checkout, native regression suite, geometric surface adapter, actual knot-instance timing, or proof-assistant formalization. Incoming ZIP metadata were inspected; incoming binary archives were not unpacked. Existing production Khovanov reductions are not modified. No remote repository writes were made.

No claim that census data determine arbitrary pointwise maps; no multiplicity-independent bound; no preservation of counts or chain-complex homology; no globally quasi-polynomial recognizer. Timeout or resource exhaustion is never a topology decision.
