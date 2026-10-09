# Claim ledger

| Claim | Status and scope | Evidence |
|---|---|---|
| Knot-group balancedness | Prior theorem, not a contribution of this article | HMT Lemma 2.3 |
| Absolute-cycle and plain-sign deletion | Proved for verified classical-knot-group relations | Article §3; graph producer and independent checker |
| Exact graph-abstraction boundary | Proved with simultaneous nontrivial trefoil models; fixed conjugator words and source generation are deliberately discarded | Article §4 |
| Polynomial exact graph inference and short replay | Proved with binary arithmetic accounting, no factorization assumption | Article §5 |
| Modular sieve soundness | Implemented; all successes replayed exactly, all misses fall back | Tests, original controls and sieve follow-up |
| Polynomial complete literal deletion closure | Proved for the precisely specified exposed-donor interface, not arbitrary relator exposure | Article §6 |
| Polynomial compressed closure | Conditional on a polynomial source-authenticated donor-discovery oracle; no native complete collector supplied | Article §6 |
| Two-power gcd-minor triviality | Proved exactly for the displayed class; sufficient direction valid in every ambient group | Article §7; paired_power.py |
| Binary pair family versus forests | Proved separation of local eligibility on unchanged supplied presentations; no lower bound against general search | Article §7 |
| Correct small-source certificates | Independently replayed; 3,227 source inputs checked against a separate full-cube oracle, no false positive observed | data/braid_audit.json |
| Coverage improvement on that source corpus | **Not observed**: zero improvement over pure-power deletion | Audit ablation |
| Polynomial literal Artin construction from all diagrams | **Not proved**; frontend is literal and capped | Article §8 |
| Native fastunknot integration and native speedup | **Not performed or claimed** | integration/INTEGRATION.md |
| General quasi-polynomial unknot recognition | **Not established** | Article §§1,10–12 |
| Formal verification / peer review / global priority | **Not claimed** | Theorems are human-readable arguments, supported by finite code audits |

The latest delivered test run contains 24 methods with no errors or failures. Exact
counts are retained in data/test_summary.json; source, mathematical and performance
claims are intentionally not conflated.
