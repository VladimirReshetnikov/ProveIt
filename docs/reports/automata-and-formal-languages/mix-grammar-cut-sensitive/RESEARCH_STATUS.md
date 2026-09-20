# Research status and verification boundaries

| Claim | Status | Evidence |
|---|---|---|
| The canonical A3/MIX equality question is a published open target | Explicitly identified as open in the cited September 12, 2026 preprint | Yuyama v1, Remark 3.19 and Section 6 |
| The chosen question has been resolved here | **No** | Neither equality nor an A3 counterexample has been proved |
| The backward recurrence equals canonical tuple membership | Complete written proof in the report | Soundness, completeness, and lexicographic termination |
| Every balanced binary interior permits the exact tuple `(a^p,v,a^(N-p))` in A3 | Complete constructive written proof | Actual original-rule certificate generator and local checker |
| The parameterized obstruction region is outside L2 | Complete written proof | All initial useful cuts and all possible peeling trajectories are covered |
| The source's first length-15 L2 obstruction is new here | **No** | Explicit attribution to Yuyama Example 1.4 / Remark 3.19 |
| One-sided binary inclusion is new here | **No** | Explicit attribution to the proof of Yuyama Proposition E.3 |
| The infinite-family extensions have confirmed bibliographic priority | **Not established** | Independently derived; no exhaustive novelty claim |
| All balanced words through length 21 are in L3 | Completed software-assisted computation | Full weighted enumeration and logs; Python cross-check through length 18 |
| A shortest L3 counterexample, if any, has length at least 24 | Conditional on the correctness of the supplied exhaustive implementation and execution | Exact recurrence plus finite counts; all balanced lengths are multiples of three |
| Two ports alone validate the recurrence | **No** | A separate forward-only original-rule oracle is included for small cases |
| All exhaustive decisions have proof-assistant certificates | **No** | Only selected positive derivations have local-rule JSON certificates |
| Written universal proofs were checked by Lean or another proof assistant | **No** | Human-readable mathematical arguments, tests, and Python certificate checks |
| Nonmembership in this canonical L3 excludes every fan-out-three well-nested grammar | **No** | The source's cofinality transformation need not preserve arity |
| The full Kanazawa–Salvati conjecture is resolved | **No** | It requires properness of every canonical level, or a counterexample to that assertion |

The negative family proof is not inferred from its first finitely many
members. It proves all positive integer parameters in the stated region.
The report does not assert a complete classification outside that region.

The entire finite search includes words with proper balanced factors.
Restricting a search to factor-balanced-primitive words would be a
heuristic, not a proved complete reduction. No such restriction is used
in the exhaustive runs. Cyclic rotation is also not used as a symmetry.

The artifact is an AI-generated research report prepared for the user's
request, not an externally refereed publication. Independent review is
appropriate before relying on any claimed extension as a published result.
