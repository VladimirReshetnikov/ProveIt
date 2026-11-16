# OCiPRA theorem ledger

Status vocabulary:

- **Human proof complete**: a detailed mathematical argument appears in the report.
- **Executable finite check**: the supplied Python implementation tests the exact finite algorithm; it is not a universal proof.
- **Lean interface only**: definitions/signatures are supplied, but no kernel build is claimed.
- **Upstream reusable result**: an existing ProveIt packet reports an object-language derivation; this package does not re-verify it.

| ID | Result | Human status | Executable status | Lean status |
|---|---|---|---|---|
| T1 | Primitive-recursive coding closure for finite tuples, lists, tables and traces | Human proof complete | Used throughout code | Reuse `PR.lean`; adapter needed |
| T2 | Bounded-formula Booleanization | Human proof complete as a compiler schema | Atomic Boolean tests exercised | Exact target/interface; proof not implemented |
| T3 | Least bounded witness with minimality | Human proof complete | `least_bounded`; tests pass | Exact target; proof not implemented |
| T4 | Deterministic contract-DAG composition with reverse demand | Human proof complete | DAG run and replay; tests pass | Exact compiler endpoint; not implemented |
| T5 | Clocked finite-trace reflection | Human proof complete | Trace replay implemented | Reuse upstream QF-induction interfaces; integration incomplete |
| T6 | Monotone finite demand closure | Human proof complete | Exact closure certificate; tests pass | Target module not implemented |
| T7 | Backward viability and least finite path | Human proof complete | Cloud algorithm; tests pass | Exact target; proof not implemented |
| T8 | Exact branch elimination under observable invariance | Human proof complete | Invariance test passes | Target record supplied; proof not implemented |
| T9 | Approximate branch elimination under diameter bound | Human proof complete | Exact rational diameter computed | Target record supplied; proof not implemented |
| T10 | Producer-verifier-derivation factorization | Human proof complete | Admissibility linter exercises examples | Statement discipline; no single Lean theorem required |
| T11 | Height bound / complete-list conversion and cardinality obstruction | Human proof complete | Classification test | Application formalization remains |
| T12 | Dual native/full-PRA proof backend correctness | Human proof complete by typed construction | Not applicable | `NativeContract.toPRA` outline; no build claimed |
| T13 | Regular-name arithmetic and apartness-guarded inversion | Human proof complete at framework level | Not implemented here | Reuse existing packets; adapter remains |
| T14 | Packet conversion workflow for the repository difficulty classes | Human synthesis complete | Profile examples classified | Engineering roadmap only |

No theorem in this package is advertised as newly kernel-checked.  The strongest
new claim is the fully developed mathematical compilation theorem, together
with executable finite algorithms and a precise no-`sorry` Lean completion
plan.
