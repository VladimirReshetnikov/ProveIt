# Claim ledger

| Claim | Status | Evidence / boundary |
|---|---|---|
| Signed compatibility factorization `K=C C^T` over F2 and rank `2^(r-1)` | Proved | Article Section 2; exhaustive independent finite graph checks |
| Full-support finite-group zeta diagonal, determinant and all-characteristic ranks | Proved | Article Section 3; C2, C3 and S3 matrix audit. General-group runtime optimizer not implemented |
| Minimum-cost original-witness basis, sharp universal cardinality | Proved | Article Section 4; independent row/cost replay |
| Linear/bilinear continuation operations including guarded projection | Proved and tested | Article Section 5; orphan loss is rejected, not forgotten silently |
| Euler-optimal connected orientable surface completion | Proved under geometric seam contract | Article Section 6; actual mesh gluing tests |
| Disk preservation | Proved under certified nonempty-boundary contract | Equality `Euler=1` is extremal. Essential boundary and ambient embedding are separate |
| Signed data necessary for every pure disk query | **Not claimed** | Under the full surface contract, unsigned weighted connectivity also suffices for bare disk existence; article states this explicitly |
| Complete finite anchored patch optimizer | Proved and implemented | Article Section 7; all finite input choices are covered; global mesh replay tests |
| `poly(N,B,b) 2^(3b)` finite patch bit bound | Proved | Width is measured at materialized checkpoints; symbolic transitions avoid temporary row expansion |
| `n^(O(log n))` for polynomial-size supplied patch systems of width `O(log^2 n)` | Proved restricted-input corollary | Does not assume those inputs can represent every relevant disk in a knot exterior |
| General quasi-polynomial unknot recognition | **Not established** | Needs complete source-faithful patch production, essential-boundary data, geometry-key and width bounds |
| Weighted representative-family method is new | **Not claimed** | Explicitly credits Bodlaender, Cygan, Kratsch, Nederlof; gain-poset factorization uses classical incidence algebra |
| Global literature priority for every specialized identity | **Not claimed** | Self-contained derivations and project continuation; no exhaustive novelty review |
| Smaller exact rational bilinear compatibility representation | Ruled out for this matrix at the stated dimension | Not a lower bound for every counting algorithm or nonlinear representation |
| Exact counts or full Euler-value spectrum preserved by a minimum basis | **False in general** | Duplicate and different-cost counterexamples are tested |
| Maintained ProveIt test suite / native recognizer benchmark | **Not run** | `results/native_status.json`; only standalone code and explicit mesh systems executed |
| Geometry replay proves a negative patch answer | **Not claimed** | `verify_witness` checks one assembled witness, not absence or optimality |
| Formal proof-assistant verification | **Not performed** | Human-readable proofs, executable tests, independent finite replay; no Lean claim |
