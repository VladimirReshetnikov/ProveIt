# Counterfactual novelty matrix

Source `e1c8914bc7064d9a8e7c06171a18069a949badd0`; exclusions closed at `91dce223cda86c0755b8a9b2504f84be04443fce`. Every prior proposal, optional mechanism and advertised real-client adapter is assumed applied.

| Family | Decision | Credited lines |
|---|---|---:|
| Sidon endpoint normalization | SURVIVES_SEMANTIC_SCREEN | 4 |
| Definitional depth proof | SURVIVES_SEMANTIC_SCREEN | 2 |
| Exact-order zero-level endpoint reuse | SURVIVES_SEMANTIC_SCREEN | 3 |
| Finite physical-order rigidity | EXCLUDED_EXACT_PRIOR_PROPOSAL | 0 |

Three families, nine claimed physical lines. This is not a compilation or performance result.

## S — Sidon endpoint normalization

Specialize weight_sum_eq_iff on diagonal pairs to prove weight injectivity; discharge the crossed sorted-pair case from both Fin ordering premises. Count the two endpoint edits once.

Nearest prior: F07, V08; closing packet y/report/report.tex:524-538 and arithmetic/patches/sidon-moment.patch; earlier packet t/report/sections/03_coefficients.tex:68-75.

The prior Sidon proposal changes only the moment-polarization proof of weight_sum_eq_iff. It does not normalize these injectivity endpoint clients. Generic coefficient fibers and cast normal forms remain assumed available; no credit is claimed for them.

## I — Definitional depth proof

Replace an expression equality proved by rfl and then congrArg Expr.depth with the same definitional equality proved directly by rfl.

Nearest prior: V03 packet b/report.tex:269-282; V17 affine/max-plus budgets and promised actual adapters.

V03 moves witness-count projection lemmas earlier in the import graph; V17 concerns resource bounds. Neither proposes this direct definitional depth proof. This is a tiny local cleanup, not new metadata infrastructure.

## P — Exact-order zero-level endpoint reuse

Specialize generator_order_succ and full_order at zero and use orderOf_eq_one_iff instead of separate modular-cast/CRT arguments. Count both endpoints as one reuse family.

Nearest prior: V18 coercion packaging, V23 finite invariant predecessor, C05 packet zd/report.tex:255-373, C15 zh/report/04-controller.tex and zj/report.tex:115-188.

C05 establishes exact numerical base orders by finite prime-factor tests, while C15 simplifies controller residue/cardinality clients. Neither specializes the existing lifting/order theorems at k=0; no new generic order or cast helper is credited.

## F — Finite physical-order rigidity

Package a finite strictly monotone endomap as an OrderIso and invoke finite ordinal rigidity.

Nearest prior: C14 packet zh/report/03-physical.tex and physical/REPORT.md; packet zj/report.tex:82-114.

None: zh gives the exact candidate proof and 180→156 accounting; zj gives an alternative finite-rigidity proof. Its 24 lines must not enter new savings.
