# Baseline audit for the final comparison

**Comparison snapshot:** `8f8fac484b976ba0ab75fd173282e838ca5a3b85` of `VladimirReshetnikov/ProveIt`. Both incoming archives below are present in that snapshot. These are specific comparison points, not a claim that any one point is globally simplest.

## Exact source-path citation table

The prefix `D/` below means `Computability/DiophantineConsistency/` in the pinned repository. For ZIP sources, the member path follows `::`.

| Point and domain | Exact metrics | Authoritative equation path | Exact-degree / explanatory source |
|---|---|---|---|
| Direct C222, nonnegative integers | **522 variables; 400 quadratic residuals; degree 4; 20,225 monomials; height 83,900,628** | `docs/incoming/ConZFC_Synchronized_Certificates_2026-10-24.zip :: con_zfc_synchronized_certificates/equations/natural522/equation.json` | Same ZIP: `con_zfc_synchronized_certificates/equations/natural522/expanded_polynomial.json`; `con_zfc_synchronized_certificates/README.md`, result table |
| Direct C222, unrestricted integers | **1,690 variables; 842 quadratic residuals; degree 4; 21,381 monomials; height 2,649,643,805,758** | `docs/incoming/con_zfc_batched_certificates_2026-10-23.zip :: con-zfc-batched-certificates/integer/signed_output/equation.json` | Same ZIP: `con-zfc-batched-certificates/integer/signed_output/expanded_polynomial.json`; `con-zfc-batched-certificates/README.md`, result table |
| Saturated norm, nine strictly positive integers | **433 live binary operations; exact degree 1,628,768** | `D/candidates/norm-tail-sharing/saturated_positive.json` | `D/candidates/norm-tail-sharing/README.md`; `D/PROPOSAL_REVIEW_ADAPTIVE_SHEARS_NORM_TAILS.md`, norm-tail section; `D/PROPOSAL_REVIEW_LATEST.md`, frontier table |
| Order-seven support, nine strictly positive integers | **475 live binary operations; exact degree 1,379,730** | `D/candidates/order7-shared-products/order7_positive.json` | `D/candidates/order7-shared-products/README.md`; `D/PROPOSAL_REVIEW_LATEST.md`, paragraph retaining the 475/1,379,730 point |
| Adaptive shear, eleven strictly positive integers | **111 live binary operations; exact degree 211** | `D/candidates/positive11-adaptive-shears/positive11.json` | `D/PROPOSAL_REVIEW_ADAPTIVE_SHEARS_NORM_TAILS.md`, first section; `D/candidates/positive11-adaptive-shears/PROOF.md` |
| Reanchored guard, thirteen unrestricted integers | **195 live binary operations; exact degree 1,072** | `docs/incoming/con_zfc_batched_certificates_2026-10-23.zip :: con-zfc-batched-certificates/guard13/equation.json` | Same ZIP: `con-zfc-batched-certificates/guard13/PROOF.md`, “Exact degree and count”; `con-zfc-batched-certificates/guard13/README.md` |

Pinned archive links:

- [Synchronized certificates](https://github.com/VladimirReshetnikov/ProveIt/blob/8f8fac484b976ba0ab75fd173282e838ca5a3b85/docs/incoming/ConZFC_Synchronized_Certificates_2026-10-24.zip).
- [Batched certificates](https://github.com/VladimirReshetnikov/ProveIt/blob/8f8fac484b976ba0ab75fd173282e838ca5a3b85/docs/incoming/con_zfc_batched_certificates_2026-10-23.zip).
- [Current reviewed frontier](https://github.com/VladimirReshetnikov/ProveIt/blob/8f8fac484b976ba0ab75fd173282e838ca5a3b85/Computability/DiophantineConsistency/PROPOSAL_REVIEW_LATEST.md).

## Independent checks and the two coefficient heights

The original research audit receipt is retained as `checks/BASELINE_AUDIT.json`. The portable checker `checks/verify_baselines.py` replays the coefficient and operation census using the pinned copies under `checks/baselines/`. The original archive-membership check is recorded in the receipt; its archive hashes are listed below. The audit independently squares every residual, collects the full integer polynomial, and compares the result term by term with each supplied expansion. It counts the variables, residuals and distinct monomials, obtains exact total degree four, and computes coefficient height from the collected polynomial. In **both** direct quartics the unique coefficient attaining the height is the constant coefficient. Thus the natural height is **83,900,628**, not an approximation beginning “838”; the unrestricted-integer height is **2,649,643,805,758**. The latter must not be confused with the same batched packet's natural667 height, 2,649,643,818,040.

The audit also independently traverses each compressed circuit from its output, counts every live binary arithmetic operation and confirms all listed circuit nodes are live. The arithmetic splits `(multiplications, additions, subtractions)` are `(256,157,20)`, `(284,162,29)`, `(63,31,17)`, and `(122,41,32)` for the 433-, 475-, 111-, and 195-operation points respectively. The compressed-circuit exact degrees in the table are the exact degrees established by their source proofs and identity certificates, rather than the generally larger uncancelled DAG degree bounds. This audit does not present those source degree proofs as a fresh full rederivation.

The ZIP equation bytes and, where applicable, expanded polynomial bytes were authenticated directly against the pinned archive members. The archive SHA-256 digests are:

| Archive | SHA-256 |
|---|---|
| `ConZFC_Synchronized_Certificates_2026-10-24.zip` | `ea82e23aa5956262c823368e947e31ad113201c22654c214b9c6f7427d63e0bf` |
| `con_zfc_batched_certificates_2026-10-23.zip` | `ff0d3f638d91a905f676f6fe3e40e134979a14880ed34cadf0741604386e8e55` |

## Comparison scope that should remain explicit

1. **The latest review table and the incoming directory have different frontiers.** `PROPOSAL_REVIEW_LATEST.md` still lists the older thirteen-integer point **195 operations / degree 1,088**. The newer incoming batched packet has **195 / 1,072**. A new **186 / 1,072** point improves the immediate incoming baseline by **nine operations at the same degree**; it does not newly obtain the 1,088-to-1,072 degree reduction.
2. **Use the final rewritten nine-variable equations.** The compact saturated current point is **433 / 1,628,768**, not the incoming 435- or intermediate 434-operation representation. The order-seven shared-product point is **475 / 1,379,730**, not its 478-operation parent.
3. **The eleven-variable count is for a single polynomial.** The source also lists a 108-operation two-residual system. The fair baseline for a single Diophantine equation is **111 / 211**. Its whole compact44 coefficient tuple is part of the fixed equation.
4. **Domains and cost conventions matter.** Strictly positive integers, nonnegative integers and unrestricted integers are distinct domains. Binary-operation counts charge multiplication by fixed scalars and squaring, but not numeral leaves or reuse. Residual counts, expanded monomial counts and compressed circuit counts are different size measures. Fixed coefficient tuples and their storage costs also differ between the nine-variable points.
5. **The direct quartic comparisons are specific materialized C222 constructions.** Natural522 and integer1690 come from different incoming packets, and they are not asserted to be globally optimal among all Diophantine representations. Their inherited C222 calibration is pinned inside the packets to commit `08200eb10fde2db408c69dffd840d6920a569b1f`; the comparison snapshot above is the later repository containing those packets.

The pinned sources were read without modification. The retained comparison files are used only for the comparison audit and carry their original source interpretation; they are not newly constructed endpoints.
