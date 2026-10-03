# Integrated mathematical review of the third-deficit article

Date: 2 October 2026.

## Verdict and scope

The integrated article preserves the independently reviewed matching coefficient bounds and establishes

D_n=C_*F[1+(7/3)log L/L+κ/L]+o(F/L),
κ=log Y_0−2log3+2c_*, L=log n.

The inverse corollary and finite-precision action interpretation are valid consequences at the stated scale. No unresolved mathematical integration defect was found. This is mathematical research verification, not journal peer review, formal proof-assistant verification, or a literature-priority certificate.

The review covered the complete main TeX source, all three included sections, the corresponding component proof notes and independent audit, and all 17 rendered PDF pages. The upper section is byte-identical to the previously reviewed standalone upper-section source. The lower and inverse sections were compared with the proof mechanisms and checked directly as described below.

## Main theorem and upper section

The exact constants, kernel normalization, full macro-degree convention, square-root amplitude, and defective critical row mass are consistent with the pinned earlier reports. The uniform growing-head estimate, corrected endpoint error O(log L/L), shrinking row gap, Legendre expansion, endpoint truncation, complementary Chernoff estimates, terminal weights and first-hit bound remain present. Their combined error is o(F/L); the statement does not replace it by an effective numerical bound.

The upper section retains the distinction between the geometric endpoint-sum error and the larger conversion error in its limiting main term. The chosen L^(-1/4) slack dominates both. It also retains the integrated squared perturbation bound needed for the κ coefficient.

## Lower section

The real cutoff has weights in [0,1], so it supplies a lower subkernel. Its uniform threshold expansion is used only on h_0<=h<=RH; global arguments use comparability and exact one-sided derivative bounds instead of differentiating an asymptotic remainder.

The scalar energy minimum constructs a duration-n arch, including the possible cutoff junctions. Rounding its macro duration creates an O(H) mean-degree change, which lies within the stated O(HL) repair allowance. Complete normalized rows retain the small-q mass, so the middle patch's mean degree has the essential factor 1−m_*.

The independent left/right sampling, prefix/suffix concentration, deterministic drift errors and shrinking legality margin are consistent. The parity choice of the number of repair slots makes their deterministic endpoint heights equal. The exact middle repair absorbs both total degree and endpoint-height errors; internal patch degree is explicitly total degree minus one. Its positive Gaussian windows have a fixed positive capacity margin, and their total logarithmic cost is o(F/L).

The fixed macro count and fixed patch positions make the weighted counting injective. Fractional cutoff factors can only decrease the retained weight. A shorthand in the initial integrated text was clarified before approval: the tilt identity now explicitly concerns the product χ_{h_j}(q_j)w(e_j,q_j,d_j), rather than suggesting equality for the unmodified weights alone. The text then states the resulting lower-bound inequality. This clarification preserves the proof while making the probability normalization exact.

The summation-by-parts, quadrature, seed and endpoint terms are below the target scale. Evaluating the fixed shifted Kepler trial avoids any unjustified moving-peak differentiation and gives the stated κ.

## Inversion and action consequence

For T=log Y and λ_0=log μ, expansion at x=T/λ_0+O(T^(1/3)(log T)^(2/3)) gives

x^(1/3)(log x)^(2/3)
 =λ_0^(-1/3)[T^(1/3)(log T)^(2/3)
 −(2/3)log(λ_0)T^(1/3)(log T)^(-1/3)
 +o(T^(1/3)(log T)^(-1/3))].

The change in x itself contributes only O(T^(-1/3)(log T)^(4/3))=o(1). The other two forward terms transfer at their stated precision. Hence κ_inv=κ−(2/3)log λ_0 is correct. The comparison at the two rounded points separated by εT^(1/3)(log T)^(-1/3), followed by ε decreasing to zero, establishes the integer threshold formula. No unconditional exact rounding rule is claimed.

The action interpretation follows by sandwiching the exact scalar minimum between the proved lower-coefficient construction and the fixed trial action, then using the matching upper-coefficient estimate. It is only an o(F/L)-precision equality, not an all-orders action reduction.

## Checks and presentation

The new third_order_checks.py and independent check_constants.py were rerun successfully. Exact algebra confirms the constant identities and κ; the inverse shift is also checked in the new diagnostics. These computations corroborate the formulas but do not substitute for the asymptotic arguments.

All 17 pages were rendered and inspected. The clarification changed only the latter part of the document; final pages 14–17 were rendered and inspected again. The approved PDF is legible with no observed clipping. Archive integrity and complete dependency replay are separate release checks.

The article explicitly leaves the remaining logarithmic error unquantified and does not claim a multiplicative equivalent, a power-law prefactor, an all-orders hierarchy, an exponentially complete transseries, or an exact integer inverse rule. Earlier artifacts remain unchanged.

## Hash-bound approved payload

All included mathematical TeX sources are listed. Any subsequent change requires reconciliation and a fresh hash signoff.

- `a202061-third-order.tex`: `aee6974bddd91086aa329c7f95aca401627ac8019c0a323393eddc6d541e4035`
- `proofs/upper-section.tex`: `e7cad8bcb5c547811fbac80e3b9d94978ace084c094dff2b67436e0a48738ed6`
- `proofs/lower-section.tex`: `f0e658aa246ebcccba8e61bbb107c1b8be6cb45211fc0be8485a3d537d639126`
- `proofs/inverse-section.tex`: `9582461e980808bcef31f498afdb409833c98e9fe220a2abdadb0b443a215742`
- `a202061-third-order.pdf`: `0e850d5b85b070f95b8980a8351f282b6d9a8814ae0462f113244c7b42439e98`
