# Proposed corrections and convention safeguards

## 1. Persistent wording: known dependencies versus assumed independence

**Source:** `Analysis/Polylogarithms/docs/manuscript/chapters/07-integration.tex`
at `fc4d3bf80534ad7c901d3b8c9e71baf2df0064ed`, paragraph labelled
`integral:neg:psim2`.

The paragraph correctly records that a known dependence in the PSLQ input
can cause the algorithm to return a relation not involving the target. Its
sentence “Basis atoms must be Q-independent” is too strong as a procedural
requirement. The intended numerical candidate list is not necessarily a
proved mathematical basis. Unknown independence cannot be silently assumed.

Replace that sentence with the paragraph in
`corrections/independence_wording.tex`. Remove known exact dependencies or
work modulo an explicitly proved relation system. Neither failure to find a
relation nor success in removing known dependencies proves independence of
the remaining numerical constants.

This is a methodological wording correction, not a newly discovered
miscomputed special value. The general caution has been raised before; the
reviewed wording remains worth correcting. No automatic patch is supplied.

## 2. State the regularization and endpoint scale

The new report proves that, in depth two at a=1, the cutoff constant is
`(gamma^2-zeta(2))/2`, the Abel constant is zero, and the diagonal spectral
constant is `(gamma^2-zeta(2))/2-gamma_1`.

Use `corrections/regularization_conventions.tex` as an optional editorial
insertion. “Finite part” without a limiting variable and subtraction rule
is insufficient when moving between these schemes. For root filtering,
`w=z^(1/q)` also changes the logarithmic scale by `log(q)` and therefore
changes a constant unless the appropriate polynomial shift is made.

This is a preventive convention proposal. No claim is made that a specific
unreviewed incoming report conflates these operations.

## 3. Keep the decorated master kernel formal

The new report's Gamma-moment kernel has zero radius on its quadratic-log
axis. Its coefficients are valid, but its unrestricted integral is not a
holomorphic master germ. This caveat concerns the present report; it is not
an alleged error in existing repository material.

## 4. Preserve proof status and attribution

Keep the standard symmetric-sum, Gamma regularization and height-one Gamma
identities attributed to the literature. Do not promote S6 or S8 on the basis
of this continuation. Do not interpret the polynomial atom ring as a theorem
of independence or minimum depth.

The incoming binary ZIP payloads were not inspected, so their detailed
claims and possible overlap remain outside this audit.
