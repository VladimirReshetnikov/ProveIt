# Integration guide

## Baseline

Repository: https://github.com/VladimirReshetnikov/ProveIt

Commit: `f7e35be357654198c1546fd40f363694c5bcc2cc`

The six archives in `docs/incoming` were extracted separately for research. This is a new mathematical continuation, not an intake rewrite of those archives. The source-map JSON names every archive considered and the precise sections on which the new theorems depend.

## Contribution map

| Component | Source question or foundation | Importable labels | Integration guidance |
|---|---|---|---|
| Order-two optimal prefix | Canonical fifth report, `conj:firstq` and tail-rank section | `thm:rank-two`, `thm:rational-row-two`, `cor:ordinary-two` | Promote the entire smaller-order-two slice to a theorem. Retain its explicit binomial omission rule. |
| General even-order determinant | Same source coefficient matrix | `lem:general-even-factor`, `thm:shifted-H-inertia`, `thm:general-small-determinant` | Import the exact rank-a perturbation and determinant reduction. Nonsingularity of the unperturbed matrix does not settle its perturbation. |
| Order-four optimal prefix | Remaining unequal-order part of `conj:firstq` | `rf:main`, `rf:det`, `rf:parity`, `rf:ordinary-46` | Promote the smaller-order-four slice; retain the exceptional `(4,6)` calculation, its convergent tail identity, and the all-b Bernoulli proof. |
| Order-six optimal prefix | Remaining unequal-order part of `conj:firstq` | `rs:main`, `rs:ratio`, `rs:integrality`, `rs:ones` | Promote the smaller-order-six slice. Retain the explicit polynomial certificate, modulo-four congruence, and the three small cases. |
| Polylogarithmic boundary identities | Harmonic-tail generating series plus the new extraction row | `prop:two-tail-polylog`, `thm:polylog-boundary` | Preserve the largest-index convention for one-argument multiple polylogarithms. |
| Cubic directional zeta | Existing coincident/directional-zeta quadratic results | `tc:main`, `tc:kernel`, `tc:example`, `tc:two-ray-example` | Append the cubic reduction and cancellations. Retain the polar subtraction and admissible-ray domain. |
| Height-one coefficient normalization | Canonical fifth report and Young's height-one literature | `prop:height-one-foundation`, `prop:Cgamma-integral-foundation` | These are inherited foundations, included for self-containment and sign control. They should not be counted as new coefficient evaluations. |
| Differential quotient and parity | Higher-digamma and canonical-fifth research questions | `dq:normalform`, `dq:parity`, `dq:Appelltransport` | Classify integration by parts as a vector-space quotient, with the endpoint functional retained separately. |
| Bilinear coincident products | Manuscript `08-stieltjes-contact-products.tex`, `shj:polyclosurezeta` | `dq:bilinear`, `dq:squareformula` | A directly proved coincident specialization supporting the sixth reduction. Do not advertise this as a new general polygamma closure theorem. |
| Sixth and seventh identities | Higher-digamma exact-reduction questions | `dq:canonicalsixth`, `dq:canonicalseventh`, `dq:M6ordinary` | Preserve the exact mixed-integral definitions, finite-part coordinate, and endpoint constants. |

## Proof-status boundaries

- The optimal first-q prefix is proved here for smaller order 2, 4, or 6, in addition to the inherited diagonal family. The remaining unequal even-order range is `8 <= p < q`.
- The order-six proof includes an exact polynomial identity with an indeterminate b. Its full integer polynomial is in `results/verify_moment_rank_six.json`, reconstructed from the finite matrix definition in the article and the verifier. It is not an interpolation argument.
- The suggested uniform valuation `v2(det(H+U)/det(H)) = -a` is false at `(a,b) = (4,9)`. This is a counterexample to that auxiliary extrapolation, not to the original rank conjecture.
- The full first-q coefficient determinant includes the factor `1/(4b-1)!!` multiplying the square minor. The minor alone and the full moment determinant must not be conflated.
- Formal rank and the local Tornheim ambiguity dimensions do not assert arithmetic independence of the evaluated constants.
- A Tornheim directional derivative is a derivative of the specified holomorphic ray restriction. It is not a global Taylor coefficient at the singular multivariable origin.
- The canonical sixth formula retains one mixed finite-part integral. The seventh retains two specified mixed integrals. These are reductions, not depth-one evaluations of every term.
- Keep the short `S6` and revised `S8` conjectures open. The older rejected `S8` vector is a different statement.
- Retain the attribution of the classical Hankel machinery, the differential-algebra background, and the inherited height-one Mellin bridge.

No new mathematical counterexample was established against the source statements that this article uses. The proposed changes are stronger theorems and explicit normalization clarifications. The audit is targeted; it is not a certification of every proof in the collective manuscript.

## Suggested review order

1. Check the moment definitions and the source-matrix coefficient convention.
2. Review the finite Padé proof and the extraction row.
3. Review the general shifted matrix and each claimed prefix family.
4. Verify the holomorphic Tornheim remainder before using its directional formulas.
5. Verify the quotient basis, endpoint functional, and Gamma/Stieltjes sign convention before the sixth and seventh formulas.
6. Replay the exact programs, then the optional numerical diagnostics.

All displayed theorem labels are local to the delivered article. When merging into the large manuscript, preserve its existing theorem-numbering and bibliography conventions and update the source map if labels are renamed.
