# Final review: 72/74-gate squared-marker polynomials

**Result: PASS. Optimization is frozen at these sources.**

The final sources change precisely one feature of their independently
reviewed parents: they remove `marker_unit = marker_square + 1` and feed
`marker_square` directly to the final product. The 16 positive unknowns,
five fixed numeral ports, every retained factor, and the compiled machine
are unchanged.

| Source | Multiplications | Additions/subtractions | Total | Exact degree |
|---|---:|---:|---:|---:|
| `fixed_input72_square_marker.json` | 41 | 31 | 72 | 157 |
| `fixed_input74_ordinary_square_marker.json` | 41 | 33 | 74 | 101 |

## Semantic review

Write \(r=q-F-Z-\alpha-C\), with \(C=Z+W_0\). At a new zero,
\(r^2=1\); for the normalized variant this follows after cancelling the
positive factor \(\Delta\). Thus \(r=\varepsilon\in\{-1,1\}\), and

\[
q=W_0+F+2Z+\alpha+\varepsilon,
\qquad \alpha+\varepsilon\ge0.
\]

The old core proof only needs the following strict budget margins before
recovering dyadicity:

\[
q-C=F+Z+\alpha+\varepsilon\ge2,
\quad q-F-Z=W_0+Z+\alpha+\varepsilon>0,
\quad q>W_0.
\]

They still hold even in the boundary case \(\alpha=1,\varepsilon=-1\).
All retained norm factors are independent of \(\alpha\), as also checked
from their literal dependency graphs. The reviewed norm-sign, main-Pell,
auxiliary-positivity, strong-rank, target-recovery, and no-wrap arguments
therefore remain valid. In particular they recover \(q=2^\ell\).

Now \(q\) and \(W_0\) are powers of two with \(q>W_0\), so
\(q\ge2W_0\). Consequently

\[
q-C=\frac{q-W_0+F+\alpha+\varepsilon}{2}
>\frac{W_0}{2}\ge2d,
\]

since \(F+\alpha+\varepsilon\ge1\). Thus
\(\alpha_{\rm raw}=q-C-2d\) is strictly positive, and the parent raw75
restoration proves soundness. There is no missing strictly positive
budget-slack assumption.

For completeness, start with a zero of the parent and replace
\(\alpha\) by \(\alpha+1\). The old residual 0 becomes \(-1\), whose
square is 1, while all retained factors remain unchanged. This proves
equivalence of existence of positive solutions. It does not assert equal
positive zero sets or a pointwise inverse using \(\alpha+\varepsilon\),
which could be zero. `SQUARED_MARKER_PROOF.md` makes this distinction
explicitly and correctly.

## Independent source replay

`check_square_marker_review.py` imports neither the producer nor its
validators. It checks the complete literal row deletion/rewire, the
unchanged source interface, all live gates and inputs, and the exact gate
counts. It also proves the retained factors' independence from \(\alpha\)
by syntactic dependency propagation.

Let \(U\) be the retained product, including the normalized strong factor
when applicable. The exact identities underlying the change are

\[
P_{\rm old}(\alpha)-P_{\rm new}(\alpha)=U,
\qquad
P_{\rm new}(\alpha+1)
=P_{\rm old}(\alpha)-2Ur(\alpha).
\]

Both identities were independently replayed on 64 signed assignments per
variant. An independent exact univariate polynomial replay also confirms
both degrees and unchanged top coefficients on the diagnostic coefficient
slice. The general degree statement follows from the already reviewed
parent leading forms: replacing \(1+r^2\) by \(r^2\) preserves the
degree-two leading form, while the removed summand has degree two less
than the full polynomial. No specialization of the actual positive fixed
coefficient ports changes the previously exhibited nonzero leading
monomial.

The complete receipt is `square_marker_review_checks.json`.

| Reviewed artifact | SHA-256 |
|---|---|
| `fixed_input72_square_marker.json` | `ff6e5a4d624cf22525cdbf149281cb17c1519b040f98c65d4793774040bc25e9` |
| `fixed_input74_ordinary_square_marker.json` | `323bb6a161e21bb11c050822e6c96666939144caaaec6142bbc5b7f85ba3a0af` |
| `SQUARED_MARKER_PROOF.md` | `b5a1d3d0ec28c88a16ee0a7ca9a74fd4f915976b17c38b5e2f3226bbf6df380a` |

The seven-equation system and its independently reviewed quadratic/quartic
lift are unchanged. This review is not a new Lean/Rocq kernel proof and
does not construct a positive solution of the fixed K215 instance.
