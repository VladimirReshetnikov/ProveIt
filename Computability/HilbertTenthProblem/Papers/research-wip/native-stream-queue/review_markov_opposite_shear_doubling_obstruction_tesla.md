# Independent review of the opposite-shear doubling obstruction

PASS, with no requested correction. Tesla read the entire frozen author
note, lines 1–117, and its complete metadata record inertly.

| Reviewed artifact | SHA-256 |
|---|---|
| `markov_opposite_shear_doubling_obstruction.md` | `9815304fec5f0ad4e5534ad7044ba275454e6bcf766e0d6121c583ef3fbe4f09` |
| `markov_opposite_shear_doubling_obstruction.json` | `2437a57f6fd1367c330d6dd8e7f4f2be93449652aba6a4dd09212457fba8a7a7` |

The positive convex weight `theta=mu*t/(mu*t-lambda*s)` lies strictly
between zero and one and cancels the shear coefficient exactly. Its mask
therefore gives a full positive-scaled identity. Rescaling to
`F=-s*f,G=g` turns the first action into a full decrement. The accepted
all-scale identity/decrement obstruction applies, including equal scales.
This proves the stated opposite-sign and zero/nonzero family consequences.

I also independently rederived the determinant identity and its sign.
The rational quotient at the doubling fixed point has no pole, because
any pole of order ell leaves a nonzero factor `2^(-ell)-1`. The resulting
strict weighted average places the unequal eigenvalues on opposite sides
of `2^(-r)`. The common eigenfunction equations instead force the two
threshold deviations to have the same sign. Only mask continuity and
positivity at the other preimage are used; the Taylor expansion belongs
to the finite trigonometric function, not to a differentiated mask.

The dilation-three upper example also checks independently. The sine
coefficient differences give precisely `[[1,-1],[0,1]]/5` and
`[[1,1],[0,1]]/5`. No frequency above two or constant mode survives.
The numerators `(4u^2-1)^2+2(1-u)` and its reflection are at least 1/2
on [-1,1]. Thus the minimum integer dilation at least two is exactly
three for this full two-direction interface, allowing independent scales.

The all-scale fixed-point note (SHA `4d3393be942ad20441f49c4846f9eba7e328d9b065fc88c2d2c73e2bfa36f1fb`),
common-scale note (SHA `baf4667547145049a6e2a842f6c337e25b4a075a7ea18c81bfa22ebd07b7e063`),
and sine lift (SHA `7b30acebde3c5576773e92030242e4e8db1d00530fa9d7733b4ac8796270d1b2`)
were previously read in full as mathematical text and reauthenticated.

This review excludes no arbitrary continuous or wholly flat smooth
encoding, nonnegative mask with zeros, changing chart, or guarded
restricted-line construction. It establishes no denominator optimum,
unbounded integer history certificate, or arithmetic gate saving.
No supplied, frozen, archived or predecessor program or source array
was executed or imported. This is a proof-only review with fresh byte
authentication; no numerical experiment or repository mutation was used.
