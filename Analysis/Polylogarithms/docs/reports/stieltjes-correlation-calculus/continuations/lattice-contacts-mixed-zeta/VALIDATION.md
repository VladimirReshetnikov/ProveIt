# Validation record

## Mathematical proof status

Every theorem in the article has an analytic proof or finite exact-algebra proof. The only inherited nontrivial starting formulas are identified, restated with their domains, and attributed.

No theorem depends on PSLQ output, presumed arithmetic independence, or a decimal residual. No Lean formalization or interval numerical certificate is claimed.

## Exact and numerical checks

| Program | Method and recorded scope |
| --- | --- |
| check_lattice_contacts.py | 60 exact contact/Pochhammer coefficient assertions, two mutation controls, 27 numerical finite-lattice diagnostics at 55 digits. |
| check_modular_transport.py | Nine exact kernel-polynomial assertions, four independent Lambert/contour comparisons, two classical boundary identities, and the self-dual contour evaluation, at 42 digits. |
| verify_mixed_tails.py | 306 formal-MZV moment comparisons, 825 boundary-parity checks, 29 simplified-generator checks, two exact prefix determinants, a rational identity, and a finite Laurent-polynomial telescoper; standard-library rational arithmetic. |
| check_mixed_tails_numeric.py | Independent ordinary-sum checks at 90 digits, with explicitly accelerated tails and recorded truncation parameters. |
| verify_independent_shifts.py | 16 exact cancellation tests and 42 comparisons at 65 digits; direct quadratures include complex shifts, pole faces, prefix invariance, ordinary derivatives, and the gamma_1–digamma coefficient. |
| verify_spectral_faces.py | 34 exact rational checks and 11 numerical comparisons at 48 digits, including the original two-dimensional Gamma face integral. |

The largest residual in the independent-shift suite is about 1.02e-56. The direct gamma_1–digamma comparison has residual about 2.24e-65. The original two-dimensional Gamma face at a = 1, B = 0, delta = 0.3 converges to the lattice formula with residuals about 2.33e-19, 3.00e-28, and 4.41e-37 at Gauss–Legendre orders 16, 24, and 32.

These digits describe observed differences of independently organized floating-point calculations. They are not certified error bounds.

## Delicate cases reviewed

The vertical-lattice paired tail was checked before differentiating. Its sine factor gives a positive finite contact at order one; the sinc factor supplies the cubic pi-squared term. The complete cutoff coordinate change is retained.

A leading asymptotic error polynomial can nearly vanish. The lattice verifier therefore compares the next two independently derived Euler–Maclaurin coefficients rather than assuming that the absolute residual decreases monotonically at every derivative order.

The independent-shift proof removes u = 0, v = 0, and u + v = 0 jointly. The unfolded lattice counts the diagonal once; the second strip starts at one. Finite-prefix invariance was independently tested.

The spectral-face proof uses the predecessor's coordinate-simplex measure, without a Euclidean surface factor. Affine terms are annihilated before Gamma sums are used. The weighted extension explicitly uses a twice-anchored normally convergent logarithmic sum.

The joint spectral-order theorem distinguishes holomorphy from ray limits and records an explicit tangential counterexample.

An independent mathematical review checked the lattice signs, Pochhammer normalization, harmonic/Bell coefficients, Gamma/Stieltjes primitive signs, modular functional factor, contour orientation, pole sets, and residue compilers.

## Document checks

The standalone PDF is compiled from the same modular source files that are supplied for integration. The build script rejects overflowing boxes and unresolved references.

All PDF pages were rasterized for visual inspection. Contact sheets were inspected for page layout, display boundaries, table placement, and missing or clipped content. Dense formulas and the rational reconstruction matrix were inspected at larger scale. The final machine-readable review is in results/document_review.json.

## Source coverage

The audit uses the pinned manuscript index, editorial/source status, relevant manuscript chapters, and the ten incoming archives. It is a targeted research-frontier audit, not a complete verification of every historical archive, every manuscript proof, or the repository's Lean code.

The literature search was targeted to primary papers and official reference material. Bibliography notes distinguish full-paper comparisons from publisher-abstract-only comparisons. Historical priority is not asserted for every specialization.

