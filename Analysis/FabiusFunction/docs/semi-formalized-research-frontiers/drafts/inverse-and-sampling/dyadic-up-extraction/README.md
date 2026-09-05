# Dyadic up-extraction

This subgroup holds two documents: the canonical extraction volume and its
evaluation-formula companion, consolidated from three arrivals of
2026-09-04.

## The canonical volume

[`Dyadic_Up_Extraction/`](Dyadic_Up_Extraction/) is the canonical volume
*Exact Dyadic Extraction of Rvachev's Up-Function from Finite Sinc-Product
Splines*.  For a dyadic rational `x` of depth `s` (least `s` with `2^s x`
an integer) and `d = ⌊s/2⌋`, it proves that the finite sinc-product spline
with factors `k = 0..n` satisfies, exactly and for every `n ≥ s`,

    up_n(x) = up(x) + Σ_{r=1}^{d} C_r(x) 4^{-rn},   C_r(x) = (-1)^r a_r 4^{-r} up^{(2r)}(x),

with `a_r` the positive rational coefficients of `1/Φ`, `Φ` the Fourier
transform of `up`; that the onset is exact (one level earlier `x` is a knot)
except for an improvement by one level at odd depth; that all `d` modes are
nonzero when `s ≥ 2`; and that geometric Lagrange interpolation at the nodes
`1, 1/4, …, 4^{-d}` yields the single extraction row recovering `up(x)`
from `d + 1` consecutive rational samples, together with every mode and
every even derivative of `up` at `x`.  It relates the result to the
Exponents volume's signed quarter-base Richardson combination, which is
asymptotic for general `x` and becomes exact at dyadic points; proves that
the defect at the last level before the onset is exactly
`-eps_k 2^(-C(s,2)) B_s/s!` (a Thue-Morse sign times a Bernoulli number, zero
at odd depth), so the onset is sharp; and records in a formalization
register which pieces are kernel-verified in Lean.

- Source: `Dyadic_Up_Extraction.tex`, 6,491 lines, 334,375 bytes.
- Publication: `Dyadic_Up_Extraction.pdf`, 77 A4 pages, 1,429,227 bytes.
- Verifier: `verify_dyadic_up_extraction.py`, 646 lines; standard library
  only, exact `fractions.Fraction` arithmetic, writes nothing unless
  `--out-dir` is given; checks every reduced dyadic point of depth ≤ 7 in
  about fifteen seconds.

Six independently written reports arrived as bare directories on 2026-09-02
and were merged editorially into this volume on 2026-09-03.  All six proved
the same theorem under six normalizations; none was a superset of the
others, and each contributed a layer the volume keeps.  The absorbed
directories and their retained arrival PDFs were deleted after a residue
audit; git history is the archive, and the volume's provenance appendix
carries each source's receipt and contribution.  Every result carries a
proof; every printed rational was checked against the packages' captured
verification outputs; corrections are marked `% ed.:` at the point of
repair and collected in the volume's ledger.

## The evaluation-formula companion

[`Recurrence_Free_Dyadic_Values/`](Recurrence_Free_Dyadic_Values/) is
*Recurrence-Free Dyadic Values of the Fabius and Rvachev Functions* (42 A4
pages; 3,197 source lines, 151,386 bytes; 18 theorems, 5 propositions,
11 lemmas, 2 corollaries, every one with a proof).  It answers a question
the volume does not pose: exact evaluation of `F(m/2^n)` and `up(m/2^n)` by
formulas in which no auxiliary quantity is defined by a moment recurrence or
a limiting process.  Its principal formula expresses `F(m/2^n)` through
`⌊n/2⌋ + 1` explicit Thue–Morse integer power sums with rational
quarter-base interpolation weights — the volume's extraction row read as an
evaluation formula, with the spline values themselves replaced by integer
sums — and proves the underlying exact polynomiality of the centred
finite-uniform distribution functions in `4^{-N}`, the exact degree
`⌊n/2⌋` at reduced interior dyadics, and the minimality of the sample count
for any grid-wide linear rule.  Around it are the other finite routes to the
same rational: the Thue–Morse master identity in raw and centred form; the
moment coefficients by positive ordered compositions, by Bernoulli
multiplicity sums with the Bernoulli numbers given as finite sums, by a
Bernoulli-free factorial formula, and by interpolation of finitely many
uniform convolutions; two binary compressions to one summand per nonzero
digit (a block identity valid for the signed extension at every numerator,
and an alternating telescope); an integer bordered determinant with two
explicit common denominators and a certified rounding formula; the
half-base row with arbitrary shift, from which the quarter base follows by
centring; direct extraction from finite densities; every dyadic derivative
and iterated primitive; and the normalized reciprocal-integer-base laws.  A
dictionary section relates its objects to the volume's (`up_n = u_{n+1}`,
`a_r = (−1)^r e_r`), and a formalization register states which ingredients
have Lean counterparts (the finite splines, the coefficients, the
deconvolution at scale one, the dilation law and dyadic jet, the weights
and their identities, the cell identity at `x = 1/4`) and that the general
polynomial law and every evaluation theorem are unformalized.

- Source: `Recurrence_Free_Dyadic_Values.tex`; loads
  `docs/fabius-notation.tex`; labels prefixed `rf:`.
- Publication: `Recurrence_Free_Dyadic_Values.pdf`, 42 A4 pages, built by
  three `pdflatex` passes with 0 errors, 0 undefined references, 0 overfull
  boxes above 15 pt.
- Verifier: `verify_recurrence_free_dyadic_values.py` with its recorded
  run `verification_results.json`; standard library only, exact rational
  arithmetic, no floating-point tolerance.  It merges the three retired
  source programs and adds the checks the consolidation introduced; at
  maximal depth 8 it compares seven value formulas on every representation
  `m/2^n`, checks the shrinking-cell identity, the scale polynomials, the
  exact degree, the derivatives against the dilation law, the rounding, the
  half-base shift identity, the density extraction, the integer bases, and
  every constant printed in the document.

### Provenance of the companion

Three independently written articles arrived on 2026-09-04 and were filed
the same day as separate members beside the volume:
`fabius_dyadic_closed_forms/` (*Recurrence-Free Closed Forms for Dyadic
Fabius and Rvachev Values*, 1,441 lines, 22 pp.),
`fabius_dyadic_closed_forms-2/` (*Recurrence-Free Dyadic Values of the
Fabius and Rvachev Functions*, 1,456 lines, 26 pp.), and
`fabius_rvachev_recurrence_free_closed_forms/` (*Recurrence-Free Dyadic
Formulae for the Fabius and Rvachev Functions*, 1,681 lines, 23 pp.).  They
overlapped on roughly four fifths of their content — the master identity,
the composition and partition coefficients, the block formula, the
quarter-base extraction, the exact degree, the weight bound, the fold to
the bump — and each carried layers the others lacked: the first the
Taylor-integral proof for the signed extension, the finite-cube formula,
the Bernoulli-free cumulants and the Prouhet route to the degree drop; the
second the shrinking-cell theorem, the minimal-sample theorem, the
finite-prefix coefficients, the certified rounding and the integer-base
cumulants; the third the raw-moment forms, the odd-depth formula, the
telescope, the `(d+1)`-bordered determinant, the general finite-jet
deconvolution lemma, the shifted half-base identity, the direct density
extraction, the primitives and the finite base-`b` arithmetic.  They were
merged editorially into the companion on 2026-09-04 — one statement of
each result, every sketched or omitted proof written, the four numerator
letters, three coefficient names, three reciprocal-coefficient names and
two spline indexings reconciled once, every printed rational re-verified —
and the three directories with their retained arrival PDFs were deleted
after a residue audit of every titled result; git history is the archive,
and the companion's provenance appendix records what each source
contributed.  No mathematical claim of any source was found to be false;
the only corrections were indexing conventions.

The same exact-polynomiality statement is also proved independently in
[`../../thue-morse/Thue_Morse_Research/`](../../thue-morse/Thue_Morse_Research/)
from the same day's batch.

### Why two documents

The volume is the extraction theory in the density normalization, with its
knot geometry, onset and defect theorems, mode recovery, Romberg tableau,
and conditioning; the companion is the evaluation calculus in the
distribution-function normalization.  They share one mechanism and one
row, and the companion's dictionary section makes the identification exact.
Folding the companion into the volume as a further part is the natural
follow-up once the volume's concurrent formalization work has settled.

See [`../../MANIFEST.md`](../../MANIFEST.md) for the group record.
