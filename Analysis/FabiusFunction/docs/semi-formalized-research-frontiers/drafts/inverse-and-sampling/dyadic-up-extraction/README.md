# Dyadic up-extraction

This subgroup holds one document.

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

- Source: `Dyadic_Up_Extraction.tex`, 6,491 lines, 334,375 bytes;
  SHA-256 `1f3d0f03119c9e76b5ca0b975c1f0ee958e1412cf8b6b2e7b85a1a30f586e582`.
- Publication: `Dyadic_Up_Extraction.pdf`, 77 A4 pages, 1,429,227 bytes;
  SHA-256 `26b967e43c3d34ba57ab5e9d8ead2a9d2a36fa504db216f8758914445072ede7`.
- Verifier: `verify_dyadic_up_extraction.py`, 646 lines, SHA-256 `11f527679a460f8c65e23fe9b277a4e7ec88f1e0818c3faf0fde9ecb3444a322`;
  standard library only, exact `fractions.Fraction` arithmetic, writes
  nothing unless `--out-dir` is given; checks every reduced dyadic point of
  depth ≤ 7 in about fifteen seconds.

## Provenance

Six independently written reports arrived as bare directories in intake
commit `8f822212d` on 2026-09-02 and were merged editorially into this
volume on 2026-09-03.  All six proved the same theorem under six
normalizations; none was a superset of the others, and each contributed a
layer the volume keeps.  The absorbed directories and their retained
arrival PDFs were deleted after a residue audit; git history is the archive,
and the volume's provenance appendix carries each source's receipt and
contribution.  Every result carries a proof; every printed rational was
checked against the packages' captured verification outputs; corrections
are marked `% ed.:` at the point of repair and collected in the volume's
ledger.

See [`../../MANIFEST.md`](../../MANIFEST.md) for the group record.
