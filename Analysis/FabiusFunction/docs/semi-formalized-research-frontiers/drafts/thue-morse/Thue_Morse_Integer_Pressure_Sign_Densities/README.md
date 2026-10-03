# Quantitative Taylor sign densities

For each integer m>=2, write p_m(t/pi)=sum c_(m,k)t^(2k). Each strict coefficient sign has lower natural density at least

    1 / [16 m (m-1)^2].

The same bound holds separately for the sequences c_(m,2j) and c_(m,2j+1), corresponding to pressure degrees 0 and 2 modulo 4. These are densities relative to the index of the specified sequence. The result does not assert that a limiting sign density exists, and the lower bound tends to zero with m.

## Contents

- `article.pdf` and `article.tex`: the six-page (five as delivered) proof and editable source
- `inputs/infinite_pressure_sign_changes.pdf` and `.tex`: the preceding sign-law proof, unchanged; it supplies the finite-radius and real/imaginary Perron facts
- `inputs/repository_integer_pressure.tex`: the inspected, pinned ProveIt normalization and finite Fourier source
  (the two `inputs/` entries were not filed; see the editorial amendments below)
- `PROVENANCE.md`: versions, input hashes and mathematical scope
- `build_local.sh`: a build helper for the reference Linux TeX configuration
- `SHA256SUMS`: all supplied file hashes (retired on filing; not in the repository)

The proof is analytic. No finite sign sample or numerical singularity approximation is used to obtain the density bound. The main steps are finite local root monodromy, removable nonzero eigenvalue limits, convergent Puiseux expansions, a C^K boundary subtraction, Darboux integration by parts, two elementary Cesaro moments, and a Laurent-discriminant degree count.

## Build

A standard TeX installation with AMS, geometry, Latin Modern, microtype, hyperref and xurl packages can build `article.tex` in two pdflatex passes. The supplied `build_local.sh` uses the explicit TeX and font-map paths of the reference environment. PDF metadata can change on rebuilding; the mathematical text is unchanged.

This is unrefereed ordinary mathematics, not a Lean formalization. The general complex-analytic mechanisms are classical; no priority claim for them is made. All previously delivered reports remain unchanged.


## Editorial amendments (ProveIt, 2026-10-01)

Made in the editorial pass after batch 72 of `docs/incoming/` (see
`docs/incoming/README.md`). Every change to the source is marked
`% ed. (2026-10-01)`, every change to a program `ed. (2026-10-01)`. The
mathematical text is unchanged; the byline and `pdfauthor` entry ("Research
note prepared for Vladimir Reshetnikov with OpenAI") are kept as delivered.
This is the ninth of thirteen packages of one series, filed beside the
manuscript they continue, `../Thue_Morse_Integer_Pressure/`, in logical order:
the positivity series `../Thue_Morse_Integer_Pressure_First_Positive/`,
`../Thue_Morse_Integer_Pressure_Higher_Positive/`,
`../Thue_Morse_Integer_Pressure_Positive_Triangle/`,
`../Thue_Morse_Integer_Pressure_Feedback_Boundary/`,
`../Thue_Morse_Integer_Pressure_Beyond_Boundary/`,
`../Thue_Morse_Integer_Pressure_Linear_Region/`,
`../Thue_Morse_Integer_Pressure_Full_Range/`, and the sign series, which
imports the full-range theorem,
`../Thue_Morse_Integer_Pressure_Sign_Changes/`,
`../Thue_Morse_Integer_Pressure_Sign_Densities/`,
`../Thue_Morse_Integer_Pressure_Negative_Bound/`,
`../Thue_Morse_Integer_Pressure_First_Negative/`,
`../Thue_Morse_Integer_Pressure_Cluster_Asymptotics/`, with the dataset
`../Thue_Morse_Integer_Pressure_First_Negative_Data/`. An earlier version of
`../Thue_Morse_Integer_Pressure_Full_Range/`, *The Full Pressure Positivity
Range for Large Integer Orders* (`m >= 4096`), was superseded by it and not
filed; neither was a duplicate archive.

- `article.tex`: an unnumbered environment `ednote` ("Editorial note (ProveIt,
  2026-10-01)") is defined after the theorem environments (no counter
  changes). Three notes:
  - after Theorem 1.1: it contains the infinite-sign statements of
    `../Thue_Morse_Integer_Pressure_Sign_Changes/` (all even coefficients, and
    each class mod 4), not its radius bound, equal exponential scales or
    first-negative corollary, and uses its radii and continuation;
  - after "Consequences and limits": the uncited "earlier positive range" is
    Theorem 1.1 of `../Thue_Morse_Integer_Pressure_Full_Range/`; the first
    negative degree as `m` varies is treated in
    `../Thue_Morse_Integer_Pressure_First_Negative/`;
  - before the bibliography, a series map: the thirteen packages in logical
    order, the superseded earlier version of the full-range article, and the
    filed directory of every source cited (`[Signs]` is
    `../Thue_Morse_Integer_Pressure_Sign_Changes/`).
- `article.pdf`: rebuilt from the amended source with three `pdflatex` passes
  (MiKTeX 26.2, pdfTeX 1.40.29), on a copy: 6 A4 pages (5 as delivered),
  334,157 bytes; all 17 fonts embedded, none Type 3; the final log has no
  error, overfull or underfull box, undefined or multiply defined reference,
  duplicate destination, or rerun request. The pages carrying the notes were
  rendered and inspected.
- The `inputs/` copies (the sign-change article and the repository manuscript)
  were not filed; they are `../Thue_Morse_Integer_Pressure_Sign_Changes/` and
  `../Thue_Morse_Integer_Pressure/`. The submitted checksum ledger was
  retired. The package has no program.
- `build_local.sh`: kept as delivered. It sets `TEXMF` to the Debian paths
  `/usr/share/texlive/texmf-dist` and `/usr/share/texmf`, writes `build/` here
  and copies the result over the filed PDF: build on a copy.
- `README.md`: the page count, the `inputs/` lines and the retired ledger
  under "Contents", and this section.
