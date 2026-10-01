# Quantitative Taylor sign densities

For each integer m>=2, write p_m(t/pi)=sum c_(m,k)t^(2k). Each strict coefficient sign has lower natural density at least

    1 / [16 m (m-1)^2].

The same bound holds separately for the sequences c_(m,2j) and c_(m,2j+1), corresponding to pressure degrees 0 and 2 modulo 4. These are densities relative to the index of the specified sequence. The result does not assert that a limiting sign density exists, and the lower bound tends to zero with m.

## Contents

- `article.pdf` and `article.tex`: the five-page proof and editable source
- `inputs/infinite_pressure_sign_changes.pdf` and `.tex`: the preceding sign-law proof, unchanged; it supplies the finite-radius and real/imaginary Perron facts
- `inputs/repository_integer_pressure.tex`: the inspected, pinned ProveIt normalization and finite Fourier source
- `PROVENANCE.md`: versions, input hashes and mathematical scope
- `build_local.sh`: a build helper for the reference Linux TeX configuration
- `SHA256SUMS`: all supplied file hashes

The proof is analytic. No finite sign sample or numerical singularity approximation is used to obtain the density bound. The main steps are finite local root monodromy, removable nonzero eigenvalue limits, convergent Puiseux expansions, a C^K boundary subtraction, Darboux integration by parts, two elementary Cesaro moments, and a Laurent-discriminant degree count.

## Build

A standard TeX installation with AMS, geometry, Latin Modern, microtype, hyperref and xurl packages can build `article.tex` in two pdflatex passes. The supplied `build_local.sh` uses the explicit TeX and font-map paths of the reference environment. PDF metadata can change on rebuilding; the mathematical text is unchanged.

This is unrefereed ordinary mathematics, not a Lean formalization. The general complex-analytic mechanisms are classical; no priority claim for them is made. All previously delivered reports remain unchanged.
