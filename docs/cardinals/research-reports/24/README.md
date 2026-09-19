# Cover exactingness between strongly compact cardinals

Research continuation IV, prepared for Vladimir Reshetnikov, 18 September 2026.

## Files

- `Cover_Exacting_Stationary_Seeds.tex`: self-contained LaTeX source with embedded bibliography.
- `Cover_Exacting_Stationary_Seeds.pdf`: the compiled 19-page report.
- `build.sh`: three-pass pdfLaTeX build script.

## Main result

In ZFC there are no cardinals delta < lambda <= gamma < kappa such that
both delta and kappa are strongly compact and lambda is gamma-cover exacting.
The upper inequality kappa > gamma is strict. The theorem does not assume
the Ground Axiom, stabilization of the HCD hierarchy, or preservation of a
particular successor cardinal.

More generally, under a strongly compact delta < lambda and gamma-cover
exactingness of lambda, no HCD(eta) with eta >= q(gamma) can be a set-forcing
ground of the ambient universe. Here q(gamma) is gamma at a singular cover
bound and gamma^+ at a regular cover bound.

The proof combines the supplied reports' completeness barrier with
omega-club amenability and a detailed stationary-seed covering argument.
An additional verification uses Goldberg's published covering dichotomy.
Further deductions include a quantitative stationary-width bound, an
explicit threshold for measurability in high HCD models that satisfy Choice,
and a weakening of the lower compactness assumption to a countably complete
fine-ultrafilter hypothesis.

## Scope and status

The deductions are new relative to the supplied synthesis. No claim of
historical priority is made. The report explicitly credits its classical
methods and separates major external inputs from the new deductions.

This is an unrefereed conventional mathematical argument, not a
machine-verified result. It does not refute cover exactingness alone or
settle coexistence above one lower strongly compact cardinal when there
is no strongly compact cardinal above the fixed cover bound. No new Lean
formalization is included.

## Building

A TeX Live or MiKTeX installation with the packages named in the source is
required, including newpx, microtype, tcolorbox, titlesec, fancyhdr, and xurl.
Run `sh build.sh`, or run pdfLaTeX on the source three times. The bibliography
is embedded, so BibTeX and external figure files are unnecessary.

The source retains the supplied reports' NewPX text and mathematical fonts,
forest/olive/sage palette, page geometry, theorem styles, and report layout.
No separate font files are included.
