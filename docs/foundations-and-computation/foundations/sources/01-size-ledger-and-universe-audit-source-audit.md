# Source and verification audit

## Supplied sources

1. `surcomplex_analysis(3).tex`
   Title: Surcomplex Analysis: Infinitesimal Calculus, Hahn-Coherent Holomorphy,
   and Contour Theory. Dated September 21, 2026.
   Relevant source labels: `sec:foundations`, `thm:smallscale`, `thm:rigidity`.
   The article preserves the source's fine-local / Hahn-coherent / all-scale
   distinctions and its permission to enlarge the initial exponent workspace.

2. `surcomplex_analytic_geometry.tex`
   Title: Infinitesimal Analytic Geometry over the Surcomplex Numbers.
   Dated September 21, 2026.
   Relevant source labels: `sec:hahn`, `sec:germs`, `thm:workspace`,
   `thm:finite-deform`, `lem:finite-dependency`.
   The article preserves radius-free analytic coefficient germs and does not
   substitute a uniform ordinary convergence radius.

These are user-supplied research manuscripts, not independently certified libraries.
They are cited as sources of claims and design requirements. Original source files
are not duplicated in this archive.

## Current software source inspection

Inspected September 21, 2026, using the public GitHub connector:

- Repository: `vihdzp/combinatorial-games`
- Immutable revision: `02b4a908ea2ecfefffecb438f691951a814a5264`
- `lean-toolchain`: `leanprover/lean4:v4.35.0-rc2`
- `lake-manifest.json` Mathlib revision:
  `dec5b2b780537b6eaf7f5e5f000c12f7387fb24d`

Concrete files inspected:

- `CombinatorialGames/Surreal/Basic.lean`
  Defines `Surreal : Type (u + 1)` by antisymmetrization of numeric games;
  provides `Surreal.out` using quotient choice.
- `CombinatorialGames/Surreal/Division.lean`
  Contains an explicit `noncomputable instance : Field Surreal`.
- `CombinatorialGames/Surreal/HahnSeries/Basic.lean`
  Defines a small-support Hahn subfield and requires `Small.{u}` support;
  contains coefficient, support and truncation infrastructure. A complete
  ordered-field normal-form equivalence was not established by this inspection.
- `CombinatorialGames.lean`
  Import inventory, not an independent proof of each module's mathematical scope.

No successful repository build, comprehensive placeholder search, or transitive
axiom audit was performed. No claim that real closedness or surcomplex analysis is
already formalized is inferred from a field instance or a module name.

## Rolling documentation

Mathlib Hahn summability and one-variable HEval documentation, Mathlib internal
ZFC/class documentation, and official Lean universe/proposition/axiom documentation
were inspected online. They are rolling sources, not asserted to be synchronized
with the pinned CombinatorialGames revision. The HEval page explicitly lists the
finite-variable analogue as a TODO in that module.

## Research status distinctions

- Pąk and Kaliszyk's ITP 2024 paper reports Mizar normal-form formalization.
- Hamkins's March 2026 lecture announcement describes work in progress with
  Junhong Chen and Ruizhi Yang. Its enriched birthday-order theory is not the
  pure ordered-field theory, and the announcement is not used as a verified
  axiomatization or consistency proof.
- The mathematical obstructions, localization argument, finite-algebra descent,
  and fixed-workspace rescaling example are proved in the article. No novelty
  claim is attached to them.

The bibliography in the LaTeX/PDF gives source links. The archive includes no
third-party source trees or font files.
