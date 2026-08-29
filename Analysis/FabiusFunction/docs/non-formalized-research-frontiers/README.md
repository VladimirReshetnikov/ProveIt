# Non-formalized Fabius research frontiers

This directory is the quarantine boundary for mathematical claims about the
Fabius function and Rvachev's up-function that do not yet have an exact,
audited Lean theorem covering their full hypotheses and conclusions.

The canonical frontier artifacts are:

- [`non-formalized-research-frontiers.tex`](non-formalized-research-frontiers.tex)
- [`non-formalized-research-frontiers.pdf`](non-formalized-research-frontiers.pdf)

The volume consolidates the eleven former standalone research notebooks into
six thematic syntheses, followed by the later primary-exposition gap register:
reusable probability/discrete/asymptotic engines, repeated integration, the
exact dyadic web, dyadic endpoint asymptotics, quantitative Thue–Morse
convergence, and inverse/small-argument saddle analysis. It preserves their
natural-language arguments, symbolic computations, numerical evidence,
warnings, citations, provenance, and explicit proof obligations without
allowing any of that material to be mistaken for the formalization-backed
primary exposition.

Some passages use already-formalized results as inputs. That does not certify
the subsequent deductions. Conversely, when one claim is promoted to the
primary exposition, adjacent exploratory material remains here until its own
exact proof obligation is discharged.

## Placement and promotion rule

A mathematical claim belongs in the primary exposition only when a current
public Lean declaration proves the exact statement, including its domain,
normalization, hypotheses, endpoint convention, and conclusion or error term.
The declaration and its defining module must be recorded next to the claim or
in the primary document's audit map.

A related definition, a theorem with stronger hypotheses or weaker
conclusions, an executable computation, a paper citation, a numerical match,
an `.olean` file, an agent report, or an apparently immediate derivation is not
an exact counterpart. Material supported only in one of those ways stays in
this volume, however standard or plausible it appears.

Promotion is claim-by-claim:

1. Verify the exact Lean declaration in current source.
2. Integrate the supported material organically into
   [`Fabius_Function_and_Rvachev_Up.tex`](../Fabius_Function_and_Rvachev_Up/Fabius_Function_and_Rvachev_Up.tex)
   without duplicating material already there.
3. Remove or relabel the matching frontier obligation while preserving every
   adjacent claim that remains unformalized.
4. Rebuild and inspect every affected PDF.

Research drafts are temporary inboxes, not archives. Once every part of a
draft has either been integrated into the primary exposition or preserved in
the canonical frontier volume, delete the processed draft. Delete the draft
directory itself when it becomes empty.

## Consolidation provenance

The unified source records a provenance banner and the historically supplied
SHA-256 value for every absorbed document. A printed checksum is provenance
metadata, not a formalization claim; where no reachable repository blob
reproduces it, the canonical TeX labels it explicitly as unverified rather than
silently treating it as authenticated. The source snapshots consolidated on
25 August 2026 were recorded as follows:

| Former source | SHA-256 |
| --- | --- |
| `Fabius_Dyadic_Formulae_and_Alternative_Representations/Fabius_Dyadic_Formulae_and_Alternative_Representations.tex` | `462276b10fcd32b0446deb7cfedc4ec07c2ae55dbd333d5ff9b1d98f07df89e1` |
| `Fabius_Dyadic_q_Connections/Fabius_Dyadic_q_Connections.tex` | `81a0a911ac7ab28e12c6b87ccaf76ffccaf32e48f873abff18fb7a2d01bcf3e5` |
| `Fabius_Dyadic_Asymptotic_Bridge/Fabius_Dyadic_Asymptotic_Bridge.tex` | `c5ad7c5298d958ab63f459a3e246c2293d3020525223bc05ef2d0e1edab58f10` |
| `Fabius_Dyadic_Formulae_to_Asymptotics/Fabius_Dyadic_Formulae_to_Asymptotics.tex` | `6e98efd3afc402159a7f080e8604c951d5bc51be4a73383da67c1241d46d54ca` |
| `Fabius_Integration_Research_Frontiers/Fabius_Integration_Research_Frontiers.tex` | `21222ae5a8c64cf556dac562fd66943ae0b6ed881408e23e37edfa9113bdecbd` |
| `Fabius_Inverse_and_Saddle_Research_Frontiers/Fabius_Inverse_and_Saddle_Research_Frontiers.tex` | `f9d8605761aaaa1b2c2af83e3c5c55dcd6acfc847402163458b03b68c7b35ff8` |
| `Fabius_Thue_Morse_Convergence_Rate/Fabius_Thue_Morse_Convergence_Rate.tex` | `577c5f3426def68a774fedf3fce61552d32200c8da526ace44178f2a8995a6d3` |
| `Fabius_Thue_Morse_Convergence_Rate-2/Fabius_Thue_Morse_Convergence_Rates.tex` | `384d69b461cb94af33f1c080703e269ea77104405d1940413f1944172b3312c0` |
| `Repeated_Integration_and_Rvachev_Up/Repeated_Integration_and_Rvachev_Up.tex` | `eadcb4b414ac93723a91acbd5062d44340f78134a2cecbc18f7d7ba67eb2c9be` |
| `Rvachev_Up_from_Repeated_Integration-2/Rvachev_Up_from_Repeated_Integration.tex` | `fad16072df30d9e6eb5df03da57dd217769180730581f1dfd19fa5be0d16b262` |
| `Small_Argument_Asymptotics/Small_Argument_Asymptotics.tex` | `85f51a20fc7b6bdf3b1d049ec4506f508aee3c4cd70554e6a68cbcc30977cb0b` |
| `Primary_Exposition_Gap_Register/Primary_Exposition_Gap_Register.tex` | `06c7b888d9601b67ad7a5c0aee3f087d44d9ecaaa9abfb3bf3edfda4bd29c0d1` |

The eleven notebooks are represented by six thematic syntheses, followed by
the post-audit gap register. Overlapping dossiers were merged around their
stronger backbones: independent derivations, sharper later statements, distinct
warnings, numerical data, figures, and useful provenance remain, while
genuinely redundant repetitions are compressed and cross-referenced. The
recorded checksums identify the intended absorbed snapshots subject to the
verification qualification above; subsequent synthesis and status corrections
are tracked by Git history in the canonical source.

## Draft layout

The draft inboxes under [`drafts/`](drafts/) are grouped thematically
(2026-08-28): `rvachev_up_fourier_decay/` (the Fourier-decay corpus),
`thue-morse/`, `exponents-and-q-series/`, `spectra-and-arithmetic/`,
`integration-and-transforms/`, `inverse-and-sampling/`,
`representations/`, `frontier-compilations/`, and `lambert-w/` (added
when four articles on the Lambert W function itself arrived), with new
archives arriving through `drafts/incoming/` (see its README for the
protocol).
Later the same day every group except the Fourier-decay corpus was
**consolidated into volumes**, in two styles: the original members were
merged mechanically — one document per group, absorbing the member
drafts verbatim with per-part label prefixes (the later second-wave
integral-transforms arrival was folded into that volume the same way,
as Part XII) — while the closely overlapping arrivals of waves two
through six were merged **editorially** into additional volumes
(`inverse-and-sampling/Dyadic_Comb_Frontiers/` and
`Inverse_Endpoint_All_Orders/`,
`representations/Up_Polynomial_Synthesis/`): shared theorems stated
once with the best proof, unified notation, cross-source constants
verified, all source-specific material retained.  Waves seven through
thirteen (all 2026-08-28) were then absorbed into these standing
volumes rather than opening new ones: the lattice draft became a
chapter of `Up_Polynomial_Synthesis`; the two representation volumes
were unified into the single eight-part `Representation_Frontiers`;
the finite-sinc, Fourier-image, transport-geometry, and
atomic-splines reports became Parts III–VI of
`Exponents_and_q_Series_Frontiers`; and the three
Euler–Maclaurin/exhaustion/phase reports were merged editorially into
the comb volume's Bernoulli-periodization section, where the
consolidation itself settled six previously open items (the spectral
positivity D(2r) > 0, the twisted positivity at every odd scale with
its Thue–Morse sign law, both phase-classification conjectures, the
alternating Bernoulli-moment sign law, and the odd half of the sharp
threshold).  The fourteenth and fifteenth waves — a second and a third
independent reconstruction of Rvachev's atomic-functions chapter —
were merged editorially into that volume's Part VI, adding the
fractal-string/tube-formula geometry, the local-degree law with its
critical exponential limit, quantitative Gaussian and uniform
parameter limits, the exact general-base Gamma–zeta Laplace
decomposition (settling the transform-level half of the
periodic-Lambert conjecture), the two Fup hierarchies (the canonical
ladder and the classical narrowing family with its triangular
reconstruction and Gaussian regime), signed gap leading coefficients,
derivative equimeasurability with the full L^p ladder, and the edge
pantograph equations.  The sixteenth and seventeenth waves — same-topic
twins on the signed/reciprocal parameter orbit of the geometric-uniform
family — were merged editorially as that volume's Part VII, adding
affine sign conjugacy, reciprocal germ inversion with its
Laplace/vertical-line dual, geometric multisection, the two-nome
Pochhammer–Prouhet partition function, the exact inverse-geometric
endpoint lattice with its jets and two-term asymptotics, and the
resolution of the periodic-cocycle conjecture via Part VI's exact
Laplace decomposition.  Four revised or expanded editions of the atomic-functions
reports were then merged into Part VI, adding the spectral
Stieltjes–Wigert bridge, the distance-Mellin law, the q-Gaussian
derivative Gram geometry with theta-function Riesz bounds, the
log-Weibull jet-intermittency law, a proof of the Fup_n Edgeworth
register conjecture, and — from the audit-aware expanded edition —
the closed Gaussian-binomial Gram–Schmidt orthogonalization with its
Rogers–Szegő identification, the wrapped-heat-kernel circle model,
the MacMahon determinant constant with triple-product Riesz bounds,
and the overlap-regime theta conjecture.  For provenance the first of
these editions shipped the Russian source scan itself; the scan and
the raw OCR were deleted once their recoverable content was merged
and verified against the volume (SHA-256 hashes stay in the volume's
provenance list; git history archives the files).  A new
`lambert-w/` group collected four independently written articles on
the Lambert W function itself; they were merged editorially into the
single consolidated volume `Lambert_W_Guide/` (the most complete
treatment as the body, the other three's unique layers in a
complements section, a four-way concordance, and a corpus-role
section tying W₋₁ to the endpoint theory).  Several volumes' part-boundary section numbering and
page-counter handling were repaired along the way (edits are marked
`% ed.:` in the sources).  Every volume carries
a provenance section with each absorbed member's SHA-256; the absorbed
directories were deleted (git history is the archive). The
Fourier-decay corpus deliberately stays as separate documents: its
structure is audit evidence (see its README). Each group carries a
`README.md` stating its purpose and contents, and
[`drafts/MANIFEST.md`](drafts/MANIFEST.md) is the global inventory:
every volume with its title and the previous paths of what it
absorbed. Path strings *inside* the documents predate the grouping and
are resolved through that manifest; the mechanical steps changed no
member's mathematical content, and the editorial merges record their
deduplication decisions in their provenance appendices.

## Maintenance

New unformalized mathematical write-ups must be merged into the canonical
LaTeX volume rather than retained as permanent parallel dossiers. A temporary
subdirectory may serve as an inbox during concurrent work (placed in the
matching thematic group above, and added to `drafts/MANIFEST.md`), but it
must be audited, absorbed, and removed promptly — updating the manifest and
group README on removal.

Build the canonical document with exactly three `pdflatex` passes, inspect the
rendered PDF, and commit the PDF with its source. A coordinator may authorize a
source-only feature-branch checkpoint for semantic review before the rebuild;
such a checkpoint is never promoted to `main`. Before integration into
`origin/main`, the matching rendered PDF must be rebuilt, inspected, and
committed. Never advance `main` with a TeX/PDF mismatch. Do not commit `.aux`,
`.log`, `.out`, `.toc`, or rendered page images.
