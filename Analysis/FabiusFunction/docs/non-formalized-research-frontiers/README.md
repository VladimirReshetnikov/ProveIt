# Non-formalized Fabius research frontiers

This directory is the quarantine boundary for mathematical claims about the
Fabius function and Rvachev's up-function that do not yet have an exact,
audited Lean theorem covering their full hypotheses and conclusions.

The canonical frontier document is:

- `non-formalized-research-frontiers.tex`
- `non-formalized-research-frontiers.pdf`

It consolidates eleven former standalone research notebooks, including their
natural-language arguments, symbolic computations, numerical evidence,
warnings, citations, provenance, and explicit proof obligations. Some passages
use already-formalized results as inputs; that does not certify the subsequent
frontier deductions.

## Promotion rule

A claim must remain in this directory until all of the following are true:

1. A current Lean declaration proves the exact mathematical statement,
   including its domain, normalization, hypotheses, endpoints, and error term.
2. The declaration and defining module have been independently audited.
3. The formalization-backed exposition at
   `../Fabius_Function_and_Rvachev_Up/Fabius_Function_and_Rvachev_Up.tex`
   records that declaration.
4. The corresponding obligation in the frontier document is removed or marked
   as discharged without disturbing adjacent claims that remain unformalized.

A related definition, a theorem with weaker conclusions, a paper citation, a
numerical match, or a plausible natural-language proof is not enough for
promotion.

## Consolidation provenance

The unified source records a SHA-256 checksum and a provenance banner for each
former document. The inputs consolidated on 25 August 2026 were:

| Former source | SHA-256 |
| --- | --- |
| `Fabius_Dyadic_Formulae_and_Alternative_Representations/Fabius_Dyadic_Formulae_and_Alternative_Representations.tex` | `462276b10fcd32b0446deb7cfedc4ec07c2ae55dbd333d5ff9b1d98f07df89e1` |
| `Fabius_Dyadic_q_Connections/Fabius_Dyadic_q_Connections.tex` | `81a0a911ac7ab28e12c6b87ccaf76ffccaf32e48f873abff18fb7a2d01bcf3e5` |
| `Fabius_Dyadic_Asymptotic_Bridge/Fabius_Dyadic_Asymptotic_Bridge.tex` | `c5ad7c5298d958ab63f459a3e246c2293d3020525223bc05ef2d0e1edab58f10` |
| `Fabius_Dyadic_Formulae_to_Asymptotics/Fabius_Dyadic_Formulae_to_Asymptotics.tex` | `6e98efd3afc402159a7f080e8604c951d5bc51be4a73383da67c1241d46d54ca` |
| `Fabius_Integration_Research_Frontiers/Fabius_Integration_Research_Frontiers.tex` | `05002480d94d3136368ea491d723378221ced6e15955e0ebc69556561af75b55` |
| `Fabius_Inverse_and_Saddle_Research_Frontiers/Fabius_Inverse_and_Saddle_Research_Frontiers.tex` | `d05a201b92ed9031a5b76819cffd68e2cbce5d824839f07bc64a6ad674f9ee0f` |
| `Fabius_Thue_Morse_Convergence_Rate/Fabius_Thue_Morse_Convergence_Rate.tex` | `577c5f3426def68a774fedf3fce61552d32200c8da526ace44178f2a8995a6d3` |
| `Fabius_Thue_Morse_Convergence_Rate-2/Fabius_Thue_Morse_Convergence_Rates.tex` | `384d69b461cb94af33f1c080703e269ea77104405d1940413f1944172b3312c0` |
| `Repeated_Integration_and_Rvachev_Up/Repeated_Integration_and_Rvachev_Up.tex` | `eadcb4b414ac93723a91acbd5062d44340f78134a2cecbc18f7d7ba67eb2c9be` |
| `Rvachev_Up_from_Repeated_Integration-2/Rvachev_Up_from_Repeated_Integration.tex` | `ef52fd2df35a140ff5c26d7a4c32e0618fce8de94f5eff301dc41ecfc1e66f16` |
| `Small_Argument_Asymptotics/Small_Argument_Asymptotics.tex` | `85f51a20fc7b6bdf3b1d049ec4506f508aee3c4cd70554e6a68cbcc30977cb0b` |

Overlapping dossiers are retained when they provide independent derivations,
stronger later statements, sharper constants, or distinct warnings. The
unified document states which later dossier should be preferred when two
versions differ.

In particular, the second repeated-integration dossier supplies the sharper
derivative threshold, and `Fabius_Dyadic_Formulae_to_Asymptotics` is the
preferred dyadic-to-asymptotic synthesis. The neighboring dossiers remain
because they preserve independent coefficient, Bromwich, geometric-simplex,
and proof-sketch routes.

## Maintenance

New unformalized mathematical write-ups should be merged into the canonical
LaTeX document rather than left as permanent subdirectories. During concurrent
work a temporary subdirectory may act as an inbox, but it should be merged,
audited, and deleted promptly.

Build the document with exactly three `pdflatex` passes and commit the PDF with
the source. Before every push that sends a changed frontier TeX source to
`origin/main`, the matching rendered PDF must already be rebuilt and committed;
never push a TeX/PDF mismatch to the main branch. Do not commit auxiliary
LaTeX files.
