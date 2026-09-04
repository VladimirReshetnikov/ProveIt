# Asymptotic transseries of combinatorial sequences

Five independently written articles, filed here on 2026-09-03 as a quick-gate
intake from five ZIP arrivals; the archives were deleted after unpacking and
git history is the archive. They are kept apart from
[`../special-function-inversion/`](../special-function-inversion/) because
they do not invert anything: each derives the complete asymptotic transseries
of a classical integer sequence *forwards*, from the analytic structure of its
exponential generating function.

They fall into two subjects. Within each subject the articles were written
independently of one another; that was noted at intake as provenance, and
**no comparison, deduplication, or canonical selection has been made**. Titles
are transcribed, not assessed.

## Bell numbers

Saddle-point transseries about the principal Cauchy saddle `r = W_0(n)` of
`exp(e^z − 1)`: finite all-orders rules for every coefficient, Lambert-`W`
sector geometry, Touchard-cumulant descriptions, remainder theorems.

| Directory | Document | Source | PDF |
| --- | --- | --- | --- |
| `Bell_Number_Asymptotic_Transseries/` | *The Full Asymptotic Transseries of the Bell Numbers: Finite all-orders saddle coefficients, Lambert-W geometry, Touchard cumulants* | 2,211 lines; 78,882 bytes | 32 A4 pp; 724,026 bytes |
| `Bell_Number_Transseries_Article/` | *The Full Saddle–Transseries Expansion of the Bell Numbers: Lambert-W sectors and combinatorial formulae for every coefficient* | 1,714 lines; 60,076 bytes | 23 A4 pp; 665,924 bytes |

## Fubini numbers

The ordered Bell numbers `F_n = Σ_j j! S(n,j)`, with exponential generating
function `1/(2 − e^z)`: the complete vertical lattice of simple poles
`ρ_k = log 2 + 2πik` gives an exact convergent representation
`F_n = (n!/2) Σ_k ρ_k^{−(n+1)}` and, from it, exact pole sectors, all-orders
coefficients, and certified remainders.

| Directory | Document | Source | PDF |
| --- | --- | --- | --- |
| `Fubini_Number_Full_Transseries/` | *The Full Asymptotic Transseries of the Fubini Numbers: Exact Pole Sectors, General Bell-Polynomial Coefficients, Nonlinear…* | 2,465 lines; 86,507 bytes | 33 A4 pp; 741,812 bytes |
| `Fubini_Number_Transseries/` | *The Complete Asymptotic Transseries of the Fubini Numbers: Exact Pole Sectors, All-Orders Coefficients, Certified Remainder…* | 1,881 lines; 64,271 bytes | 25 A4 pp; 699,100 bytes |
| `Fubini_Number_Transseries_Article/` | (untitled in source; abstract opens with the exact identity `F_n = Γ(N)/2 · Σ_k ρ_k^{−N}`, `N = n+1`) | 1,472 lines; 57,681 bytes | 25 Letter pp; 490,186 bytes |

## Intake receipts

All five archives passed a CRC check with no absolute-path, parent-traversal,
or symlink entry, and each contained exactly one `.tex` and one `.pdf` with no
wrapping directory, so the archive stems name the directories. Two archives
shipped a `.tex` of the same inner name (`Fubini_Number_Transseries.tex`);
the distinct stems keep them apart. The longest filed path is 252 characters,
inside the Windows limit that this tree has already met once. All sources are
LF with a final newline and were filed byte-for-byte. All PDFs are readable,
unencrypted, pdfTeX-1.40.26, with every font embedded and no Type 3 rows; four
are A4 with Libertinus faces and one is Letter without. None loads
`docs/fabius-notation.tex`, so canonical restyling is post-publication debt
here as in the neighbouring subgroups. No checksum ledger was submitted and
none was added.

## Deferred

Comparison of the two Bell articles and of the three Fubini articles,
deduplication, canonical selection, proof checking, numerical reproduction,
notation migration, and Lean crosswalking.
