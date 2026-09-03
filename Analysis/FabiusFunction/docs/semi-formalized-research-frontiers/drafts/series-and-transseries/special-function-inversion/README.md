# Special-function inversion at infinity

Twelve independently written articles that invert a rapidly growing special
function at infinity to all orders, filed here on 2026-09-03 as quick-gate
intakes in three batches: three from commit `5a453e1dc`, six more that
arrived while that first batch was being published, and three (the Fibonacci
subject below, arrival commit `912d3bfbe`) later the same day.  All twelve came as ZIP
archives; the archives were deleted after unpacking and git history is the
archive.

They share a method rather than a function.  In each, the map to be inverted
has a dominant *power–logarithmic* phase, so ordinary series reversion does not
apply; the first step is to invert that phase exactly with the Lambert
`W`-function, and the remaining Stirling- or Bell-type corrections then
generate a finer grid of transseries blocks above that core.  Each article also
extracts a general reversion calculus from its worked case.

This is why they are filed apart from
[`../lambert-inverse-transseries/`](../lambert-inverse-transseries/), whose
three articles all invert the single map `x + W(x)`: the subgroups share the
Lambert-core technique, but that one treats one map in depth while this one
applies the technique across different special functions.

## The four subjects

The twelve fall into four subjects, three articles each, written independently
of one another.  That was noted at intake as provenance; **no comparison,
deduplication, or canonical selection has been made**, and the titles below are
transcribed rather than assessed.

### Gamma and Barnes `G`

| Directory | Document | Source | PDF |
| --- | --- | --- | --- |
| `Asymptotic_Inversion_Gamma_Barnes_G/` | *Asymptotic Inversion of the Gamma and Barnes `G`-Functions: Lambert-Core Transseries and a General Reversion Calculus* | 2,376 lines; 83,252 bytes | 29 A4 pages; 646,225 bytes |
| `inverse_gamma_barnesG_transseries/` | *Asymptotic Transseries for the Inverses of the Gamma and Barnes `G`-Functions: Lambert–`W` Normal Forms, All-Orders Reversion, and Residual Certification* | 1,655 lines; 72,966 bytes | 28 A4 pages; 663,480 bytes |
| `inverse_gamma_barnes_transseries/` | *Asymptotic Inversion of the Gamma and Barnes `G` Functions: Lambert-Normalized Transseries, Explicit Coefficients, and a General Power–Logarithmic Reversion Calculus* | 1,827 lines; 60,596 bytes | 25 A4 pages; 324,795 bytes |

### The hyperfactorial `K`-function

| Directory | Document | Source | PDF |
| --- | --- | --- | --- |
| `inverse_k_function_transseries/` | *Inverting the K-Function at Infinity: Lambert–`W` Normalization, All-Orders Transseries, and a General Theory of Power–Logarithmic Reversion* | 2,259 lines; 66,867 bytes | 29 A4 pages; 349,822 bytes |
| `K_Function_Inverse_Transseries/` | *Asymptotic Inversion of the Generalized Hyperfactorial `K`-Function: Lambert and `r`-Lambert Anchors, Centered Bernoulli Structure, and a General Calculus for Power–Logarithmic Transseries* | 2,644 lines; 90,380 bytes | 33 A4 pages; 724,630 bytes |
| `K_function_inverse_transseries_article/` | *Asymptotic Inversion of the Kinkelin–Bendersky `K`-Function: Lambert-Anchored Transseries for the Generalized Hyperfactorial and a General Theory of `x^p log x` Reversion* | 2,581 lines; 84,722 bytes | 30 A4 pages; 743,783 bytes |

### The subfactorial

| Directory | Document | Source | PDF |
| --- | --- | --- | --- |
| `inverse_subfactorial_transseries/` | *Inverting the Subfactorial at Infinity: Bell-Sector Transseries, Inverse-Gamma Geometry, and a General Reversion Calculus for Rapid Cores with Tiny Oscillatory Tails* | 2,631 lines; 95,404 bytes | 38 A4 pages; 688,626 bytes |
| `inverse_subfactorial_transseries-2/` | *Asymptotic Inversion of the Subfactorial: Bell-Number Tails, Inverse-Gamma Anchoring, and a Calculus for Exponentially Separated Transseries* | 2,188 lines; 73,742 bytes | 27 A4 pages; 725,870 bytes |
| `inverse_subfactorial_transseries-3/` | *Inverse Subfactorials at Infinity: Lambert–`W` Carriers, Bell-Number Sectors, and a General Calculus of Gamma-Dominant Transseries* | 1,878 lines; 81,203 bytes | 35 Letter pages; 530,302 bytes |

### A real-argument Fibonacci function

The fourth subject differs from the first three in its core: the map inverted
is a real continuation of the Fibonacci numbers, so the dominant phase is a pure
exponential in the golden ratio and the inverse transseries is *log-periodic*
(oscillatory in `log` of the argument) rather than Lambert-cored.  Filed here
because the purpose is the same, inverting a rapidly growing special function
at infinity to all orders with an extracted general reversion calculus; the
titles are transcribed, not assessed.

| Directory | Document | Source | PDF |
| --- | --- | --- | --- |
| `Fibonacci_Inverse_LogPeriodic_Transseries/` | *Inverting a Real-Argument Fibonacci Function: Log-Periodic Transseries, Exact Coefficients, and a General Product-Reversion Calculus* | 2,554 lines; 89,365 bytes | 33 A4 pages; 787,646 bytes |
| `fibonacci_inverse_transseries_article/` | *Log-Periodic Transseries for the Inverse of a Real Fibonacci Continuation* | 2,857 lines; 98,788 bytes | 36 A4 pages; 797,090 bytes |
| `fibonacci_inverse_transseries_article-2/` | *Inverse Asymptotics for a Real-Argument Fibonacci Function* | 1,884 lines; 64,334 bytes | 24 A4 pages; 759,845 bytes |

## Intake receipts

Every archive passed a CRC check and carried no absolute path, no
parent-directory traversal, and no symlink entry.  Each contained exactly one
`.tex` and one `.pdf` at top level with no wrapping directory, so each
destination directory was created at filing.  No checksum ledger was submitted
and none was added.

All nine sources are LF with a final newline, so no line-ending normalization
was applied and the filed bytes are exactly the submitted bytes.  Where an
archive's inner filenames differ from its directory name — as in
`inverse_subfactorial_transseries-2/` and `-3/`, whose inner files are both
plain `inverse_subfactorial_transseries.*` — the submitted names were kept
verbatim, following the precedent of
[`../lambert-inverse-transseries/lambert_inverse_transseries_bundle/`](../lambert-inverse-transseries/lambert_inverse_transseries_bundle/).

All nine PDFs are readable and unencrypted, produced by pdfTeX-1.40.26, with
every font row embedded and no Type 3 font.  Eight are A4, which is canonical;
`inverse_subfactorial_transseries-3/` is Letter.  Five carry Libertinus faces
and four do not (`inverse_k_function_transseries/`,
`inverse_gamma_barnes_transseries/`, `inverse_subfactorial_transseries-3/`,
and, on the page-size axis as well, the same Letter package).  Those are the
batch's only styling debts.

None of the nine loads the shared notation file `docs/fabius-notation.tex`;
each uses document-local notation, so all nine are outside the corpus notation
migration and free of its defect classes.

**One directory was renamed at filing.**  The archive
`K_Function_Inverse_Transseries_LaTeX_and_PDF.zip` would have produced a full
path of 263 characters for its PDF, past the Windows `MAX_PATH` limit of 260,
and tools then fail with a misleading *"No such file or directory"* for a file
that plainly exists — `pdfinfo` did exactly that here.  The directory is
therefore named `K_Function_Inverse_Transseries/`, after the document, which is
also the convention the rest of the corpus follows.  Its contents are
unchanged.  The remaining paths run 249–259 characters; the longest,
`Asymptotic_Inversion_Gamma_Barnes_G/`, sits one character inside the limit, so
this subgroup has no headroom for deeper nesting or longer names.

## Deferred

Nothing beyond title, abstract, and package metadata was read at intake.  Claim
comparison against the corpus, comparison *among* the three articles in each
subject, deduplication against
[`../lambert-inverse-transseries/`](../lambert-inverse-transseries/) and
[`../../lambert-w/`](../../lambert-w/), proof checking, numerical reproduction,
canonical selection, editorial consolidation, styling repair, and Lean
crosswalking are all deferred.  Nothing here has been merged, rewritten, or
verified.

One connection worth recording for that later phase, and *not* acted on: the
corpus already carries a Lambert-`W` layer of its own — analyticity of both
real branches, the lower-branch bracket with its explicit remainder rate, and
the Fabius saddle expansions — so the "Lambert core" these articles build on is
formalized here to a degree they do not assume.  Whether any of their reversion
machinery is already available in that layer is unexamined.

See [`../../MANIFEST.md`](../../MANIFEST.md) for the group record.
