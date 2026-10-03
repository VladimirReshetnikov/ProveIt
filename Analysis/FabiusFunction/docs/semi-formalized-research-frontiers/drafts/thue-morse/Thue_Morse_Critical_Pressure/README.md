# Critical Cusps in Digital-Product Pressure

**A Jordan collision, square-root phase scaling, and explicit subcritical response**

Research draft prepared with ChatGPT for Vladimir Reshetnikov, 29 September 2026.

## Main results

For the unnormalized digital-mask pressure in every integer base `b >= 2`:

- At the critical absolute-moment exponent `s = 1`,
  `P_{b,1}(c) = sqrt(2(b-1) log b) sqrt(|c|) + O(|c|^(1-eta))`
  for every fixed `0 < eta < 1/2`.
- The critical atomic transfer operator has an explicit size-two Jordan block,
  with an exponentially decaying complement on every `C^alpha`, `0 < alpha < 1`.
- A uniform detuned crossover holds for `s = 1 + u sqrt(|c|)`, including an
  operator-norm finite-size law on the scale `n sqrt(|c|)`.
- For every fixed `1/2 < s < 1`,
  `P_{b,s}(c) = (1-s) log b + (b-1) pi s tan(pi s/2) |c| + o(|c|)`.

In the binary convention `psi_c(x) = log cos^2(pi(x-c))`, the pressure order
is `q = s/2`. Thus the critical theorem is at `q = 1/2`, and the subcritical
theorem covers `1/4 < q < 1/2`.

The paper includes ten proposed research directions and a proof-dependency audit.

## Status

The article supplies ordinary mathematical proofs. It is **not independently
refereed or Lean/Rocq verified**. The numerical results are diagnostics, not
rigorous enclosures of infinite-dimensional spectra. Literature novelty has
not been independently established. The interval `0 < s <= 1/2` is explicitly
left unresolved rather than extrapolated from an insufficient remainder bound.

The target extends the repository's *Fractional Cusps at the Atomic Phase*,
which treats `s > 1` and excludes critical and subcritical phase asymptotics.
No unverified repository theorem is assumed in the proofs of the new results.
See `SOURCES.md` and `CLAIMS_AND_VALIDATION.md` for exact scope and provenance.

## Files

- `article.pdf`: compiled article (22 pages as delivered; 23 since the
  editorial notes of batch 57).
- `article.tex`: complete source, with embedded bibliography.
- `code/verify.py`: high-precision identities, symbolic matrix check, collocation,
  mesh comparisons, and finite-size diagnostics.
- `data/verification.json`: actual output, including library versions and residuals.
- `data/run.log`: console output from the full diagnostic run.
- `data/*_table.tex`: generated numerical tables used in the article.
- `requirements.txt`: numerical package dependencies.
- `Makefile`: rebuild and verification targets.
- `SOURCES.md`, `CLAIMS_AND_VALIDATION.md`: source and claim audits.
- `SHA256SUMS`: checksums of the distributed files (except the checksum file itself).

## Rebuild

With a TeX installation containing the packages listed in the preamble:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

No BibTeX step is needed. Keep the two table files in `data/` alongside the source.
The compiled PDF can be read without installing any tools.

For the full numerical checks:

```sh
python -m pip install -r requirements.txt
OPENBLAS_NUM_THREADS=1 python code/verify.py --full
```

The environment-variable syntax above is for POSIX shells. On Windows, set it
using the shell's syntax or omit it. The code works from any current directory;
outputs are placed relative to its own file. Omitting `--full` runs a smaller
set and regenerates smaller tables. The included data are from a full run.

Collocation runs use up to 262,144 grid points and require substantially more
memory than the high-precision identity checks. No internet access is needed
after the packages and TeX dependencies are installed.

## Editorial amendments (ProveIt, 2026-09-29)

In the editorial pass after batch 54 of the repository-level `docs/incoming/`
drop zone (see `docs/incoming/README.md`), a later package of this tree was
found to take up its first research question. The article gains reciprocal notes; its
mathematical text is unchanged.

- `article.tex`: an unnumbered environment `ednote` ("Editorial note
  (ProveIt, 2026-09-29)") is defined after the last theorem style.
- `article.tex`: after the research question "The remaining subcritical
  interval", a note records that `../Thue_Morse_Subcritical_Pressure/`
  (filed 2026-09-29, unreviewed) answers it at the atomic phase:
  `eq:subcritical` holds for every `0 < s < 1`, with remainder
  `O(|c|^(1+s-alpha))` for every `0 < alpha < s`; nonzero phases remain
  open. The Status sentence above ("The interval `0 < s <= 1/2` is
  explicitly left unresolved") remains true of this article.
- `article.tex`: the title page no longer sets a hyperref page anchor
  (`\hypersetup{pageanchor=false}` around it), because the build reported a
  duplicate destination `page.1`. Both changes are marked `% ed.`.
- `article.pdf`: rebuilt with `latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex` (MiKTeX pdfTeX): 22 pages, as before, 779,453
  bytes; no error, undefined reference, rerun request, duplicate
  destination or overfull box; no Type 3 font.
- `SHA256SUMS`, listed under Files, was retired when the package was filed
  (batch 44 of `docs/incoming/`). Runs of `code/verify.py` without `--full`
  (including `make quick`) still regenerate the two table files in `data/`
  in place with smaller meshes, so run them only on a copy.

In the editorial pass after batch 57, a later package of this tree was found
to take up two more of its research questions.

- `article.tex`: after "The next critical term", a note records that
  `../Thue_Morse_Critical_Pressure_Corrections/` (filed 2026-09-29,
  unreviewed) answers it: both corrections occur, and
  `P_(b,1)(c) = kappa_b sqrt|c| - (b-1)|c| log(1/|c|)
  + [b log b + (b-1)(gamma-1)]|c| + O(|c|^(3/2-eta))` for every
  `0 < eta < 1/2`. After "Eigenfunctions, eigenmeasures, and equilibrium
  measures", a note records that the same package gives the first normalized
  eigenvector corrections, a right boundary layer on the scale `sqrt|c|` and
  the weak limits of the equilibrium measures (`(1/2) delta_0 + (1/2)`
  Lebesgue at `s = 1`, an explicit mixture along `s = 1 + u sqrt|c|`,
  `u` bounded); the left boundary layer remains open. Both notes are marked
  `% ed.`. Conversely, that package's amplitude corollary repeats this
  article's `eq:critical-amplitudes`, as a note there says.
- `article.pdf`: rebuilt with `latexmk -pdf -interaction=nonstopmode
  -halt-on-error article.tex` (MiKTeX 26.2 pdfTeX 1.40.29): 23 pages (22 before; the notes add
  one), 782,505 bytes; no error, undefined reference, duplicate
  destination or overfull box; no Type 3 font; the pages carrying the notes
  were rendered and inspected.

## Editorial amendments (ProveIt, 2026-09-30)

In the editorial pass after batches 66 to 68 of `docs/incoming/` (see
`docs/incoming/README.md`), a later package of this tree was found to bear on
one of its research questions.

- `article.tex`: a second unnumbered environment `ednotelater` ("Editorial
  note (ProveIt, 2026-09-30)") is defined after `ednote`. After the research
  question "Nonatomic phases", a note records that
  `../Periodic_Anchors_Exact_Mixed_Moment_Phase_Diagrams/` (batch 68, unreviewed) computes exactly the pressure of products of shifted digital
  masks whose phases fill complete periodic orbits of `x -> bx mod 1`, with
  a common exponent on each orbit, with every equilibrium measure, in every
  base; it bears on the question without answering it (fixed phases; a
  single mask whose phase has period at least two is not covered; no
  phase regularity). Both changes are marked `% ed. (2026-09-30)`.
- `article.pdf`: rebuilt the same way: 23 pages, as before, with no error,
  undefined reference, duplicate destination or overfull box; no Type 3
  font; the page carrying the note was rendered and inspected.
