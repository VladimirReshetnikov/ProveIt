# Exact eventual maximizers of Rudin–Shapiro autocorrelations

**Proposed computer-assisted solution; 20 September 2026.**

The article addresses the discrete uniqueness-and-location conjecture in
Daniel Tarnu's 2023 paper, repeated as Conjecture 1.5 of Choi–Tarnu (2025).
The random area draw selected **Harmonic analysis, 45 of 100**. None of the
71 entries in the supplied exclusion manifest is this problem.

## Result

Let r_j = (-1)^(number of overlapping 11s in the binary expansion of j),
C_m(k) = sum_{j=0}^{2^m-1-k} r_j r_{j+k}, and A_m = max_{0<k<2^m}|C_m(k)|.

For every m >= 3 there is exactly one positive maximizing shift. For every
m >= 40 it is (2^(m+1) + (-1)^m)/3. The onset 40 is sharp: m=39 is an
exception. The elementary tie at m=2 is explicitly excluded.

With b_0=1, b_1=1, b_2=5 and b_n=-b_(n-1)+2b_(n-2)+4b_(n-3), one has
A_m=b_(m-2) for m>=40. The article includes the complete finite exception
table, the rational generating function, the exact limiting peak constant,
and the periodic-autocorrelation consequences.

## Read and build

`article.pdf` is the typeset article; `article.tex` is the complete LaTeX source.
Keep the `data/` and `figures/` folders beside the source when rebuilding.
From the archive root:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

`build.sh` runs these commands. Standard LaTeX packages listed in the source
are needed; **BibTeX is not required**. `references.bib` is supplied as reusable
bibliographic metadata; the source contains its own bibliography.

## Verify without third-party Python packages

Python 3.9 or later, standard library only:

```sh
python code/verify.py --output data/verification_summary.json
python code/test_verifier.py
python code/verify_consequences.py
python code/rs_maximum.py 40
python code/rs_maximum.py 39 --shift 366503875925
```

The verifier reconstructs the finite hulls and unique maximizing words for
m=3,...,402, then checks the moving-polytope certificate for an induction
covering all subsequent levels. It replays the recorded random area draw,
checks direct defining sums through m=10, and compares all computed finite
maxima against the recorded data. The six test methods supply additional
independent small-instance and algebraic checks.

The supplementary `verify_consequences.py` checks the generating function
through level 500, the mirrored template matrices, the stored full-array scan,
and 1,009 periodic defining sums. These checks supplement the induction.

The proof uses exact Python integers and `fractions.Fraction`, **not**
floating-point hull or eigenvalue routines. It is still an unrefereed
mathematical proof and executable certificate, not a proof-assistant
formalization. See `STATUS.md` and `notes/proof_audit.md`.

## Evaluator

`code/rs_maximum.py` exports `autocorrelation(m,k)` and `maximum(m)`.
The latter returns every positive maximizing shift (two at m=2, one otherwise).
For m>=40 the peak value is evaluated by O(log m) integer matrix products.
This arithmetic-operation bound does not suppress the cost of large integers.
Arbitrary-shift correlations use O(m) address steps. The CLI prints exact JSON.

## Regenerate discovery artifacts

Discovery is optional. It requires NumPy, SciPy and SymPy; figure regeneration
also requires matplotlib. Recorded development versions are in
`requirements-discovery.txt`. In a copy of this directory, run:

```sh
python code/discover_templates.py
python code/discover_parametric.py
python code/discover_box.py
python code/discover_finite.py
python code/verify.py
```

Floating-point routines only propose certificates; verification is separate.
Different library versions may choose different valid hull triangulations,
so certificate bytes need not match. The mathematical assertions must still
pass the exact checker. The chosen 13 template words are stored explicitly;
these scripts reconstruct and certify that choice, rather than claiming to
rediscover it by an automatic search.

For the full-array exploratory check (memory grows exponentially):

```sh
python code/explore_full_arrays.py --max-level 20
python code/explore_full_arrays.py --max-level 26 --output data/direct_scan.json
python code/generate_figures.py
```

The stored all-array exploration reaches level 26; it is corroboration, not
the infinite proof. Most users only need the dependency-free verifier.

The original random draw is replayed by `verify.py`. `select_area.py` is a
separate utility for a **new** experiment and refuses to overwrite its output.
Do not redraw when reproducing this experiment. Its explicit CLI is
`python code/select_area.py --manifest PATH --output NEW_JSON_PATH`.

## Contents and provenance

`data/finite_certificate.json` and `data/polytope_certificate.json` contain
proof-bearing witnesses. `data/certified_maxima.json` contains exact results
through level 402. `data/generating_function.json` contains all coefficients
of the reduced numerator. `data/verification_log.txt`, `verification_summary.json`
and `test_log.txt` record successful executions.

`notes/sources.md` gives primary references and the dated search audit.
`notes/selection_exclusion.md` records the manifest hash and area-selection method.
No third-party paper or font file is bundled. Original text, code and generated certificate data are released
under MIT-0; external mathematical results retain the cited attribution.
