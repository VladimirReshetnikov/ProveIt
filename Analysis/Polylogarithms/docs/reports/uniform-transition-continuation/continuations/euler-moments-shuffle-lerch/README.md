# Sharp Euler Bounds and Uniform Asymptotics in Polylogarithmic Analysis

Research continuation for the ProveIt project, 10 October 2026.

**Start with `article.pdf`.** The complete TeX source is `article.tex`;
editable modular sources are in `sections/`. This package is prepared
against ProveIt commit `3447bc59b78d138a7f0d536b66ac6e5cc5d5e49f`.

## Main results and their status

1. **Proved:** the optimal Euler remainder constant uniform in every
   positive real order and every Euler index is
   `C* = max_{b>0} (beta(b) + 2^(-b) eta(b))`.
   The new scalar kernel inequality proves the missing domination.
   The unique-axis-maximum theorem is inherited and explicitly credited.
   Exact rational certificates enclose the maximizer and constant and
   prove the convenient bound `C* < 57/50`.
2. **Proved, using the inherited certified gamma-slope theorem:** an
   all-orders reflected log-gamma moment expansion, uniformly for
   `0 <= m <= n` as `n -> infinity`, including the axis `m = 0`.
   Reflection covers every nonnegative exponent ratio. This is an
   algebraic relative-error theorem, not an exponentially accurate
   replacement for the fixed-order residue expansions.
3. **Proved:** explicit all-index Lerch zero saturation and simultaneous
   logarithmic root-location bounds, uniform over `rho in [0,1]`.
   The growing-index range `n <= alpha log(k)/loglog(k)`, `alpha < 1/2`,
   follows. The sufficient thresholds are conservative, not sharp.
   Every simple terminal branch moves strictly left wherever it persists.
4. **Proved:** explicit integral diagonalization of the odd-weight
   shuffle minor to `diag(1,3,...,2m-1)`. This determines its cokernel,
   Smith factors, field ranks and optimal inverse denominator.
   The formal quotient is specified; numerical period independence is
   not asserted. The relation to Zagier's matrix and published work by
   Ding Ma and by Yawen Ma–Lee-Peng Teo is credited.
5. **Proved:** a short weight-eleven functional shuffle identity and its
   exact Gaussian specialization. Its four-row certificate is included.
6. **Conjectural equalities:** new retained S10 and S12 Gaussian identities.
   For each, a standard-library rational computation proves the normalized
   residual lies in `(-10^-650,10^-650)`; both intervals contain zero.
   These are proximity proofs, not equality proofs. The first, discarded
   S12 vector is rigorously rejected by a nonzero residual interval.

**The existing S6 conjecture remains unresolved.** The research advances
its coordinate structure but does not provide the missing mixed-color
reduction certificate. The article includes a detailed future programme.

## Package contents

| Item | Purpose |
|---|---|
| `article.pdf` | Complete research article with proofs, figures and references |
| `article.tex` | Complete, directly compilable TeX source |
| `preamble.tex`, `sections/`, `references.tex` | Modular editable source |
| `figures/` | Three publication figures, each in PDF and PNG form |
| `code/euler/` | Exact Euler kernel and constant verifiers and certificates |
| `code/moments/` | Moment diagnostics and unchanged inherited slope verifier |
| `code/lerch/` | Exact rational polynomial/Sturm checks and thresholds |
| `code/shuffle/` | Exact SymPy construction, Smith forms and row certificate |
| `code/gaussian/` | Frozen vectors, exact interval proof, independent audit and search history |
| `data/` | Moment diagnostics, replay manifest, environment and PDF validation |
| `integration/` | Insertion map, proposed wording and inherited source attribution |
| `provenance.json` | Pinned source paths and hashes, literature and dependency map |
| `CLAIMS.json` | Machine-readable classification of the principal claims |
| `MANIFEST.sha256` | Hashes of every release file except the manifest itself |

## Build the article

The bundled complete source and PDF figure assets can be compiled directly:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

After editing modular sections, rebuild the complete source and PDF:

```bash
python3 code/build_article.py --compile
```

This needs a standard LaTeX installation with the packages named in the
preamble. Python is not needed when compiling the complete TeX source
directly. No bibliography database or external image download is needed.

## Replay the certificates

Use Python 3.11 or later, with assertions enabled (do not use `python -O`).
Install the optional scientific packages from `requirements.txt` if they
are absent. Only the finite matrix audit needs SymPy; all proof-relevant
interval certificates use the Python standard library.

```bash
python3 code/verify_all.py
```

This performs seven exact/finite replay tasks, including the inherited
gamma-slope certificate and both Gaussian candidates. It runs without
network access or the source checkout. The command rewrites the generated
certificate JSON files and `data/replay_manifest.json`. Elapsed-time
metadata naturally changes on a new replay.

Optional numerical diagnostics and figure regeneration:

```bash
python3 code/verify_all.py --numerical
python3 code/gaussian/audit_s10.py 120
python3 code/make_figures.py
```

The saved 24 moment cases use 60 working decimal digits. The independent
Mellin audit uses 120 digits. Neither is a rigorous quadrature certificate;
their role is to catch normalization and implementation mistakes. The
all-ratio theorem is proved in the article, and the Gaussian proximity
claims use the separate exact rational verifier.

For exploratory search details, see
`code/gaussian/gaussian_reproduction_README.txt`. In particular,
`gaussian_candidates.json` is the canonical candidate input. The historical
`s12_search.json` intentionally preserves the rejected first vector and
must not be used as the final candidate source.

## Integration and provenance

Read `integration/INTEGRATION.md` before merging section fragments. The
source revision's open universal Euler question is now settled, while its
constant-one counterexample remains correct. Earlier compact-ratio
moment theorems and sharp low-index Lerch results retain their own scope.
The source's existing S4 proof is not presented as new work.

`integration/inherited_global_slope.tex` and
`code/moments/certify_gamma_saddle.py` reproduce an inherited dependency
unchanged, with original-source hashes in `provenance.json`. They are
credited to the pinned ProveIt report. This package is mathematical prose
and executable exact arithmetic; no proof-assistant formalization or
exhaustive literature-priority claim is made.
