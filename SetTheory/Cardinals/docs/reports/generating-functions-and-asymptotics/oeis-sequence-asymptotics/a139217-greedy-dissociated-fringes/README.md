# Finite-fringe rigidity for OEIS A139217 and A139218

This package contains an AI-assisted ProveIt research report dated 1 October 2026.

## Files

- `finite_fringe_dissociated_sequences.tex` — LaTeX source.
- `finite_fringe_dissociated_sequences.pdf` — compiled 20-page article.
- `verify.py` — exact bitset verifier; uses only the Python standard library.
- `oeis_update_draft.txt` — proposed entry updates, not submitted.

## Main results

The report proves that the signed subset-sum sets for the two greedy sequences are complete integer intervals with permanent finite fringes:

- A139217: the only positive missing signed value is `S_n - 3` for every `n >= 3`.
- A139218: the positive missing signed values are `S_n - h`, where `h` is in `{1,3,6,11}`, for every `n >= 3`.

This proves the conjectured period-three near-doubling laws, closed forms, rational generating functions, asymptotic and inverse transseries, and the common recurrence. It also corrects the current A139217 recurrence range: the recurrence starts at `n = 6`, not at every `n > 4`.

## Reproduce the checks

```sh
python verify.py
```

The script generates 22 terms directly from the greedy rule, checks the published prefixes, verifies every missing ternary-support exponent through that range, checks the closed forms and recurrences, and expands both rational generating functions through degree 30.

## Build the PDF

A standard TeX Live installation with `latexmk` is sufficient:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error finite_fringe_dissociated_sequences.tex
```

The manuscript is unrefereed and not formally verified in Lean. Independent mathematical review is recommended before an OEIS submission or a priority claim.
