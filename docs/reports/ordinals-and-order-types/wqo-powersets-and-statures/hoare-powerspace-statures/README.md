# Sharp ordinal bounds for Hoare powerspaces

Research manuscript prepared for Vladimir Reshetnikov, 19 September 2026.

## Results and limits

The manuscript supplies proposed proofs of:

* the sharp bound `1 + ||X|| <= ||H X|| <= 2^(||X||)` for all Noetherian spaces;
* witnesses attaining both endpoints at every ordinal, with T1 upper witnesses;
* the criterion that the older `omega^alpha` bound is attainable at infinite
  input stature alpha exactly when `omega * alpha = alpha`;
* the complete spectrum at `omega+n`:
  `omega * j(U) + (j(Q)-j(U))`, for an n-point poset Q and a downset U of Q.

All arithmetic in those statements is ordinal except the finite downset
counts. In particular, `2^omega = omega`. H includes the empty closed set
and uses the lower Vietoris topology.

The binary upper bound and all-ordinal sharpness are already known in the
well-quasi-order setting (Abriola et al., Theorems 3.3 and 4.3). The work here
extends the proof to arbitrary Noetherian spaces, gives T1 witnesses, and
classifies the finite tails of omega. Priority is not established. The proofs
are not independently refereed or proof-assistant checked. General spectra
beyond `omega+n` are not classified. See the article and audit notes.

## Files

| File | Contents |
|---|---|
| `article.pdf` | Typeset article with full English proofs |
| `article.tex` | Complete LaTeX source, including bibliography |
| `references.bib` | Reusable bibliographic records |
| `verify_spectra.py` | Python 3.9+ exhaustive finite enumeration |
| `verification_results.json` | Run configuration and counts |
| `spectra.csv` | All distinct pairs `(omega_coefficient, finite_tail)` through n=6 |
| `witnesses.json` | One finite poset/downset witness per spectrum value |
| `proof_audit.md` | Proof dependencies and delicate points |
| `literature_notes.md` | Exact source locations and novelty-search limits |
| `Makefile` | Optional build and verification commands |
| `SHA256SUMS.txt` | Hashes of the distributed files, excluding the manifest itself |

## Reproduce the computations

From this directory:

```sh
python verify_spectra.py
```

No third-party Python packages are needed. On Windows the command may be
`py -3 verify_spectra.py`. The default calculation is small. The optional
`--max-n 7` is substantially more expensive because 2^21 candidate relations
are tested. The guard intentionally rejects n>7.

The enumeration considers all transitive subrelations of the natural order
on labels `0,...,n-1`. Every finite poset has a linear extension, so every
isomorphism type is covered, but repetitions occur. Do not interpret the
relation counts as unlabeled-poset counts or all-labeled-poset counts.

The number of distinct spectrum values for n=0,...,6 is:

```
1, 2, 6, 18, 53, 154, 431
```

The default run also verifies 1,221 finite identities by independently
building a finite-core poset and enumerating its downsets. These are finite
checks of the realizing construction, not a proof of the transfinite rank
formula. The proofs of the ordinal assertions are in the article.

### Data format

A row with `n=2, omega_coefficient=2, finite_tail=1` denotes
`omega*2+1` in the spectrum at input `omega+2`.

Each witness contains:

* `strict_order_pairs`: the entire strict relation, not just Hasse edges;
* `U`: the distinguished downset, as a list of labels;
* `j_Q`, `j_U`: downset counts including the empty downset;
* `omega_coefficient` and `finite_tail`: the corresponding ordinal normal form.

## Build the PDF

A TeX Live installation with newtx, amsthm, aliascnt, tcolorbox, and the
other standard packages named in the preamble is sufficient:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively run `pdflatex` twice (a third pass may be needed after changes
to page numbers). The bibliography is embedded, so BibTeX is not needed.
No external image or font files are required. Font files and third-party
research PDFs are not distributed.
