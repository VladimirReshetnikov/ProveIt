# OEIS A225114: a complete proof and reproducible elaboration

**Article:** *Skew partitions, continued fractions, and connected components*  
**Date:** 20 September 2026  
**Result:** The generating function recorded as conjectural in OEIS A225114 is correct.

## Historical status and scope

A225114 counts skew partition diagrams with no empty rows or columns, including
one empty diagram. Its OEIS entry attributes the repeated-power continued-fraction
conjecture to Mikhail Kurkov (3 September 2024).

After the recorded random selection, a prior-art check found Dima Pasechnik's
MathOverflow proof sketch from 10 September 2024. The connected-diagram continued
fraction and q-series identities are older. This package therefore provides a
complete self-contained proof and elaboration, **not a claim to the first solution
of a previously unresolved problem**. The article credits these sources and does
not claim novelty for all its refinements or consequences.

The arguments are conventional mathematical proofs, not proof-assistant-checked
formalizations. Finite computations are independent checks, not the proof. There
has been no external refereeing or submission to OEIS as part of this work.

## Main mathematics

Writing P(q) for the generating function of nonempty edge-connected diagrams,
unique concatenation gives A(q) = 1/(1-P(q)). Boundary-path encoding, followed by a
weighted two-colored Motzkin-path decomposition, gives

    P(q) = q / (1 - 2q - q^3/(1 - 2q^2 - q^5/(1 - 2q^3 - ...))).

Elementary contraction gives C(q) = 1+P(q), where C has partial numerators
q,q,q^2,q^2,q^3,q^3,..., establishing the selected identity A(q)=1/(2-C(q)).

The article also proves a four-variable refinement, the formula by height, width,
and component count, a q-series ratio, a sharp truncation bound, exponential
asymptotics, and a central limit theorem for the number of components.

## Archive contents

| File | Contents |
|---|---|
| `article.tex` | Complete editable LaTeX source, with bibliography |
| `article.pdf` | Compiled 22-page article |
| `verify.py` | Exact independent checks; Python standard library only |
| `asymptotics.py` | Optional high-precision numerical illustrations |
| `requirements.txt` | Optional numerical dependency, mpmath 1.3.0 |
| `candidates.json` | The four candidates frozen before the random draw |
| `selection.json` | Seed, selected index, candidate digest, and draw count |
| `select_candidate.py` | The selection procedure; refuses to overwrite a draw |
| `verification_results.json` | Successful exact-check report |
| `coefficients.csv` | Both area sequences for n=0,...,1000 |
| `components.csv` | Nonzero area/component counts through area 13 |
| `numerical_results.json` | Numerical estimates of the asymptotic constants |
| `asymptotic_checks.csv` | Asymptotic and component-moment diagnostics |
| `SOURCES.md` | Source URLs and their role in the article |

The original source materials are linked, not redistributed in the archive.

## Compile the article

Use a standard TeX Live or MiKTeX installation with the packages named in the
preamble. No external figures or bibliography processor are needed.

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

A third pass may be needed if pagination or references change during editing.
Alternatively:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

## Run the exact checks

Python 3.10 or later is required. From the extracted folder:

```sh
python3 verify.py --limit 1000
```

On Windows, `py -3 verify.py --limit 1000` is an equivalent invocation when the
Python launcher is installed. Do not use Python's `-O` option: the verification
suite deliberately relies on assertions and refuses optimized execution.

This command replays (but does not redraw) the random selection, checks the
published initial terms, compares independent enumeration algorithms through
n=1000, checks additional refinements in the ranges recorded in the output, and
verifies a strict root interval using exact rational arithmetic. It regenerates
`verification_results.json`, `coefficients.csv`, and `components.csv`. The elapsed
time field naturally varies between machines and runs.

The supplied result is `ALL EXACT CHECKS PASSED`. The four-variable checks are at
27 integer specializations through area 20; they are not full symbolic tests
through area 1000. The boundary-pair checks cover area at most 10. See the exact
report for every scope limit.

## Reproduce the optional numerical results

```sh
python3 -m pip install -r requirements.txt
python3 asymptotics.py
```

This regenerates the numerical JSON and asymptotic CSV. The script uses the exact
continuant routine to compute its own coefficient arrays through n=1000, so it
does not require reading the CSV produced by `verify.py`.

The approximate constants are

    rho   = 0.3195967180593874655186028919827139236...
    1/rho = 3.128943269730886252277447995387754161...
    kappa = 0.2893214639716513230848453480726559061...

with a_n = kappa*rho^(-n) + O(R^(-n)) for some R>rho.

**Certification boundary:** The strict interval

    0.31959671805938746551 < rho < 0.31959671805938746552

is verified by exact rational inequalities and a proved transfer-kernel error
bound. Further displayed decimals, the prefactor, and the component variance
constant are high-precision numerical estimates, not individually certified
intervals. Comparing two continued-fraction depths is only a stability check.

## Random selection record

The frozen ordered candidate list is

    0: A225114
    1: A244475
    2: A381190
    3: A391632

The 128-bit seed came from `secrets.randbits(128)`:

    203225573310603175027560032786773102290

The single call `random.Random(seed).randrange(4)` returned index 0. There was no
reroll. The exact candidate-file SHA-256 digest is recorded in `selection.json`.
Keep the original JSON files unchanged to preserve the audit check. Running
`select_candidate.py` in the supplied directory intentionally refuses to create
another selection; `verify.py` is the correct way to replay the recorded draw.
