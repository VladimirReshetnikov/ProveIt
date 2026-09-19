# Coarse Degrees with Unattained Turing Infima

Research note prepared for Vladimir Reshetnikov, 18 September 2026.

## Main mathematical content

The paper attacks C1 of the supplied Turing-degree survey, the coarse instance
of Gerdes's Question 7 about least Turing representatives.

It gives an explicit computably enumerable binary set A with no computable
coarse description and a perfect family of coarse descriptions of A whose
distinct members form ordinary Turing minimal pairs. Two members can be
chosen below the second jump of the empty set. Hence neither the uniform nor
the nonuniform coarse class of A has a least Turing representative, even when
arbitrary total numerical functions are allowed as representatives.

A relative construction gives, for every degree z, a coarse class whose
representative spectrum has greatest lower bound z but does not contain z.
The paper also characterizes the nonuniform coarse classes with a least
representative as exactly the classes obtained by robust coding of a real.

## Status and provenance

The bare negative answer already follows from Hirschfeldt–Jockusch–Kuyper–Schupp,
*Coarse Reducibility and Algorithmic Randomness*, Theorem 4.2 (2015 preprint;
2016 journal publication). It is not claimed as a new discovery here.
Gerdes's 2025 paper and July 2026 slides explicitly display the question.

The perfect-family construction and prescribed-infimum extension are fully
proved in conventional mathematics in this note. Their originality has not
been established. No independent referee review or Lean verification is claimed.
The finite scripts do not prove the infinite computability-theoretic results.

## Files

- `coarse_degrees.pdf`: compiled research paper.
- `coarse_degrees.tex`: self-contained LaTeX source with bibliography.
- `checks/enumerate_witness.py`: a concrete register-machine enumeration and
  finite c.e. approximations to the diagonal witness.
- `checks/check_finite.py`: deterministic finite tests, standard library only.
- `checks/results.json`: actual test results from Python 3.13.5.
- `checks/witness_stage_1024.json`: sample approximation A_1024.
- `notes/proof_audit.md`: theorem dependencies, quantifiers, and limitations.
- `notes/source_audit.md`: primary-source checks and novelty boundary.
- `notes/verification.json`: document-build and finite-check verification record.
- `SHA256SUMS.txt`: SHA-256 hashes of the other packaged files.

## Build the PDF

A standard TeX Live installation with pdfLaTeX, Latin Modern, and the packages
listed in the preamble is sufficient. No custom fonts are required or included.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error coarse_degrees.tex
```

Alternatively run pdfLaTeX three times to resolve the contents and references:

```sh
pdflatex -interaction=nonstopmode -halt-on-error coarse_degrees.tex
pdflatex -interaction=nonstopmode -halt-on-error coarse_degrees.tex
pdflatex -interaction=nonstopmode -halt-on-error coarse_degrees.tex
```

## Run the finite artifacts

Python 3.9 or later; no third-party packages required. Run from this directory:

```sh
python checks/check_finite.py --output checks/results.json
python checks/enumerate_witness.py --stage 1024 --output checks/witness_stage_1024.json
```

The checks use explicit exceptions, so `python -O` does not disable validation.
All output is deterministic apart from the recorded Python version.

## Interpreting the enumeration

The finite approximation lists positive membership witnesses only. An
unlisted position is not a certified zero of the final set. A program that
has not halted within the step budget is **unknown**, not proved divergent.

In the chosen enumeration, the first program is the constant-zero function.
Consequently every even position belongs to A. At stage 1024 the observed
ones are precisely the 512 even positions. This simple prefix is not evidence
of coarse computability: diagonal requirements for other program indices lie
in other positive-density columns and are not decided by this finite run.

The perfect-family level construction uses the second jump to choose indices
and decide finite-extension existence questions. The enumeration script does
not purport to implement that oracle or evaluate the resulting infinite
minimal-pair witnesses without it.
