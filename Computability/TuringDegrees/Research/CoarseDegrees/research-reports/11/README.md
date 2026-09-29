# Finite Realization of Coarse-Information Profiles

**28-page research article, 28 September 2026**  
Prepared for Vladimir Reshetnikov with ChatGPT.

## Main statement

For finitely many participants, every monotone assignment of countable Turing
ideals to coalitions, with the computable ideal assigned to the empty coalition,
is realized as the coarse-information cores of their periodic oracle joins.
All nonempty coalition classes can simultaneously have no least Turing-degree
representative. Given a presentation P of the ideals, the full join H can satisfy

    P <_T H <_T P'     and     H' =_T P'.

The equality is of Turing degrees, not literal sets. Each nonempty coalition C
also satisfies (P + X_C)' =_T P', where + here denotes oracle join.

A direct two-share version gives individually 1-generic X and Y with computable
cores but an arbitrarily prescribed countable ideal as Core(X + Y). A separate
access-structure construction makes every unauthorized nonempty view itself
1-generic relative to the secret presentation. The article also proves a
necessary union-closure condition on coalitions with least representatives.

## Status and provenance

The paper supplies conventional proofs. The main finite-profile theorem and its
combined refinements are proposed research contributions. Their priority has not
been established; they have not been independently refereed or checked in Lean
or Rocq. Two non-elementary inputs are the published cone-avoiding compactness
and generic-core theorems of Hirschfeldt, Jockusch, Kuyper, and Schupp.

The single-ideal column construction was already sketched in target C4 of the
ProveIt research plan and uses an architecture already appearing in the density-
metric literature. Its proof is verified and expanded here, not presented as a
new discovery. No new solution to the retired C1 is claimed. The question about
minimal (as opposed to least) elements of representative spectra is not settled.
The secret-sharing terminology is mathematical, not a claim of practical
cryptographic security.

Repository snapshot inspected:

    1a1396d4d3a2ac6812692df520517d86ba3a4785

## Files

- `article.tex`: complete standalone LaTeX source, with embedded bibliography.
- `article.pdf`: compiled 28-page article.
- `build.sh`: three-pass PDF build.
- `checks/verify_finite.py`: standard-library finite algebra/counting checks.
- `checks/results.json`: results of the executed verification program.
- `PROOF_AUDIT.md`: dependency and quantifier audit.
- `SOURCES.md`: exact repository and literature sources, with scope of review.
- `validation.json`: document checks and their limits.
- `CHECKSUMS.sha256`: hashes of the delivered files (other than the checksum file).

## Build

A TeX Live installation with pdfLaTeX, New PX text/math, AMS, geometry, microtype,
booktabs, tabularx, longtable, enumitem, xcolor, titlesec, fancyhdr, xurl, and hyperref
is sufficient. No bibliography processor or external images are needed.

```sh
sh build.sh
```

On Windows, run the following command three times in the package directory:

```text
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

## Re-run finite checks

Requires Python 3.10 or later, standard library only:

```sh
python3 checks/verify_finite.py
```

The program checks additive reconstruction and proper-observation distributions
through eight shares, exact profile ranks through seven participants, affine
normal-form examples, dyadic counting, majority decoding, and all four-participant
monotone access families with unauthorized empty coalition.

These finite tests do not certify genericity, an infinite universal oracle
quantifier, cone-avoiding compactness, a jump bound, or mathematical novelty.
The article's proofs, rather than the tests, establish the infinite conclusions
from the two stated published inputs.
