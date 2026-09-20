# Synchronizing Dżyga's Automata by a Cyclic Retract

Research draft prepared for Vladimir Reshetnikov, 20 September 2026.
The manuscript and accompanying programs were developed in this ChatGPT session.

## Main mathematical result

For the Figure-3-complete automaton A_k in Conjecture 8 of Marek Szykuła's
2026 survey, put r = k+4, c = ab, p = c^r and e = a p b p c^(r-1).
Then

    R_k = p (e c^(r-1))^(r-2) e

sends every state to q_2 for every integer k >= 1. Its expanded length is

    8 k^2 + 54 k + 92 = (8/9)n^2 + (22/3)n + 16,  n = 3k+6.

The proof does not depend on the finite computations. It uses a cyclic
retraction and two projected reflections, whose discrepancy gives one
adjacent merger. A separate theorem shows that shortening the reflected
tail by one state gives a nonsynchronizing automaton with a dihedral
permutation quotient.

This settles the synchronization clause in the stated model, not the full
numerical threshold conjecture. The universal lower bound tau(q_0) >= 4k+8
is NOT proved here. The all-parameter upper bound and corrected short
merging word are prior results, credited in the manuscript. Independent
human review and an exhaustive priority assessment have not been performed.

## Contents

- `article.pdf`: the complete mathematical article.
- `article.tex`: self-contained LaTeX source, with embedded bibliography.
- `references.bib`: reusable bibliography entries (not needed to compile).
- `code/automata.py`: the family, word actions and explicit reset construction.
- `code/generate_certificates.py`: reverse-BFS pair-distance generator.
- `code/verify_certificates.py`: independent local-identity certificate checker.
- `code/test_structure.py`: algebraic identity, model, word and negative checks.
- `certificates/k_0001.json.gz` through `k_0200.json.gz`: all exact distances.
- `results/summary.csv`: full parameter-by-parameter numerical results.
- `results/generation.txt`, `verification.txt`, `structure_tests.txt`: run logs.
- `PROOF_AUDIT.md`: precise claim/proof/status map and limitations.
- `SOURCE_NOTES.md`: primary-source provenance and model conventions.
- `Makefile`: build and test commands.

## Reproduce without additional Python packages

Python 3.10 or newer is required. From this directory:

```sh
python code/test_structure.py
python code/verify_certificates.py --max-k 200
```

To regenerate all certificates and the summary:

```sh
python code/generate_certificates.py --max-k 200
python code/verify_certificates.py --max-k 200
```

The generation can be split when the execution environment has a short
per-command timeout:

```sh
python code/generate_certificates.py --max-k 150
python code/generate_certificates.py --min-k 151 --max-k 200
```

Starting at k=1 replaces the summary. Starting later appends to it; do not
append a range twice without rebuilding the summary. Existing certificate
files for generated parameters are replaced. All operations remain local.

The verifier imports neither the generator nor its automaton constructor.
It reconstructs transitions from transpositions and exceptional arrows and
checks every pair's Bellman identity. It also rejects deliberate corruptions.
This is algorithmic independence, not a separately authored or Lean-verified
checker. Code and arithmetic run on ordinary Python, not a proof assistant.

## Results of the completed runs

Exact pair distances were generated and independently checked for EVERY
k from 1 to 200, comprising 12,486,300 pair entries in total. The largest
automaton has 606 states. Throughout that range:

    tau(q_0) = 4k+8
    dist(q_0,q_1) = 4k+9
    optimal partners of q_0 = {q_2, q_(2k+5)}

The candidate diameter formula also holds on that finite range:

    (5k^2+32k+47)/4,  k odd;
    (5k^2+34k+44)/4,  k even.

Structural formulas were tested for k=1..300 and k=500,1000,10000. The large
cases use composition and exponentiation of transformations; they do not
expand the reset word. The reset words for k=1..10 were expanded and checked
by two evaluators. The universal proofs are in the article and do not
extrapolate from any of these finite ranges.

## Rebuild the PDF

A standard TeX Live installation with NewTX, amsthm, mathtools, microtype,
tcolorbox, listings, hyperref and cleveref is sufficient:

```sh
pdflatex -halt-on-error article.tex
pdflatex -halt-on-error article.tex
pdflatex -halt-on-error article.tex
```

Alternatively run `make pdf`. No network access, BibTeX invocation or
nonstandard Python package is needed. The included bibliography database
is for reuse; the article itself contains its bibliography.

## Important conventions

Words are read left to right. For arrays f and g, compose(f,g)[q] = g[f[q]].
The missing printed transitions are completed from the source's Figure 3:
b(0)=1, and the nonloop transition at the last state returns to its predecessor.
Cycle indices modulo r are different from original state labels. The word
c^(r-1) is an inverse cycle rotation only on the retract, NOT on all states.

The CSV's explicit_reset_length column is NOT a computed shortest reset
threshold. All lower-bound formula checks in the CSV are finite claims.
