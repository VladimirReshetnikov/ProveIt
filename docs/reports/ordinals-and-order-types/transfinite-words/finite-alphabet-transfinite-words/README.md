# Exact maximal order types of finite-alphabet transfinite words

Research manuscript prepared for Vladimir Reshetnikov, September 19, 2026.

## Result

For a finite poset P with at least two elements, let W_k(P) consist of words
of ordinal length less than omega^k, ordered by subsequence embedding, with
mutually embeddable words identified. Let N_k(P) count its indecomposable
classes. The manuscript gives a complete claimed proof of

    o(W_k(P)) = omega^(omega^(N_k(P)-1)).

The finite atom poset I_k(P) is constructed canonically. Its cardinalities
satisfy N_1(P)=|P| and N_{k+1}(P)=|P|+J(I_k(P))-1, where J counts all order
ideals, including empty.

In particular, for k=2 the answer is omega^(omega^(|P|+J(P)-2)). For the
binary antichain it is omega^(omega^4); for the binary chain it is
omega^(omega^3). The binary antichain case answers the tightness question
as stated in Altman's arXiv:2409.03199v2, Example 3.15.

This is a proposed research solution, not an independently refereed or
machine-formalized result. Computational tests are supporting checks;
the proof is the written argument. The known finite-tree/indecomposable
correspondence is credited, not claimed as a new discovery.

## Files

- `article.pdf`: the 22-page typeset manuscript, with full proofs and references.
- `article.tex`: self-contained LaTeX source; bibliography included inline.
- `references.bib`: reusable bibliographic entries (not required to build).
- `code/atoms.py`: canonical finite atom posets, exact comparison and two ideal counters.
- `code/omega_words.py`: exact symbolic subsequence embedding below omega^2.
- `code/verify.py`: all reproducible checks and count-table generation.
- `data/atom_counts.csv`: exact counts and finite exponent parameters.
- `data/atoms_*.json`: explicit selected atom posets and order matrices.
- `data/verification.json`: completed test results, seed, and interpreter version.
- `proof_audit.md`: dependency map and fragile steps reviewed.
- `source_status.md`: source versions, specific open question, and novelty limitations.
- `build.py`: cross-platform test-and-build driver.

No third-party paper PDFs or font files are bundled.

## Reproduce the mathematics-related computations

Python 3.9 or later; standard library only. The recorded run used Python 3.13.5.

```sh
python code/verify.py --out data
python code/atoms.py --kind antichain --size 2 --k 3 --output atoms.json
python code/atoms.py --kind chain --size 2 --k 4
```

Custom alphabets are accepted with `--poset-json FILE`, using this format:

```json
{
  "labels": ["a", "b"],
  "relation": [[true, false], [false, true]]
}
```

The matrix must be the full reflexive order relation, not just cover edges.
Invalid posets are rejected. Node materialization has a default cap of 5,000
atoms; change `--cap` deliberately. Counting can still be exponential.

The CSV's `constructed` field records whether the actual atom poset for that
row was materialized during table generation. A terminal row with `False`
is still an exact count: it is obtained by the proved recurrence from the
preceding poset, whose ideal count was checked by two different algorithms.

## Build the PDF

A TeX installation with pdfLaTeX, New PX, AMS packages, tcolorbox, hyperref,
cleveref, and the other packages in the source preamble is required.

```sh
python build.py
```

The driver reruns checks, prefers `latexmk`, falls back to three pdfLaTeX
passes, and copies the resulting PDF to `article.pdf`. Intermediates go
into `build/`. To skip rerunning the checks, use `python build.py --skip-tests`.

Alternatively:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

## Interpreting the verification

The run checked 24 labelled alphabets on at most three elements and 72
associated bounded-height atom posets, with 87 agreements between two ideal
counters and 64 brute-force ideal checks. It also checked 1,922 marker pairs,
10,000 equal-block pairs, 18,000 separator pairs, 625 singleton length pairs,
and two absorption controls. These are exact finite or symbolic computations,
not finite truncations of omega and not a formal verification of the theorem.

The full theorem depends on the classical maximal-order-type product and
residual calculus, Higman's wqo theorem, and the written cofinality and
separator arguments. The one-letter answer is omega^k and is intentionally
excluded from the main formula for k >= 2.
