# Guarded periodic blocks and maximal order types below omega squared

This archive accompanies the research article `article.pdf`. The editable
LaTeX source, exact symbolic algorithms, and executed test results are included.

## The selected problem

Harry Altman, *Bounding finite-image sequences of length omega^k*,
arXiv:2409.03199v2 (10 March 2026), Example 3.15, printed page 10, leaves
unverified whether the upper bound omega^(omega^4) is sharp for words of
length **strictly less than omega^2** on the two-element antichain.

The manuscript presents a candidate proof that the bound is sharp and a
stronger finite-poset formula. With n = |X| >= 2 and J(X) the downward-closed
subsets of X, including empty and full,

    o(s_{omega^2}(X)) = omega^(omega^(n + |J(X)| - 2)).

The empty alphabet has type 1. The one-letter alphabet has type omega^2;
the displayed formula must NOT be applied to that exception.

Embeddings are strictly increasing on ordinal positions and monotone on
labels. Non-strict index maps define a different problem.

## Research status

This is a proposed research solution with a complete written argument. It has
not been peer reviewed or formalized in a proof assistant. Its novelty has
not been certified by an exhaustive literature review. The specific
unverified example was checked in the cited March 2026 source. The article
separates established inputs from its guarded-product argument.

The code does not establish the transfinite theorem by enumeration. It tests
finite symbolic representatives of actual transfinite words, relying on the
abstraction proved in the article. There is no replacement of omega by a
large finite number, and no numerical estimation of ordinal values.

## Files

- `article.tex`: complete manuscript, with embedded bibliography.
- `article.pdf`: compiled, typeset article.
- `ordinal_words.py`: finite posets, recurrent ideals, exact token comparators,
  normalization, guard maps, and product encodings.
- `verify.py`: exhaustive and seeded checks plus negative controls.
- `verification_results.json`: output from the executed default run.
- `finite_posets.csv`: all 50 naturally labelled posets through size four,
  their ideal counts, and the exponents given by the main formula.
- `build.sh`: three-pass LaTeX build.
- `README.md`: this file.

## Reproduce the calculations

Requires Python 3.10 or later. Only the standard library is used.

```sh
python verify.py
```

This recreates `verification_results.json` and `finite_posets.csv` beside
the script. It checks 892,159 ordered-pair test cases, with no mismatches
in the supplied run, and three negative controls. The recorded runtime is
machine-dependent. To save new results separately:

```sh
python verify.py --output-dir rerun --seed 17 --samples 1000
```

The default seed is 20260919. `--pair-bound 4` is the default exhaustive
binary expression bound. Increasing it grows the pair enumeration quickly.

The 50-poset enumeration is of **naturally labelled** orders, meaning every
strict comparison goes from a smaller integer label to a larger one. These
are not all labelled posets. Every unlabelled isomorphism type of size at
most four is represented, with possible repeated isomorphism types.

## Use the symbolic comparator

```python
from ordinal_words import Poset, letter, omega, embeds, normalize

X = Poset.antichain(2)
# Masks: {0}=1, {1}=2, {0,1}=3.
# Each omega(mask) is a genuine infinite periodic segment.
u = (letter(1), omega(1), letter(0), letter(1))
v = (omega(3), letter(1), omega(1), letter(1))

X.validate_word(u)
X.validate_word(v)
assert embeds(X, u, v)
print(normalize(u))
```

The iterative comparator assumes valid input words; call `validate_word`
on externally supplied data. For a fixed alphabet, it runs in linear time
in the two token-list lengths. The recursive dynamic program is an
independent implementation for testing moderate-sized expressions, not the
recommended comparator for very long lists.

Ideal masks denote downward-closed sets, not necessarily literal sets of
recurrent labels. A token for D repeats the maximal elements of D. For a
chain 0<1, the full-ideal token is equivalent to the constant word 1^omega.

## Build the PDF

Requires a TeX installation with `pdflatex`, `newpxtext`, `newpxmath`,
`amsmath`, `amsthm`, `mathtools`, `microtype`, `booktabs`, `enumitem`,
`fancyhdr`, `listings`, `hyperref`, `aliascnt`, and `cleveref`, among the usual base
packages. A normal full TeX Live installation provides these.

```sh
sh build.sh
```

Alternatively:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Three passes stabilize the table of contents and page references on a clean
build. The precompiled PDF is supplied, so TeX is not needed to read it.
No font files are distributed.

## Mathematical audit priorities

The main mechanism is the equivalence

    Phi_m(u_0,...,u_m) <= Phi_m(v_0,...,v_m)
        iff every u_i <= v_i.

For a new proper recurrent ideal D, use the guard u -> u a with a outside D.
For the new full ideal, use u -> u a c_R, where R is an earlier proper
nonempty ideal and a is outside R. Insert ideals in increasing cardinality.
The latter guard has nonzero limit length, so it cannot leak into a finite
prefix of a synchronized target separator.

The case with full support as the ONLY allowed recurrent ideal is an
essential exception: its maximal type is H_n * omega, not H_(n+1), where
H_n = omega^(omega^(n-1)). See the full proof in the article.

External mathematical inputs are the finite Higman maximal-order-type
formula and classical maximal-linear-extension theory. The main proof uses
an explicit lexicographic linear extension of a Cartesian power, not an
unjustified formula about arbitrary lexicographic products of partial orders.

The optional exact-length section additionally uses the classical natural
sum and natural product identities for maximal order types. It is not
needed for the solution to the two-letter problem.
