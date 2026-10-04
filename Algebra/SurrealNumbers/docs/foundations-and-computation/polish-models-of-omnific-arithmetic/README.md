# Polish Presburger Arithmetic inside the Omnific Integers

**An affirmative construction for Glazer's Question 2, effective Baire-space models, and structural obstructions**

Research manuscript prepared for Vladimir Reshetnikov, October 3, 2026.

## Main result

The positive cone of the lexicographically ordered additive group

    G_R = R lex Z,  1 = (0,1)
    M_R = (R_{>0} x Z) union ({0} x N)

is a model of the full first-order theory of `(N;0,1,+,<)`. Give it the
subspace topology from the usual real line times the discrete integers.
This is an uncountable, locally compact, perfect Polish space, and addition
is continuous. The construction answers Question 2 as stated on page 8 of
Elliot Glazer, *A Topological Tennenbaum Theorem*, arXiv:2311.13699v1.

Replacing R by the lexicographically ordered group Q^N, with **discrete**
rational coordinates, gives an explicit Baire-space model with Type-2
computable addition and standard Euclidean division. The manuscript
provides full proofs, additive embeddings into Conway's omnific integers,
structural results, and ten further research questions.

## Files

- `polish_presburger_glazer.pdf`: the 24-page article.
- `polish_presburger_glazer.tex`: self-contained LaTeX source, including references.
- `polish_presburger.py`: exact arithmetic, all-valid Baire codes, addition,
  division, and a limit approximation to comparison.
- `verify.py`: deterministic verification of finite instances and stream prefixes.
- `verification_results.json`: executed results (17,930 checks, all passed).
- `CLAIM_LEDGER.md`: theorem locations and evidence boundaries.
- `SOURCES.md`: primary sources, repository snapshot, and priority limitations.
- `build.sh`: three-pass PDF build.
- `SHA256SUMS`: checksums for the other delivered files.

## Reproduce the computations

Use Python 3.10 or later; no third-party Python packages are required.

```sh
python verify.py
```

The script writes `verification_results.json`. Its randomness is seeded
with `231113699`. The delivered run used Python 3.13.5. Tests cover exact
finite-rank arithmetic and finite prefixes of the Baire operations; they
are not a formal verification of infinite-stream semantics or theorems.

The Baire interface represents an infinite sequence by a callable
`code(i)` returning a natural number. Every total such code is valid.
The low-level `encode` routine has a positive-cone precondition; the
public arithmetic operations preserve it. Comparison is approximated
with at most one change, not decided by a terminating equality oracle.

## Build the article

Use a LaTeX distribution with `pdflatex` and the packages listed in the
source preamble, including `newpxtext`, `newpxmath`, `tcolorbox`, and
`cleveref`. No external bibliography database or bibliography program is
needed.

```sh
sh build.sh
```

The delivered PDF was built in three passes and checked for unresolved
references and layout warnings. It has 24 A4 pages. The archive does not
include font files or build intermediates.

## Proof, priority, and formalization status

The article supplies mathematical proofs. It is an AI-assisted,
unrefereed research manuscript, not an independently certified publication.
It establishes an affirmative construction for the cited question **as
written**; the searches performed do not establish bibliographic priority.
Classical Z-group/Presburger elimination and basic topology are explicitly
identified as background, not claimed as new.

No new Lean or Rocq formalization is included. The ProveIt connection is
a precise mathematical and implementation interface, not a claim that the
repository already verifies this manuscript. The inspected integer Cooper
lemmas are correct on `Int`; generalizing them to nonstandard groups needs
full invariance under congruence classes, not just a standard one-step shift.

The omnific embeddings are additive and order-preserving, not ring
embeddings. Neither example admits **any** unital semiring multiplication
with the displayed addition and unit. No result here contradicts Glazer's
obstruction for stronger arithmetic, and his separate Question 1 is not
answered.
