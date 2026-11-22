# Approximate Brouwer fixed points in iPRA

Read **brouwer.pdf** for the complete argument. Theorem 1 gives a rational approximate fixed point for a uniformly presented self-map of the standard simplex. The construction works uniformly in the dimension and in the requested precision. Section 5 proves the cube and closed Euclidean ball versions. Sections 6 and 7 give the arithmetic sentence, induction invariants, Lean results, and remaining formalization work.

## Contents

| File | Purpose |
| --- | --- |
| `brouwer.tex`, `parity.tex`, `formalization.tex` | Editable article, explicit Sperner incidence proof, and formalization plan |
| `figure.pdf`, `figure.py` | Vector illustration of the two-dimensional certificate and its optional regeneration script |
| `lean/Brouwer.lean`, `lean/README.md` | Standalone Lean companion, examples, and exact scope of the checked theorems |
| `code/brouwer.py` | Finite simplex search and local certificate checker |
| `code/named_simplex.py` | Precision-controlled search using a supplied evaluator and modulus, with a checker for any requested later stage |
| `code/cube.py` | Direct cubical method and a rational disk example |
| `code/test_brouwer.py` | Eight reproducible finite tests |
| `verification.txt` | Compiler version, dependency audit, and test results from this build |

## Reproduce

From the extracted directory, compile the article with a standard TeX Live installation.

```sh
pdflatex -halt-on-error brouwer.tex
pdflatex -halt-on-error brouwer.tex
```

The included PDF figure is sufficient for compilation. Regenerating it with `python figure.py` also requires Matplotlib. The other Python programs use only the standard library.

```sh
python3 -B code/test_brouwer.py
python3 -B code/brouwer.py --dimension 2 --mesh 5 --map rotate
python3 -B code/named_simplex.py --dimension 2 --bits 1 --tail 3 4 8
python3 -B code/cube.py --mesh 9 --ball
lean lean/Brouwer.lean
```

Use Lean 4.19.0 for the standalone check. Its file imports `Std` and can be checked outside a Lake project. The paper cites the ProveIt object theory at commit `022dfb4c54c22782f927a903f25bcf6491b7eba2`; that upstream project uses Lean 4.32.0.

## Using a different evaluator

Add `code/` to the Python import path and call `find_named_witness(dimension, bits, evaluate, modulus)` from `named_simplex`. The callable `evaluate(x,s)` takes a tuple of rational barycentric coordinates and a natural stage and returns a simplex point, using integers or `fractions.Fraction` coordinates. Supply `modulus(m)` with the convention in equation (1). The returned object's `.anchor` is the rational witness and `.cell` gives the certificate. Pass the object, the same evaluator, and a stage at least `bits + 2` to `check_named_tail` to verify the relevant finite inequalities at that stage. The proof covers every such stage when the evaluator satisfies its contract. The mathematical iPRA claim applies to PR terms implementing the supplied routines.

The companion verifies the geometric and numerical bounds for a successful search. The dimension-uniform parity proof and the full derivation in embedded iPRA are given as a mathematical proof and formalization plan. The article identifies the existing fixed-dimensional cubical Sperner derivation that can be reused for that route.
