# The constructive hairy ball theorem in iPRA

Open **hairy_ball.pdf** for the manuscript. Its main numerical theorem gives a primitive recursive approximate-zero search for every even sphere and a PR-presented field with a uniform modulus. Section 5 gives a rational unit vector on the round sphere. Section 6 includes a single Lipschitz field on the 2-sphere for which neither exact pole has a primitive recursive fast name.

## Build the paper

Use a standard TeX Live installation with pdfLaTeX.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error hairy_ball.tex
```

The main source loads the files in `sections/`. Bibliographic references are embedded in the source.

## Check the Lean files

Use Lean 4.19.0 and its bundled standard library. No Lake project or downloads are required if this toolchain is installed.

```sh
lean code/HairyBall.lean
lean code/NamedField.lean
```

The former checks bounded search, the general antipodal sign, and the octahedral prism and cycle calculations. The latter defines the field contract, mesh-independent search and its target, and proves assembly conditional on the grid-hit and tail-bound lemmas. Section 7 gives proofs for the remaining targets and the implementation plan for a full Lean and embedded-iPRA derivation.

## Run the exact examples

Use Python 3.10 or later with the standard library.

```sh
python3 code/hairy_ball.py --self-test
python3 code/hairy_ball.py --denominator 16 --tol 2/5 --degree-demo
python3 code/round_witness.py --test
python3 code/round_witness.py -a 12 1/2 1/3 1/6
```

The grid example uses a rational projection field and a denominator small enough for inspection. The proof supplies the general grid bound from a modulus. The rounding example returns rational coordinates with exact squared norm one, and checks its error relative to the exact unit direction using rational sign comparisons. `verification.txt` records the results of the included checks.
