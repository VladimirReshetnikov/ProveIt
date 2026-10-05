# A007716 asymptotics and inverses

This package contains a self-contained research article on nonnegative integer matrices modulo separate row and column permutations, equivalently bipartite multigraphs with distinguished shores and a fixed number of edges.

## Results

- A relative leading equivalent with its nonnegligible parallel-edge factor.
- A complete fixed-order algebraic expansion with rational Lambert-W coefficient functions and a finite profile algorithm.
- Two explicit corrections, reconstructed separately by exact symbolic methods.
- Explicit smooth inverse models and qualified integer-threshold rounding.
- Non-P-recursiveness and a fixed-number-of-shores comparison.

The claims are ordinary mathematical proofs, not formal verification or an effective numerical-onset certificate. The article records the primary-literature scope and remaining questions.

## Contents

- `article.tex`, `article.pdf`: editable source and compiled article.
- `build_local.sh`: optional local TeX build helper. A standard LaTeX installation with the listed packages can also compile the source normally.
- `code/`: exact producer and independent verification scripts with their recorded JSON outputs.
- `verification.md`: the meaning and scope of the checks.
- `SHA256SUMS`: integrity manifest for packaged files.

## Replay

Python 3 and SymPy are required for the symbolic scripts (tested with Python 3.12.14 and SymPy 1.14.0). The cycle-type scripts use only the standard library. Run from the extracted package directory:

```
python -O code/check_cycle_formula.py
python -O code/check_invariant_partitions.py
python -O code/check_independent.py
python -O code/compute_first_two.py
python -O code/reconstruct_Q2.py
```

All acceptance conditions use explicit exceptions, so optimization does not disable them. Outputs are written beside each script. No network access, external software service or repository checkout is needed for replay.

The exact code is regression evidence and an implementation of the finite coefficient algorithm. The analytic estimates and remainders are proved in the article.
